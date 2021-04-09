// © 2021, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::encoder::Encoder;
use crate::encoder::errors::EncodingResult;
use crate::encoder::fn_signatures::{extract_fn_sig, ExtractedFnSig, ExtractedFnKind};
use prusti_common::vir;
use rustc_middle::ty;
use rustc_hir::def_id::DefId;
use std::collections::HashMap;

pub enum SpecFunctionKind {
    Pre,
    Post,
    HistInv,
}

impl std::fmt::Display for SpecFunctionKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", match self {
            SpecFunctionKind::Pre => "pre",
            SpecFunctionKind::Post => "post",
            SpecFunctionKind::HistInv => "histinv",
        })
    }
}

fn encode_spec_func_name<'p, 'v: 'p, 'tcx: 'v>(
    encoder: &'p Encoder<'v, 'tcx>,
    def_id: DefId,
    kind: SpecFunctionKind
) -> String {
    encoder.encode_item_name_prefixed(def_id, &format!("sf_{}", kind))
}

#[derive(Clone)]
struct SpecFunctionSet {
    /// Whether the first argument of the specification functions represents
    /// the "self" argument of the closure or type parameter.
    /// TODO: generalise to e.g. instance functions; closure self should not be
    /// a special argument, it is only special in that it is mutable. Any
    /// mutable argument in the call should eventually be duplicated for the
    /// pre- and poststate.
    has_self: bool,

    /// Precondition specification function. Arguments:
    /// - (if has_self) closure self
    /// - all call arguments (snapshot)

    pre: vir::Function,

    /// Postcondition specification function. Arguments:
    /// - (if has_self) old closure self
    /// - all old call arguments (snapshot)
    /// - returned value (snapshot)
    /// - (if has_self) new closure self
    /// TODO: arguments in the poststate
    post: vir::Function,

    // hist_inv: vir::Function,
}

pub struct SpecFunctionEncoder {
    encoded: HashMap<DefId, SpecFunctionSet>,
    // encoded_dyn: // TODO: sets for signatures (Box<dyn Fn...>)
}
impl SpecFunctionEncoder {
    pub fn new() -> Self {
        Self {
            encoded: HashMap::new(),
        }
    }

    /// Returns a list of Viper functions needed by the encoded snapshots.
    pub fn get_viper_functions(&self) -> Vec<vir::Function> {
        let mut funcs = vec![];
        for sf_set in self.encoded.values() {
            funcs.push(sf_set.pre.clone());
            funcs.push(sf_set.post.clone());
        }
        funcs
    }

    pub fn encode_spec_call_pre<'p, 'v: 'p, 'tcx: 'v>(
        &mut self,
        encoder: &'p Encoder<'v, 'tcx>,
        cl_type: ty::Ty<'tcx>,
        args: Vec<vir::Expr>,
    ) -> EncodingResult<vir::Expr> {
        let spec_funcs = self.encode_spec_functions(encoder, cl_type)?;
        Ok(spec_funcs.pre.apply(args))
    }

    pub fn encode_spec_call_post<'p, 'v: 'p, 'tcx: 'v>(
        &mut self,
        encoder: &'p Encoder<'v, 'tcx>,
        pre_label: &str,
        cl_type: ty::Ty<'tcx>,
        args: Vec<vir::Expr>,
        ret: vir::Expr,
    ) -> EncodingResult<vir::Expr> {
        let spec_funcs = self.encode_spec_functions(encoder, cl_type)?;
        let mut app_args = args.iter()
            .map(|arg| vir::Expr::labelled_old(pre_label, arg.clone()))
            .collect::<Vec<_>>();
        app_args.push(ret);
        if spec_funcs.has_self {
            app_args.push(args[0].clone());
        }
        let post_app = spec_funcs.post.apply(app_args);
        Ok(post_app)
    }

    pub fn encode_spec_entailment<'p, 'v: 'p, 'tcx: 'v>(
        &mut self,
        encoder: &'p Encoder<'v, 'tcx>,
        once: bool,
        cl_expr: &vir::Expr,
        cl_type: ty::Ty<'tcx>,
        qargs_pre: Vec<vir::LocalVar>,
        qargs_post: Vec<vir::LocalVar>,
        qret_post: vir::LocalVar,
        encoded_pre: vir::Expr,
        encoded_post: vir::Expr,
    ) -> EncodingResult<vir::Expr> {
        let spec_funcs = self.encode_spec_functions(encoder, cl_type)?;
        let cl_type_vir = encoder.encode_type(cl_type)?;

        // Encode the precondition conjunct of the form:
        // forall closure, args... ::
        //   <preconditions(closure, args...)> => sf_pre(closure, args...)
        // This asserts the weakening of the precondition.
        // If this is a single-call entailment (|=!) or [cl_type] is [FnPtr],
        // we do not need to quantify over the closure.
        let mut qvars_pre = qargs_pre.clone();
        if !once {
            qvars_pre.insert(0, vir::LocalVar::new("_cl".to_string(), cl_type_vir.clone()));
        }
        let mut sf_pre_args = qvars_pre.iter()
            .cloned()
            .map(vir::Expr::local)
            .collect::<Vec<_>>();
        if once {
            sf_pre_args.insert(0, cl_expr.clone());
        }
        let pre_app = spec_funcs.pre.apply(sf_pre_args);
        let pre_conjunct = vir::Expr::forall(
            qvars_pre.clone(),
            vec![vir::Trigger::new(vec![pre_app.clone()])],
            vir::Expr::implies(
                encoded_pre.clone(),
                pre_app,
            ),
        );

        // Encode the postcondition conjunct of the form:
        // forall closure_pre, closure_post, args..., result ::
        //   <preconditions(closure_pre, args...)> =>
        //     (sf_post(closure, closure_post, args..., result) =>
        //       <postconditions(closure_pre, closure_post, args..., result)>)
        // This asserts the strengthening of the postcondition.
        // If this is a single-call entailment (|=!) we do not need to quantify
        // over the closure pre-state.
        let mut qvars_post: Vec<_> = qargs_post.clone();
        if !once {
            qvars_post.insert(0, vir::LocalVar::new("_cl_pre".to_string(), cl_type_vir.clone()));
        }
        qvars_post.push(qret_post);
        qvars_post.push(vir::LocalVar::new("_cl_post".to_string(), cl_type_vir.clone()));
        let mut sf_post_args = qvars_post.iter()
            .cloned()
            .map(vir::Expr::local)
            .collect::<Vec<_>>();
        if once {
            sf_post_args.insert(0, cl_expr.clone());
        }
        let encoded_pre_renamed = (0 .. qargs_pre.len())
            .fold(encoded_pre, |e, i| {
                e.replace_place(&vir::Expr::local(qargs_pre[i].clone()),
                                &vir::Expr::local(qargs_post[i].clone()))
            });
        let post_app = spec_funcs.post.apply(sf_post_args);
        let post_conjunct = vir::Expr::forall(
            qvars_post.clone(),
            vec![vir::Trigger::new(vec![post_app.clone()])],
            vir::Expr::implies(
                encoded_pre_renamed,
                vir::Expr::implies(
                    post_app,
                    patch_old_views(
                        encoded_post,
                        qvars_post[0].clone(),
                        qvars_post[qvars_post.len() - 1].clone(),
                    ),
                ),
            ),
        );

        Ok(vir::Expr::and(pre_conjunct, post_conjunct))
    }

    fn encode_spec_functions<'p, 'v: 'p, 'tcx: 'v>(
        &mut self,
        encoder: &'p Encoder<'v, 'tcx>,
        fn_type: ty::Ty<'tcx>,
    ) -> EncodingResult<SpecFunctionSet> {
        let fn_sig = extract_fn_sig(encoder, fn_type);

        // were the specification functions already encoded?
        if let Some(sf_set) = self.encoded.get(&fn_sig.def_id) {
            return Ok(sf_set.clone());
        }

        // otherwise, encode and store
        let sf_set = SpecFunctionSet {
            has_self: matches!(fn_sig.kind, ExtractedFnKind::Closure | ExtractedFnKind::Param),
            pre: self.encode_pre_spec_func(encoder, &fn_sig)?,
            post: self.encode_post_spec_func(encoder, &fn_sig)?,
        };
        self.encoded.insert(fn_sig.def_id, sf_set.clone());

        Ok(sf_set)
    }

    // TODO: SFs should have a body for non-closure functions (FnPtrs), since
    // there is no Aggregate assignment like with closures; on the other hand,
    // can this correctly handle generics?

    fn encode_pre_spec_func<'p, 'v: 'p, 'tcx: 'v>(
        &mut self,
        encoder: &'p Encoder<'v, 'tcx>,
        fn_sig: &ExtractedFnSig<'tcx>,
    ) -> EncodingResult<vir::Function> {
        // Closure and Param functions will already have the instance as their
        // first argument in inputs.
        let formal_args = fn_sig.inputs
            .iter()
            .map(|arg_ty| encoder.encode_snapshot_type(arg_ty))
            .collect::<Result<Vec<_>, _>>()?;

        Ok(vir::Function {
            name: encode_spec_func_name(encoder, fn_sig.def_id, SpecFunctionKind::Pre),
            formal_args: formal_args.iter()
                .enumerate()
                .map(|(num, ty)| vir::LocalVar::new(format!("_{}", num), ty.clone()))
                .collect(),
            return_type: vir::Type::Bool,
            pres: vec![],
            posts: vec![],
            body: None,
        })
    }

    fn encode_post_spec_func<'p, 'v: 'p, 'tcx: 'v>(
        &mut self,
        encoder: &'p Encoder<'v, 'tcx>,
        fn_sig: &ExtractedFnSig<'tcx>,
    ) -> EncodingResult<vir::Function> {
        let mut formal_args = fn_sig.inputs
            .iter()
            .map(|arg_ty| encoder.encode_snapshot_type(arg_ty))
            .collect::<Result<Vec<_>, _>>()?;

        formal_args.push(encoder.encode_snapshot_type(fn_sig.output)?); // return
        formal_args.push(encoder.encode_snapshot_type(fn_sig.ty)?); // cl_post

        Ok(vir::Function {
            name: encode_spec_func_name(encoder, fn_sig.def_id, SpecFunctionKind::Post),
            formal_args: formal_args.iter()
                .enumerate()
                .map(|(num, ty)| vir::LocalVar::new(format!("_{}", num), ty.clone()))
                .collect(),
            return_type: vir::Type::Bool,
            pres: vec![],
            posts: vec![],
            body: None,
        })
    }
}

fn patch_old_views(
    expr: vir::Expr,
    cl_pre: vir::LocalVar,
    cl_post: vir::LocalVar,
) -> vir::Expr {
    struct OldPatcher {
        cl_pre: vir::Expr,
        cl_post: vir::Expr,
    };
    // old(**... cl_pre) -> cl_post
    impl vir::ExprFolder for OldPatcher {
        fn fold_labelled_old(
            &mut self,
            label: String,
            body: Box<vir::Expr>,
            pos: vir::Position
        ) -> vir::Expr {
            // TODO: check if label == ""?
            (*body).replace_place(&self.cl_pre, &self.cl_post)
        }
    }
    vir::ExprFolder::fold(&mut OldPatcher {
        cl_pre: vir::Expr::local(cl_pre),
        cl_post: vir::Expr::local(cl_post),
    }, expr)
}
