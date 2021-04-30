


    // ---- ALSO OLD -----

    /*
    fn encode_spec_entailment(
        &self,
        closure: &typed::Expression,
        cl_type: ty::Ty<'tcx>,
        vars: &typed::SpecEntailmentVars<'tcx>,
        once: bool,
        pres: &Vec<typed::Assertion<'tcx>>,
        posts: &Vec<typed::Assertion<'tcx>>,
        def_id: &DefId,
    ) -> SpannedEncodingResult<vir::Expr> {
        let tcx = self.encoder.env().tcx();
        let span = tcx.def_span(*def_id); // TODO: span of assertion?
        let cl_expr = self.encode_expression(closure)?;

        let is_closure;
        match cl_type.kind() {
            ty::TyKind::Closure(def_id, substs) => {
                is_closure = true;
            }
            ty::TyKind::FnDef(def_id, _) => {
                is_closure = false;
            }
            _ => unreachable!(),
        }

        let fn_sig = self.extract_fn_sig(encoder, cl_type);

        let encoded_pres = pres.iter()
            .map(|x| self.encode_assertion(x))
            .collect::<Result<Vec<_>, _>>()?
            .into_iter()
            .conjoin();
        let encoded_posts = posts.iter()
            .map(|x| self.encode_assertion(x))
            .collect::<Result<Vec<_>, _>>()?
            .into_iter()
            .conjoin();

        let forall_pre_id = format!("{}_{}", vars.spec_id, vars.pre_id);
        let forall_post_id = format!("{}_{}", vars.spec_id, vars.post_id);

        let spec_funcs = self.encode_spec_funcs(encoder, cl_type)?;

        // Encode call arguments as forall variables.
        let qargs_pre = vars.args
            .iter()
            .map(|(arg, arg_ty)| self.encode_forall_arg(*arg, arg_ty, &forall_pre_id))
            .collect::<Vec<_>>();
        // TODO: mutable arguments should be duplicated (pre/post state)
        let qargs_post = vars.args
            .iter()
            .map(|(arg, arg_ty)| self.encode_forall_arg(*arg, arg_ty, &forall_post_id))
            .collect::<Vec<_>>();

        // Encode the precondition conjunct of the form:
        // forall closure, args... ::
        //   <preconditions(closure, args...)> => sf_pre(closure, args...)
        // This asserts the weakening of the precondition.
        // If this is a single-call entailment (|=!) or [cl_type] is [FnPtr],
        // we do not need to quantify over the closure.
        let mut qvars_pre = qargs_pre.clone();
        if is_closure && !once {
            qvars_pre.insert(0, vir::LocalVar::new("_cl".to_string(), cl_type));
        }
        let mut sf_pre_args = qvars_pre.iter()
            .cloned()
            .map(vir::Expr::local)
            .collect::<Vec<_>>();
        if is_closure && once {
            sf_pre_args.insert(0, cl_expr.clone());
        }
        let pre_app = vir::Expr::func_app(
            spec_funcs.pre.name.to_string(),
            sf_pre_args,
            spec_funcs.pre.formal_args.clone(),
            vir::Type::Bool,
            vir::Position::default(),
        );
        let pre_conjunct = vir::Expr::forall(
            qvars_pre.clone(),
            vec![vir::Trigger::new(vec![pre_app.clone()])],
            vir::Expr::implies(
                encoded_pres.clone(),
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
        // over the closure pre-state. If [cl_type] is [FnPtr], we do not need
        // to quantify over the post-state either.
        let mut qvars_post: Vec<_> = qargs_post.clone();
        if is_closure && !once {
            qvars_post.push(vir::LocalVar::new("_cl_pre".to_string(), cl_type));
        }
        qvars_post.push(vir::LocalVar::new(
            format!("_{}_forall_{}", vars.args.len() + 2, &forall_post_id),
            self.encoder.encode_type(fn_sig.output()).with_span(span)?,
        ));
        if is_closure {
            qvars_post.insert(0, vir::LocalVar::new("_cl_post".to_string(), cl_type));
        }
        let mut sf_post_args = qvars_post.iter()
            .cloned()
            .map(vir::Expr::local)
            .collect::<Vec<_>>();
        if is_closure && once {
            sf_post_args.insert(0, cl_expr.clone());
        }
        let encoded_pres_renamed = (0 .. qargs_pre.len())
            .fold(encoded_pres, |e, i| {
                e.replace_place(&vir::Expr::local(qargs_pre[i].clone()),
                                &vir::Expr::local(qargs_post[i].clone()))
            });
        let post_app = vir::Expr::func_app(
            spec_funcs.post.name.to_string(),
            sf_post_args,
            spec_funcs.post.formal_args.clone(),
            vir::Type::Bool,
            vir::Position::default(),
        );
        let post_conjunct = vir::Expr::forall(
            qvars_post.clone(),
            vec![vir::Trigger::new(vec![post_app.clone()])],
            vir::Expr::implies(
                encoded_pres_renamed,
                vir::Expr::implies(
                    post_app,
                    encoded_posts,
                ),
            ),
        );

        Ok(vir::Expr::and(pre_conjunct, post_conjunct))
    }*/

    // ---- OLD -----

    /*
    pub fn new(
        encoder: &'p Encoder<'v, 'tcx>,
        procedure: &'p Procedure<'p, 'tcx>,
    ) -> Self {
        let proc_def_id = procedure.get_id();
        Self {
            env: encoder.env(),
            encoder: encoder,
            procedure: procedure,
            span: procedure.get_span(),
            proc_def_id,
            is_closure: encoder.env().tcx().is_closure(proc_def_id),
            mir: procedure.get_mir(),
            mir_encoder: MirEncoder::new(encoder, procedure.get_mir(), proc_def_id),
        }
    }

    pub fn encode(&self) -> SpannedEncodingResult<Vec<vir::Function>> {
        let specs = if let Some(specs) = self.encoder.get_procedure_specs(self.proc_def_id) {
            specs
        } else {
            return Ok(vec![]);
        };

        let contract = compute_procedure_contract(
            self.proc_def_id,
            self.encoder.env().tcx(),
            typed::SpecificationSet::Procedure(specs),
            Some(&self.encoder.current_tymap())
        ).with_span(self.span)?.to_def_site_contract();

        let closure_snapshot = if self.is_closure {
            Some(self.encoder
                .encode_snapshot_type(self.mir.local_decls[1usize.into()].ty)
                .with_span(self.span)?)
        } else {
            None
        };

        let pre_func = self.encode_pre_spec_func(&contract, closure_snapshot.clone())?;
        let post_func = self.encode_post_spec_func(&contract, closure_snapshot.clone())?;
        // let invariant_func = self.encode_invariant_func()?;

        Ok(vec![pre_func, post_func] // , invariant_func]
            .into_iter()
            .map(|func| self.encoder.patch_snapshots_function(func))
            .collect::<Result<_, _>>()
            .with_span(self.span)?)
    }

    fn encode_pre_spec_func(
        &self,
        contract: &ProcedureContract<'tcx>,
        closure_snapshot: Option<vir::Type>,
    ) -> SpannedEncodingResult<vir::Function> {
        let mut encoded_args: Vec<vir::LocalVar> = contract
            .args
            .iter()
            .map(|local| self.encode_local(local.clone().into()))
            .collect::<Result<Vec<_>, _>>()?;

        if self.is_closure {
            encoded_args[0] = vir::LocalVar::new(
                encoded_args[0].name.to_string(),
                closure_snapshot.unwrap(),
            );
        }

        let encoded_args_exprs = encoded_args
            .iter()
            .cloned()
            .map(vir::Expr::local)
            .collect::<Vec<_>>();

        let func_spec = self.encoder
           .get_procedure_specs(self.proc_def_id)
           .map_or_else(|| vec![], |specs| specs.pres)
           .iter()
           .map(|item| encode_spec_assertion(
                self.encoder,
                &item,
                None,
                &encoded_args_exprs,
                None,
                true,
                None,
            ))
            .collect::<Result<Vec<_>, _>>()?;

        Ok(vir::Function {
            name: self.encode_spec_func_name(self.proc_def_id, SpecFunctionKind::Pre),
            formal_args: encoded_args,
            return_type: vir::Type::Bool,
            pres: vec![],
            posts: vec![],
            body: Some(func_spec.into_iter().conjoin()),
        })
    }

    fn encode_post_spec_func(
        &self,
        contract: &ProcedureContract<'tcx>,
        closure_snapshot: Option<vir::Type>,
    ) -> SpannedEncodingResult<vir::Function> {
        let mut encoded_args: Vec<vir::LocalVar> = contract
            .args
            .iter()
            .map(|local| self.encode_local(local.clone().into()))
            .collect::<Result<Vec<_>, _>>()?;

        if self.is_closure {
            let original_arg = encoded_args[0].clone();
            encoded_args[0] = vir::LocalVar::new(
                original_arg.name.to_string(),
                closure_snapshot.clone().unwrap(),
            );
            encoded_args.push(vir::LocalVar::new(
                format!("{}_old", original_arg.name),
                closure_snapshot.unwrap(),
            ));
        }

        let encoded_args_exprs = encoded_args
            .iter()
            .cloned()
            .map(vir::Expr::local)
            .collect::<Vec<_>>();

        // TODO: (after CAV) snapshot and duplicate any mutable argument

        let encoded_return = self.encode_local(contract.returned_value.clone().into())?;
        // encoded_args:
        // _1    - closure "self"
        // _2... - additional arguments
        // encoded return: _0

        let func_spec = self.encoder
           .get_procedure_specs(self.proc_def_id)
           .map_or_else(|| vec![], |specs| specs.posts)
           .iter()
           .map(|item| encode_spec_assertion(
                self.encoder,
                &item,
                None,
                &encoded_args_exprs,
                Some(&encoded_return.clone().into()),
                true,
                None,
            ))
            .collect::<Result<Vec<_>, _>>()?
            .into_iter()
            .map(|encoded_item| self.patch_old_access(
                encoded_item,
                &encoded_args[0],
                &encoded_args[encoded_args.len() - 1],
            ))
            .collect::<Vec<_>>();

        Ok(vir::Function {
            name: self.encode_spec_func_name(self.proc_def_id, SpecFunctionKind::Post),
            formal_args: encoded_args
                .into_iter()
                .chain(std::iter::once(encoded_return))
                .collect(),
            return_type: vir::Type::Bool,
            pres: vec![],
            posts: vec![],
            body: Some(func_spec.into_iter().conjoin()),
        })
    }
    /*
    fn encode_invariant_func(&self, contract: &ProcedureContract<'tcx>)
        -> SpannedEncodingResult<vir::Function> {

        Ok(vir::Function {
            name: self.encoder.encode_spec_func_name(self.proc_def_id,
                                                     SpecFunctionKind::HistInv),
            formal_args: vec![],
            return_type: vir::Type::Bool,
            pres: vec![],
            posts: vec![],
            body: Some(func_spec.into_iter()
                                .map(|post| SnapshotSpecPatcher::new(self.encoder).patch_spec(post))
                                .collect::<Result<Vec<vir::Expr>, _>>()
                                .with_span(self.span)?
                                .into_iter()
                                .conjoin()),
        })
    }
*/
    fn patch_old_access(&self, expr: vir::Expr, local_post: &vir::LocalVar, local_pre: &vir::LocalVar) -> vir::Expr {
        if self.is_closure {
            // TODO: do replacement for all fields -- as a field in snapshot_encoder ??? expr?
            return expr.replace_place(
                &vir::Expr::labelled_old(
                    "",
                    vir::Expr::field(
                        vir::Expr::field(
                            vir::Expr::field(
                                vir::Expr::local(local_post.clone()),
                                vir::Field::new(
                                    "f$count",
                                    vir::Type::TypedRef("i32".to_string()),
                                ),
                            ),
                            vir::Field::new(
                                "val_ref",
                                vir::Type::TypedRef("i32".to_string()),
                            ),
                        ),
                        vir::Field::new(
                            "val_int",
                            vir::Type::Int,
                        ),
                    )
                ),
                &vir::Expr::field(
                    vir::Expr::field(
                        vir::Expr::field(
                            vir::Expr::local(local_pre.clone()),
                            vir::Field::new(
                                "f$count",
                                vir::Type::TypedRef("i32".to_string()),
                            ),
                        ),
                        vir::Field::new(
                            "val_ref",
                            vir::Type::TypedRef("i32".to_string()),
                        ),
                    ),
                    vir::Field::new(
                        "val_int",
                        vir::Type::Int,
                    ),
                ),
            );
        }
        return expr;
    }

    fn encode_local(&self, local: mir::Local) -> SpannedEncodingResult<vir::LocalVar> {
        let var_name = self.mir_encoder.encode_local_var_name(local);
        let var_type = self
            .encoder
            .encode_value_or_ref_type(self.mir_encoder.get_local_ty(local))
            .with_span(self.span)?;
        Ok(vir::LocalVar::new(var_name, var_type))
    }*/