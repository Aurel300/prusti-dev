// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::{
    ast_factory::{Expr, Program},
    jni_utils::JniUtils,
    verifier::extract_pos_id,
    JavaException,
};
use jni::{objects::JObject, JNIEnv};
use viper_sys::wrappers::viper::*;

#[derive(Clone, Copy)]
pub struct AstUtils<'a> {
    env: &'a JNIEnv<'a>,
    jni: JniUtils<'a>,
}

impl<'a> AstUtils<'a> {
    pub fn new(env: &'a JNIEnv) -> Self {
        let jni = JniUtils::new(env);
        AstUtils { env, jni }
    }

    /// Returns a vector of consistency errors, or a Java exception
    #[tracing::instrument(level = "debug", skip_all)]
    pub(crate) fn check_consistency(
        &self,
        program: Program<'a>,
    ) -> Result<Vec<JObject<'a>>, JavaException> {
        self.jni
            .unwrap_or_exception(
                silver::ast::Node::with(self.env).call_checkTransitively(program.to_jobject()),
            )
            .map(|java_vec| self.jni.seq_to_vec(java_vec))
    }

    #[tracing::instrument(level = "debug", skip_all)]
    pub fn pretty_print(&self, program: Program<'a>) -> String {
        let fast_pretty_printer_wrapper =
            silver::ast::pretty::FastPrettyPrinter_object::with(self.env);
        self.jni.get_string(
            self.jni.unwrap_result(
                fast_pretty_printer_wrapper.call_pretty(
                    self.jni
                        .unwrap_result(fast_pretty_printer_wrapper.singleton()),
                    program.to_jobject(),
                ),
            ),
        )
    }

    pub fn to_string(&self, program: Program<'a>) -> String {
        self.jni.to_string(program.to_jobject())
    }

    /// Applies silver's general-purpose `Simplifier` (constant folding and
    /// other local semantics-preserving rewrites) to an expression.
    pub fn simplify_expr(&self, expr: Expr<'a>) -> Expr<'a> {
        let simplifier_wrapper = silver::ast::utility::Simplifier_object::with(self.env);
        Expr::new(self.jni.unwrap_result(simplifier_wrapper.call_simplify(
            self.jni.unwrap_result(simplifier_wrapper.singleton()),
            expr.to_jobject(),
            false,
        )))
    }

    /// The position identifier of an expression, if it has one.
    pub fn pos_id(&self, expr: Expr<'a>) -> Option<String> {
        let pos = self
            .jni
            .unwrap_result(silver::ast::Positioned::with(self.env).call_pos(expr.to_jobject()));
        extract_pos_id(&self.jni, self.env, pos)
    }

    /// Rebuilds `expr` with the position, info and error transformer of
    /// `like`. `None` for the expressions whose metadata silver's reflective
    /// `withMeta` cannot replace: those with extra constructor arguments
    /// besides the metadata (plugin expressions such as adt applications, and
    /// backend function applications).
    pub fn with_meta_of(&self, expr: Expr<'a>, like: Expr<'a>) -> Option<Expr<'a>> {
        let obj = expr.to_jobject();
        if self
            .jni
            .is_instance_of(obj, "viper/silver/ast/ExtensionExp")
            || self
                .jni
                .is_instance_of(obj, "viper/silver/ast/BackendFuncApp")
        {
            return None;
        }
        let rewritable = silver::ast::utility::rewriter::Rewritable::with(self.env);
        let meta = self
            .jni
            .unwrap_result(rewritable.call_meta(like.to_jobject()));
        Some(Expr::new(
            self.jni.unwrap_result(rewritable.call_withMeta(obj, meta)),
        ))
    }

    /// Important: the result of the `f` call must not contain Java objects. Use carefully.
    pub fn with_local_frame<T>(&self, capacity: i32, f: impl FnOnce() -> T) -> T {
        self.jni.unwrap_result(self.env.push_local_frame(capacity));
        let result = f();
        self.jni
            .unwrap_result(self.env.pop_local_frame(JObject::null()));
        result
    }
}
