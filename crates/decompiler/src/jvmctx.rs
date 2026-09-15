//! The JVM front-end's implementation of `jdc_core::Ctx`.
//!
//! Every method here answers a *semantic* question about class metadata using
//! the class pool — the core never sees a constant pool.

use jcdc_jvm::{ClassPool, JavaType, PoolClass};

use crate::ctx_shim::*;

/// Front-end context handed to the core's passes and printer.
pub struct JvmCtx<'a> {
    pub pc: &'a PoolClass,
    pub pool: &'a ClassPool,
}

impl<'a> JvmCtx<'a> {
    pub fn new(pc: &'a PoolClass, pool: &'a ClassPool) -> Self {
        JvmCtx { pc, pool }
    }
}

impl<'a> jdc_core::Ctx for JvmCtx<'a> {
    fn class_name(&self) -> &str {
        &self.pc.internal_name
    }

    fn source_level(&self) -> u16 {
        self.pc.cf.major_version
    }

    fn find_outer(&self, internal: &str) -> Option<String> {
        let pc = self.pool.get(internal)?;
        find_outer_of(&pc, self.pool)
    }

    fn family(&self, root: &str) -> jdc_core::Family {
        convert_family(self.pc, self.pool, root)
    }

    fn nested_is_static(&self, internal: &str) -> bool {
        match self.pool.get(internal) {
            Some(pc) => nested_is_static_pc(&pc),
            None => true,
        }
    }

    fn class_has_this0(&self, internal: &str) -> bool {
        match self.pool.get(internal) {
            Some(pc) => class_has_this0_pc(&pc),
            None => false,
        }
    }

    fn outer_param_via_super(&self, internal: &str) -> bool {
        match self.pool.get(internal) {
            Some(pc) => outer_param_via_super_pc(&pc),
            None => false,
        }
    }

    fn is_subtype_of(&self, sub: &JavaType, sup: &str) -> bool {
        is_subtype_of_pool(self.pool, sub, sup)
    }

    fn is_interface(&self, internal: &str) -> bool {
        self.pool
            .get(internal)
            .map(|pc| pc.is_interface())
            .unwrap_or(false)
    }

    fn is_sealed(&self, internal: &str) -> bool {
        self.pool
            .get(internal)
            .map(|pc| pc.class_attr("PermittedSubclasses").is_some())
            .unwrap_or(false)
    }

    fn super_name(&self, internal: &str) -> Option<String> {
        self.pool.get(internal).and_then(|pc| pc.super_name().map(str::to_string))
    }

    fn has_class(&self, internal: &str) -> bool {
        self.pool.get(internal).is_some() || internal == self.pc.internal_name
    }

    fn class_supers_args(
        &self,
        internal: &str,
        args: &[jdc_core::types::GenericType],
    ) -> Vec<(String, Vec<jdc_core::types::GenericType>)> {
        match self.pool.get(internal) {
            Some(pc) => crate::classdec::class_supers_args(&pc, args),
            None => Vec::new(),
        }
    }

    fn class_bases(&self, internal: &str) -> Option<(Vec<String>, Option<String>)> {
        let pc = self.pool.get(internal)?;
        let ifaces = pc.interface_names().into_iter().map(str::to_string).collect();
        Some((ifaces, pc.super_name().map(str::to_string)))
    }

    fn field_flags(
        &self,
        internal: &str,
        name: &str,
    ) -> Option<jdc_core::types::FieldAccessFlags> {
        let pc = self.pool.get(internal)?;
        pc.cf.fields.iter().find_map(|f| {
            (pc.utf8(f.name_index) == Some(name)).then_some(f.access_flags)
        })
    }

    fn method_flags(
        &self,
        internal: &str,
        name: &str,
        desc: &str,
    ) -> Option<jdc_core::types::MethodAccessFlags> {
        let pc = self.pool.get(internal)?;
        (0..pc.cf.methods.len()).find_map(|i| {
            (pc.method_name(i) == Some(name) && pc.method_desc(i) == Some(desc))
                .then(|| pc.method_access(i))
        })
    }

    fn declares_method_named(&self, internal: &str, name: &str) -> bool {
        match self.pool.get(internal) {
            Some(pc) => (0..pc.cf.methods.len()).any(|i| pc.method_name(i) == Some(name)),
            None => false,
        }
    }

    fn class_type_params(&self, internal: &str) -> Vec<jdc_core::types::TypeParam> {
        class_type_params_of(self.pool, internal)
    }

    fn is_generic_call(&self, e: &jdc_core::Expr) -> bool {
        is_generic_call_expr(e, self.pool)
    }

    fn generic_call_formals(
        &self,
        e: &jdc_core::Expr,
    ) -> Option<(Vec<jdc_core::types::GenericType>, Vec<String>)> {
        generic_call_formals_expr(e, self.pool, self.pc)
    }

    fn polymorphic_ret_cast(
        &self,
        cls: &str,
        name: &str,
        desc: &jdc_core::types::MethodDescriptor,
    ) -> Option<JavaType> {
        polymorphic_ret_cast_fn(cls, name, desc)
    }

    fn ctor_formals_by_arity(
        &self,
        internal: &str,
        arity: usize,
    ) -> Option<Vec<jdc_core::types::GenericType>> {
        ctor_formals_by_arity_fn(internal, arity, self.pool)
    }

    fn ctor_param_types(
        &self,
        internal: &str,
        skip: usize,
        n: usize,
        args: &[jdc_core::Expr],
    ) -> Option<Vec<JavaType>> {
        ctor_param_types_fn(self, internal, skip, n, args)
    }

    fn sam_ret_cast(
        &self,
        g: &jdc_core::types::GenericType,
        sam_name: &str,
    ) -> Option<jdc_core::ir::expr::TypeRef> {
        sam_ret_cast_fn(self, g, sam_name)
    }

    fn local_class_internal(&self, simple: &str) -> Option<String> {
        local_class_internal_fn(&self.pc.internal_name, simple, self.pool)
    }

    fn nested_method(
        &self,
        l: &jdc_core::ir::expr::LambdaExpr,
        outer_vt: &crate::varalloc::VarTable,
    ) -> Option<jdc_core::MethodBody> {
        nested_method_fn(self, l, outer_vt)
    }
}

