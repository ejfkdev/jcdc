//! jcdc decompiler core: class file → Java source.
//!
//! Pipeline: classfile parse → CFG → per-block expression building →
//! control flow structuring → statement conversion → refinement passes →
//! Java emission.

pub mod block;
pub mod builder;
pub mod classdec;
pub mod convert;
pub mod emit;
pub mod expr;
pub mod method;
pub mod stmt;
pub mod structure;
pub mod sese;
pub mod varalloc;

pub use classdec::{decompile_class, ClassOptions};
pub use jcdc_jvm::{ClassPool, PoolClass};

use jcdc_classfile::{parse_classfile, CpLookup};

/// Convenience: decompile a single class file's bytes.
pub fn decompile_bytes(data: &[u8], pool: &ClassPool) -> anyhow::Result<String> {
    let (_, cf) = parse_classfile(data)
        .map_err(|e| anyhow::anyhow!("class parse error: {:?}", e))?;
    let cp = CpLookup::new(&cf.constant_pool);
    let name = cp
        .class_name(&cf.constant_pool, cf.this_class)
        .unwrap_or("Unknown")
        .to_string();
    let pc = std::sync::Arc::new(PoolClass { internal_name: name, cf, cp });
    decompile_class(&pc, pool, &ClassOptions::default())
}

/// Process-lifetime cache for a debug env flag. `std::env::var` takes a
/// global lock and walks the environ per call — 2.4% of rt.jar-render
/// samples sat in `__findenv_locked` because the structurer checks
/// JCDC_DBG_* at every decision point. These flags are process-start
/// configuration; freezing them at first use is semantics-preserving.
#[macro_export]
macro_rules! dbg_flag {
    ($name:literal) => {{
        static CACHED: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
        *CACHED.get_or_init(|| std::env::var($name).is_ok())
    }};
}

/// Process-lifetime cache for a parsed env value (see dbg_flag).
#[macro_export]
macro_rules! dbg_value {
    ($name:literal, $ty:ty) => {{
        static CACHED: std::sync::OnceLock<Option<$ty>> = std::sync::OnceLock::new();
        CACHED
            .get_or_init(|| {
                std::env::var($name)
                    .ok()
                    .and_then(|v| v.parse::<$ty>().ok())
            })
            .clone()
    }};
}
