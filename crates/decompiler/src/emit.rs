//! Java source emission — provided by `jdc-core` now.
//!
//! The printer is machine-neutral (it prints Java, not bytecode); what used to
//! be JVM-specific here — resolving names through the class pool, decompiling
//! lambda bodies — goes through `jdc_core::ctx::Ctx`, implemented for the JVM
//! by [`crate::jvmctx::JvmCtx`].

pub use jdc_core::analysis::dead_end_infinite_while;
pub use jdc_core::emit::{escape_char, escape_string, format_float, Printer};
pub use crate::jvmctx::JvmCtx;
