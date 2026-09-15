//! JVM data model layer: descriptors, generic signatures, class pool,
//! and per-version feature configuration.

mod features;
mod pool;

// The descriptor / generic-signature / type model is shared with every other
// Java-family front-end and lives in `jdc-core`; this crate adds the class
// pool and the per-version feature configuration on top.
pub use jdc_core::types::*;

pub use features::*;
pub use pool::*;
