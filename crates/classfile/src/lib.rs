//! Java class file format parser.
//!
//! Parses `.class` files according to the JVM Specification (JVMS Chapter 4).
//! Supports all 17 constant pool entry types, access flags, fields, methods,
//! and 20+ specialized attributes including Code, StackMapTable, BootstrapMethods,
//! annotations, and more.
//!
//! # Example
//!
//! ```no_run
//! use jcdc_classfile::parse_classfile;
//!
//! fn main() {
//!     let data = std::fs::read("MyClass.class").unwrap();
//!     let (_, class_file) = parse_classfile(&data).unwrap();
//!     println!("Class: {:?}", class_file.this_class_name());
//! }
//! ```

mod attribute;
mod constant_pool;
mod field;
mod method;
mod parser;
mod types;

pub use parser::parse_classfile;
pub use types::*;

// Re-export commonly used helpers
pub use attribute::parse_specialized_attribute;
pub use constant_pool::{get_entry, get_utf8, CpLookup};

pub mod instruction;
pub use instruction::*;
