# java-class-rs

A Java `.class` file parser written in Rust, based on the [JVM Specification §4](https://docs.oracle.com/javase/specs/jvms/se21/html/jvms-4.html).

English | [中文](README.zh.md)

[![CI](https://github.com/ejfkdev/java-class-rs/actions/workflows/ci.yml/badge.svg)](https://github.com/ejfkdev/java-class-rs/actions/workflows/ci.yml)
[![crates.io](https://img.shields.io/crates/v/java-class-rs.svg)](https://crates.io/crates/java-class-rs)
[![docs.rs](https://docs.rs/java-class-rs/badge.svg)](https://docs.rs/java-class-rs)
[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](LICENSE)
[![Rust](https://img.shields.io/badge/Rust-1.71%2B-orange.svg)](https://www.rust-lang.org/)
[![Downloads](https://img.shields.io/crates/d/java-class-rs.svg)](https://crates.io/crates/java-class-rs)
[![unsafe forbidden](https://img.shields.io/badge/unsafe-forbidden-success.svg)](https://github.com/rust-secure-code/safety-dance/)

## Features

- **Full constant pool** — all 17 entry types including MethodHandle, InvokeDynamic, Module, Package
- **Access flags** — class, field, and method level
- **20+ specialized attributes** — Code, StackMapTable, Exceptions, BootstrapMethods, InnerClasses, Annotations (runtime/parameter/type), NestHost/Members, Record, PermittedSubclasses, and more
- **Modified UTF-8** — CESU-8 decoding via the `cesu8` crate
- **Serde support** — optional `serde` feature for JSON/serialization
- **No unsafe** — pure safe Rust

## Quick Start

```toml
# Cargo.toml
[dependencies]
java-class-rs = "0.1"
```

```rust
use java_class_rs::parse_classfile;

let data = std::fs::read("MyClass.class").unwrap();
let (_, class_file) = parse_classfile(&data).unwrap();

println!("Class: {:?}", class_file.this_class_name());
println!("Super: {:?}", class_file.super_class_name());
println!("Java {}.{}", class_file.major_version, class_file.minor_version);
```

## Examples

### Iterate methods and fields

```rust
for method in &class_file.methods {
    let name = class_file.method_name(method).unwrap_or("<unknown>");
    let desc = class_file.method_descriptor(method).unwrap_or("");
    println!("{} {}", name, desc);
}
```

### Parse specialized attributes

Raw attributes are stored as `AttributeInfo` (name index + bytes). Use `parse_specialized_attribute` to decode them:

```rust
use java_class_rs::{get_utf8, parse_specialized_attribute, ParsedAttribute};

for attr in &class_file.methods[0].attributes {
    if get_utf8(&class_file.constant_pool, attr.attribute_name_index) == Some("Code") {
        if let ParsedAttribute::Code(code) = parse_specialized_attribute(attr, &class_file.constant_pool) {
            println!("max_stack={}, max_locals={}, bytecode={} bytes",
                code.max_stack, code.max_locals, code.code.len());
        }
    }
}
```

### Serde support

```toml
[dependencies]
java-class-rs = { version = "0.1", features = ["serde"] }
```

```rust
let json = serde_json::to_string_pretty(&class_file).unwrap();
println!("{}", json);
```

### Constant pool helpers

```rust
use java_class_rs::{get_entry, get_utf8, ConstantPoolEntry};

for (i, entry) in class_file.constant_pool.iter().enumerate() {
    match entry {
        ConstantPoolEntry::Methodref(m) => {
            let class = get_utf8(&class_file.constant_pool, m.class_index).unwrap_or("?");
            println!("#{} Methodref -> {}", i + 1, class);
        }
        _ => {}
    }
}
```

## Supported Attributes

| Category | Attributes |
|----------|-----------|
| Bytecode | Code, StackMapTable, Exceptions |
| Linkage | BootstrapMethods, NestHost, NestMembers |
| Debug | SourceFile, LineNumberTable, LocalVariableTable, LocalVariableTypeTable |
| Annotations | RuntimeVisible/InvisibleAnnotations, RuntimeVisible/InvisibleParameterAnnotations, RuntimeVisible/InvisibleTypeAnnotations |
| Sealed | PermittedSubclasses |
| Records | Record |
| Other | ConstantValue, InnerClasses, Signature, Deprecated, Synthetic |

## MSRV

Minimum Supported Rust Version: **1.71**

## License

[MIT](LICENSE)
