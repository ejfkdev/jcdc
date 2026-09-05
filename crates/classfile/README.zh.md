# java-class-rs

基于 [JVM 规范 §4](https://docs.oracle.com/javase/specs/jvms/se21/html/jvms-4.html) 的 Java `.class` 文件解析器，使用 Rust 编写。

[English](README.md) | 中文

[![CI](https://github.com/ejfkdev/java-class-rs/actions/workflows/ci.yml/badge.svg)](https://github.com/ejfkdev/java-class-rs/actions/workflows/ci.yml)
[![crates.io](https://img.shields.io/crates/v/java-class-rs.svg)](https://crates.io/crates/java-class-rs)
[![docs.rs](https://docs.rs/java-class-rs/badge.svg)](https://docs.rs/java-class-rs)
[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](LICENSE)
[![Rust](https://img.shields.io/badge/Rust-1.71%2B-orange.svg)](https://www.rust-lang.org/)
[![Downloads](https://img.shields.io/crates/d/java-class-rs.svg)](https://crates.io/crates/java-class-rs)
[![unsafe forbidden](https://img.shields.io/badge/unsafe-forbidden-success.svg)](https://github.com/rust-secure-code/safety-dance/)

## 特性

- **完整常量池** — 全部 17 种条目类型，包括 MethodHandle、InvokeDynamic、Module、Package
- **访问标志** — 类、字段、方法级别
- **20+ 专用属性** — Code、StackMapTable、Exceptions、BootstrapMethods、InnerClasses、注解（运行时/参数/类型）、NestHost/Members、Record、PermittedSubclasses 等
- **Modified UTF-8** — 通过 `cesu8` crate 实现 CESU-8 解码
- **Serde 支持** — 可选 `serde` feature，支持 JSON 序列化
- **无 unsafe** — 纯 safe Rust

## 快速开始

```toml
# Cargo.toml
[dependencies]
java-class-rs = "0.1"
```

```rust
use java_class_rs::parse_classfile;

let data = std::fs::read("MyClass.class").unwrap();
let (_, class_file) = parse_classfile(&data).unwrap();

println!("类名: {:?}", class_file.this_class_name());
println!("父类: {:?}", class_file.super_class_name());
println!("Java {}.{}", class_file.major_version, class_file.minor_version);
```

## 示例

### 遍历方法和字段

```rust
for method in &class_file.methods {
    let name = class_file.method_name(method).unwrap_or("<unknown>");
    let desc = class_file.method_descriptor(method).unwrap_or("");
    println!("{} {}", name, desc);
}
```

### 解析专用属性

原始属性以 `AttributeInfo`（名称索引 + 字节数据）形式存储，使用 `parse_specialized_attribute` 进行解码：

```rust
use java_class_rs::{get_utf8, parse_specialized_attribute, ParsedAttribute};

for attr in &class_file.methods[0].attributes {
    if get_utf8(&class_file.constant_pool, attr.attribute_name_index) == Some("Code") {
        if let ParsedAttribute::Code(code) = parse_specialized_attribute(attr, &class_file.constant_pool) {
            println!("max_stack={}, max_locals={}, 字节码={} 字节",
                code.max_stack, code.max_locals, code.code.len());
        }
    }
}
```

### Serde 支持

```toml
[dependencies]
java-class-rs = { version = "0.1", features = ["serde"] }
```

```rust
let json = serde_json::to_string_pretty(&class_file).unwrap();
println!("{}", json);
```

### 常量池辅助方法

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

## 支持的属性

| 分类 | 属性 |
|------|------|
| 字节码 | Code, StackMapTable, Exceptions |
| 链接 | BootstrapMethods, NestHost, NestMembers |
| 调试 | SourceFile, LineNumberTable, LocalVariableTable, LocalVariableTypeTable |
| 注解 | RuntimeVisible/InvisibleAnnotations, RuntimeVisible/InvisibleParameterAnnotations, RuntimeVisible/InvisibleTypeAnnotations |
| 密封类 | PermittedSubclasses |
| 记录类 | Record |
| 其他 | ConstantValue, InnerClasses, Signature, Deprecated, Synthetic |

## MSRV

最低支持 Rust 版本：**1.71**

## 许可证

[MIT](LICENSE)
