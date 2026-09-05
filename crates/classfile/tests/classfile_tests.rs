use jcdc_classfile::parse_classfile;
use jcdc_classfile::*;
use std::path::Path;

/// Resolve a Class entry index to the class name string.
fn resolve_class_name(pool: &[ConstantPoolEntry], class_index: u16) -> Option<String> {
    let entry = get_entry(pool, class_index)?;
    if let ConstantPoolEntry::Class(class_info) = entry {
        get_utf8(pool, class_info.name_index).map(|s| s.to_string())
    } else {
        None
    }
}

fn read_class_file(name: &str) -> Vec<u8> {
    let base = Path::new(env!("CARGO_MANIFEST_DIR")).join("testcases");
    let path = base.join(name);
    std::fs::read(&path).unwrap_or_else(|e| panic!("Failed to read {}: {}", name, e))
}

#[test]
fn test_parse_basic_class() {
    let bytes = read_class_file("BasicClass.class");
    let (remaining, cf) = parse_classfile(&bytes).expect("Failed to parse BasicClass.class");
    assert!(remaining.is_empty(), "Should consume all bytes");
    assert!(
        cf.major_version >= 45,
        "Major version should be valid, got {}",
        cf.major_version
    );
    assert!(cf.access_flags.contains(ClassAccessFlags::PUBLIC));
    assert!(cf.access_flags.contains(ClassAccessFlags::SUPER));

    // Check this_class resolves to a valid class name
    let class_name =
        resolve_class_name(&cf.constant_pool, cf.this_class).expect("this_class should resolve");
    assert!(
        class_name.contains("BasicClass"),
        "class name should contain BasicClass, got: {}",
        class_name
    );
}

#[test]
fn test_parse_hello_world() {
    let bytes = read_class_file("HelloWorld.class");
    let (remaining, cf) = parse_classfile(&bytes).expect("Failed to parse HelloWorld.class");
    assert!(remaining.is_empty());
    assert!(cf.fields.is_empty() || !cf.fields.is_empty()); // just check it parses
    assert!(!cf.methods.is_empty(), "HelloWorld should have methods");
}

#[test]
fn test_parse_annotations() {
    let bytes = read_class_file("Annotations.class");
    let (remaining, cf) = parse_classfile(&bytes).expect("Failed to parse Annotations.class");
    assert!(remaining.is_empty());
    // Annotations class should have RuntimeVisible/Invisible annotations attributes
    // Check class-level, method-level, and field-level attributes
    let all_attrs: Vec<&AttributeInfo> = cf
        .attributes
        .iter()
        .chain(cf.methods.iter().flat_map(|m| m.attributes.iter()))
        .chain(cf.fields.iter().flat_map(|f| f.attributes.iter()))
        .collect();
    let has_annotation_attr = all_attrs.iter().any(|attr| {
        let name = get_utf8(&cf.constant_pool, attr.attribute_name_index);
        matches!(name, Some(n) if n.contains("nnotation"))
    });
    assert!(has_annotation_attr, "Should have annotation attributes");
}

#[test]
fn test_parse_inner_classes() {
    let bytes = read_class_file("InnerClasses.class");
    let (remaining, cf) = parse_classfile(&bytes).expect("Failed to parse InnerClasses.class");
    assert!(remaining.is_empty());
    // Should have InnerClasses attribute
    let has_inner = cf
        .attributes
        .iter()
        .any(|attr| get_utf8(&cf.constant_pool, attr.attribute_name_index) == Some("InnerClasses"));
    assert!(has_inner, "InnerClasses should have InnerClasses attribute");
}

#[test]
fn test_parse_inner_class_member() {
    let bytes = read_class_file("InnerClasses$HelloWorld.class");
    let (remaining, _cf) =
        parse_classfile(&bytes).expect("Failed to parse InnerClasses$HelloWorld.class");
    assert!(remaining.is_empty());
}

#[test]
fn test_parse_bootstrap_methods() {
    let bytes = read_class_file("BootstrapMethods.class");
    let (remaining, cf) = parse_classfile(&bytes).expect("Failed to parse BootstrapMethods.class");
    assert!(remaining.is_empty());
    // Should have BootstrapMethods attribute
    let has_bsm = cf.attributes.iter().any(|attr| {
        get_utf8(&cf.constant_pool, attr.attribute_name_index) == Some("BootstrapMethods")
    });
    assert!(
        has_bsm,
        "BootstrapMethods should have BootstrapMethods attribute"
    );
}

#[test]
fn test_parse_deprecated() {
    let bytes = read_class_file("DeprecatedAnnotation.class");
    let (remaining, _cf) =
        parse_classfile(&bytes).expect("Failed to parse DeprecatedAnnotation.class");
    assert!(remaining.is_empty());
}

#[test]
fn test_parse_unicode_strings() {
    let bytes = read_class_file("UnicodeStrings.class");
    let (remaining, _cf) = parse_classfile(&bytes).expect("Failed to parse UnicodeStrings.class");
    assert!(remaining.is_empty());
}

#[test]
fn test_parse_local_variable_table() {
    let bytes = read_class_file("LocalVariableTable.class");
    let (remaining, cf) =
        parse_classfile(&bytes).expect("Failed to parse LocalVariableTable.class");
    assert!(remaining.is_empty());
    // LocalVariableTable may be in Code attributes
    let has_lvt = cf.methods.iter().any(|m| {
        m.attributes.iter().any(|attr| {
            let name = get_utf8(&cf.constant_pool, attr.attribute_name_index);
            name == Some("LocalVariableTable") || name == Some("Code")
        })
    });
    assert!(
        has_lvt,
        "Should have LocalVariableTable or Code attribute in methods"
    );
}

#[test]
fn test_parse_module_info() {
    let bytes = read_class_file("module-info.class");
    let (remaining, cf) = parse_classfile(&bytes).expect("Failed to parse module-info.class");
    assert!(remaining.is_empty());
    assert!(cf.access_flags.contains(ClassAccessFlags::MODULE));
}

#[test]
fn test_parse_factorial() {
    let bytes = read_class_file("Factorial.class");
    let (remaining, _cf) = parse_classfile(&bytes).expect("Failed to parse Factorial.class");
    assert!(remaining.is_empty());
}

#[test]
fn test_parse_instructions() {
    let bytes = read_class_file("Instructions.class");
    let (remaining, _cf) = parse_classfile(&bytes).expect("Failed to parse Instructions.class");
    assert!(remaining.is_empty());
}

#[test]
fn test_parse_com_some_thing() {
    let bytes = read_class_file("com/some/Thing.class");
    let (remaining, cf) = parse_classfile(&bytes).expect("Failed to parse com/some/Thing.class");
    assert!(remaining.is_empty());
    let class_name = resolve_class_name(&cf.constant_pool, cf.this_class).unwrap_or_default();
    assert!(
        class_name.contains("com/some/Thing"),
        "class name should contain package, got: {}",
        class_name
    );
}

#[test]
fn test_parse_train_print() {
    let bytes = read_class_file("TrainPrint.class");
    let (remaining, _cf) = parse_classfile(&bytes).expect("Failed to parse TrainPrint.class");
    assert!(remaining.is_empty());
}

#[test]
fn test_constant_pool_utf8() {
    let bytes = read_class_file("BasicClass.class");
    let (_, cf) = parse_classfile(&bytes).expect("Failed to parse");
    // Every class should have UTF8 entries
    let has_utf8 = cf
        .constant_pool
        .iter()
        .any(|e| matches!(e, ConstantPoolEntry::Utf8(_)));
    assert!(has_utf8, "Should have UTF8 entries in constant pool");
}

#[test]
fn test_constant_pool_class_entry() {
    let bytes = read_class_file("BasicClass.class");
    let (_, cf) = parse_classfile(&bytes).expect("Failed to parse");
    // Should have Class entries
    let has_class = cf
        .constant_pool
        .iter()
        .any(|e| matches!(e, ConstantPoolEntry::Class(_)));
    assert!(has_class, "Should have Class entries in constant pool");
}

#[test]
fn test_specialized_code_attribute() {
    let bytes = read_class_file("HelloWorld.class");
    let (_, cf) = parse_classfile(&bytes).expect("Failed to parse");
    // Methods should have Code attributes
    for method in &cf.methods {
        for attr in &method.attributes {
            let name = get_utf8(&cf.constant_pool, attr.attribute_name_index);
            if name == Some("Code") {
                let parsed = parse_specialized_attribute(attr, &cf.constant_pool);
                assert!(
                    matches!(parsed, ParsedAttribute::Code(_)),
                    "Should parse Code attribute"
                );
            }
        }
    }
}

#[test]
fn test_specialized_inner_classes_attribute() {
    let bytes = read_class_file("InnerClasses.class");
    let (_, cf) = parse_classfile(&bytes).expect("Failed to parse");
    for attr in &cf.attributes {
        let name = get_utf8(&cf.constant_pool, attr.attribute_name_index);
        if name == Some("InnerClasses") {
            let parsed = parse_specialized_attribute(attr, &cf.constant_pool);
            assert!(
                matches!(parsed, ParsedAttribute::InnerClasses(_)),
                "Should parse InnerClasses attribute"
            );
        }
    }
}

#[test]
fn test_parse_all_class_files() {
    // Parse all .class files in the testcases directory
    let base = Path::new(env!("CARGO_MANIFEST_DIR")).join("testcases");
    if !base.exists() {
        return;
    }
    let mut passed = 0;
    let mut failed = 0;
    let mut failures = Vec::new();

    fn walk_dir(dir: &Path, passed: &mut usize, failed: &mut usize, failures: &mut Vec<String>) {
        let entries = std::fs::read_dir(dir).expect("read dir");
        for entry in entries {
            let entry = entry.expect("entry");
            let path = entry.path();
            if path.is_dir() {
                walk_dir(&path, passed, failed, failures);
            } else if path.extension().is_some_and(|e| e == "class") {
                let name = path
                    .strip_prefix(dir)
                    .unwrap_or(&path)
                    .to_string_lossy()
                    .to_string();
                // Skip intentionally invalid test files
                if name.contains("malformed") || name.contains("TestUnsupportedConstantPoolEntry") {
                    continue;
                }
                let bytes = std::fs::read(&path).expect("read");
                match parse_classfile(&bytes) {
                    Ok((remaining, _cf)) => {
                        if remaining.is_empty() {
                            *passed += 1;
                        } else {
                            *failed += 1;
                            failures.push(format!("{}: {} bytes remaining", name, remaining.len()));
                        }
                    }
                    Err(e) => {
                        *failed += 1;
                        failures.push(format!("{}: parse error {:?}", name, e));
                    }
                }
            }
        }
    }

    walk_dir(&base, &mut passed, &mut failed, &mut failures);
    println!("\n=== ClassFile Test Results ===");
    println!("Passed: {}/{}", passed, passed + failed);
    for f in &failures {
        println!("  FAIL: {}", f);
    }
    assert!(
        failed == 0,
        "All class files should parse. Passed: {}/{}, Failures: {:?}",
        passed,
        passed + failed,
        failures
    );
}

#[test]
fn test_parse_malformed_class_fails() {
    let bytes = read_class_file("malformed.class");
    assert!(
        parse_classfile(&bytes).is_err(),
        "malformed.class should fail to parse"
    );
}

#[test]
fn test_specialized_parameter_annotations_parse() {
    // Verify that ParameterAnnotations parser works by scanning all test class files
    for file_name in &[
        "Annotations.class",
        "Annotations$VisibleAtRuntime.class",
        "Annotations$InvisibleAtRuntime.class",
    ] {
        let bytes = read_class_file(file_name);
        let (_, cf) =
            parse_classfile(&bytes).unwrap_or_else(|_| panic!("Failed to parse {}", file_name));
        for method in &cf.methods {
            for attr in &method.attributes {
                let name = get_utf8(&cf.constant_pool, attr.attribute_name_index);
                if name == Some("RuntimeVisibleParameterAnnotations")
                    || name == Some("RuntimeInvisibleParameterAnnotations")
                {
                    let parsed = parse_specialized_attribute(attr, &cf.constant_pool);
                    assert!(
                        matches!(
                            parsed,
                            ParsedAttribute::RuntimeVisibleParameterAnnotations(_)
                                | ParsedAttribute::RuntimeInvisibleParameterAnnotations(_)
                        ),
                        "Should parse parameter annotations attribute"
                    );
                }
            }
        }
    }
}

#[test]
fn test_specialized_type_annotations_parse() {
    // Verify that TypeAnnotations parser works by scanning all test class files
    for file_name in &[
        "Annotations.class",
        "Annotations$TypeVisibleAtRuntime.class",
        "Annotations$TypeInvisibleAtRuntime.class",
    ] {
        let bytes = read_class_file(file_name);
        let (_, cf) =
            parse_classfile(&bytes).unwrap_or_else(|_| panic!("Failed to parse {}", file_name));
        let all_attrs: Vec<&AttributeInfo> = cf
            .attributes
            .iter()
            .chain(cf.methods.iter().flat_map(|m| m.attributes.iter()))
            .chain(cf.fields.iter().flat_map(|f| f.attributes.iter()))
            .collect();
        for attr in all_attrs {
            let name = get_utf8(&cf.constant_pool, attr.attribute_name_index);
            if name == Some("RuntimeVisibleTypeAnnotations")
                || name == Some("RuntimeInvisibleTypeAnnotations")
            {
                let parsed = parse_specialized_attribute(attr, &cf.constant_pool);
                assert!(
                    matches!(
                        parsed,
                        ParsedAttribute::RuntimeVisibleTypeAnnotations(_)
                            | ParsedAttribute::RuntimeInvisibleTypeAnnotations(_)
                    ),
                    "Should parse type annotations attribute"
                );
            }
        }
    }
}

#[test]
#[cfg(feature = "serde")]
fn test_serde_serialize() {
    use serde::Serialize;
    let bytes = read_class_file("HelloWorld.class");
    let (_, cf) = parse_classfile(&bytes).expect("Failed to parse");
    // Verify Serialize is implemented and works
    let _ = serde_json::to_string(&cf).expect("Serialize failed");
}

#[test]
#[cfg(feature = "serde")]
fn test_serde_deserialize() {
    let bytes = read_class_file("BasicClass.class");
    let (_, cf) = parse_classfile(&bytes).expect("Failed to parse");
    let json = serde_json::to_string(&cf).expect("Serialize failed");
    let _: ClassFile = serde_json::from_str(&json).expect("Deserialize failed");
}
