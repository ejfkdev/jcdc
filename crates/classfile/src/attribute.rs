use nom::{
    bytes::complete::take,
    multi::count,
    number::complete::{be_u16, be_u32, be_u8},
    IResult,
};

use crate::constant_pool::get_utf8;

use crate::types::*;

/// Parse a generic attribute (name_index + length + raw bytes).
pub(crate) fn parse_attribute(input: &[u8]) -> IResult<&[u8], AttributeInfo> {
    let (input, attribute_name_index) = be_u16(input)?;
    let (input, length) = be_u32(input)?;
    let (input, info) = take(length as usize)(input)?;
    Ok((
        input,
        AttributeInfo {
            attribute_name_index,
            info: info.to_vec(),
        },
    ))
}

/// Parse multiple attributes.
pub(crate) fn parse_attributes(input: &[u8]) -> IResult<&[u8], Vec<AttributeInfo>> {
    let (input, attributes_count) = be_u16(input)?;
    let (input, attributes) = count(parse_attribute, attributes_count as usize)(input)?;
    Ok((input, attributes))
}

/// Try to parse a raw attribute into a specialized attribute type based on the attribute name.
pub fn parse_specialized_attribute(
    attr: &AttributeInfo,
    pool: &[ConstantPoolEntry],
) -> ParsedAttribute {
    let name = match get_utf8(pool, attr.attribute_name_index) {
        Some(n) => n,
        None => return ParsedAttribute::Unknown(attr.clone()),
    };

    match name {
        "Code" => parse_code_attribute(&attr.info)
            .map(|(_, a)| ParsedAttribute::Code(a))
            .unwrap_or(ParsedAttribute::Unknown(attr.clone())),
        "ConstantValue" => parse_constant_value_attribute(&attr.info)
            .map(|(_, a)| ParsedAttribute::ConstantValue(a))
            .unwrap_or(ParsedAttribute::Unknown(attr.clone())),
        "Exceptions" => parse_exceptions_attribute(&attr.info)
            .map(|(_, a)| ParsedAttribute::Exceptions(a))
            .unwrap_or(ParsedAttribute::Unknown(attr.clone())),
        "BootstrapMethods" => parse_bootstrap_methods_attribute(&attr.info)
            .map(|(_, a)| ParsedAttribute::BootstrapMethods(a))
            .unwrap_or(ParsedAttribute::Unknown(attr.clone())),
        "StackMapTable" => parse_stack_map_table_attribute(&attr.info)
            .map(|(_, a)| ParsedAttribute::StackMapTable(a))
            .unwrap_or(ParsedAttribute::Unknown(attr.clone())),
        "InnerClasses" => parse_inner_classes_attribute(&attr.info)
            .map(|(_, a)| ParsedAttribute::InnerClasses(a))
            .unwrap_or(ParsedAttribute::Unknown(attr.clone())),
        "EnclosingMethod" => parse_enclosing_method_attribute(&attr.info)
            .map(|(_, a)| ParsedAttribute::EnclosingMethod(a))
            .unwrap_or(ParsedAttribute::Unknown(attr.clone())),
        "AnnotationDefault" => parse_annotation_default_attribute(&attr.info)
            .map(|(_, a)| ParsedAttribute::AnnotationDefault(a))
            .unwrap_or(ParsedAttribute::Unknown(attr.clone())),
        "MethodParameters" => parse_method_parameters_attribute(&attr.info)
            .map(|(_, a)| ParsedAttribute::MethodParameters(a))
            .unwrap_or(ParsedAttribute::Unknown(attr.clone())),
        "Module" => parse_module_attribute(&attr.info)
            .map(|(_, a)| ParsedAttribute::Module(a))
            .unwrap_or(ParsedAttribute::Unknown(attr.clone())),
        "ModulePackages" => parse_module_packages_attribute(&attr.info)
            .map(|(_, a)| ParsedAttribute::ModulePackages(a))
            .unwrap_or(ParsedAttribute::Unknown(attr.clone())),
        "ModuleMainClass" => parse_module_main_class_attribute(&attr.info)
            .map(|(_, a)| ParsedAttribute::ModuleMainClass(a))
            .unwrap_or(ParsedAttribute::Unknown(attr.clone())),
        "SourceFile" => parse_source_file_attribute(&attr.info)
            .map(|(_, a)| ParsedAttribute::SourceFile(a))
            .unwrap_or(ParsedAttribute::Unknown(attr.clone())),
        "LineNumberTable" => parse_line_number_table_attribute(&attr.info)
            .map(|(_, a)| ParsedAttribute::LineNumberTable(a))
            .unwrap_or(ParsedAttribute::Unknown(attr.clone())),
        "LocalVariableTable" => parse_local_variable_table_attribute(&attr.info)
            .map(|(_, a)| ParsedAttribute::LocalVariableTable(a))
            .unwrap_or(ParsedAttribute::Unknown(attr.clone())),
        "LocalVariableTypeTable" => parse_local_variable_type_table_attribute(&attr.info)
            .map(|(_, a)| ParsedAttribute::LocalVariableTypeTable(a))
            .unwrap_or(ParsedAttribute::Unknown(attr.clone())),
        "RuntimeVisibleAnnotations" => parse_runtime_annotations_attribute(&attr.info)
            .map(|(_, a)| ParsedAttribute::RuntimeVisibleAnnotations(a))
            .unwrap_or(ParsedAttribute::Unknown(attr.clone())),
        "RuntimeInvisibleAnnotations" => parse_runtime_annotations_attribute(&attr.info)
            .map(|(_, a)| ParsedAttribute::RuntimeInvisibleAnnotations(a))
            .unwrap_or(ParsedAttribute::Unknown(attr.clone())),
        "RuntimeVisibleParameterAnnotations" => {
            parse_runtime_parameter_annotations_attribute(&attr.info)
                .map(|(_, a)| ParsedAttribute::RuntimeVisibleParameterAnnotations(a))
                .unwrap_or(ParsedAttribute::Unknown(attr.clone()))
        }
        "RuntimeInvisibleParameterAnnotations" => {
            parse_runtime_parameter_annotations_attribute(&attr.info)
                .map(|(_, a)| ParsedAttribute::RuntimeInvisibleParameterAnnotations(a))
                .unwrap_or(ParsedAttribute::Unknown(attr.clone()))
        }
        "RuntimeVisibleTypeAnnotations" => parse_runtime_type_annotations_attribute(&attr.info)
            .map(|(_, a)| ParsedAttribute::RuntimeVisibleTypeAnnotations(a))
            .unwrap_or(ParsedAttribute::Unknown(attr.clone())),
        "RuntimeInvisibleTypeAnnotations" => parse_runtime_type_annotations_attribute(&attr.info)
            .map(|(_, a)| ParsedAttribute::RuntimeInvisibleTypeAnnotations(a))
            .unwrap_or(ParsedAttribute::Unknown(attr.clone())),
        "NestHost" => parse_nest_host_attribute(&attr.info)
            .map(|(_, a)| ParsedAttribute::NestHost(a))
            .unwrap_or(ParsedAttribute::Unknown(attr.clone())),
        "NestMembers" => parse_nest_members_attribute(&attr.info)
            .map(|(_, a)| ParsedAttribute::NestMembers(a))
            .unwrap_or(ParsedAttribute::Unknown(attr.clone())),
        "Record" => parse_record_attribute(&attr.info)
            .map(|(_, a)| ParsedAttribute::Record(a))
            .unwrap_or(ParsedAttribute::Unknown(attr.clone())),
        "PermittedSubclasses" => parse_permitted_subclasses_attribute(&attr.info)
            .map(|(_, a)| ParsedAttribute::PermittedSubclasses(a))
            .unwrap_or(ParsedAttribute::Unknown(attr.clone())),
        "Deprecated" => ParsedAttribute::Deprecated,
        "Synthetic" => ParsedAttribute::Synthetic,
        "Signature" => parse_signature_attribute(&attr.info)
            .map(|(_, signature_index)| ParsedAttribute::Signature { signature_index })
            .unwrap_or(ParsedAttribute::Unknown(attr.clone())),
        _ => ParsedAttribute::Unknown(attr.clone()),
    }
}

fn parse_code_attribute(input: &[u8]) -> IResult<&[u8], CodeAttribute> {
    let (input, max_stack) = be_u16(input)?;
    let (input, max_locals) = be_u16(input)?;
    let (input, code_length) = be_u32(input)?;
    let (input, code) = take(code_length as usize)(input)?;
    let (input, exception_table_length) = be_u16(input)?;
    let (input, exception_table) =
        count(parse_exception_table_entry, exception_table_length as usize)(input)?;
    let (input, attributes) = parse_attributes(input)?;
    Ok((
        input,
        CodeAttribute {
            max_stack,
            max_locals,
            code: code.to_vec(),
            exception_table,
            attributes,
        },
    ))
}

fn parse_exception_table_entry(input: &[u8]) -> IResult<&[u8], ExceptionTableEntry> {
    let (input, start_pc) = be_u16(input)?;
    let (input, end_pc) = be_u16(input)?;
    let (input, handler_pc) = be_u16(input)?;
    let (input, catch_type) = be_u16(input)?;
    Ok((
        input,
        ExceptionTableEntry {
            start_pc,
            end_pc,
            handler_pc,
            catch_type,
        },
    ))
}

fn parse_constant_value_attribute(input: &[u8]) -> IResult<&[u8], ConstantValueAttribute> {
    let (input, constantvalue_index) = be_u16(input)?;
    Ok((
        input,
        ConstantValueAttribute {
            constantvalue_index,
        },
    ))
}

fn parse_exceptions_attribute(input: &[u8]) -> IResult<&[u8], ExceptionsAttribute> {
    let (input, number_of_exceptions) = be_u16(input)?;
    let (input, exception_index_table) = count(be_u16, number_of_exceptions as usize)(input)?;
    Ok((
        input,
        ExceptionsAttribute {
            exception_index_table,
        },
    ))
}

fn parse_bootstrap_methods_attribute(input: &[u8]) -> IResult<&[u8], BootstrapMethodsAttribute> {
    let (input, num_bootstrap_methods) = be_u16(input)?;
    let (input, bootstrap_methods) =
        count(parse_bootstrap_method_entry, num_bootstrap_methods as usize)(input)?;
    Ok((input, BootstrapMethodsAttribute { bootstrap_methods }))
}

fn parse_bootstrap_method_entry(input: &[u8]) -> IResult<&[u8], BootstrapMethodEntry> {
    let (input, bootstrap_method_ref) = be_u16(input)?;
    let (input, num_bootstrap_arguments) = be_u16(input)?;
    let (input, bootstrap_arguments) = count(be_u16, num_bootstrap_arguments as usize)(input)?;
    Ok((
        input,
        BootstrapMethodEntry {
            bootstrap_method_ref,
            bootstrap_arguments,
        },
    ))
}

fn parse_stack_map_table_attribute(input: &[u8]) -> IResult<&[u8], StackMapTableAttribute> {
    let (input, number_of_entries) = be_u16(input)?;
    let mut remaining = input;
    let mut entries = Vec::with_capacity(number_of_entries as usize);
    for _ in 0..number_of_entries {
        let (rem, frame) = parse_stack_map_frame(remaining)?;
        entries.push(frame);
        remaining = rem;
    }
    Ok((remaining, StackMapTableAttribute { entries }))
}

fn parse_stack_map_frame(input: &[u8]) -> IResult<&[u8], StackMapFrame> {
    let (input, frame_type) = be_u8(input)?;
    match frame_type {
        0..=63 => Ok((input, StackMapFrame::SameFrame { frame_type })),
        64..=127 => {
            let (input, stack) = parse_verification_type_info(input)?;
            Ok((
                input,
                StackMapFrame::SameLocals1StackItemFrame { frame_type, stack },
            ))
        }
        247 => {
            let (input, offset_delta) = be_u16(input)?;
            let (input, stack) = parse_verification_type_info(input)?;
            Ok((
                input,
                StackMapFrame::SameLocals1StackItemFrameExtended {
                    offset_delta,
                    stack,
                },
            ))
        }
        248..=250 => {
            let (input, offset_delta) = be_u16(input)?;
            Ok((
                input,
                StackMapFrame::ChopFrame {
                    frame_type,
                    offset_delta,
                },
            ))
        }
        251 => {
            let (input, offset_delta) = be_u16(input)?;
            Ok((input, StackMapFrame::SameFrameExtended { offset_delta }))
        }
        252..=254 => {
            let (input, offset_delta) = be_u16(input)?;
            let num_locals = (frame_type - 251) as usize;
            let (input, locals) = count(parse_verification_type_info, num_locals)(input)?;
            Ok((
                input,
                StackMapFrame::AppendFrame {
                    frame_type,
                    offset_delta,
                    locals,
                },
            ))
        }
        255 => {
            let (input, offset_delta) = be_u16(input)?;
            let (input, number_of_locals) = be_u16(input)?;
            let (input, locals) =
                count(parse_verification_type_info, number_of_locals as usize)(input)?;
            let (input, number_of_stack_items) = be_u16(input)?;
            let (input, stack) =
                count(parse_verification_type_info, number_of_stack_items as usize)(input)?;
            Ok((
                input,
                StackMapFrame::FullFrame {
                    offset_delta,
                    locals,
                    stack,
                },
            ))
        }
        // Reserved frame types 128-246
        _ => Err(nom::Err::Error(nom::error::Error::new(
            input,
            nom::error::ErrorKind::Tag,
        ))),
    }
}

fn parse_verification_type_info(input: &[u8]) -> IResult<&[u8], VerificationTypeInfo> {
    let (input, tag) = be_u8(input)?;
    match tag {
        0 => Ok((input, VerificationTypeInfo::Top)),
        1 => Ok((input, VerificationTypeInfo::Integer)),
        2 => Ok((input, VerificationTypeInfo::Float)),
        3 => Ok((input, VerificationTypeInfo::Double)),
        4 => Ok((input, VerificationTypeInfo::Long)),
        5 => Ok((input, VerificationTypeInfo::Null)),
        6 => Ok((input, VerificationTypeInfo::UninitializedThis)),
        7 => {
            let (input, cpool_index) = be_u16(input)?;
            Ok((input, VerificationTypeInfo::Object { cpool_index }))
        }
        8 => {
            let (input, offset) = be_u16(input)?;
            Ok((input, VerificationTypeInfo::Uninitialized { offset }))
        }
        _ => Err(nom::Err::Error(nom::error::Error::new(
            input,
            nom::error::ErrorKind::Tag,
        ))),
    }
}

fn parse_inner_classes_attribute(input: &[u8]) -> IResult<&[u8], InnerClassesAttribute> {
    let (input, number_of_classes) = be_u16(input)?;
    let (input, classes) = count(parse_inner_class, number_of_classes as usize)(input)?;
    Ok((input, InnerClassesAttribute { classes }))
}

fn parse_inner_class(input: &[u8]) -> IResult<&[u8], InnerClass> {
    let (input, inner_class_info_index) = be_u16(input)?;
    let (input, outer_class_info_index) = be_u16(input)?;
    let (input, inner_name_index) = be_u16(input)?;
    let (input, access_flags) = be_u16(input)?;
    Ok((
        input,
        InnerClass {
            inner_class_info_index,
            outer_class_info_index,
            inner_name_index,
            inner_class_access_flags: ClassAccessFlags::from_bits_truncate(access_flags),
        },
    ))
}

fn parse_source_file_attribute(input: &[u8]) -> IResult<&[u8], SourceFileAttribute> {
    let (input, sourcefile_index) = be_u16(input)?;
    Ok((input, SourceFileAttribute { sourcefile_index }))
}

fn parse_line_number_table_attribute(input: &[u8]) -> IResult<&[u8], LineNumberTableAttribute> {
    let (input, line_number_table_length) = be_u16(input)?;
    let (input, line_number_table) =
        count(parse_line_number_entry, line_number_table_length as usize)(input)?;
    Ok((input, LineNumberTableAttribute { line_number_table }))
}

fn parse_line_number_entry(input: &[u8]) -> IResult<&[u8], LineNumberEntry> {
    let (input, start_pc) = be_u16(input)?;
    let (input, line_number) = be_u16(input)?;
    Ok((
        input,
        LineNumberEntry {
            start_pc,
            line_number,
        },
    ))
}

fn parse_local_variable_table_attribute(
    input: &[u8],
) -> IResult<&[u8], LocalVariableTableAttribute> {
    let (input, local_variable_table_length) = be_u16(input)?;
    let (input, local_variable_table) = count(
        parse_local_variable_entry,
        local_variable_table_length as usize,
    )(input)?;
    Ok((
        input,
        LocalVariableTableAttribute {
            local_variable_table,
        },
    ))
}

fn parse_local_variable_entry(input: &[u8]) -> IResult<&[u8], LocalVariableEntry> {
    let (input, start_pc) = be_u16(input)?;
    let (input, length) = be_u16(input)?;
    let (input, name_index) = be_u16(input)?;
    let (input, descriptor_index) = be_u16(input)?;
    let (input, index) = be_u16(input)?;
    Ok((
        input,
        LocalVariableEntry {
            start_pc,
            length,
            name_index,
            descriptor_index,
            index,
        },
    ))
}

fn parse_local_variable_type_table_attribute(
    input: &[u8],
) -> IResult<&[u8], LocalVariableTypeTableAttribute> {
    let (input, local_variable_type_table_length) = be_u16(input)?;
    let (input, local_variable_type_table) = count(
        parse_local_variable_type_entry,
        local_variable_type_table_length as usize,
    )(input)?;
    Ok((
        input,
        LocalVariableTypeTableAttribute {
            local_variable_type_table,
        },
    ))
}

fn parse_local_variable_type_entry(input: &[u8]) -> IResult<&[u8], LocalVariableTypeEntry> {
    let (input, start_pc) = be_u16(input)?;
    let (input, length) = be_u16(input)?;
    let (input, name_index) = be_u16(input)?;
    let (input, signature_index) = be_u16(input)?;
    let (input, index) = be_u16(input)?;
    Ok((
        input,
        LocalVariableTypeEntry {
            start_pc,
            length,
            name_index,
            signature_index,
            index,
        },
    ))
}

fn parse_runtime_annotations_attribute(
    input: &[u8],
) -> IResult<&[u8], RuntimeAnnotationsAttribute> {
    let (input, num_annotations) = be_u16(input)?;
    let (input, annotations) = count(parse_annotation, num_annotations as usize)(input)?;
    Ok((input, RuntimeAnnotationsAttribute { annotations }))
}

fn parse_annotation(input: &[u8]) -> IResult<&[u8], Annotation> {
    let (input, type_index) = be_u16(input)?;
    let (input, num_element_value_pairs) = be_u16(input)?;
    let (input, element_value_pairs) =
        count(parse_element_value_pair, num_element_value_pairs as usize)(input)?;
    Ok((
        input,
        Annotation {
            type_index,
            element_value_pairs,
        },
    ))
}

fn parse_element_value_pair(input: &[u8]) -> IResult<&[u8], (u16, ElementValue)> {
    let (input, element_name_index) = be_u16(input)?;
    let (input, value) = parse_element_value(input)?;
    Ok((input, (element_name_index, value)))
}

fn parse_element_value(input: &[u8]) -> IResult<&[u8], ElementValue> {
    let (input, tag) = be_u8(input)?;
    match tag {
        b'B' | b'C' | b'D' | b'F' | b'I' | b'J' | b'S' | b'Z' | b's' => {
            let (input, const_value_index) = be_u16(input)?;
            let ev = match tag {
                b'B' => ElementValue::Byte { const_value_index },
                b'C' => ElementValue::Char { const_value_index },
                b'D' => ElementValue::Double { const_value_index },
                b'F' => ElementValue::Float { const_value_index },
                b'I' => ElementValue::Int { const_value_index },
                b'J' => ElementValue::Long { const_value_index },
                b'S' => ElementValue::Short { const_value_index },
                b'Z' => ElementValue::Boolean { const_value_index },
                b's' => ElementValue::String { const_value_index },
                _ => unreachable!(),
            };
            Ok((input, ev))
        }
        b'e' => {
            let (input, type_name_index) = be_u16(input)?;
            let (input, const_name_index) = be_u16(input)?;
            Ok((
                input,
                ElementValue::Enum {
                    type_name_index,
                    const_name_index,
                },
            ))
        }
        b'c' => {
            let (input, class_info_index) = be_u16(input)?;
            Ok((input, ElementValue::Class { class_info_index }))
        }
        b'@' => {
            let (input, annotation) = parse_annotation(input)?;
            Ok((input, ElementValue::AnnotationType { annotation }))
        }
        b'[' => {
            let (input, num_values) = be_u16(input)?;
            let (input, values) = count(parse_element_value, num_values as usize)(input)?;
            Ok((input, ElementValue::Array { values }))
        }
        _ => Err(nom::Err::Error(nom::error::Error::new(
            input,
            nom::error::ErrorKind::Tag,
        ))),
    }
}

fn parse_nest_host_attribute(input: &[u8]) -> IResult<&[u8], NestHostAttribute> {
    let (input, host_class_index) = be_u16(input)?;
    Ok((input, NestHostAttribute { host_class_index }))
}

fn parse_nest_members_attribute(input: &[u8]) -> IResult<&[u8], NestMembersAttribute> {
    let (input, number_of_classes) = be_u16(input)?;
    let (input, classes) = count(be_u16, number_of_classes as usize)(input)?;
    Ok((input, NestMembersAttribute { classes }))
}

fn parse_record_attribute(input: &[u8]) -> IResult<&[u8], RecordAttribute> {
    let (input, number_of_components) = be_u16(input)?;
    let (input, components) = count(parse_record_component, number_of_components as usize)(input)?;
    Ok((input, RecordAttribute { components }))
}

fn parse_record_component(input: &[u8]) -> IResult<&[u8], RecordComponentInfo> {
    let (input, name_index) = be_u16(input)?;
    let (input, descriptor_index) = be_u16(input)?;
    let (input, attributes) = parse_attributes(input)?;
    Ok((
        input,
        RecordComponentInfo {
            name_index,
            descriptor_index,
            attributes,
        },
    ))
}

fn parse_permitted_subclasses_attribute(
    input: &[u8],
) -> IResult<&[u8], PermittedSubclassesAttribute> {
    let (input, number_of_classes) = be_u16(input)?;
    let (input, classes) = count(be_u16, number_of_classes as usize)(input)?;
    Ok((input, PermittedSubclassesAttribute { classes }))
}

fn parse_signature_attribute(input: &[u8]) -> IResult<&[u8], u16> {
    let (input, signature_index) = be_u16(input)?;
    Ok((input, signature_index))
}

fn parse_runtime_parameter_annotations_attribute(
    input: &[u8],
) -> IResult<&[u8], RuntimeParameterAnnotationsAttribute> {
    let (input, num_parameters) = be_u8(input)?;
    let mut remaining = input;
    let mut parameter_annotations = Vec::with_capacity(num_parameters as usize);
    for _ in 0..num_parameters {
        let (rem, annotations) = parse_runtime_annotations_attribute(remaining)?;
        parameter_annotations.push(ParameterAnnotation {
            annotations: annotations.annotations,
        });
        remaining = rem;
    }
    Ok((
        remaining,
        RuntimeParameterAnnotationsAttribute {
            parameter_annotations,
        },
    ))
}

fn parse_runtime_type_annotations_attribute(
    input: &[u8],
) -> IResult<&[u8], RuntimeTypeAnnotationsAttribute> {
    let (input, num_annotations) = be_u16(input)?;
    let mut remaining = input;
    let mut annotations = Vec::with_capacity(num_annotations as usize);
    for _ in 0..num_annotations {
        let (rem, annotation) = parse_type_annotation(remaining)?;
        annotations.push(annotation);
        remaining = rem;
    }
    Ok((remaining, RuntimeTypeAnnotationsAttribute { annotations }))
}

fn parse_type_annotation(input: &[u8]) -> IResult<&[u8], TypeAnnotation> {
    let (input, target) = parse_type_annotation_target(input)?;
    let (input, target_path) = parse_type_path(input)?;
    let (input, type_index) = be_u16(input)?;
    let (input, num_element_value_pairs) = be_u16(input)?;
    let (input, element_value_pairs) =
        count(parse_element_value_pair, num_element_value_pairs as usize)(input)?;
    Ok((
        input,
        TypeAnnotation {
            target,
            target_path,
            type_index,
            element_value_pairs,
        },
    ))
}

fn parse_type_annotation_target(input: &[u8]) -> IResult<&[u8], TypeAnnotationTarget> {
    let (input, target_type) = be_u8(input)?;
    match target_type {
        0x00 | 0x01 => {
            let (input, type_parameter_index) = be_u8(input)?;
            Ok((
                input,
                TypeAnnotationTarget::TypeParameter {
                    type_parameter_index,
                },
            ))
        }
        0x10 => {
            let (input, super_type_index) = be_u16(input)?;
            Ok((input, TypeAnnotationTarget::SuperType { super_type_index }))
        }
        0x11 | 0x12 => {
            let (input, type_parameter_index) = be_u8(input)?;
            let (input, bound_index) = be_u8(input)?;
            Ok((
                input,
                TypeAnnotationTarget::TypeParameterBound {
                    type_parameter_index,
                    bound_index,
                },
            ))
        }
        0x13..=0x15 => Ok((input, TypeAnnotationTarget::Empty)),
        0x16 => {
            let (input, formal_parameter_index) = be_u8(input)?;
            Ok((
                input,
                TypeAnnotationTarget::FormalParameter {
                    formal_parameter_index,
                },
            ))
        }
        0x17 => {
            let (input, throws_type_index) = be_u16(input)?;
            Ok((input, TypeAnnotationTarget::Throws { throws_type_index }))
        }
        0x40 | 0x41 => {
            let (input, table_length) = be_u16(input)?;
            let (input, table) = count(parse_local_var_target_entry, table_length as usize)(input)?;
            Ok((input, TypeAnnotationTarget::LocalVar { table }))
        }
        0x42 => {
            let (input, exception_table_index) = be_u16(input)?;
            Ok((
                input,
                TypeAnnotationTarget::Catch {
                    exception_table_index,
                },
            ))
        }
        0x43..=0x46 => {
            let (input, offset) = be_u16(input)?;
            Ok((input, TypeAnnotationTarget::Offset { offset }))
        }
        0x47..=0x4B => {
            let (input, offset) = be_u16(input)?;
            let (input, type_argument_index) = be_u8(input)?;
            Ok((
                input,
                TypeAnnotationTarget::TypeArgument {
                    offset,
                    type_argument_index,
                },
            ))
        }
        _ => Err(nom::Err::Error(nom::error::Error::new(
            input,
            nom::error::ErrorKind::Tag,
        ))),
    }
}

fn parse_local_var_target_entry(input: &[u8]) -> IResult<&[u8], LocalVarTargetEntry> {
    let (input, start_pc) = be_u16(input)?;
    let (input, length) = be_u16(input)?;
    let (input, index) = be_u16(input)?;
    Ok((
        input,
        LocalVarTargetEntry {
            start_pc,
            length,
            index,
        },
    ))
}

fn parse_type_path(input: &[u8]) -> IResult<&[u8], Vec<TypePathEntry>> {
    let (input, path_length) = be_u8(input)?;
    let (input, entries) = count(parse_type_path_entry, path_length as usize)(input)?;
    Ok((input, entries))
}

fn parse_type_path_entry(input: &[u8]) -> IResult<&[u8], TypePathEntry> {
    let (input, type_path_kind) = be_u8(input)?;
    let (input, type_argument_index) = be_u8(input)?;
    Ok((
        input,
        TypePathEntry {
            type_path_kind,
            type_argument_index,
        },
    ))
}

fn parse_enclosing_method_attribute(input: &[u8]) -> IResult<&[u8], EnclosingMethodAttribute> {
    let (input, class_index) = be_u16(input)?;
    let (input, method_index) = be_u16(input)?;
    Ok((
        input,
        EnclosingMethodAttribute {
            class_index,
            method_index,
        },
    ))
}

fn parse_annotation_default_attribute(input: &[u8]) -> IResult<&[u8], AnnotationDefaultAttribute> {
    let (input, default_value) = parse_element_value(input)?;
    Ok((input, AnnotationDefaultAttribute { default_value }))
}

fn parse_method_parameters_attribute(input: &[u8]) -> IResult<&[u8], MethodParametersAttribute> {
    let (input, parameters_count) = be_u8(input)?;
    let (input, parameters) = count(parse_method_parameter, parameters_count as usize)(input)?;
    Ok((input, MethodParametersAttribute { parameters }))
}

fn parse_method_parameter(input: &[u8]) -> IResult<&[u8], MethodParameter> {
    let (input, name_index) = be_u16(input)?;
    let (input, access_flags) = be_u16(input)?;
    Ok((
        input,
        MethodParameter {
            name_index,
            access_flags,
        },
    ))
}

fn parse_module_attribute(input: &[u8]) -> IResult<&[u8], ModuleAttribute> {
    let (input, module_name_index) = be_u16(input)?;
    let (input, module_flags) = be_u16(input)?;
    let (input, module_version_index) = be_u16(input)?;
    let (input, requires_count) = be_u16(input)?;
    let (input, requires) = count(parse_module_requires, requires_count as usize)(input)?;
    let (input, exports_count) = be_u16(input)?;
    let (input, exports) = count(parse_module_exports, exports_count as usize)(input)?;
    let (input, opens_count) = be_u16(input)?;
    let (input, opens) = count(parse_module_opens, opens_count as usize)(input)?;
    let (input, uses_count) = be_u16(input)?;
    let (input, uses_index) = count(be_u16, uses_count as usize)(input)?;
    let (input, provides_count) = be_u16(input)?;
    let (input, provides) = count(parse_module_provides, provides_count as usize)(input)?;
    Ok((
        input,
        ModuleAttribute {
            module_name_index,
            module_flags,
            module_version_index,
            requires,
            exports,
            opens,
            uses_index,
            provides,
        },
    ))
}

fn parse_module_requires(input: &[u8]) -> IResult<&[u8], ModuleRequires> {
    let (input, requires_index) = be_u16(input)?;
    let (input, requires_flags) = be_u16(input)?;
    let (input, requires_version_index) = be_u16(input)?;
    Ok((
        input,
        ModuleRequires {
            requires_index,
            requires_flags,
            requires_version_index,
        },
    ))
}

fn parse_module_exports(input: &[u8]) -> IResult<&[u8], ModuleExports> {
    let (input, exports_index) = be_u16(input)?;
    let (input, exports_flags) = be_u16(input)?;
    let (input, exports_to_count) = be_u16(input)?;
    let (input, exports_to_index) = count(be_u16, exports_to_count as usize)(input)?;
    Ok((
        input,
        ModuleExports {
            exports_index,
            exports_flags,
            exports_to_index,
        },
    ))
}

fn parse_module_opens(input: &[u8]) -> IResult<&[u8], ModuleOpens> {
    let (input, opens_index) = be_u16(input)?;
    let (input, opens_flags) = be_u16(input)?;
    let (input, opens_to_count) = be_u16(input)?;
    let (input, opens_to_index) = count(be_u16, opens_to_count as usize)(input)?;
    Ok((
        input,
        ModuleOpens {
            opens_index,
            opens_flags,
            opens_to_index,
        },
    ))
}

fn parse_module_provides(input: &[u8]) -> IResult<&[u8], ModuleProvides> {
    let (input, provides_index) = be_u16(input)?;
    let (input, provides_with_count) = be_u16(input)?;
    let (input, provides_with_index) = count(be_u16, provides_with_count as usize)(input)?;
    Ok((
        input,
        ModuleProvides {
            provides_index,
            provides_with_index,
        },
    ))
}

fn parse_module_packages_attribute(input: &[u8]) -> IResult<&[u8], ModulePackagesAttribute> {
    let (input, package_count) = be_u16(input)?;
    let (input, package_index) = count(be_u16, package_count as usize)(input)?;
    Ok((input, ModulePackagesAttribute { package_index }))
}

fn parse_module_main_class_attribute(input: &[u8]) -> IResult<&[u8], ModuleMainClassAttribute> {
    let (input, main_class_index) = be_u16(input)?;
    Ok((input, ModuleMainClassAttribute { main_class_index }))
}
