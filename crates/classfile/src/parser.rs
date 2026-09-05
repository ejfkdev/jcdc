use nom::{bytes::complete::tag, multi::count, number::complete::be_u16, IResult};

use crate::attribute::parse_attributes;
use crate::constant_pool::parse_constant_pool;
use crate::field::parse_field;
use crate::method::parse_method;
use crate::types::*;

/// Parse a Java class file from raw bytes.
///
/// Returns the remaining unparsed bytes and the parsed `ClassFile`.
/// Fails if the magic number (0xCAFEBABE) doesn't match or the data is malformed.
pub fn parse_classfile(input: &[u8]) -> IResult<&[u8], ClassFile> {
    // Magic number: 0xCAFEBABE
    let (input, _) = tag(&[0xCA, 0xFE, 0xBA, 0xBE])(input)?;

    let (input, minor_version) = be_u16(input)?;
    let (input, major_version) = be_u16(input)?;

    let (input, constant_pool_count) = be_u16(input)?;
    let (input, constant_pool) = parse_constant_pool(input, constant_pool_count)?;

    let (input, access_flags) = be_u16(input)?;
    let (input, this_class) = be_u16(input)?;
    let (input, super_class) = be_u16(input)?;

    let (input, interfaces_count) = be_u16(input)?;
    let (input, interfaces) = count(be_u16, interfaces_count as usize)(input)?;

    let (input, fields_count) = be_u16(input)?;
    let (input, fields) = count(parse_field, fields_count as usize)(input)?;

    let (input, methods_count) = be_u16(input)?;
    let (input, methods) = count(parse_method, methods_count as usize)(input)?;

    let (input, attributes) = parse_attributes(input)?;

    Ok((
        input,
        ClassFile {
            minor_version,
            major_version,
            constant_pool,
            access_flags: ClassAccessFlags::from_bits_truncate(access_flags),
            this_class,
            super_class,
            interfaces,
            fields,
            methods,
            attributes,
        },
    ))
}
