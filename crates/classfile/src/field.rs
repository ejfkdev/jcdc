use nom::{number::complete::be_u16, IResult};

use crate::attribute::parse_attributes;
use crate::types::{FieldAccessFlags, FieldInfo};

pub fn parse_field(input: &[u8]) -> IResult<&[u8], FieldInfo> {
    let (input, access_flags) = be_u16(input)?;
    let (input, name_index) = be_u16(input)?;
    let (input, descriptor_index) = be_u16(input)?;
    let (input, attributes) = parse_attributes(input)?;
    Ok((
        input,
        FieldInfo {
            access_flags: FieldAccessFlags::from_bits_truncate(access_flags),
            name_index,
            descriptor_index,
            attributes,
        },
    ))
}
