use nom::{number::complete::be_u16, IResult};

use crate::attribute::parse_attributes;
use crate::types::{MethodAccessFlags, MethodInfo};

pub fn parse_method(input: &[u8]) -> IResult<&[u8], MethodInfo> {
    let (input, access_flags) = be_u16(input)?;
    let (input, name_index) = be_u16(input)?;
    let (input, descriptor_index) = be_u16(input)?;
    let (input, attributes) = parse_attributes(input)?;
    Ok((
        input,
        MethodInfo {
            access_flags: MethodAccessFlags::from_bits_truncate(access_flags),
            name_index,
            descriptor_index,
            attributes,
        },
    ))
}
