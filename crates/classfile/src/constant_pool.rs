use nom::{
    bytes::complete::take,
    combinator::map,
    number::complete::{be_f32, be_f64, be_u16, be_u32, be_u64, be_u8},
    IResult,
};

use crate::types::*;

pub fn parse_constant_pool(input: &[u8], count: u16) -> IResult<&[u8], Vec<ConstantPoolEntry>> {
    let mut entries = Vec::with_capacity(count as usize);
    // Index 0 is unused, but we skip it; entries are 1-indexed.
    // We parse count-1 entries (index 1 to count-1).
    let mut remaining = input;
    let mut i = 1u16;
    while i < count {
        let (rem, entry) = parse_constant_pool_entry(remaining)?;
        let takes_two = entry.takes_two_slots();
        entries.push(entry);
        i += 1;
        if takes_two {
            // Long and Double occupy two slots; the second slot is unusable.
            i += 1;
        }
        remaining = rem;
    }
    Ok((remaining, entries))
}

fn parse_constant_pool_entry(input: &[u8]) -> IResult<&[u8], ConstantPoolEntry> {
    let (input, tag) = be_u8(input)?;
    match tag {
        cp_tag::UTF8 => map(parse_utf8_info, ConstantPoolEntry::Utf8)(input),
        cp_tag::INTEGER => map(parse_integer_info, ConstantPoolEntry::Integer)(input),
        cp_tag::FLOAT => map(parse_float_info, ConstantPoolEntry::Float)(input),
        cp_tag::LONG => map(parse_long_info, ConstantPoolEntry::Long)(input),
        cp_tag::DOUBLE => map(parse_double_info, ConstantPoolEntry::Double)(input),
        cp_tag::CLASS => map(parse_class_info, ConstantPoolEntry::Class)(input),
        cp_tag::STRING => map(parse_string_info, ConstantPoolEntry::String)(input),
        cp_tag::FIELDREF => map(parse_fieldref_info, ConstantPoolEntry::Fieldref)(input),
        cp_tag::METHODREF => map(parse_methodref_info, ConstantPoolEntry::Methodref)(input),
        cp_tag::INTERFACE_METHODREF => map(
            parse_interface_methodref_info,
            ConstantPoolEntry::InterfaceMethodref,
        )(input),
        cp_tag::NAME_AND_TYPE => {
            map(parse_name_and_type_info, ConstantPoolEntry::NameAndType)(input)
        }
        cp_tag::METHOD_HANDLE => {
            map(parse_method_handle_info, ConstantPoolEntry::MethodHandle)(input)
        }
        cp_tag::METHOD_TYPE => map(parse_method_type_info, ConstantPoolEntry::MethodType)(input),
        cp_tag::DYNAMIC => map(parse_dynamic_info, ConstantPoolEntry::Dynamic)(input),
        cp_tag::INVOKE_DYNAMIC => {
            map(parse_invoke_dynamic_info, ConstantPoolEntry::InvokeDynamic)(input)
        }
        cp_tag::MODULE => map(parse_module_info, ConstantPoolEntry::Module)(input),
        cp_tag::PACKAGE => map(parse_package_info, ConstantPoolEntry::Package)(input),
        _ => Err(nom::Err::Error(nom::error::Error::new(
            input,
            nom::error::ErrorKind::Tag,
        ))),
    }
}

fn parse_utf8_info(input: &[u8]) -> IResult<&[u8], Utf8Info> {
    let (input, length) = be_u16(input)?;
    let (input, bytes) = take(length as usize)(input)?;
    // Modified UTF-8 decoding (CESU-8)
    let value = cesu8::from_java_cesu8(bytes)
        .map(|s| s.into_owned())
        .unwrap_or_else(|_| String::from_utf8_lossy(bytes).into_owned());
    Ok((input, Utf8Info { value }))
}

fn parse_integer_info(input: &[u8]) -> IResult<&[u8], IntegerInfo> {
    let (input, value) = be_u32(input)?;
    Ok((
        input,
        IntegerInfo {
            value: value as i32,
        },
    ))
}

fn parse_float_info(input: &[u8]) -> IResult<&[u8], FloatInfo> {
    let (input, value) = be_f32(input)?;
    Ok((input, FloatInfo { value }))
}

fn parse_long_info(input: &[u8]) -> IResult<&[u8], LongInfo> {
    let (input, value) = be_u64(input)?;
    Ok((
        input,
        LongInfo {
            value: value as i64,
        },
    ))
}

fn parse_double_info(input: &[u8]) -> IResult<&[u8], DoubleInfo> {
    let (input, value) = be_f64(input)?;
    Ok((input, DoubleInfo { value }))
}

fn parse_class_info(input: &[u8]) -> IResult<&[u8], ClassInfo> {
    let (input, name_index) = be_u16(input)?;
    Ok((input, ClassInfo { name_index }))
}

fn parse_string_info(input: &[u8]) -> IResult<&[u8], StringInfo> {
    let (input, string_index) = be_u16(input)?;
    Ok((input, StringInfo { string_index }))
}

fn parse_fieldref_info(input: &[u8]) -> IResult<&[u8], FieldrefInfo> {
    let (input, class_index) = be_u16(input)?;
    let (input, name_and_type_index) = be_u16(input)?;
    Ok((
        input,
        FieldrefInfo {
            class_index,
            name_and_type_index,
        },
    ))
}

fn parse_methodref_info(input: &[u8]) -> IResult<&[u8], MethodrefInfo> {
    let (input, class_index) = be_u16(input)?;
    let (input, name_and_type_index) = be_u16(input)?;
    Ok((
        input,
        MethodrefInfo {
            class_index,
            name_and_type_index,
        },
    ))
}

fn parse_interface_methodref_info(input: &[u8]) -> IResult<&[u8], InterfaceMethodrefInfo> {
    let (input, class_index) = be_u16(input)?;
    let (input, name_and_type_index) = be_u16(input)?;
    Ok((
        input,
        InterfaceMethodrefInfo {
            class_index,
            name_and_type_index,
        },
    ))
}

fn parse_name_and_type_info(input: &[u8]) -> IResult<&[u8], NameAndTypeInfo> {
    let (input, name_index) = be_u16(input)?;
    let (input, descriptor_index) = be_u16(input)?;
    Ok((
        input,
        NameAndTypeInfo {
            name_index,
            descriptor_index,
        },
    ))
}

fn parse_method_handle_info(input: &[u8]) -> IResult<&[u8], MethodHandleInfo> {
    let (input, reference_kind) = be_u8(input)?;
    let (input, reference_index) = be_u16(input)?;
    Ok((
        input,
        MethodHandleInfo {
            reference_kind,
            reference_index,
        },
    ))
}

fn parse_method_type_info(input: &[u8]) -> IResult<&[u8], MethodTypeInfo> {
    let (input, descriptor_index) = be_u16(input)?;
    Ok((input, MethodTypeInfo { descriptor_index }))
}

fn parse_dynamic_info(input: &[u8]) -> IResult<&[u8], DynamicInfo> {
    let (input, bootstrap_method_attr_index) = be_u16(input)?;
    let (input, name_and_type_index) = be_u16(input)?;
    Ok((
        input,
        DynamicInfo {
            bootstrap_method_attr_index,
            name_and_type_index,
        },
    ))
}

fn parse_invoke_dynamic_info(input: &[u8]) -> IResult<&[u8], InvokeDynamicInfo> {
    let (input, bootstrap_method_attr_index) = be_u16(input)?;
    let (input, name_and_type_index) = be_u16(input)?;
    Ok((
        input,
        InvokeDynamicInfo {
            bootstrap_method_attr_index,
            name_and_type_index,
        },
    ))
}

fn parse_module_info(input: &[u8]) -> IResult<&[u8], ModuleInfo> {
    let (input, name_index) = be_u16(input)?;
    Ok((input, ModuleInfo { name_index }))
}

fn parse_package_info(input: &[u8]) -> IResult<&[u8], PackageInfo> {
    let (input, name_index) = be_u16(input)?;
    Ok((input, PackageInfo { name_index }))
}

/// Helper to resolve a UTF8 string from the constant pool by index (1-based).
/// Returns None if the index is out of bounds or not a UTF8 entry.
pub fn get_utf8(pool: &[ConstantPoolEntry], index: u16) -> Option<&str> {
    if index == 0 {
        return None;
    }
    // Entries are stored sequentially; we need to account for Long/Double taking 2 slots.
    let mut slot = 1u16;
    for entry in pool {
        if slot == index {
            if let ConstantPoolEntry::Utf8(utf8) = entry {
                return Some(&utf8.value);
            }
            return None;
        }
        slot += 1;
        if entry.takes_two_slots() {
            slot += 1;
        }
    }
    None
}

/// Helper to get a constant pool entry by its logical index (1-based, accounting for Long/Double double-slot).
pub fn get_entry(pool: &[ConstantPoolEntry], index: u16) -> Option<&ConstantPoolEntry> {
    if index == 0 {
        return None;
    }
    let mut slot = 1u16;
    for entry in pool {
        if slot == index {
            return Some(entry);
        }
        slot += 1;
        if entry.takes_two_slots() {
            slot += 1;
        }
    }
    None
}

/// O(1) constant pool lookup table. Build once per class file; `pos[slot]`
/// stores the vec position + 1 of the entry occupying that logical slot
/// (0 = no entry: index 0 or the unusable second slot of Long/Double).
#[derive(Debug, Clone)]
pub struct CpLookup {
    pos: Vec<u32>,
}

impl CpLookup {
    pub fn new(pool: &[ConstantPoolEntry]) -> Self {
        let mut pos = Vec::with_capacity(pool.len() + 1);
        pos.push(0); // slot 0 unused
        let mut slot = 1u32;
        for (i, entry) in pool.iter().enumerate() {
            while pos.len() <= slot as usize {
                pos.push(0);
            }
            pos[slot as usize] = i as u32 + 1;
            slot += 1;
            if entry.takes_two_slots() {
                pos.push(0);
                slot += 1;
            }
        }
        CpLookup { pos }
    }

    /// Get a constant pool entry by its logical 1-based index.
    pub fn get<'a>(&self, pool: &'a [ConstantPoolEntry], index: u16) -> Option<&'a ConstantPoolEntry> {
        let p = *self.pos.get(index as usize)?;
        if p == 0 {
            return None;
        }
        pool.get(p as usize - 1)
    }

    /// Get a CONSTANT_Utf8 string by its logical index.
    pub fn utf8<'a>(&self, pool: &'a [ConstantPoolEntry], index: u16) -> Option<&'a str> {
        match self.get(pool, index)? {
            ConstantPoolEntry::Utf8(u) => Some(&u.value),
            _ => None,
        }
    }

    /// Resolve a CONSTANT_Class index to its internal name.
    pub fn class_name<'a>(&self, pool: &'a [ConstantPoolEntry], index: u16) -> Option<&'a str> {
        match self.get(pool, index)? {
            ConstantPoolEntry::Class(c) => self.utf8(pool, c.name_index),
            ConstantPoolEntry::Module(m) => self.utf8(pool, m.name_index),
            ConstantPoolEntry::Package(p) => self.utf8(pool, p.name_index),
            _ => None,
        }
    }

    /// Resolve a CONSTANT_String index to its value.
    pub fn string_value<'a>(&self, pool: &'a [ConstantPoolEntry], index: u16) -> Option<&'a str> {
        match self.get(pool, index)? {
            ConstantPoolEntry::String(s) => self.utf8(pool, s.string_index),
            _ => None,
        }
    }

    /// Resolve a NameAndType index to (name, descriptor).
    pub fn name_and_type<'a>(
        &self,
        pool: &'a [ConstantPoolEntry],
        index: u16,
    ) -> Option<(&'a str, &'a str)> {
        match self.get(pool, index)? {
            ConstantPoolEntry::NameAndType(nt) => Some((
                self.utf8(pool, nt.name_index)?,
                self.utf8(pool, nt.descriptor_index)?,
            )),
            _ => None,
        }
    }

    /// Resolve a field/method/interface-method ref index to
    /// (owner_internal_name, name, descriptor).
    pub fn member_ref<'a>(
        &self,
        pool: &'a [ConstantPoolEntry],
        index: u16,
    ) -> Option<(&'a str, &'a str, &'a str)> {
        let (class_index, nat_index) = match self.get(pool, index)? {
            ConstantPoolEntry::Fieldref(i) => (i.class_index, i.name_and_type_index),
            ConstantPoolEntry::Methodref(i) => (i.class_index, i.name_and_type_index),
            ConstantPoolEntry::InterfaceMethodref(i) => (i.class_index, i.name_and_type_index),
            _ => return None,
        };
        let (name, desc) = self.name_and_type(pool, nat_index)?;
        Some((self.class_name(pool, class_index)?, name, desc))
    }
}
