/// Parsed Java class file.
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug, Clone)]
pub struct ClassFile {
    pub minor_version: u16,
    pub major_version: u16,
    pub constant_pool: Vec<ConstantPoolEntry>,
    pub access_flags: ClassAccessFlags,
    pub this_class: u16,
    pub super_class: u16,
    pub interfaces: Vec<u16>,
    pub fields: Vec<FieldInfo>,
    pub methods: Vec<MethodInfo>,
    pub attributes: Vec<AttributeInfo>,
}

// Access flags live in the shared core now (JVM and DEX share the bit
// values), so the parser and the decompiler cannot drift apart on them.
pub use jdc_core::types::{ClassAccessFlags, FieldAccessFlags, MethodAccessFlags};

/// Constant pool entry tags.
pub mod cp_tag {
    pub const UTF8: u8 = 1;
    pub const INTEGER: u8 = 3;
    pub const FLOAT: u8 = 4;
    pub const LONG: u8 = 5;
    pub const DOUBLE: u8 = 6;
    pub const CLASS: u8 = 7;
    pub const STRING: u8 = 8;
    pub const FIELDREF: u8 = 9;
    pub const METHODREF: u8 = 10;
    pub const INTERFACE_METHODREF: u8 = 11;
    pub const NAME_AND_TYPE: u8 = 12;
    pub const METHOD_HANDLE: u8 = 15;
    pub const METHOD_TYPE: u8 = 16;
    pub const DYNAMIC: u8 = 17;
    pub const INVOKE_DYNAMIC: u8 = 18;
    pub const MODULE: u8 = 19;
    pub const PACKAGE: u8 = 20;
}

/// Method handle reference kinds.
pub mod ref_kind {
    pub const GETFIELD: u8 = 1;
    pub const GETSTATIC: u8 = 2;
    pub const PUTFIELD: u8 = 3;
    pub const PUTSTATIC: u8 = 4;
    pub const INVOKEVIRTUAL: u8 = 5;
    pub const INVOKESTATIC: u8 = 6;
    pub const INVOKESPECIAL: u8 = 7;
    pub const NEWINVOKESPECIAL: u8 = 8;
    pub const INVOKEINTERFACE: u8 = 9;
}

/// A constant pool entry. Index 0 is unused; entries are 1-indexed.
/// Long and Double entries occupy two slots.
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug, Clone)]
pub enum ConstantPoolEntry {
    Utf8(Utf8Info),
    Integer(IntegerInfo),
    Float(FloatInfo),
    Long(LongInfo),
    Double(DoubleInfo),
    Class(ClassInfo),
    String(StringInfo),
    Fieldref(FieldrefInfo),
    Methodref(MethodrefInfo),
    InterfaceMethodref(InterfaceMethodrefInfo),
    NameAndType(NameAndTypeInfo),
    MethodHandle(MethodHandleInfo),
    MethodType(MethodTypeInfo),
    Dynamic(DynamicInfo),
    InvokeDynamic(InvokeDynamicInfo),
    Module(ModuleInfo),
    Package(PackageInfo),
}

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug, Clone)]
pub struct Utf8Info {
    pub value: String,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug, Clone)]
pub struct IntegerInfo {
    pub value: i32,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug, Clone)]
pub struct FloatInfo {
    pub value: f32,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug, Clone)]
pub struct LongInfo {
    pub value: i64,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug, Clone)]
pub struct DoubleInfo {
    pub value: f64,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug, Clone)]
pub struct ClassInfo {
    pub name_index: u16,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug, Clone)]
pub struct StringInfo {
    pub string_index: u16,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug, Clone)]
pub struct FieldrefInfo {
    pub class_index: u16,
    pub name_and_type_index: u16,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug, Clone)]
pub struct MethodrefInfo {
    pub class_index: u16,
    pub name_and_type_index: u16,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug, Clone)]
pub struct InterfaceMethodrefInfo {
    pub class_index: u16,
    pub name_and_type_index: u16,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug, Clone)]
pub struct NameAndTypeInfo {
    pub name_index: u16,
    pub descriptor_index: u16,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug, Clone)]
pub struct MethodHandleInfo {
    pub reference_kind: u8,
    pub reference_index: u16,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug, Clone)]
pub struct MethodTypeInfo {
    pub descriptor_index: u16,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug, Clone)]
pub struct DynamicInfo {
    pub bootstrap_method_attr_index: u16,
    pub name_and_type_index: u16,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug, Clone)]
pub struct InvokeDynamicInfo {
    pub bootstrap_method_attr_index: u16,
    pub name_and_type_index: u16,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug, Clone)]
pub struct ModuleInfo {
    pub name_index: u16,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug, Clone)]
pub struct PackageInfo {
    pub name_index: u16,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug, Clone)]
pub struct FieldInfo {
    pub access_flags: FieldAccessFlags,
    pub name_index: u16,
    pub descriptor_index: u16,
    pub attributes: Vec<AttributeInfo>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug, Clone)]
pub struct MethodInfo {
    pub access_flags: MethodAccessFlags,
    pub name_index: u16,
    pub descriptor_index: u16,
    pub attributes: Vec<AttributeInfo>,
}

/// Generic attribute info. Specialized attributes are parsed separately.
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug, Clone)]
pub struct AttributeInfo {
    pub attribute_name_index: u16,
    pub info: Vec<u8>,
}

// Specialized attribute data structures

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug, Clone)]
pub struct CodeAttribute {
    pub max_stack: u16,
    pub max_locals: u16,
    pub code: Vec<u8>,
    pub exception_table: Vec<ExceptionTableEntry>,
    pub attributes: Vec<AttributeInfo>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug, Clone)]
pub struct ExceptionTableEntry {
    pub start_pc: u16,
    pub end_pc: u16,
    pub handler_pc: u16,
    pub catch_type: u16,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug, Clone)]
pub struct ConstantValueAttribute {
    pub constantvalue_index: u16,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug, Clone)]
pub struct ExceptionsAttribute {
    pub exception_index_table: Vec<u16>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug, Clone)]
pub struct BootstrapMethodsAttribute {
    pub bootstrap_methods: Vec<BootstrapMethodEntry>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug, Clone)]
pub struct BootstrapMethodEntry {
    pub bootstrap_method_ref: u16,
    pub bootstrap_arguments: Vec<u16>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug, Clone)]
pub struct StackMapTableAttribute {
    pub entries: Vec<StackMapFrame>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug, Clone)]
pub enum StackMapFrame {
    SameFrame {
        frame_type: u8,
    },
    SameLocals1StackItemFrame {
        frame_type: u8,
        stack: VerificationTypeInfo,
    },
    SameLocals1StackItemFrameExtended {
        offset_delta: u16,
        stack: VerificationTypeInfo,
    },
    ChopFrame {
        frame_type: u8,
        offset_delta: u16,
    },
    SameFrameExtended {
        offset_delta: u16,
    },
    AppendFrame {
        frame_type: u8,
        offset_delta: u16,
        locals: Vec<VerificationTypeInfo>,
    },
    FullFrame {
        offset_delta: u16,
        locals: Vec<VerificationTypeInfo>,
        stack: Vec<VerificationTypeInfo>,
    },
}

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug, Clone)]
pub enum VerificationTypeInfo {
    Top,
    Integer,
    Float,
    Double,
    Long,
    Null,
    UninitializedThis,
    Object { cpool_index: u16 },
    Uninitialized { offset: u16 },
}

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug, Clone)]
pub struct InnerClass {
    pub inner_class_info_index: u16,
    pub outer_class_info_index: u16,
    pub inner_name_index: u16,
    pub inner_class_access_flags: ClassAccessFlags,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug, Clone)]
pub struct InnerClassesAttribute {
    pub classes: Vec<InnerClass>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug, Clone)]
pub struct SourceFileAttribute {
    pub sourcefile_index: u16,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug, Clone)]
pub struct LineNumberTableAttribute {
    pub line_number_table: Vec<LineNumberEntry>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug, Clone)]
pub struct LineNumberEntry {
    pub start_pc: u16,
    pub line_number: u16,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug, Clone)]
pub struct LocalVariableTableAttribute {
    pub local_variable_table: Vec<LocalVariableEntry>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug, Clone)]
pub struct LocalVariableEntry {
    pub start_pc: u16,
    pub length: u16,
    pub name_index: u16,
    pub descriptor_index: u16,
    pub index: u16,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug, Clone)]
pub struct LocalVariableTypeTableAttribute {
    pub local_variable_type_table: Vec<LocalVariableTypeEntry>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug, Clone)]
pub struct LocalVariableTypeEntry {
    pub start_pc: u16,
    pub length: u16,
    pub name_index: u16,
    pub signature_index: u16,
    pub index: u16,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug, Clone)]
pub struct Annotation {
    pub type_index: u16,
    pub element_value_pairs: Vec<(u16, ElementValue)>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug, Clone)]
pub enum ElementValue {
    Byte {
        const_value_index: u16,
    },
    Char {
        const_value_index: u16,
    },
    Double {
        const_value_index: u16,
    },
    Float {
        const_value_index: u16,
    },
    Int {
        const_value_index: u16,
    },
    Long {
        const_value_index: u16,
    },
    Short {
        const_value_index: u16,
    },
    Boolean {
        const_value_index: u16,
    },
    String {
        const_value_index: u16,
    },
    Enum {
        type_name_index: u16,
        const_name_index: u16,
    },
    Class {
        class_info_index: u16,
    },
    AnnotationType {
        annotation: Annotation,
    },
    Array {
        values: Vec<ElementValue>,
    },
}

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug, Clone)]
pub struct RuntimeAnnotationsAttribute {
    pub annotations: Vec<Annotation>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug, Clone)]
pub struct ParameterAnnotation {
    pub annotations: Vec<Annotation>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug, Clone)]
pub struct RuntimeParameterAnnotationsAttribute {
    pub parameter_annotations: Vec<ParameterAnnotation>,
}

/// Target type for a type annotation (JVMS 4.7.20).
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug, Clone)]
pub enum TypeAnnotationTarget {
    TypeParameter {
        type_parameter_index: u8,
    },
    SuperType {
        super_type_index: u16,
    },
    TypeParameterBound {
        type_parameter_index: u8,
        bound_index: u8,
    },
    Empty,
    FormalParameter {
        formal_parameter_index: u8,
    },
    Throws {
        throws_type_index: u16,
    },
    LocalVar {
        table: Vec<LocalVarTargetEntry>,
    },
    Catch {
        exception_table_index: u16,
    },
    Offset {
        offset: u16,
    },
    TypeArgument {
        offset: u16,
        type_argument_index: u8,
    },
}

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug, Clone)]
pub struct LocalVarTargetEntry {
    pub start_pc: u16,
    pub length: u16,
    pub index: u16,
}

/// A type annotation (JVMS 4.7.20).
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug, Clone)]
pub struct TypeAnnotation {
    pub target: TypeAnnotationTarget,
    pub target_path: Vec<TypePathEntry>,
    pub type_index: u16,
    pub element_value_pairs: Vec<(u16, ElementValue)>,
}

/// A step in the type_path of a type annotation.
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug, Clone)]
pub struct TypePathEntry {
    pub type_path_kind: u8,
    pub type_argument_index: u8,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug, Clone)]
pub struct RuntimeTypeAnnotationsAttribute {
    pub annotations: Vec<TypeAnnotation>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug, Clone)]
pub struct NestHostAttribute {
    pub host_class_index: u16,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug, Clone)]
pub struct NestMembersAttribute {
    pub classes: Vec<u16>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug, Clone)]
pub struct RecordAttribute {
    pub components: Vec<RecordComponentInfo>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug, Clone)]
pub struct RecordComponentInfo {
    pub name_index: u16,
    pub descriptor_index: u16,
    pub attributes: Vec<AttributeInfo>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug, Clone)]
pub struct PermittedSubclassesAttribute {
    pub classes: Vec<u16>,
}

/// Parsed attribute with its specialized form if recognized.
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug, Clone)]
pub enum ParsedAttribute {
    Code(CodeAttribute),
    ConstantValue(ConstantValueAttribute),
    Exceptions(ExceptionsAttribute),
    BootstrapMethods(BootstrapMethodsAttribute),
    StackMapTable(StackMapTableAttribute),
    InnerClasses(InnerClassesAttribute),
    EnclosingMethod(EnclosingMethodAttribute),
    SourceFile(SourceFileAttribute),
    LineNumberTable(LineNumberTableAttribute),
    LocalVariableTable(LocalVariableTableAttribute),
    LocalVariableTypeTable(LocalVariableTypeTableAttribute),
    RuntimeVisibleAnnotations(RuntimeAnnotationsAttribute),
    RuntimeInvisibleAnnotations(RuntimeAnnotationsAttribute),
    RuntimeVisibleParameterAnnotations(RuntimeParameterAnnotationsAttribute),
    RuntimeInvisibleParameterAnnotations(RuntimeParameterAnnotationsAttribute),
    RuntimeVisibleTypeAnnotations(RuntimeTypeAnnotationsAttribute),
    RuntimeInvisibleTypeAnnotations(RuntimeTypeAnnotationsAttribute),
    AnnotationDefault(AnnotationDefaultAttribute),
    MethodParameters(MethodParametersAttribute),
    NestHost(NestHostAttribute),
    NestMembers(NestMembersAttribute),
    Record(RecordAttribute),
    PermittedSubclasses(PermittedSubclassesAttribute),
    Module(ModuleAttribute),
    ModulePackages(ModulePackagesAttribute),
    ModuleMainClass(ModuleMainClassAttribute),
    Deprecated,
    Synthetic,
    Signature { signature_index: u16 },
    Unknown(AttributeInfo),
}

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug, Clone)]
pub struct EnclosingMethodAttribute {
    pub class_index: u16,
    pub method_index: u16,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug, Clone)]
pub struct AnnotationDefaultAttribute {
    pub default_value: ElementValue,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug, Clone)]
pub struct MethodParametersAttribute {
    pub parameters: Vec<MethodParameter>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug, Clone)]
pub struct MethodParameter {
    pub name_index: u16,
    pub access_flags: u16,
}

/// Module attribute (module-info classes, JVMS 4.7.25).
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug, Clone)]
pub struct ModuleAttribute {
    pub module_name_index: u16,
    pub module_flags: u16,
    pub module_version_index: u16,
    pub requires: Vec<ModuleRequires>,
    pub exports: Vec<ModuleExports>,
    pub opens: Vec<ModuleOpens>,
    pub uses_index: Vec<u16>,
    pub provides: Vec<ModuleProvides>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug, Clone)]
pub struct ModuleRequires {
    pub requires_index: u16,
    pub requires_flags: u16,
    pub requires_version_index: u16,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug, Clone)]
pub struct ModuleExports {
    pub exports_index: u16,
    pub exports_flags: u16,
    pub exports_to_index: Vec<u16>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug, Clone)]
pub struct ModuleOpens {
    pub opens_index: u16,
    pub opens_flags: u16,
    pub opens_to_index: Vec<u16>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug, Clone)]
pub struct ModuleProvides {
    pub provides_index: u16,
    pub provides_with_index: Vec<u16>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug, Clone)]
pub struct ModulePackagesAttribute {
    pub package_index: Vec<u16>,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug, Clone)]
pub struct ModuleMainClassAttribute {
    pub main_class_index: u16,
}

impl ConstantPoolEntry {
    /// Returns the tag byte for this constant pool entry.
    pub fn tag(&self) -> u8 {
        match self {
            ConstantPoolEntry::Utf8(_) => cp_tag::UTF8,
            ConstantPoolEntry::Integer(_) => cp_tag::INTEGER,
            ConstantPoolEntry::Float(_) => cp_tag::FLOAT,
            ConstantPoolEntry::Long(_) => cp_tag::LONG,
            ConstantPoolEntry::Double(_) => cp_tag::DOUBLE,
            ConstantPoolEntry::Class(_) => cp_tag::CLASS,
            ConstantPoolEntry::String(_) => cp_tag::STRING,
            ConstantPoolEntry::Fieldref(_) => cp_tag::FIELDREF,
            ConstantPoolEntry::Methodref(_) => cp_tag::METHODREF,
            ConstantPoolEntry::InterfaceMethodref(_) => cp_tag::INTERFACE_METHODREF,
            ConstantPoolEntry::NameAndType(_) => cp_tag::NAME_AND_TYPE,
            ConstantPoolEntry::MethodHandle(_) => cp_tag::METHOD_HANDLE,
            ConstantPoolEntry::MethodType(_) => cp_tag::METHOD_TYPE,
            ConstantPoolEntry::Dynamic(_) => cp_tag::DYNAMIC,
            ConstantPoolEntry::InvokeDynamic(_) => cp_tag::INVOKE_DYNAMIC,
            ConstantPoolEntry::Module(_) => cp_tag::MODULE,
            ConstantPoolEntry::Package(_) => cp_tag::PACKAGE,
        }
    }

    /// Long and Double take two constant pool slots.
    pub fn takes_two_slots(&self) -> bool {
        matches!(
            self,
            ConstantPoolEntry::Long(_) | ConstantPoolEntry::Double(_)
        )
    }
}

impl ClassFile {
    /// Resolve the class name from this_class index (CONSTANT_Class -> CONSTANT_Utf8).
    pub fn this_class_name(&self) -> Option<&str> {
        self.class_name(self.this_class)
    }

    /// Resolve the super class name from super_class index.
    pub fn super_class_name(&self) -> Option<&str> {
        if self.super_class == 0 {
            return None;
        }
        self.class_name(self.super_class)
    }

    /// Resolve a CONSTANT_Class index to its internal name.
    pub fn class_name(&self, class_index: u16) -> Option<&str> {
        match crate::constant_pool::get_entry(&self.constant_pool, class_index)? {
            ConstantPoolEntry::Class(info) => {
                crate::constant_pool::get_utf8(&self.constant_pool, info.name_index)
            }
            ConstantPoolEntry::Module(info) => {
                crate::constant_pool::get_utf8(&self.constant_pool, info.name_index)
            }
            ConstantPoolEntry::Package(info) => {
                crate::constant_pool::get_utf8(&self.constant_pool, info.name_index)
            }
            _ => None,
        }
    }

    /// Resolve a CONSTANT_String index to its value.
    pub fn string_value(&self, string_index: u16) -> Option<&str> {
        match crate::constant_pool::get_entry(&self.constant_pool, string_index)? {
            ConstantPoolEntry::String(info) => {
                crate::constant_pool::get_utf8(&self.constant_pool, info.string_index)
            }
            _ => None,
        }
    }

    /// Resolve a CONSTANT_NameAndType index to (name, descriptor).
    pub fn name_and_type(&self, index: u16) -> Option<(&str, &str)> {
        match crate::constant_pool::get_entry(&self.constant_pool, index)? {
            ConstantPoolEntry::NameAndType(info) => Some((
                crate::constant_pool::get_utf8(&self.constant_pool, info.name_index)?,
                crate::constant_pool::get_utf8(&self.constant_pool, info.descriptor_index)?,
            )),
            _ => None,
        }
    }

    /// Resolve a field/method ref index to (class_internal_name, name, descriptor).
    pub fn member_ref(&self, index: u16) -> Option<(&str, &str, &str)> {
        let (class_index, nat_index) =
            match crate::constant_pool::get_entry(&self.constant_pool, index)? {
                ConstantPoolEntry::Fieldref(i) => (i.class_index, i.name_and_type_index),
                ConstantPoolEntry::Methodref(i) => (i.class_index, i.name_and_type_index),
                ConstantPoolEntry::InterfaceMethodref(i) => (i.class_index, i.name_and_type_index),
                _ => return None,
            };
        let (name, desc) = self.name_and_type(nat_index)?;
        Some((self.class_name(class_index)?, name, desc))
    }

    /// Get the name of a method from its name_index.
    pub fn method_name(&self, method: &MethodInfo) -> Option<&str> {
        crate::constant_pool::get_utf8(&self.constant_pool, method.name_index)
    }

    /// Get the descriptor of a method from its descriptor_index.
    pub fn method_descriptor(&self, method: &MethodInfo) -> Option<&str> {
        crate::constant_pool::get_utf8(&self.constant_pool, method.descriptor_index)
    }

    /// Get the name of a field from its name_index.
    pub fn field_name(&self, field: &FieldInfo) -> Option<&str> {
        crate::constant_pool::get_utf8(&self.constant_pool, field.name_index)
    }

    /// Get the descriptor of a field from its descriptor_index.
    pub fn field_descriptor(&self, field: &FieldInfo) -> Option<&str> {
        crate::constant_pool::get_utf8(&self.constant_pool, field.descriptor_index)
    }

    /// Get the Java version as (major, minor).
    pub fn version(&self) -> (u16, u16) {
        (self.major_version, self.minor_version)
    }
}
