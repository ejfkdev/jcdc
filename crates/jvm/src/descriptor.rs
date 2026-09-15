//! JVM field/method descriptor parsing (JVMS 4.3).

use std::fmt;

/// A JVM type as it appears in descriptors (no generics; see `signature` for those).
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum JavaType {
    Void,
    Boolean,
    Byte,
    Char,
    Short,
    Int,
    Float,
    Long,
    Double,
    /// Reference type, internal name (e.g. `java/lang/String`).
    Object(String),
    Array(Box<JavaType>),
}

impl JavaType {
    /// Number of local variable / operand stack slots this type occupies.
    pub fn slot_size(&self) -> usize {
        match self {
            JavaType::Long | JavaType::Double => 2,
            JavaType::Void => 0,
            _ => 1,
        }
    }

    pub fn is_wide(&self) -> bool {
        matches!(self, JavaType::Long | JavaType::Double)
    }

    pub fn is_primitive(&self) -> bool {
        matches!(
            self,
            JavaType::Boolean
                | JavaType::Byte
                | JavaType::Char
                | JavaType::Short
                | JavaType::Int
                | JavaType::Float
                | JavaType::Long
                | JavaType::Double
        )
    }

    pub fn is_numeric(&self) -> bool {
        matches!(
            self,
            JavaType::Byte
                | JavaType::Char
                | JavaType::Short
                | JavaType::Int
                | JavaType::Float
                | JavaType::Long
                | JavaType::Double
        )
    }

    pub fn is_integral(&self) -> bool {
        matches!(
            self,
            JavaType::Byte | JavaType::Char | JavaType::Short | JavaType::Int | JavaType::Long
        )
    }

    pub fn is_reference(&self) -> bool {
        matches!(self, JavaType::Object(_) | JavaType::Array(_) | JavaType::Void)
            && !matches!(self, JavaType::Void)
    }

    /// The JVM descriptor character for primitives; None otherwise.
    pub fn primitive_char(&self) -> Option<char> {
        Some(match self {
            JavaType::Void => 'V',
            JavaType::Boolean => 'Z',
            JavaType::Byte => 'B',
            JavaType::Char => 'C',
            JavaType::Short => 'S',
            JavaType::Int => 'I',
            JavaType::Float => 'F',
            JavaType::Long => 'J',
            JavaType::Double => 'D',
            _ => return None,
        })
    }

    /// Re-render as a JVM descriptor string.
    pub fn to_descriptor(&self) -> String {
        match self {
            JavaType::Array(inner) => format!("[{}", inner.to_descriptor()),
            JavaType::Object(name) => format!("L{};", name),
            p => p.primitive_char().map(|c| c.to_string()).unwrap_or_default(),
        }
    }

    /// Render as a Java source type name. `qualify` controls whether
    /// object types use fully qualified dotted names.
    pub fn to_java(&self, qualify: bool) -> String {
        match self {
            JavaType::Void => "void".into(),
            JavaType::Boolean => "boolean".into(),
            JavaType::Byte => "byte".into(),
            JavaType::Char => "char".into(),
            JavaType::Short => "short".into(),
            JavaType::Int => "int".into(),
            JavaType::Float => "float".into(),
            JavaType::Long => "long".into(),
            JavaType::Double => "double".into(),
            JavaType::Object(name) => internal_name_to_java(name, qualify),
            JavaType::Array(inner) => format!("{}[]", inner.to_java(qualify)),
        }
    }
}

impl fmt::Display for JavaType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.to_java(true))
    }
}

/// Convert an internal binary name (`java/lang/String`, `a/b/C$D`) to Java
/// source form. With `qualify=false` only the last segment (after the final
/// `/`) is kept, with `$` preserved (the emitter resolves nesting later).
pub fn internal_name_to_java(internal: &str, qualify: bool) -> String {
    if qualify {
        dotted_source(internal)
    } else {
        binary_simple_name(internal)
    }
}

/// Source form of a `$`-bearing binary name. `Outer$Inner` renders as
/// `Outer.Inner`, but javac's desugared LOCAL classes (`Outer$1Name`) have
/// no qualified form — their source name is the digit-prefix-stripped
/// simple name, referenced without qualification — and a literal-`$` name
/// (`DolTest2$$dollah$$`) must keep its `$` (`A..b` does not parse).
pub fn binary_simple_name(internal: &str) -> String {
    let simple = internal.rsplit(['/', '$']).next().unwrap_or(internal);
    if simple.chars().next().map(|c| c.is_ascii_digit()).unwrap_or(false) {
        let stripped = simple.trim_start_matches(|c: char| c.is_ascii_digit());
        if !stripped.is_empty() {
            return stripped.to_string();
        }
    }
    if internal.contains('$') && internal.split('$').skip(1).any(|seg| seg.is_empty() || seg.rsplit('/').next().unwrap_or(seg).is_empty()) {
        return internal.rsplit('/').next().unwrap_or(internal).to_string();
    }
    internal.rsplit('/').next().unwrap_or(internal).to_string()
}

/// Fully qualified source form (`a.b.Outer.Inner`), applying the same
/// local-class / literal-`$` rules per segment.
pub fn dotted_source(internal: &str) -> String {
    let (pkg, simple) = match internal.rfind('/') {
        Some(i) => (&internal[..i], &internal[i + 1..]),
        None => ("", internal),
    };
    let mut out = String::new();
    if !pkg.is_empty() {
        out.push_str(&pkg.replace('/', "."));
        out.push('.');
    }
    let mut segs = simple.split('$');
    let mut acc = String::new();
    if let Some(first) = segs.next() {
        acc.push_str(first);
    }
    for seg in segs {
        if seg.chars().next().map(|c| c.is_ascii_digit()).unwrap_or(false) {
            let stripped = seg.trim_start_matches(|c: char| c.is_ascii_digit());
            if !stripped.is_empty() {
                // local class: unqualified simple name
                out.clear();
                return stripped.to_string();
            }
        }
        if seg.is_empty() {
            // literal-$ name: keep the binary form
            out.clear();
            return simple.to_string();
        }
        acc.push('.');
        acc.push_str(seg);
    }
    out.push_str(&acc);
    out
}

/// A parsed method descriptor.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MethodDescriptor {
    pub args: Vec<JavaType>,
    pub ret: JavaType,
}

impl MethodDescriptor {
    /// Total argument slots (long/double count as two).
    pub fn arg_slots(&self) -> usize {
        self.args.iter().map(|t| t.slot_size()).sum()
    }
}

impl fmt::Display for MethodDescriptor {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "(")?;
        for a in &self.args {
            write!(f, "{}", a.to_descriptor())?;
        }
        write!(f, "){}", self.ret.to_descriptor())
    }
}

/// Parse a field descriptor (single type). Returns None on malformed input.
pub fn parse_field_descriptor(s: &str) -> Option<JavaType> {
    let (t, rest) = parse_type_at(s.as_bytes(), 0)?;
    if rest != s.len() {
        return None;
    }
    Some(t)
}

/// Parse a method descriptor `(args)ret`.
pub fn parse_method_descriptor(s: &str) -> Option<MethodDescriptor> {
    let b = s.as_bytes();
    if b.first() != Some(&b'(') {
        return None;
    }
    let mut i = 1;
    let mut args = Vec::new();
    while i < b.len() && b[i] != b')' {
        let (t, next) = parse_type_at(b, i)?;
        args.push(t);
        i = next;
    }
    if i >= b.len() {
        return None;
    }
    i += 1; // skip ')'
    let (ret, next) = parse_type_at(b, i)?;
    if next != b.len() {
        return None;
    }
    Some(MethodDescriptor { args, ret })
}

/// Parse one type starting at `i`; returns (type, index after).
pub fn parse_type_at(b: &[u8], i: usize) -> Option<(JavaType, usize)> {
    let c = *b.get(i)?;
    match c {
        b'V' => Some((JavaType::Void, i + 1)),
        b'Z' => Some((JavaType::Boolean, i + 1)),
        b'B' => Some((JavaType::Byte, i + 1)),
        b'C' => Some((JavaType::Char, i + 1)),
        b'S' => Some((JavaType::Short, i + 1)),
        b'I' => Some((JavaType::Int, i + 1)),
        b'F' => Some((JavaType::Float, i + 1)),
        b'J' => Some((JavaType::Long, i + 1)),
        b'D' => Some((JavaType::Double, i + 1)),
        b'[' => {
            let (inner, next) = parse_type_at(b, i + 1)?;
            Some((JavaType::Array(Box::new(inner)), next))
        }
        b'L' => {
            let end = b[i + 1..].iter().position(|&x| x == b';')? + i + 1;
            let name = std::str::from_utf8(&b[i + 1..end]).ok()?.to_string();
            Some((JavaType::Object(name), end + 1))
        }
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn field_descriptors() {
        assert_eq!(parse_field_descriptor("I"), Some(JavaType::Int));
        assert_eq!(
            parse_field_descriptor("[[Ljava/lang/String;"),
            Some(JavaType::Array(Box::new(JavaType::Array(Box::new(
                JavaType::Object("java/lang/String".into())
            )))))
        );
        assert_eq!(parse_field_descriptor("Lx;extra"), None);
    }

    #[test]
    fn method_descriptors() {
        let d = parse_method_descriptor("(IDLjava/lang/Thread;)Ljava/lang/Object;").unwrap();
        assert_eq!(d.args.len(), 3);
        assert_eq!(d.ret, JavaType::Object("java/lang/Object".into()));
        assert_eq!(d.arg_slots(), 4);
        let d2 = parse_method_descriptor("()V").unwrap();
        assert!(d2.args.is_empty());
        assert_eq!(d2.ret, JavaType::Void);
        assert_eq!(parse_method_descriptor("(I"), None);
    }

    #[test]
    fn roundtrip_descriptor() {
        let s = "(J[D[[C)V";
        let d = parse_method_descriptor(s).unwrap();
        assert_eq!(d.to_string(), s);
    }
}
