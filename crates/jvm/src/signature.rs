//! Generic signature parsing (JVMS 4.7.9.1): class, method and field signatures.

use std::fmt;

/// A type appearing inside a generic signature.
#[derive(Debug, Clone, PartialEq)]
pub enum GenericType {
    /// Base (primitive) type.
    Primitive(char),
    /// Class type signature, possibly with type arguments and `.`-nesting.
    Class(ClassSig),
    Array(Box<GenericType>),
    /// Type variable reference `Tname;`.
    TypeVar(String),
    /// Type argument wildcard: `*`, `+T`, `-T`.
    Wildcard(WildcardBound),
}

#[derive(Debug, Clone, PartialEq)]
pub enum WildcardBound {
    Any,
    Extends(Box<GenericType>),
    Super(Box<GenericType>),
}

/// A class type signature: `Ljava/util/Map<K, V>.Entry<X>;` becomes parts
/// `[Map<K,V>, Entry<X>]` with package `java/util`.
#[derive(Debug, Clone, PartialEq)]
pub struct ClassSig {
    pub package: String,
    pub parts: Vec<ClassSigPart>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct ClassSigPart {
    pub name: String,
    pub args: Vec<GenericType>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct TypeParam {
    pub name: String,
    pub class_bound: Option<GenericType>,
    pub interface_bounds: Vec<GenericType>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct ClassSignature {
    pub params: Vec<TypeParam>,
    pub superclass: GenericType,
    pub interfaces: Vec<GenericType>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct MethodSignature {
    pub params: Vec<TypeParam>,
    pub args: Vec<GenericType>,
    pub ret: GenericType,
    pub throws: Vec<GenericType>,
}

impl GenericType {
    /// Render as Java source (fully qualified class names).
    pub fn to_java(&self) -> String {
        match self {
            GenericType::Primitive(c) => prim_name(*c).to_string(),
            GenericType::Class(cs) => cs.to_java(),
            GenericType::Array(inner) => format!("{}[]", inner.to_java()),
            GenericType::TypeVar(n) => n.clone(),
            GenericType::Wildcard(w) => match w {
                WildcardBound::Any => "?".to_string(),
                WildcardBound::Extends(t) => format!("? extends {}", t.to_java()),
                WildcardBound::Super(t) => format!("? super {}", t.to_java()),
            },
        }
    }

    /// If this is a plain class reference (no type arguments), its internal name.
    pub fn as_internal_name(&self) -> Option<String> {
        match self {
            GenericType::Class(cs) if cs.parts.iter().all(|p| p.args.is_empty()) => {
                Some(cs.internal_name())
            }
            _ => None,
        }
    }
}

fn prim_name(c: char) -> &'static str {
    match c {
        'V' => "void",
        'Z' => "boolean",
        'B' => "byte",
        'C' => "char",
        'S' => "short",
        'I' => "int",
        'F' => "float",
        'J' => "long",
        'D' => "double",
        _ => "?",
    }
}

impl fmt::Display for ClassSignature {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.to_java())
    }
}

impl ClassSignature {
    pub fn to_java(&self) -> String {
        let mut s = String::new();
        render_type_params(&self.params, &mut s);
        s.push_str(&self.superclass.to_java());
        for i in &self.interfaces {
            s.push_str(" + ");
            s.push_str(&i.to_java());
        }
        s
    }
}

impl MethodSignature {
    pub fn to_java(&self) -> String {
        let mut s = String::new();
        render_type_params(&self.params, &mut s);
        s.push('(');
        for (i, a) in self.args.iter().enumerate() {
            if i > 0 {
                s.push_str(", ");
            }
            s.push_str(&a.to_java());
        }
        s.push(')');
        s.push_str(&self.ret.to_java());
        s
    }
}

pub fn render_type_params(params: &[TypeParam], out: &mut String) {
    if params.is_empty() {
        return;
    }
    out.push('<');
    for (i, p) in params.iter().enumerate() {
        if i > 0 {
            out.push_str(", ");
        }
        out.push_str(&p.name);
        let mut first_bound = true;
        if let Some(cb) = &p.class_bound {
            if !is_java_lang_object(cb) {
                out.push_str(" extends ");
                out.push_str(&cb.to_java());
                first_bound = false;
            }
        }
        for (j, ib) in p.interface_bounds.iter().enumerate() {
            out.push_str(if first_bound && j == 0 { " extends " } else { " & " });
            out.push_str(&ib.to_java());
        }
    }
    out.push('>');
}

fn is_java_lang_object(t: &GenericType) -> bool {
    matches!(t, GenericType::Class(cs) if cs.package == "java/lang" && cs.parts.len() == 1 && cs.parts[0].name == "Object" && cs.parts[0].args.is_empty())
}

// ---------------------------------------------------------------------------
// Parser
// ---------------------------------------------------------------------------

struct SigParser<'a> {
    b: &'a [u8],
    i: usize,
}

type PResult<T> = Result<T, ()>;

impl<'a> SigParser<'a> {
    fn peek(&self) -> Option<u8> {
        self.b.get(self.i).copied()
    }
    fn eat(&mut self, c: u8) -> PResult<()> {
        if self.peek() == Some(c) {
            self.i += 1;
            Ok(())
        } else {
            Err(())
        }
    }
    fn ident(&mut self) -> PResult<String> {
        let start = self.i;
        while let Some(c) = self.peek() {
            // Java identifiers in signatures: stop at signature metacharacters
            if matches!(c, b'.' | b';' | b':' | b'<' | b'>' | b'*' | b'+' | b'-' | b'[' | b'^' | b'(' | b')' | b'|' | b'/') {
                break;
            }
            self.i += 1;
        }
        if self.i == start {
            return Err(());
        }
        Ok(String::from_utf8_lossy(&self.b[start..self.i]).into_owned())
    }

    fn type_params(&mut self) -> PResult<Vec<TypeParam>> {
        if self.peek() != Some(b'<') {
            return Ok(Vec::new());
        }
        self.i += 1;
        let mut params = Vec::new();
        while self.peek() != Some(b'>') {
            let name = self.ident()?;
            // ClassBound: ':' [FieldTypeSignature]
            self.eat(b':')?;
            let class_bound = if self.peek() == Some(b':') || self.peek() == Some(b'>') {
                None
            } else {
                Some(self.field_type()?)
            };
            let mut interface_bounds = Vec::new();
            while self.peek() == Some(b':') {
                self.i += 1;
                interface_bounds.push(self.field_type()?);
            }
            params.push(TypeParam { name, class_bound, interface_bounds });
        }
        self.eat(b'>')?;
        Ok(params)
    }

    fn field_type(&mut self) -> PResult<GenericType> {
        match self.peek().ok_or(())? {
            b'L' => Ok(GenericType::Class(self.class_type()?)),
            b'[' => {
                self.i += 1;
                Ok(GenericType::Array(Box::new(self.type_sig()?)))
            }
            b'T' => {
                self.i += 1;
                let name = self.ident()?;
                self.eat(b';')?;
                Ok(GenericType::TypeVar(name))
            }
            _ => Err(()),
        }
    }

    fn class_type(&mut self) -> PResult<ClassSig> {
        self.eat(b'L')?;
        // Collect the raw span up to the terminating ';' at <> depth 0.
        let start = self.i;
        let mut depth = 0i32;
        loop {
            let c = self.peek().ok_or(())?;
            match c {
                b'<' => depth += 1,
                b'>' => depth -= 1,
                b';' if depth == 0 => break,
                _ => {}
            }
            self.i += 1;
        }
        let raw = &self.b[start..self.i];
        self.eat(b';')?;

        // Split on top-level '.' separators.
        let mut pieces: Vec<&[u8]> = Vec::new();
        let mut depth = 0i32;
        let mut pstart = 0usize;
        for (idx, &c) in raw.iter().enumerate() {
            match c {
                b'<' => depth += 1,
                b'>' => depth -= 1,
                b'.' if depth == 0 => {
                    pieces.push(&raw[pstart..idx]);
                    pstart = idx + 1;
                }
                _ => {}
            }
        }
        pieces.push(&raw[pstart..]);

        // First piece: `package/Outer[<args>]`.
        let (head, args0) = split_args(pieces[0])?;
        let (package, name) = match head.rfind('/') {
            Some(p) => (head[..p].to_string(), head[p + 1..].to_string()),
            None => (String::new(), head),
        };
        let mut parts = vec![ClassSigPart { name, args: args0 }];
        for piece in &pieces[1..] {
            let (head, args) = split_args(piece)?;
            parts.push(ClassSigPart { name: head, args });
        }
        Ok(ClassSig { package, parts })
    }

    fn type_args(&mut self) -> PResult<Vec<GenericType>> {
        self.eat(b'<')?;
        let mut args = Vec::new();
        while self.peek() != Some(b'>') {
            args.push(self.type_arg()?);
        }
        self.eat(b'>')?;
        Ok(args)
    }

    fn type_arg(&mut self) -> PResult<GenericType> {
        match self.peek().ok_or(())? {
            b'*' => {
                self.i += 1;
                Ok(GenericType::Wildcard(WildcardBound::Any))
            }
            b'+' => {
                self.i += 1;
                Ok(GenericType::Wildcard(WildcardBound::Extends(Box::new(
                    self.field_type()?,
                ))))
            }
            b'-' => {
                self.i += 1;
                Ok(GenericType::Wildcard(WildcardBound::Super(Box::new(
                    self.field_type()?,
                ))))
            }
            _ => self.field_type(),
        }
    }

    fn type_sig(&mut self) -> PResult<GenericType> {
        match self.peek().ok_or(())? {
            b'V' | b'Z' | b'B' | b'C' | b'S' | b'I' | b'F' | b'J' | b'D' => {
                let c = self.b[self.i] as char;
                self.i += 1;
                Ok(GenericType::Primitive(c))
            }
            _ => self.field_type(),
        }
    }
}

/// Split `Name<args...>` into (Name, parsed args). Args are empty if no '<'.
fn split_args(piece: &[u8]) -> PResult<(String, Vec<GenericType>)> {
    match piece.iter().position(|&c| c == b'<') {
        None => Ok((String::from_utf8_lossy(piece).into_owned(), Vec::new())),
        Some(lt) => {
            let head = String::from_utf8_lossy(&piece[..lt]).into_owned();
            let mut sub = SigParser { b: piece, i: lt };
            let args = sub.type_args()?;
            if sub.i != piece.len() {
                return Err(());
            }
            Ok((head, args))
        }
    }
}

impl ClassSig {
    pub fn to_java(&self) -> String {
        let mut s = if self.package.is_empty() {
            String::new()
        } else {
            format!("{}.", self.package.replace('/', "."))
        };
        for (i, p) in self.parts.iter().enumerate() {
            if i > 0 {
                s.push('.');
            }
            // Nested-class references inside a signature part use the
            // binary `$` separator; source form uses `.` — except javac's
            // local-class encoding `Outer$1Name`, which has no qualified
            // form (`DocLint.1Pair` does not parse): the source name is the
            // digit-stripped simple name, standing alone.
            let segs: Vec<&str> = p.name.split('$').collect();
            if let Some(last) = segs.last() {
                let stripped = last.trim_start_matches(|c: char| c.is_ascii_digit());
                if segs.len() > 1
                    && last.chars().next().map(|c| c.is_ascii_digit()).unwrap_or(false)
                    && !stripped.is_empty()
                {
                    s = stripped.to_string();
                    continue;
                }
                if segs.iter().skip(1).any(|x| x.is_empty()) {
                    s = p.name.clone();
                    continue;
                }
            }
            s.push_str(&p.name.replace('$', "."));
            if !p.args.is_empty() {
                s.push('<');
                for (j, a) in p.args.iter().enumerate() {
                    if j > 0 {
                        s.push_str(", ");
                    }
                    s.push_str(&a.to_java());
                }
                s.push('>');
            }
        }
        s
    }

    /// Internal name joining nested parts with `$`.
    pub fn internal_name(&self) -> String {
        let mut s = if self.package.is_empty() {
            String::new()
        } else {
            format!("{}/", self.package)
        };
        for (i, p) in self.parts.iter().enumerate() {
            if i > 0 {
                s.push('$');
            }
            s.push_str(&p.name);
        }
        s
    }
}

/// Parse a ClassSignature attribute value.
pub fn parse_class_signature(s: &str) -> Option<ClassSignature> {
    let mut p = SigParser { b: s.as_bytes(), i: 0 };
    let params = p.type_params().ok()?;
    let superclass = p.field_type().ok()?;
    let mut interfaces = Vec::new();
    while p.peek().is_some() {
        interfaces.push(p.field_type().ok()?);
    }
    if p.i != s.len() {
        return None;
    }
    Some(ClassSignature { params, superclass, interfaces })
}

/// Parse a MethodSignature attribute value.
pub fn parse_method_signature(s: &str) -> Option<MethodSignature> {
    let mut p = SigParser { b: s.as_bytes(), i: 0 };
    let params = p.type_params().ok()?;
    p.eat(b'(').ok()?;
    let mut args = Vec::new();
    while p.peek() != Some(b')') {
        args.push(p.type_sig().ok()?);
    }
    p.eat(b')').ok()?;
    let ret = p.type_sig().ok()?;
    let mut throws = Vec::new();
    while p.peek() == Some(b'^') {
        p.i += 1;
        throws.push(p.field_type().ok()?);
    }
    if p.i != s.len() {
        return None;
    }
    Some(MethodSignature { params, args, ret, throws })
}

/// Parse a field (FieldTypeSignature) attribute value.
pub fn parse_field_signature(s: &str) -> Option<GenericType> {
    let mut p = SigParser { b: s.as_bytes(), i: 0 };
    let t = p.field_type().ok()?;
    if p.i != s.len() {
        return None;
    }
    Some(t)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn class_sigs() {
        let cs = parse_class_signature("<T:Ljava/lang/Object;>Ljava/util/AbstractList<Ljava/lang/String;>;Ljava/util/List<Ljava/lang/String;>;").unwrap();
        assert_eq!(cs.params.len(), 1);
        assert_eq!(cs.params[0].name, "T");
        assert!(cs.to_java().starts_with("<T>"));
        assert!(cs.to_java().contains("java.util.AbstractList<java.lang.String>"));
    }

    #[test]
    fn nested_class_sig() {
        let g = parse_field_signature("Ljava/util/Map<Ljava/lang/String;Ljava/lang/Integer;>.Entry<Ljava/lang/String;Ljava/lang/Integer;>;").unwrap();
        let java = g.to_java();
        assert_eq!(java, "java.util.Map<java.lang.String, java.lang.Integer>.Entry<java.lang.String, java.lang.Integer>");
        if let GenericType::Class(cs) = &g {
            assert_eq!(cs.internal_name(), "java/util/Map$Entry");
        } else {
            panic!();
        }
    }

    #[test]
    fn method_sig() {
        let m = parse_method_signature("<K:Ljava/lang/Object;V:Ljava/lang/Object;>(TK;TV;)TV;^Ljava/io/IOException;").unwrap();
        assert_eq!(m.params.len(), 2);
        assert_eq!(m.args.len(), 2);
        assert_eq!(m.throws.len(), 1);
        assert!(m.to_java().contains("(K, V)V"));
    }

    #[test]
    fn wildcards_and_arrays() {
        let g = parse_field_signature("Ljava/util/List<+Ljava/lang/Number;>;").unwrap();
        assert_eq!(g.to_java(), "java.util.List<? extends java.lang.Number>");
        let g2 = parse_field_signature("[[Ljava/util/List<*>;").unwrap();
        assert_eq!(g2.to_java(), "java.util.List<?>[][]");
        let g3 = parse_field_signature("Ljava/util/List<-Ljava/lang/Integer;>;").unwrap();
        assert_eq!(g3.to_java(), "java.util.List<? super java.lang.Integer>");
    }

    #[test]
    fn typevar_bound() {
        let cs = parse_class_signature("<E:Ljava/lang/Comparable<-TE;>;>Ljava/lang/Object;").unwrap();
        assert_eq!(cs.params.len(), 1);
        let cb = cs.params[0].class_bound.as_ref().unwrap();
        assert!(cb.to_java().contains("java.lang.Comparable<? super E>"));
    }
}
