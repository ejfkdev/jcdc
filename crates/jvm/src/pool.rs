//! Class pool: lazy loading of classes from directories and jars, with a
//! shared cache and hierarchy-aware member resolution.

use std::collections::{HashMap, HashSet};
use std::io::Read as _;
use std::path::{Path, PathBuf};
use std::sync::{Arc, Mutex};

use jcdc_classfile::{
    parse_classfile, ClassAccessFlags, ClassFile, CpLookup, FieldAccessFlags, FieldInfo,
    MethodAccessFlags, MethodInfo,
};

/// A class loaded into the pool.
pub struct PoolClass {
    pub internal_name: String,
    pub cf: ClassFile,
    pub cp: CpLookup,
}

impl PoolClass {
    pub fn parse(data: &[u8], internal_name: String) -> anyhow::Result<Arc<PoolClass>> {
        let (_, cf) = parse_classfile(data)
            .map_err(|e| anyhow::anyhow!("parse error for {}: {:?}", internal_name, e))?;
        let cp = CpLookup::new(&cf.constant_pool);
        // The constant pool's this_class is authoritative; the passed name
        // is only a guess (e.g. a bare file stem for single-class inputs)
        // and would break same-class comparisons when it lacks the package.
        let real = cp
            .class_name(&cf.constant_pool, cf.this_class)
            .map(|s| s.to_string())
            .unwrap_or(internal_name);
        Ok(Arc::new(PoolClass { internal_name: real, cf, cp }))
    }

    // -- constant pool shortcuts --

    pub fn utf8(&self, idx: u16) -> Option<&str> {
        self.cp.utf8(&self.cf.constant_pool, idx)
    }

    /// CONSTANT_Class index -> internal name.
    pub fn class_name(&self, idx: u16) -> Option<&str> {
        self.cp.class_name(&self.cf.constant_pool, idx)
    }

    /// CONSTANT_String index -> value.
    pub fn string_value(&self, idx: u16) -> Option<&str> {
        self.cp.string_value(&self.cf.constant_pool, idx)
    }

    pub fn name_and_type(&self, idx: u16) -> Option<(&str, &str)> {
        self.cp.name_and_type(&self.cf.constant_pool, idx)
    }

    /// Fieldref/Methodref/InterfaceMethodref index -> (owner, name, descriptor).
    pub fn member_ref(&self, idx: u16) -> Option<(&str, &str, &str)> {
        self.cp.member_ref(&self.cf.constant_pool, idx)
    }

    // -- class-level facts --

    pub fn access(&self) -> ClassAccessFlags {
        self.cf.access_flags
    }

    pub fn is_interface(&self) -> bool {
        self.cf.access_flags.contains(ClassAccessFlags::INTERFACE)
    }

    pub fn is_enum(&self) -> bool {
        self.cf.access_flags.contains(ClassAccessFlags::ENUM)
    }

    pub fn is_annotation(&self) -> bool {
        self.cf.access_flags.contains(ClassAccessFlags::ANNOTATION)
    }

    pub fn is_module(&self) -> bool {
        self.cf.access_flags.contains(ClassAccessFlags::MODULE)
    }

    /// Records carry the Record attribute (ACC_RECORD shares a bit with ACC_FINAL).
    pub fn is_record(&self) -> bool {
        self.class_attr("Record").is_some()
    }

    pub fn super_name(&self) -> Option<&str> {
        if self.cf.super_class == 0 {
            None
        } else {
            self.class_name(self.cf.super_class)
        }
    }

    pub fn interface_names(&self) -> Vec<&str> {
        self.cf
            .interfaces
            .iter()
            .filter_map(|&i| self.class_name(i))
            .collect()
    }

    // -- attribute access --

    pub fn class_attr(&self, name: &str) -> Option<&[u8]> {
        self.cf
            .attributes
            .iter()
            .find(|a| self.utf8(a.attribute_name_index) == Some(name))
            .map(|a| a.info.as_slice())
    }

    pub fn method_attr<'m>(&self, m: &'m MethodInfo, name: &str) -> Option<&'m [u8]> {
        m.attributes
            .iter()
            .find(|a| self.utf8(a.attribute_name_index) == Some(name))
            .map(|a| a.info.as_slice())
    }

    pub fn field_attr<'f>(&self, f: &'f FieldInfo, name: &str) -> Option<&'f [u8]> {
        f.attributes
            .iter()
            .find(|a| self.utf8(a.attribute_name_index) == Some(name))
            .map(|a| a.info.as_slice())
    }

    // -- member lookup (own declarations only) --

    /// Find a directly declared method by name + descriptor; returns its index.
    pub fn find_own_method(&self, name: &str, desc: &str) -> Option<usize> {
        self.cf.methods.iter().position(|m| {
            self.utf8(m.name_index) == Some(name) && self.utf8(m.descriptor_index) == Some(desc)
        })
    }

    /// Find a directly declared field by name (and optionally descriptor).
    pub fn find_own_field(&self, name: &str, desc: Option<&str>) -> Option<usize> {
        self.cf.fields.iter().position(|f| {
            self.utf8(f.name_index) == Some(name)
                && desc
                    .map(|d| self.utf8(f.descriptor_index) == Some(d))
                    .unwrap_or(true)
        })
    }

    pub fn method_name(&self, idx: usize) -> Option<&str> {
        self.cf.methods.get(idx).and_then(|m| self.utf8(m.name_index))
    }

    pub fn method_desc(&self, idx: usize) -> Option<&str> {
        self.cf.methods.get(idx).and_then(|m| self.utf8(m.descriptor_index))
    }

    pub fn method_access(&self, idx: usize) -> MethodAccessFlags {
        self.cf
            .methods
            .get(idx)
            .map(|m| m.access_flags)
            .unwrap_or_else(MethodAccessFlags::empty)
    }

    pub fn field_access(&self, idx: usize) -> FieldAccessFlags {
        self.cf
            .fields
            .get(idx)
            .map(|f| f.access_flags)
            .unwrap_or_else(FieldAccessFlags::empty)
    }
}

#[derive(Default)]
struct PoolState {
    dir_index: HashMap<String, PathBuf>,
    jars: Vec<PathBuf>,
    /// per jar: internal class name -> zip entry name
    jar_indexes: Vec<HashMap<String, String>>,
    cache: HashMap<String, Arc<PoolClass>>,
    negative: HashSet<String>,
    /// Names from primary sources (the inputs being decompiled), as
    /// opposed to classpath references. Family/nested-class enumeration
    /// must only use these, or classpath jars leak foreign nested classes
    /// into the output.
    primary: HashSet<String>,
}

/// A searchable collection of classes (directories and jars), with a shared
/// parse cache. Cheap to clone (all state behind Arc).
#[derive(Clone, Default)]
pub struct ClassPool {
    state: Arc<Mutex<PoolState>>,
}

impl ClassPool {
    pub fn new() -> Self {
        ClassPool::default()
    }

    /// Create a pool from a list of paths (dirs, jars, or single class files).
    pub fn from_paths<P: AsRef<Path>>(paths: impl IntoIterator<Item = P>) -> anyhow::Result<Self> {
        let pool = ClassPool::new();
        for p in paths {
            pool.add_source(p.as_ref())?;
        }
        Ok(pool)
    }

    /// Add a directory, jar, or single class file source.
    pub fn add_source(&self, path: &Path) -> anyhow::Result<()> {
        self.add_source_with(path, true)
    }

    /// Add a reference-only source (classpath): classes resolve for type
    /// lookups but never join family/nested-class enumeration.
    pub fn add_classpath_source(&self, path: &Path) -> anyhow::Result<()> {
        self.add_source_with(path, false)
    }

    fn add_source_with(&self, path: &Path, primary: bool) -> anyhow::Result<()> {
        if path.is_dir() {
            let mut index = HashMap::new();
            index_dir(path, path, &mut index)?;
            let mut st = self.state.lock().unwrap();
            if primary {
                st.primary.extend(index.keys().cloned());
            }
            // First source wins (javac classpath semantics): the primary
            // family dir is added before reference classpath dirs, so a
            // stale platform copy must never mask the freshly compiled
            // family class.
            for (k, v) in index {
                st.dir_index.entry(k).or_insert(v);
            }
        } else if is_zip(path) {
            let mut index = HashMap::new();
            index_jar(path, &mut index);
            let mut st = self.state.lock().unwrap();
            if primary {
                st.primary.extend(index.keys().cloned());
            }
            st.jars.push(path.to_path_buf());
            st.jar_indexes.push(index);
        } else if path.extension().and_then(|e| e.to_str()) == Some("class") {
            let data = std::fs::read(path)?;
            let guess = path
                .file_stem()
                .and_then(|s| s.to_str())
                .unwrap_or("Unknown")
                .to_string();
            let pc = PoolClass::parse(&data, guess)?;
            let name = pc.internal_name.clone();
            let real = pc
                .class_name(pc.cf.this_class)
                .map(|s| s.to_string())
                .unwrap_or(name);
            let mut st = self.state.lock().unwrap();
            if primary {
                st.primary.insert(real.clone());
            }
            st.cache.insert(real, pc);
        } else {
            anyhow::bail!("unsupported source: {:?}", path);
        }
        Ok(())
    }

    /// Look up a class by internal name (e.g. `java/lang/String`).
    pub fn get(&self, internal_name: &str) -> Option<Arc<PoolClass>> {
        {
            let st = self.state.lock().unwrap();
            if let Some(pc) = st.cache.get(internal_name) {
                return Some(pc.clone());
            }
            if st.negative.contains(internal_name) {
                return None;
            }
        }
        let data = self.read_class_bytes(internal_name);
        let mut st = self.state.lock().unwrap();
        let Some(data) = data else {
            st.negative.insert(internal_name.to_string());
            return None;
        };
        match PoolClass::parse(&data, internal_name.to_string()) {
            Ok(pc) => {
                st.cache.insert(internal_name.to_string(), pc.clone());
                Some(pc)
            }
            Err(_) => {
                st.negative.insert(internal_name.to_string());
                None
            }
        }
    }

    fn read_class_bytes(&self, internal_name: &str) -> Option<Vec<u8>> {
        let st = self.state.lock().unwrap();
        if let Some(path) = st.dir_index.get(internal_name) {
            return std::fs::read(path).ok();
        }
        for (jar_idx, index) in st.jar_indexes.iter().enumerate() {
            if let Some(entry) = index.get(internal_name) {
                let path = &st.jars[jar_idx];
                let file = std::fs::File::open(path).ok()?;
                let mut zip = zip::ZipArchive::new(file).ok()?;
                let mut e = zip.by_name(entry).ok()?;
                let mut buf = Vec::with_capacity(e.size() as usize);
                e.read_to_end(&mut buf).ok()?;
                return Some(buf);
            }
        }
        None
    }

    /// Names from primary (input) sources; falls back to all names when
    /// nothing was registered as primary (e.g. insert_bytes-only pools).
    pub fn primary_names(&self) -> Vec<String> {
        let st = self.state.lock().unwrap();
        if st.primary.is_empty() {
            drop(st);
            return self.all_names();
        }
        let mut v: Vec<String> = st.primary.iter().cloned().collect();
        v.sort_unstable();
        v
    }

    /// All class names known to the pool indexes (without parsing).
    pub fn all_names(&self) -> Vec<String> {
        let st = self.state.lock().unwrap();
        let mut v: Vec<String> = Vec::with_capacity(st.dir_index.len() + 1024);
        v.extend(st.dir_index.keys().cloned());
        for idx in &st.jar_indexes {
            v.extend(idx.keys().cloned());
        }
        v.extend(st.cache.keys().cloned());
        v.sort_unstable();
        v.dedup();
        v
    }

    /// Insert a class directly from bytes (used by tests and pipelines).
    pub fn insert_bytes(&self, internal_name: &str, data: &[u8]) -> anyhow::Result<Arc<PoolClass>> {
        let pc = PoolClass::parse(data, internal_name.to_string())?;
        let mut st = self.state.lock().unwrap();
        st.negative.remove(internal_name);
        st.cache.insert(internal_name.to_string(), pc.clone());
        Ok(pc)
    }

    /// Resolve a method reference the way the JVM does: search the class,
    /// then superclasses, then superinterfaces (default methods).
    /// Returns (defining class, method index).
    pub fn resolve_method(
        &self,
        owner: &str,
        name: &str,
        desc: &str,
    ) -> Option<(Arc<PoolClass>, usize)> {
        let mut visited = HashSet::new();
        self.resolve_method_rec(owner, name, desc, &mut visited)
    }

    fn resolve_method_rec(
        &self,
        owner: &str,
        name: &str,
        desc: &str,
        visited: &mut HashSet<String>,
    ) -> Option<(Arc<PoolClass>, usize)> {
        if !visited.insert(owner.to_string()) {
            return None;
        }
        let pc = self.get(owner)?;
        if let Some(i) = pc.find_own_method(name, desc) {
            return Some((pc, i));
        }
        if let Some(sup) = pc.super_name().map(|s| s.to_string()) {
            if let Some(hit) = self.resolve_method_rec(&sup, name, desc, visited) {
                return Some(hit);
            }
        }
        for ifc in pc.interface_names().into_iter().map(|s| s.to_string()).collect::<Vec<_>>() {
            if let Some(hit) = self.resolve_method_rec(&ifc, name, desc, visited) {
                return Some(hit);
            }
        }
        None
    }

    /// Resolve a field reference: class, then superclasses, then interfaces.
    pub fn resolve_field(
        &self,
        owner: &str,
        name: &str,
        desc: &str,
    ) -> Option<(Arc<PoolClass>, usize)> {
        let mut visited = HashSet::new();
        self.resolve_field_rec(owner, name, Some(desc), &mut visited)
    }

    fn resolve_field_rec(
        &self,
        owner: &str,
        name: &str,
        desc: Option<&str>,
        visited: &mut HashSet<String>,
    ) -> Option<(Arc<PoolClass>, usize)> {
        if !visited.insert(owner.to_string()) {
            return None;
        }
        let pc = self.get(owner)?;
        if let Some(i) = pc.find_own_field(name, desc) {
            return Some((pc, i));
        }
        if let Some(sup) = pc.super_name().map(|s| s.to_string()) {
            if let Some(hit) = self.resolve_field_rec(&sup, name, desc, visited) {
                return Some(hit);
            }
        }
        for ifc in pc.interface_names().into_iter().map(|s| s.to_string()).collect::<Vec<_>>() {
            if let Some(hit) = self.resolve_field_rec(&ifc, name, desc, visited) {
                return Some(hit);
            }
        }
        None
    }

    /// True if `sub` is the same as, or a subtype of, `sup` (best effort;
    /// missing classes make the answer false).
    pub fn is_subtype(&self, sub: &str, sup: &str) -> bool {
        if sub == sup {
            return true;
        }
        let mut visited = HashSet::new();
        self.is_subtype_rec(sub, sup, &mut visited)
    }

    fn is_subtype_rec(&self, sub: &str, sup: &str, visited: &mut HashSet<String>) -> bool {
        if !visited.insert(sub.to_string()) {
            return false;
        }
        let Some(pc) = self.get(sub) else { return false };
        let mut parents: Vec<String> = Vec::new();
        if let Some(s) = pc.super_name() {
            parents.push(s.to_string());
        }
        parents.extend(pc.interface_names().into_iter().map(|s| s.to_string()));
        parents.iter().any(|p| p == sup || self.is_subtype_rec(p, sup, visited))
    }
}

fn is_zip(path: &Path) -> bool {
    match path.extension().and_then(|e| e.to_str()) {
        Some("jar") | Some("zip") | Some("war") | Some("ear") | Some("apk") | Some("jmod") => true,
        _ => {
            if let Ok(mut f) = std::fs::File::open(path) {
                let mut b = [0u8; 4];
                if f.read_exact(&mut b).is_ok() {
                    return b.starts_with(b"PK\x03\x04");
                }
            }
            false
        }
    }
}

fn index_dir(root: &Path, dir: &Path, out: &mut HashMap<String, PathBuf>) -> anyhow::Result<()> {
    for entry in std::fs::read_dir(dir)? {
        let entry = entry?;
        let path = entry.path();
        if path.is_dir() {
            index_dir(root, &path, out)?;
        } else if path.extension().and_then(|e| e.to_str()) == Some("class") {
            let rel = path.strip_prefix(root).unwrap_or(&path);
            let mut name = rel.to_string_lossy().replace(std::path::MAIN_SEPARATOR, "/");
            name.truncate(name.len() - ".class".len());
            out.insert(name, path);
        }
    }
    Ok(())
}

fn index_jar(path: &Path, out: &mut HashMap<String, String>) {
    let Ok(file) = std::fs::File::open(path) else { return };
    let Ok(zip) = zip::ZipArchive::new(file) else { return };
    for i in 0..zip.len() {
        let Some(name) = zip.name_for_index(i) else { continue };
        if name.ends_with(".class") {
            // .jmod images nest everything under classes/.
            let rel = name.strip_prefix("classes/").unwrap_or(name);
            let key = rel.trim_end_matches(".class").to_string();
            out.entry(key).or_insert_with(|| name.to_string());
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn pool_from_testcases_dir() {
        let dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../classfile/testcases");
        if !dir.exists() {
            return;
        }
        let pool = ClassPool::from_paths([&dir]).unwrap();
        let hw = pool.get("HelloWorld").expect("HelloWorld.class should be indexed");
        assert_eq!(hw.super_name(), Some("java/lang/Object"));
        let main = hw.find_own_method("main", "([Ljava/lang/String;)V");
        assert!(main.is_some());
    }
}
