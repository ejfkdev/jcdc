//! Per-class-file-version feature configuration.
//!
//! Built-in defaults cover class file majors 45 (JDK 1.1) .. 70+; a TOML
//! config file (`config/versions.toml`) may override individual entries so
//! new JDK versions can be supported without code changes.

use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::path::Path;

/// Feature set implied by a class file major version.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(default)]
pub struct VersionFeatures {
    /// Class file major version (45..).
    pub class_major: u16,
    /// Human-readable Java version ("1.1", "8", "17", ...).
    pub java_version: String,
    /// jsr/ret bytecode is legal (class major <= 50).
    pub jsr_ret: bool,
    /// StackMapTable present & required (>= 50; mandatory from 51).
    pub stack_map_table: bool,
    /// invokedynamic legal (>= 51).
    pub invokedynamic: bool,
    /// Default/static interface methods (>= 52).
    pub interface_default_methods: bool,
    /// module-info classes (>= 53).
    pub module_info: bool,
    /// Private interface methods (>= 53).
    pub private_interface_methods: bool,
    /// NestHost/NestMembers attributes (>= 55).
    pub nest_based_access: bool,
    /// CONSTANT_Dynamic (>= 55).
    pub dynamic_constant: bool,
    /// Record classes (>= 60).
    pub records: bool,
    /// Sealed classes / PermittedSubclasses (>= 60).
    pub sealed_classes: bool,
    /// javac emits StringConcatFactory indy for `+` (source level >= 9).
    pub string_concat_indy: bool,
    /// javac emits LambdaMetafactory indy for lambdas (source level >= 8).
    pub lambda_indy: bool,
}

impl Default for VersionFeatures {
    fn default() -> Self {
        VersionFeatures {
            class_major: 52,
            java_version: "8".into(),
            jsr_ret: false,
            stack_map_table: true,
            invokedynamic: true,
            interface_default_methods: true,
            module_info: false,
            private_interface_methods: false,
            nest_based_access: false,
            dynamic_constant: false,
            records: false,
            sealed_classes: false,
            string_concat_indy: false,
            lambda_indy: true,
        }
    }
}

/// File format for `versions.toml`.
#[derive(Debug, Default, Serialize, Deserialize)]
struct VersionsFile {
    #[serde(default)]
    version: Vec<VersionFeatures>,
}

/// Registry mapping class major version -> features, with overrides.
#[derive(Debug, Clone, Default)]
pub struct VersionConfig {
    overrides: HashMap<u16, VersionFeatures>,
}

impl VersionConfig {
    pub fn new() -> Self {
        VersionConfig { overrides: HashMap::new() }
    }

    /// Load overrides from a TOML file. Missing file is not an error.
    pub fn load(path: &Path) -> anyhow::Result<Self> {
        let mut cfg = VersionConfig::new();
        if path.exists() {
            let text = std::fs::read_to_string(path)?;
            let f: VersionsFile = toml::from_str(&text)?;
            for v in f.version {
                cfg.overrides.insert(v.class_major, v);
            }
        }
        Ok(cfg)
    }

    /// Features for a class file major version (override or built-in default).
    pub fn features_for(&self, major: u16) -> VersionFeatures {
        if let Some(f) = self.overrides.get(&major) {
            return f.clone();
        }
        builtin_features(major)
    }

    /// Register/replace an override.
    pub fn set_override(&mut self, f: VersionFeatures) {
        self.overrides.insert(f.class_major, f);
    }
}

/// Built-in mapping from class file major version to feature flags.
pub fn builtin_features(major: u16) -> VersionFeatures {
    let java = major_to_java_version(major);
    VersionFeatures {
        class_major: major,
        java_version: java.to_string(),
        jsr_ret: major <= 50,
        stack_map_table: major >= 50,
        invokedynamic: major >= 51,
        interface_default_methods: major >= 52,
        module_info: major >= 53,
        private_interface_methods: major >= 53,
        nest_based_access: major >= 55,
        dynamic_constant: major >= 55,
        records: major >= 60,
        sealed_classes: major >= 60,
        // String concat via indy starts at source level 9 (class major 53).
        string_concat_indy: major >= 53,
        lambda_indy: major >= 52,
    }
}

/// Map class file major version to Java SE version string.
pub fn major_to_java_version(major: u16) -> &'static str {
    match major {
        45 => "1.1",
        46 => "1.2",
        47 => "1.3",
        48 => "1.4",
        49 => "5",
        50 => "6",
        51 => "7",
        52 => "8",
        53 => "9",
        54 => "10",
        55 => "11",
        56 => "12",
        57 => "13",
        58 => "14",
        59 => "15",
        60 => "16",
        61 => "17",
        62 => "18",
        63 => "19",
        64 => "20",
        65 => "21",
        66 => "22",
        67 => "23",
        68 => "24",
        69 => "25",
        70 => "26",
        _ => "unknown",
    }
}

/// Map Java SE version string ("1.8", "8", "17") to class file major.
pub fn java_version_to_major(v: &str) -> Option<u16> {
    let v = v.strip_prefix("1.").unwrap_or(v);
    let n: u16 = v.split('.').next()?.parse().ok()?;
    match n {
        1..=8 => Some(44 + n),
        9.. => Some(44 + n),
        0 => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn version_mapping() {
        assert_eq!(major_to_java_version(52), "8");
        assert_eq!(major_to_java_version(61), "17");
        assert_eq!(major_to_java_version(45), "1.1");
        assert_eq!(java_version_to_major("1.8"), Some(52));
        assert_eq!(java_version_to_major("8"), Some(52));
        assert_eq!(java_version_to_major("17"), Some(61));
        assert_eq!(java_version_to_major("21.0.2"), Some(65));
    }

    #[test]
    fn builtin_feature_boundaries() {
        let f50 = builtin_features(50);
        assert!(f50.jsr_ret && f50.stack_map_table && !f50.invokedynamic);
        let f51 = builtin_features(51);
        assert!(!f51.jsr_ret && f51.invokedynamic && !f51.interface_default_methods);
        let f53 = builtin_features(53);
        assert!(f53.module_info && f53.string_concat_indy && !f53.nest_based_access);
        let f55 = builtin_features(55);
        assert!(f55.nest_based_access && f55.dynamic_constant && !f55.records);
        let f60 = builtin_features(60);
        assert!(f60.records && f60.sealed_classes);
    }

    #[test]
    fn overrides() {
        let toml_text = r#"
[[version]]
class_major = 61
java_version = "17-custom"
records = false
"#;
        let dir = std::env::temp_dir().join("jcdc_vcfg_test");
        std::fs::create_dir_all(&dir).unwrap();
        let path = dir.join("versions.toml");
        std::fs::write(&path, toml_text).unwrap();
        let cfg = VersionConfig::load(&path).unwrap();
        let f = cfg.features_for(61);
        assert_eq!(f.java_version, "17-custom");
        assert!(!f.records);
        // other fields keep serde defaults, not builtin — document that
        // overrides replace the whole entry.
        assert!(cfg.features_for(60).records); // builtin for other majors
    }
}
