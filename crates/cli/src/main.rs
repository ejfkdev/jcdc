//! jcdc — Java class file decompiler CLI.

use std::path::{Path, PathBuf};

use anyhow::Context;
use jcdc_decompiler::{ClassOptions, ClassPool};

fn main() -> anyhow::Result<()> {
    if std::env::var("JCDC_PANIC_VERBOSE").is_err() {
        std::panic::set_hook(Box::new(|info| {
        if std::env::var("JCDC_PANIC_LOG").is_ok() {
            eprintln!("jcdc-panic: {}", info);
        }
    }));
    }
    let args: Vec<String> = std::env::args().skip(1).collect();
    let mut inputs: Vec<PathBuf> = Vec::new();
    let mut classpath: Vec<PathBuf> = Vec::new();
    let mut out: Option<PathBuf> = None;
    let mut show_synthetic = false;

    let mut i = 0;
    while i < args.len() {
        match args[i].as_str() {
            "-o" | "--output" => {
                i += 1;
                out = Some(PathBuf::from(args.get(i).context("-o needs a value")?));
            }
            "-cp" | "--classpath" => {
                i += 1;
                let v = args.get(i).context("-cp needs a value")?;
                classpath.extend(v.split(':').map(PathBuf::from));
            }
            "--synthetic" => show_synthetic = true,
            "-h" | "--help" => {
                println!("jcdc — Java class file decompiler");
                println!();
                println!("Usage: jcdc [OPTIONS] <class|jar|dir>...");
                println!();
                println!("Options:");
                println!("  -o, --output <path>    output directory (default: stdout for single class)");
                println!("  -cp, --classpath <p>   colon-separated classpath for type resolution");
                println!("  --synthetic            include synthetic/bridge members");
                return Ok(());
            }
            other => {
                if other.starts_with('-') {
                    anyhow::bail!("unknown option {}", other);
                }
                inputs.push(PathBuf::from(other));
            }
        }
        i += 1;
    }
    if inputs.is_empty() {
        anyhow::bail!("no input given (try --help)");
    }

    // Build pool: inputs themselves (primary) + classpath (reference-only).
    let pool = ClassPool::new();
    for p in inputs.iter() {
        pool.add_source(p).with_context(|| format!("adding source {:?}", p))?;
    }
    for p in classpath.iter() {
        pool.add_classpath_source(p)
            .with_context(|| format!("adding classpath {:?}", p))?;
    }

    let opts = ClassOptions { show_synthetic, ..Default::default() };

    for input in &inputs {
        decompile_path(input, &pool, &opts, out.as_deref())?;
    }
    Ok(())
}

fn decompile_path(path: &Path, pool: &ClassPool, opts: &ClassOptions, out: Option<&Path>) -> anyhow::Result<()> {
    if path.is_dir() {
        // every .class file
        for entry in walkdir(path)? {
            decompile_class_file(&entry, pool, opts, out, Some(path))?;
        }
    } else if is_zip_like(path) {
        // jar: extract and decompile each class entry
        let file = std::fs::File::open(path)?;
        let mut zip = zip::ZipArchive::new(file)?;
        for i in 0..zip.len() {
            let mut e = zip.by_index(i)?;
            let name = e.name().to_string();
            if !name.ends_with(".class") {
                continue;
            }
            let mut buf = Vec::with_capacity(e.size() as usize);
            std::io::Read::read_to_end(&mut e, &mut buf)?;
            let stem = name.trim_end_matches(".class");
            if jcdc_decompiler::classdec::is_nested_in_pool(stem, pool) {
                continue;
            }
            let java_name = format!("{}.java", stem);
            match decompile_one(&buf, pool, opts, stem) {
                Ok(source) => write_output(out, path, &java_name, &source),
                Err(e) => eprintln!("jcdc: failed to decompile {}: {}", name, e),
            }
        }
    } else {
        let stem = path.file_stem().and_then(|s| s.to_str()).unwrap_or("Unknown").to_string();
        decompile_class_file(path, pool, opts, out, None)?;
        let _ = stem;
    }
    Ok(())
}

fn decompile_class_file(path: &Path, pool: &ClassPool, opts: &ClassOptions, out: Option<&Path>, root: Option<&Path>) -> anyhow::Result<()> {
    if std::env::var("JCDC_TRACE_FILES").is_ok() {
        eprintln!("jcdc-file: {}", path.display());
    }
    let data = std::fs::read(path).with_context(|| format!("reading {:?}", path))?;
    let stem = path.file_stem().and_then(|s| s.to_str()).unwrap_or("Unknown").to_string();
    // Internal-name based nesting check (dir names are package dirs).
    let internal = internal_name_of(path, root);
    if jcdc_decompiler::classdec::is_nested_in_pool(&internal, pool) {
        return Ok(());
    }
    let source = match decompile_one(&data, pool, opts, &stem) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("jcdc: failed to decompile {:?}: {}", path, e);
            return Ok(());
        }
    };
    let rel = match root {
        Some(r) => path.strip_prefix(r).unwrap_or(path).with_extension("java").to_string_lossy().to_string(),
        None => format!("{}.java", stem),
    };
    write_output(out, path, &rel, &source);
    Ok(())
}

fn decompile_one(data: &[u8], pool: &ClassPool, opts: &ClassOptions, fallback_name: &str) -> anyhow::Result<String> {
    // Use pool-based path so that the class itself is resolvable during
    // decompilation (self references); fall back to standalone bytes.
    match decompile_with_pool(data, pool, opts) {
        Ok(s) => Ok(s),
        Err(e) => {
            let _ = fallback_name;
            Err(e)
        }
    }
}

fn decompile_with_pool(data: &[u8], pool: &ClassPool, opts: &ClassOptions) -> anyhow::Result<String> {
    use jcdc_classfile::parse_classfile;
    use jcdc_classfile::CpLookup;
    let (_, cf) = parse_classfile(data).map_err(|e| anyhow::anyhow!("parse error: {:?}", e))?;
    let cp = CpLookup::new(&cf.constant_pool);
    let name = cp.class_name(&cf.constant_pool, cf.this_class).unwrap_or("Unknown").to_string();
    let owned = (cf, cp, name);
    // Panic isolation: a bug on one class must not abort the whole run.
    // Big-stack thread: pathological methods (giant expression trees, deep
    // CFG recursion) would otherwise overflow the default 2-8 MB stack and
    // abort the process outright (uncatchable).
    let pool2 = pool.clone();
    let opts2 = opts.clone();
    let worker = std::thread::Builder::new()
        .stack_size(512 * 1024 * 1024)
        .spawn(move || {
            std::panic::catch_unwind(std::panic::AssertUnwindSafe(move || {
                let (cf, cp, name) = owned;
                let pc = std::sync::Arc::new(jcdc_jvm::PoolClass { internal_name: name, cf, cp });
                jcdc_decompiler::decompile_class(&pc, &pool2, &opts2)
            }))
        });
    let res: Result<anyhow::Result<String>, Box<dyn std::any::Any + Send>> = match worker {
        Ok(h) => match h.join() {
            Ok(r) => r,
            Err(e) => Err(e),
        },
        Err(e) => Err(Box::new(e)),
    };
    match res {
        Ok(r) => r,
        Err(_) => anyhow::bail!("internal panic during decompilation"),
    }
}

fn write_output(out: Option<&Path>, origin: &Path, rel: &str, source: &str) {
    match out {
        Some(dir) => {
            let p = dir.join(rel);
            if let Some(parent) = p.parent() {
                let _ = std::fs::create_dir_all(parent);
            }
            let _ = std::fs::write(&p, source);
        }
        None => {
            if rel.contains('/') || rel.contains('\\') || origin.extension().map(|e| e == "jar").unwrap_or(false) {
                // multi-file mode without -o: print separators to stdout
                println!("// ===== {} =====", rel);
            }
            print!("{}", source);
        }
    }
}

fn walkdir(root: &Path) -> anyhow::Result<Vec<PathBuf>> {
    let mut out = Vec::new();
    let mut stack = vec![root.to_path_buf()];
    while let Some(d) = stack.pop() {
        for entry in std::fs::read_dir(&d)? {
            let p = entry?.path();
            if p.is_dir() {
                stack.push(p);
            } else if p.extension().and_then(|e| e.to_str()) == Some("class") {
                out.push(p);
            }
        }
    }
    Ok(out)
}

fn is_zip_like(path: &Path) -> bool {
    matches!(path.extension().and_then(|e| e.to_str()), Some("jar") | Some("zip") | Some("war"))
}

fn internal_name_of(path: &Path, root: Option<&Path>) -> String {
    match root {
        Some(r) => path
            .strip_prefix(r)
            .unwrap_or(path)
            .with_extension("")
            .to_string_lossy()
            .replace(std::path::MAIN_SEPARATOR, "/"),
        None => path.file_stem().and_then(|s| s.to_str()).unwrap_or("").to_string(),
    }
}

#[allow(dead_code)]
fn find_outer_in_pool(name: &str, pool: &ClassPool) -> Option<String> {
    let mut cut = name;
    while let Some(d) = cut.rfind('$') {
        cut = &cut[..d];
        if pool.get(cut).is_some() {
            return Some(cut.to_string());
        }
    }
    None
}
