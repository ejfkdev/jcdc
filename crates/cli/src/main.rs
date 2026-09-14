//! jcdc — Java class file decompiler CLI.

use std::path::{Path, PathBuf};

use anyhow::Context;
use jcdc_decompiler::{ClassOptions, ClassPool};

/// Where the decompiled source goes for one input.
#[derive(Debug, Clone)]
enum OutTarget {
    /// Print to stdout (single class: bare source; dir/jar: `// ===== rel =====` separators).
    Stdout,
    /// Root directory; every file is placed at its package-relative path.
    Dir(PathBuf),
    /// One explicit .java file (single-class inputs only).
    File(PathBuf),
}

fn print_help() {
    println!("jcdc — Java class file decompiler");
    println!();
    println!("Usage: jcdc [OPTIONS] <INPUT>...");
    println!("       jcdc <help|version>");
    println!();
    println!("INPUT is a single .class file, a directory tree of classes, or a");
    println!(".jar/.zip/.war archive. Multiple inputs may be given.");
    println!();
    println!("Options:");
    println!("  -o, --output <path>    Where to write the decompiled source:");
    println!("                           single .class  a .java file, or a directory");
    println!("                                          (package structure preserved)");
    println!("                           dir / jar      output root directory");
    println!("                           -              force stdout");
    println!("                         Defaults: single .class → stdout; dir/jar →");
    println!("                         sibling directory \"<input-name>-dec\".");
    println!("  -cp, --classpath <p>   colon-separated classpath for type resolution");
    println!("  --synthetic            include synthetic/bridge members");
    println!("  -h, --help             print this help");
    println!("  -V, --version          print version");
    println!();
    println!("Examples:");
    println!("  jcdc Foo.class                          # print Foo.java to stdout");
    println!("  jcdc -o Foo.java Foo.class              # write one file");
    println!("  jcdc -o out/ Foo.class                  # out/<package>/Foo.java");
    println!("  jcdc -cp rt.jar Foo.class               # with classpath context");
    println!("  jcdc classes/                           # classes-dec/ next to input");
    println!("  jcdc -o src-dec/ rt.jar                 # whole jar, structure kept");
    println!("  jcdc -o - classes/                      # dump everything to stdout");
}

fn main() -> anyhow::Result<()> {
    if !jcdc_decompiler::dbg_flag!("JCDC_PANIC_VERBOSE") {
        std::panic::set_hook(Box::new(|info| {
            if jcdc_decompiler::dbg_flag!("JCDC_PANIC_LOG") {
                eprintln!("jcdc-panic: {}", info);
            }
        }));
    }
    let args: Vec<String> = std::env::args().skip(1).collect();
    let mut inputs: Vec<PathBuf> = Vec::new();
    let mut classpath: Vec<PathBuf> = Vec::new();
    let mut out: Option<String> = None;
    let mut show_synthetic = false;

    let mut i = 0;
    while i < args.len() {
        // Bare commands (only when they cannot be an input yet).
        if inputs.is_empty() && !args[i].starts_with('-') {
            match args[i].as_str() {
                "help" => {
                    print_help();
                    return Ok(());
                }
                "version" => {
                    println!("jcdc {}", env!("CARGO_PKG_VERSION"));
                    return Ok(());
                }
                _ => {}
            }
        }
        // Split `--opt=value` into name + inline value.
        let (name, inline_val) = match args[i].split_once('=') {
            Some((n, v)) if n.starts_with("--") || n == "-o" || n == "-cp" => {
                (n.to_string(), Some(v.to_string()))
            }
            _ => (args[i].clone(), None),
        };
        macro_rules! take_value {
            () => {{
                match inline_val.clone() {
                    Some(v) => v,
                    None => {
                        i += 1;
                        args.get(i)
                            .cloned()
                            .with_context(|| format!("{} needs a value", name))?
                    }
                }
            }};
        }
        match name.as_str() {
            "-h" | "--help" => {
                print_help();
                return Ok(());
            }
            "-V" | "--version" => {
                println!("jcdc {}", env!("CARGO_PKG_VERSION"));
                return Ok(());
            }
            "-o" | "--output" => {
                out = Some(take_value!());
            }
            "-cp" | "--classpath" => {
                let v = take_value!();
                classpath.extend(v.split(':').map(PathBuf::from));
            }
            "--synthetic" => show_synthetic = true,
            other => {
                if other.starts_with('-') {
                    anyhow::bail!("unknown option {} (try --help)", other);
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

    let mut total = 0usize;
    for input in &inputs {
        let target = resolve_target(input, out.as_deref(), inputs.len() > 1)?;
        let n = decompile_path(input, &pool, &opts, &target)?;
        total += n;
        if let OutTarget::Dir(d) = &target {
            eprintln!("jcdc: wrote {} file(s) to {}", n, d.display());
        }
    }
    if total == 0 && inputs.len() == 1 {
        eprintln!("jcdc: no classes decompiled from {}", inputs[0].display());
    }
    Ok(())
}

/// Decide where one input's output goes. `-o` semantics:
/// `-` forces stdout; a `.java` suffix (or an existing non-directory) is a
/// single output file (single-class inputs only); anything else is an output
/// root directory. With no `-o`, a single class prints to stdout and a
/// directory/jar writes to a sibling `<name>-dec` directory.
fn resolve_target(input: &Path, out: Option<&str>, multi: bool) -> anyhow::Result<OutTarget> {
    let single_class = input.is_file() && !is_zip_like(input);
    match out {
        Some("-") => Ok(OutTarget::Stdout),
        Some(o) => {
            let p = PathBuf::from(o);
            if p.extension().and_then(|e| e.to_str()) == Some("java")
                || (p.exists() && p.is_file())
            {
                if !single_class {
                    anyhow::bail!(
                        "-o {} names a file but {} is a directory/jar input (use a directory or '-')",
                        o,
                        input.display()
                    );
                }
                if multi {
                    anyhow::bail!(
                        "a single -o FILE cannot serve multiple inputs (use a directory or '-')"
                    );
                }
                return Ok(OutTarget::File(p));
            }
            Ok(OutTarget::Dir(p))
        }
        None => {
            if single_class {
                return Ok(OutTarget::Stdout);
            }
            let name = input
                .file_stem()
                .or_else(|| input.file_name())
                .and_then(|s| s.to_str())
                .context("input has no usable name")?;
            let dir = input
                .parent()
                .unwrap_or(Path::new("."))
                .join(format!("{}-dec", name));
            eprintln!(
                "jcdc: no -o given; writing to {} (pass -o to override, -o - for stdout)",
                dir.display()
            );
            Ok(OutTarget::Dir(dir))
        }
    }
}

/// One unit of parallel work.
enum Job {
    File { path: PathBuf, root: Option<PathBuf> },
    Bytes { name: String, data: Vec<u8> },
}

fn job_label(j: &Job) -> String {
    match j {
        Job::File { path, .. } => path.display().to_string(),
        Job::Bytes { name, .. } => name.clone(),
    }
}

fn process_job(
    job: &Job,
    pool: &ClassPool,
    opts: &ClassOptions,
    target: &OutTarget,
) -> anyhow::Result<usize> {
    match job {
        Job::File { path, root } => {
            decompile_class_file(path, pool, opts, target, root.as_deref())
        }
        Job::Bytes { name, data } => {
            let stem = name.trim_end_matches(".class");
            if jcdc_decompiler::classdec::is_nested_in_pool(stem, pool) {
                return Ok(0);
            }
            let java_name = format!("{}.java", stem);
            match decompile_one(data, pool, opts, stem) {
                Ok(source) => Ok(usize::from(write_source(target, &java_name, &source))),
                Err(e) => {
                    eprintln!("jcdc: failed to decompile {}: {}", name, e);
                    Ok(0)
                }
            }
        }
    }
}

/// Run jobs across a pool of big-stack workers. A worker that catches a
/// panic EXITS and is replaced by a fresh thread: renderer thread-locals
/// (e.g. structure.rs COPY_DEPTH) are not panic-drop-guarded, so a
/// contaminated thread must never render another class (output would
/// depend on job-to-thread assignment).
fn run_jobs(
    jobs: Vec<Job>,
    pool: &ClassPool,
    opts: &ClassOptions,
    target: &OutTarget,
) -> usize {
    use std::sync::atomic::{AtomicUsize, Ordering};
    use std::sync::Arc;
    let n_jobs = jobs.len();
    // Default: one worker per available CPU core (JCDC_THREADS overrides;
    // the 64 clamp only guards absurd core counts — each worker reserves
    // a 512MB virtual stack and its own L1 pool cache slice).
    let workers = jcdc_decompiler::dbg_value!("JCDC_THREADS", usize)
        .unwrap_or_else(|| std::thread::available_parallelism().map(|n| n.get()).unwrap_or(1))
        .clamp(1, 64)
        .min(n_jobs.max(1));
    let jobs = Arc::new(jobs);
    let next = Arc::new(AtomicUsize::new(0));
    let written = Arc::new(AtomicUsize::new(0));
    let mut handles: Vec<std::thread::JoinHandle<bool>> = Vec::new();
    for _ in 0..workers {
        let (jobs, next, written) = (jobs.clone(), next.clone(), written.clone());
        let pool = pool.clone();
        let opts = opts.clone();
        let target = target.clone();
        let h = std::thread::Builder::new()
            .stack_size(512 * 1024 * 1024)
            .spawn(move || {
                loop {
                    let i = next.fetch_add(1, Ordering::Relaxed);
                    if i >= jobs.len() {
                        return false; // queue drained, clean exit
                    }
                    let job = &jobs[i];
                    let res = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                        process_job(job, &pool, &opts, &target)
                    }));
                    match res {
                        Ok(Ok(n)) => {
                            written.fetch_add(n, Ordering::Relaxed);
                        }
                        Ok(Err(e)) => {
                            eprintln!("jcdc: {}: {}", job_label(job), e);
                        }
                        Err(_) => {
                            eprintln!("jcdc: internal panic on {}", job_label(job));
                            return true; // contaminated TLS: exit for replacement
                        }
                    }
                }
            });
        match h {
            Ok(h) => handles.push(h),
            Err(e) => eprintln!("jcdc: cannot spawn worker: {}", e),
        }
    }
    // Supervisor: join workers; replace panicked ones while work remains.
    let mut i = 0;
    while i < handles.len() {
        let h = std::mem::replace(&mut handles[i], std::thread::spawn(|| false));
        match h.join() {
            Ok(true) => {
                if next.load(Ordering::Relaxed) < n_jobs {
                    let (jobs, next, written) = (jobs.clone(), next.clone(), written.clone());
                    let pool = pool.clone();
                    let opts = opts.clone();
                    let target = target.clone();
                    if let Ok(nh) = std::thread::Builder::new()
                        .stack_size(512 * 1024 * 1024)
                        .spawn(move || {
                            loop {
                                let i = next.fetch_add(1, Ordering::Relaxed);
                                if i >= jobs.len() {
                                    return false;
                                }
                                let job = &jobs[i];
                                let res = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                                    process_job(job, &pool, &opts, &target)
                                }));
                                match res {
                                    Ok(Ok(n)) => {
                                        written.fetch_add(n, Ordering::Relaxed);
                                    }
                                    Ok(Err(e)) => eprintln!("jcdc: {}: {}", job_label(job), e),
                                    Err(_) => {
                                        eprintln!("jcdc: internal panic on {}", job_label(job));
                                        return true;
                                    }
                                }
                            }
                        })
                    {
                        handles[i] = nh;
                        continue; // re-join this slot
                    }
                }
            }
            Err(_) => eprintln!("jcdc: worker thread failed"),
            _ => {}
        }
        i += 1;
    }
    written.load(Ordering::Relaxed)
}

fn decompile_path(
    path: &Path,
    pool: &ClassPool,
    opts: &ClassOptions,
    target: &OutTarget,
) -> anyhow::Result<usize> {
    if path.is_dir() {
        // every .class file, rendered in parallel
        let jobs = walkdir(path)?
            .into_iter()
            .map(|entry| Job::File {
                path: entry,
                root: Some(path.to_path_buf()),
            })
            .collect();
        return Ok(run_jobs(jobs, pool, opts, target));
    }
    if is_zip_like(path) {
        if let OutTarget::File(_) = target {
            anyhow::bail!("a file output is not valid for a jar input");
        }
        let file = std::fs::File::open(path)?;
        let mut zip = zip::ZipArchive::new(file)?;
        let mut jobs = Vec::with_capacity(zip.len());
        for i in 0..zip.len() {
            let mut e = zip.by_index(i)?;
            let name = e.name().to_string();
            if !name.ends_with(".class") {
                continue;
            }
            let mut buf = Vec::with_capacity(e.size() as usize);
            std::io::Read::read_to_end(&mut e, &mut buf)?;
            jobs.push(Job::Bytes { name, data: buf });
        }
        return Ok(run_jobs(jobs, pool, opts, target));
    }
    // Single class file: still via the worker pool so it gets the 512MB
    // stack + panic isolation the main thread cannot provide.
    Ok(run_jobs(
        vec![Job::File {
            path: path.to_path_buf(),
            root: None,
        }],
        pool,
        opts,
        target,
    ))
}

fn decompile_class_file(
    path: &Path,
    pool: &ClassPool,
    opts: &ClassOptions,
    target: &OutTarget,
    root: Option<&Path>,
) -> anyhow::Result<usize> {
    if jcdc_decompiler::dbg_flag!("JCDC_TRACE_FILES") {
        eprintln!("jcdc-file: {}", path.display());
    }
    let data = std::fs::read(path).with_context(|| format!("reading {:?}", path))?;
    let stem = path
        .file_stem()
        .and_then(|s| s.to_str())
        .unwrap_or("Unknown")
        .to_string();
    // Internal-name based nesting check (dir names are package dirs).
    let internal = internal_name_of(path, root);
    if jcdc_decompiler::classdec::is_nested_in_pool(&internal, pool) {
        return Ok(0);
    }
    let source = match decompile_one(&data, pool, opts, &stem) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("jcdc: failed to decompile {:?}: {}", path, e);
            return Ok(0);
        }
    };
    let written = match target {
        OutTarget::Stdout => {
            write_source(target, &internal, &source);
            1usize
        }
        OutTarget::File(f) => {
            usize::from(write_source(target, &f.to_string_lossy(), &source))
        }
        OutTarget::Dir(_) => {
            // Package structure preserved: directory inputs use their
            // relative path; a lone class file uses its THIS_CLASS name
            // (the file may sit anywhere, e.g. `jcdc -o out/ ./Foo.class`).
            let rel = match root {
                Some(_) => format!("{}.java", internal),
                None => class_rel_name(&data).unwrap_or_else(|| format!("{}.java", stem)),
            };
            usize::from(write_source(target, &rel, &source))
        }
    };
    Ok(written)
}

/// `<internal-name>.java` for a single class file, from its THIS_CLASS.
fn class_rel_name(data: &[u8]) -> Option<String> {
    let (_, cf) = jcdc_classfile::parse_classfile(data).ok()?;
    let cp = jcdc_classfile::CpLookup::new(&cf.constant_pool);
    let name = cp.class_name(&cf.constant_pool, cf.this_class)?;
    Some(format!("{}.java", name))
}

fn decompile_one(
    data: &[u8],
    pool: &ClassPool,
    opts: &ClassOptions,
    fallback_name: &str,
) -> anyhow::Result<String> {
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
    let slow_ms: Option<u128> = jcdc_decompiler::dbg_value!("JCDC_SLOW_LOG", u128);
    let t0 = slow_ms.map(|_| std::time::Instant::now());
    let (_, cf) = parse_classfile(data).map_err(|e| anyhow::anyhow!("parse error: {:?}", e))?;
    let cp = CpLookup::new(&cf.constant_pool);
    let name = cp
        .class_name(&cf.constant_pool, cf.this_class)
        .unwrap_or("Unknown")
        .to_string();
    // Runs directly on the caller's thread: run_jobs workers provide the
    // 512MB stacks and the panic catch (a panic replaces the whole worker
    // so contaminated thread-locals never render another class).
    let pc = std::sync::Arc::new(jcdc_jvm::PoolClass { internal_name: name, cf, cp });
    let res = jcdc_decompiler::decompile_class(&pc, pool, opts);
    if let (Some(thresh), Some(t0)) = (slow_ms, t0) {
        let el = t0.elapsed().as_millis();
        if el >= thresh {
            match &res {
                Ok(r) => eprintln!("jcdc-slow: {} {}ms out={}B", pc.internal_name, el, r.len()),
                Err(_) => eprintln!("jcdc-slow: {} (err)", pc.internal_name),
            }
        }
    }
    res
}

/// Send one rendered source to its target: stdout (with a separator header
/// when part of a multi-file dump), an exact file path, or a directory that
/// gets the package-relative path created under it. Returns false when a
/// file write failed (reported to stderr; stdout writes always succeed).
fn write_source(target: &OutTarget, rel: &str, source: &str) -> bool {
    match target {
        OutTarget::Stdout => {
            if rel.contains('/') || rel.contains('\\') {
                // multi-file mode without -o: print separators to stdout
                println!("// ===== {} =====", rel);
            }
            print!("{}", source);
            true
        }
        OutTarget::Dir(d) => {
            let p = d.join(rel);
            if let Some(parent) = p.parent() {
                if let Err(e) = std::fs::create_dir_all(parent) {
                    eprintln!("jcdc: cannot create {}: {}", parent.display(), e);
                    return false;
                }
            }
            match std::fs::write(&p, source) {
                Ok(()) => true,
                Err(e) => {
                    eprintln!("jcdc: cannot write {}: {}", p.display(), e);
                    false
                }
            }
        }
        OutTarget::File(f) => {
            if let Some(parent) = f.parent() {
                if !parent.as_os_str().is_empty() {
                    if let Err(e) = std::fs::create_dir_all(parent) {
                        eprintln!("jcdc: cannot create {}: {}", parent.display(), e);
                        return false;
                    }
                }
            }
            match std::fs::write(f, source) {
                Ok(()) => true,
                Err(e) => {
                    eprintln!("jcdc: cannot write {}: {}", f.display(), e);
                    false
                }
            }
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
    matches!(
        path.extension().and_then(|e| e.to_str()),
        Some("jar") | Some("zip") | Some("war")
    )
}

fn internal_name_of(path: &Path, root: Option<&Path>) -> String {
    match root {
        Some(r) => path
            .strip_prefix(r)
            .unwrap_or(path)
            .with_extension("")
            .to_string_lossy()
            .replace(std::path::MAIN_SEPARATOR, "/"),
        None => path
            .file_stem()
            .and_then(|s| s.to_str())
            .unwrap_or("")
            .to_string(),
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
