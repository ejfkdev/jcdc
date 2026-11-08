//! jcdc — Java class file decompiler CLI.

use std::collections::HashMap;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicBool, Ordering};

use anyhow::Context;
use jcdc_decompiler::{ClassOptions, ClassPool};

/// Allocation is roughly a third of the profile on whole-jar runs and the
/// system allocator throttles under the render worker pool (18 threads:
/// ~11 s of system time). mimalloc keeps per-thread arenas and hands pages
/// back more eagerly, which also lowers the peak.
#[global_allocator]
static GLOBAL: mimalloc::MiMalloc = mimalloc::MiMalloc;

/// Any failed output write makes the process exit non-zero: a partial tree
/// must not look like a successful run.
static WRITE_FAILED: AtomicBool = AtomicBool::new(false);

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

/// Precomputed output path for one job: (chosen relative path, optional
/// rename note). Plans are assigned in job order BEFORE the worker pool
/// starts, so case-insensitive collision suffixes are deterministic
/// regardless of thread scheduling.
type OutPlan = (String, Option<String>);

/// Sanitize one path segment (Windows-invalid chars, overlong names).
/// A class name of thousands of spaces used to fail with os error 123 and
/// drop the class; sanitizing keeps the output.
fn sanitize_segment(seg: &str) -> String {
    fn hash(s: &str) -> u32 {
        let mut h: u32 = 0x811c9dc5;
        for b in s.bytes() {
            h ^= b as u32;
            h = h.wrapping_mul(0x01000193);
        }
        h
    }
    let mut out = String::with_capacity(seg.len());
    for c in seg.chars() {
        let bad = c.is_control() || matches!(c, '<' | '>' | ':' | '"' | '\\' | '|' | '?' | '*');
        if bad {
            out.push('_');
        } else {
            out.push(c);
        }
    }
    // Windows forbids trailing dots/spaces; an all-space name is unusable.
    let trimmed = out.trim_end_matches([' ', '.']);
    let mut seg = if trimmed.is_empty() { "_" } else { trimmed }.to_string();
    // Cap BOTH chars and UTF-8 bytes: a 120-char CJK name is 360 bytes and
    // still exceeds the per-component filesystem limit.
    if seg.chars().count() > 120 || seg.len() > 200 {
        let mut keep = String::new();
        for c in seg.chars() {
            if keep.chars().count() >= 100 || keep.len() + c.len_utf8() > 160 {
                break;
            }
            keep.push(c);
        }
        seg = format!("{keep}~{:08x}", hash(seg.as_str()));
    }
    seg
}

/// Stable 64-bit FNV-1a, used to fold over-long directory chains without
/// relying on any external hasher.
fn fnv64(s: &str) -> u64 {
    let mut h: u64 = 0xcbf29ce484222325;
    for b in s.bytes() {
        h ^= b as u64;
        h = h.wrapping_mul(0x100000001b3);
    }
    h
}

/// Path-length budget for the RELATIVE output path, after the root prefix.
/// Windows still enforces MAX_PATH (~260) for relative paths unless long
/// paths are enabled; macOS/Linux have much larger limits but not
/// unlimited ones. Keep a margin for the separator and `_N` suffixes.
fn path_budget(root: &Path) -> usize {
    // Debug override (also used by the test matrix to emulate the Windows
    // MAX_PATH budget on other platforms).
    if let Ok(v) = std::env::var("JCDC_PATH_BUDGET") {
        if let Ok(n) = v.parse::<usize>() {
            return n;
        }
    }
    let max: usize = if cfg!(windows) {
        250
    } else if cfg!(target_os = "macos") {
        1000
    } else {
        4000
    };
    let root_len = root.as_os_str().to_string_lossy().chars().count();
    max.saturating_sub(root_len + 8)
}

/// A path of thousands of `nmsl/` segments fits no filesystem. Keep the
/// first directory segment and the class file name, folding the rest into
/// one stable hashed directory: `xx/_jcdc_<16 hex>/Class.java` (issue #2).
/// The PACKAGE declaration keeps its full name (identifier-escaped, but
/// every segment); only the on-disk location is compacted.
fn fit_path_budget(rel: &str, budget: usize) -> (String, bool) {
    if rel.chars().count() <= budget {
        return (rel.to_string(), false);
    }
    let (dirs, file) = match rel.rsplit_once('/') {
        Some((d, f)) => (d, f),
        None => ("", rel),
    };
    let folded = if dirs.is_empty() {
        file.to_string()
    } else {
        let first = dirs.split('/').next().unwrap_or("");
        let h = fnv64(dirs);
        if !first.is_empty() && first != dirs {
            format!("{first}/_jcdc_{h:016x}/{file}")
        } else {
            format!("_jcdc_{h:016x}/{file}")
        }
    };
    if folded.chars().count() <= budget {
        (folded, true)
    } else {
        // Even the first segment + hash + file do not fit: the file name
        // alone is the last resort; dedupe suffixes still apply.
        (file.to_string(), true)
    }
}

/// Shorten an obfuscated path for the in-file comment; hundreds of
/// segments would otherwise bloat every affected file.
fn short_path(rel: &str) -> String {
    const MAX: usize = 120;
    if rel.chars().count() <= MAX {
        return rel.to_string();
    }
    let head: String = rel.chars().take(MAX - 20).collect();
    format!("{head}...({} chars)", rel.chars().count())
}

/// Sanitize a `/`-separated relative path (keeping `.java`).
fn sanitize_rel(rel: &str) -> String {
    let mut parts: Vec<String> = rel
        .split('/')
        .map(|p| {
            if let Some(stem) = p.strip_suffix(".java") {
                format!("{}.java", sanitize_segment(stem))
            } else {
                sanitize_segment(p)
            }
        })
        .collect();
    if parts.is_empty() {
        parts.push("Unknown.java".to_string());
    }
    parts.join("/")
}

/// Does the output filesystem fold case? A case-only collision can only be
/// resolved by renaming on such filesystems; on case-sensitive ones the
/// two names coexist and a rename would needlessly break the public
/// class/file-name match.
fn fs_is_case_insensitive(dir: &Path) -> bool {
    let mut d = dir.to_path_buf();
    while !d.exists() {
        if !d.pop() {
            return cfg!(any(windows, target_os = "macos"));
        }
    }
    let probe = d.join(format!(".jcdc_case_{}", std::process::id()));
    if std::fs::write(&probe, b"").is_err() {
        return cfg!(windows);
    }
    let upper = d.join(format!(".JCDC_CASE_{}", std::process::id()));
    let ins = upper.exists();
    let _ = std::fs::remove_file(&probe);
    ins
}

/// Assign deterministic, collision-free output paths for `rels` in order.
/// Two classes whose paths differ only by case land on the same file on
/// NTFS/APFS; the later one gets `_0`, `_1`, ... (issue #1).
fn plan_rels(rels: Vec<String>, case_insensitive: bool, budget: usize) -> Vec<OutPlan> {
    let mut used: HashMap<String, ()> = HashMap::new();
    let mut out = Vec::with_capacity(rels.len());
    for rel in rels {
        let sanitized = sanitize_rel(&rel);
        let mut notes: Vec<String> = Vec::new();
        if sanitized != rel {
            notes.push(format!("sanitized to `{}`", short_path(&sanitized)));
        }
        let (fitted, folded) = fit_path_budget(&sanitized, budget);
        if folded {
            notes.push(format!(
                "directory chain folded to `{}` to fit the filesystem path limit",
                fitted
            ));
        }
        let key = if case_insensitive {
            fitted.to_lowercase()
        } else {
            fitted.clone()
        };
        let mut chosen = fitted.clone();
        if used.contains_key(&key) {
            let (stem, ext) = match fitted.strip_suffix(".java") {
                Some(s) => (s.to_string(), ".java"),
                None => (fitted.clone(), ""),
            };
            let mut n = 0usize;
            loop {
                let cand = format!("{}_{}{}", stem, n, ext);
                let ck = if case_insensitive { cand.to_lowercase() } else { cand.clone() };
                if !used.contains_key(&ck) {
                    chosen = cand;
                    break;
                }
                n += 1;
            }
            notes.push(format!(
                "collided with an earlier class; written as `{}`",
                chosen
            ));
        }
        let ck = if case_insensitive { chosen.to_lowercase() } else { chosen.clone() };
        used.insert(ck, ());
        let note = if notes.is_empty() {
            None
        } else {
            Some(format!(
                "// jcdc: output path `{}`: {}\n",
                short_path(&rel),
                notes.join("; ")
            ))
        };
        out.push((chosen, note));
    }
    out
}

fn print_help() {
    println!(
        "jcdc {} — Java class file decompiler",
        env!("CARGO_PKG_VERSION")
    );
    println!();
    println!("Decompiles .class files (class version 45-72, Java 1.1-28) back");
    println!("into readable, recompilable Java source.");
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
    println!("  --synthetic            include synthetic/bridge members (default: hidden,");
    println!("                         with a per-class comment giving the count)");
    println!("  --cure                 simplify/format the emitted source with cure");
    println!("                         (constant folding, redundant branch/cast cleanup)");
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

fn main() {
    if let Err(e) = run() {
        // Invalid invocation: show what went wrong, then the full help so
        // the user does not have to re-run with -h.
        eprintln!("jcdc: {e:?}");
        eprintln!();
        print_help();
        std::process::exit(2);
    }
}

fn run() -> anyhow::Result<()> {
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
    let mut cure = false;

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
            "--cure" => cure = true,
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
        let n = decompile_path(input, &pool, &opts, &target, cure)?;
        total += n;
        if let OutTarget::Dir(d) = &target {
            eprintln!("jcdc: wrote {} file(s) to {}", n, d.display());
        }
    }
    if total == 0 && inputs.len() == 1 {
        eprintln!("jcdc: no classes decompiled from {}", inputs[0].display());
    }
    if WRITE_FAILED.load(Ordering::Relaxed) {
        anyhow::bail!("one or more output files could not be written");
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
    cure: bool,
    plan: Option<&OutPlan>,
) -> anyhow::Result<usize> {
    match job {
        Job::File { path, root } => {
            decompile_class_file(path, pool, opts, target, root.as_deref(), cure, plan)
        }
        Job::Bytes { name, data } => {
            // Name jar output by the class's OWN internal name, not the zip
            // entry path: obfuscated jars can have duplicate/differently
            // cased entry names that disagree with the class declared
            // inside (issue #1).
            let internal = class_rel_name(data)
                .map(|n| n.trim_end_matches(".java").to_string())
                .unwrap_or_else(|| name.trim_end_matches(".class").to_string());
            if jcdc_decompiler::classdec::is_nested_in_pool(&internal, pool) {
                if std::env::var("JCDC_TRACE_FILES").is_ok() {
                    eprintln!("jcdc-skip-nested: {}", internal);
                }
                return Ok(0);
            }
            let java_name = format!("{}.java", internal);
            match decompile_one(data, pool, opts, &internal, cure) {
                Ok(source) => Ok(usize::from(emit_to_target(
                    target, plan, &java_name, &source,
                ))),
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
    cure: bool,
    plans: &[OutPlan],
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
    let plans = Arc::new(plans.to_vec());
    let next = Arc::new(AtomicUsize::new(0));
    let written = Arc::new(AtomicUsize::new(0));
    let mut handles: Vec<std::thread::JoinHandle<bool>> = Vec::new();
    for _ in 0..workers {
        let (jobs, next, written) = (jobs.clone(), next.clone(), written.clone());
        let pool = pool.clone();
        let opts = opts.clone();
        let target = target.clone();
        let plans = plans.clone();
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
                        process_job(job, &pool, &opts, &target, cure, plans.get(i))
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
                    let plans = plans.clone();
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
                                    process_job(job, &pool, &opts, &target, cure, plans.get(i))
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
    cure: bool,
) -> anyhow::Result<usize> {
    let dir_target = matches!(target, OutTarget::Dir(_));
    if path.is_dir() {
        // every .class file, rendered in parallel. Sorted so the collision
        // plan (and therefore output names) is deterministic.
        let mut entries = walkdir(path)?;
        entries.sort();
        let mut rels = Vec::with_capacity(entries.len());
        for entry in &entries {
            let internal = internal_name_of(entry, Some(path));
            rels.push(format!("{}.java", internal));
        }
        let plans = if dir_target {
            let d = match target {
                OutTarget::Dir(d) => d.clone(),
                _ => PathBuf::new(),
            };
            plan_rels(rels, fs_is_case_insensitive(&d), path_budget(&d))
        } else {
            Vec::new()
        };
        let jobs = entries
            .into_iter()
            .map(|entry| Job::File {
                path: entry,
                root: Some(path.to_path_buf()),
            })
            .collect();
        return Ok(run_jobs(jobs, pool, opts, target, cure, &plans));
    }
    if is_zip_like(path) {
        if let OutTarget::File(_) = target {
            anyhow::bail!("a file output is not valid for a jar input");
        }
        let file = std::fs::File::open(path)?;
        let mut zip = zip::ZipArchive::new(file)?;
        let mut jobs = Vec::with_capacity(zip.len());
        let mut rels: Vec<String> = Vec::with_capacity(zip.len());
        for i in 0..zip.len() {
            let mut e = zip.by_index(i)?;
            let name = e.name()?.to_string();
            if !name.ends_with(".class") {
                continue;
            }
            let mut buf = Vec::with_capacity(e.size() as usize);
            std::io::Read::read_to_end(&mut e, &mut buf)?;
            // Output by the class's OWN internal name, not the zip entry
            // path: obfuscated jars can carry duplicate or differently
            // cased entry names that disagree with the class inside.
            let internal = class_rel_name(&buf)
                .map(|n| n.trim_end_matches(".java").to_string())
                .unwrap_or_else(|| name.trim_end_matches(".class").to_string());
            // Escape identifier-unsafe characters exactly as the class
            // DECLARATION does (`sanitize_source_name`), so a public
            // class's file name matches its printed name. `package-info`
            // and `module-info` are MANDATED file names (javac rejects a
            // package annotation anywhere else) — keep their hyphen.
            let parts: Vec<&str> = internal.split('/').collect();
            let last = parts.len().saturating_sub(1);
            let rel_internal: Vec<String> = parts
                .iter()
                .enumerate()
                .map(|(i, seg)| {
                    if i == last && (*seg == "package-info" || *seg == "module-info") {
                        seg.to_string()
                    } else {
                        let s = jcdc_decompiler::emit::sanitize_source_name(seg);
                        if s.is_empty() {
                            // Empty class name: `__` (the escape for the
                            // reserved lone `_`), matching the declaration.
                            "__".to_string()
                        } else {
                            s
                        }
                    }
                })
                .collect();
            rels.push(format!("{}.java", rel_internal.join("/")));
            jobs.push(Job::Bytes { name, data: buf });
        }
        let plans = if dir_target {
            let d = match target {
                OutTarget::Dir(d) => d.clone(),
                _ => PathBuf::new(),
            };
            plan_rels(rels, fs_is_case_insensitive(&d), path_budget(&d))
        } else {
            Vec::new()
        };
        return Ok(run_jobs(jobs, pool, opts, target, cure, &plans));
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
        cure,
        &[],
    ))
}

fn decompile_class_file(
    path: &Path,
    pool: &ClassPool,
    opts: &ClassOptions,
    target: &OutTarget,
    root: Option<&Path>,
    cure: bool,
    plan: Option<&OutPlan>,
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
    // Nesting check against the class's OWN name: the pool indexes by
    // this_class, and a directory tree need not be a package tree rooted at
    // the input dir (corpus layouts like `cfr/java_8/...`), where the
    // path-derived name misses and the nested class would get its own file
    // on top of being inlined into its family.
    let internal = internal_name_of(path, root);
    let nesting = class_rel_name(&data).unwrap_or_else(|| internal.clone());
    if jcdc_decompiler::classdec::is_nested_in_pool(&nesting, pool) {
        return Ok(0);
    }
    let source = match decompile_one(&data, pool, opts, &stem, cure) {
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
            usize::from(emit_to_target(target, plan, &rel, &source))
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
    cure: bool,
) -> anyhow::Result<String> {
    // Use pool-based path so that the class itself is resolvable during
    // decompilation (self references); fall back to standalone bytes.
    match decompile_with_pool(data, pool, opts) {
        Ok(s) => Ok(if cure { cure_source(&s) } else { s }),
        Err(e) => {
            let _ = fallback_name;
            Err(e)
        }
    }
}

/// Post-process one decompiled unit with cure's Java backend:
/// parse -> simplify to a fixed point -> print. The parser is
/// fault-tolerant (a malformed region is preserved verbatim), but a
/// rule panic must never lose jcdc's output: fall back to the
/// original text instead.
fn cure_source(source: &str) -> String {
    let src = source.to_string();
    let out = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let mut outcome = cure_java_parser::parse(&src);
        let cfg = cure_engine::Config::default();
        let _ = cure_java_simplify::simplify_unit(&mut outcome.ast, &mut outcome.unit, &cfg);
        cure_java_print::print_unit(&outcome.ast, &outcome.unit)
    }));
    match out {
        Ok(s) => s,
        Err(_) => source.to_string(),
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

/// Write one class through the collision-safe naming pipeline. `plan` is
/// the pre-assigned (chosen path, note) for pooled inputs; single-class
/// outputs have none and are sanitized here.
fn emit_to_target(
    target: &OutTarget,
    plan: Option<&OutPlan>,
    rel: &str,
    source: &str,
) -> bool {
    match target {
        OutTarget::Dir(_) => {
            let (chosen, note) = match plan {
                Some((c, n)) => (c.clone(), n.clone()),
                None => {
                    let san = sanitize_rel(rel);
                    let n = (san != rel).then(|| {
                        format!(
                            "// jcdc: output path `{}` sanitized to a filesystem-safe `{}`\n",
                            rel, san
                        )
                    });
                    (san, n)
                }
            };
            if let Some(note) = note {
                let mut s = String::with_capacity(source.len() + note.len());
                s.push_str(&note);
                s.push_str(source);
                write_source(target, &chosen, &s)
            } else {
                write_source(target, &chosen, source)
            }
        }
        _ => write_source(target, rel, source),
    }
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
                    WRITE_FAILED.store(true, Ordering::Relaxed);
                    return false;
                }
            }
            match std::fs::write(&p, source) {
                Ok(()) => true,
                Err(e) => {
                    eprintln!("jcdc: cannot write {}: {}", p.display(), e);
                    WRITE_FAILED.store(true, Ordering::Relaxed);
                    false
                }
            }
        }
        OutTarget::File(f) => {
            if let Some(parent) = f.parent() {
                if !parent.as_os_str().is_empty() {
                    if let Err(e) = std::fs::create_dir_all(parent) {
                        eprintln!("jcdc: cannot create {}: {}", parent.display(), e);
                        WRITE_FAILED.store(true, Ordering::Relaxed);
                        return false;
                    }
                }
            }
            match std::fs::write(f, source) {
                Ok(()) => true,
                Err(e) => {
                    eprintln!("jcdc: cannot write {}: {}", f.display(), e);
                    WRITE_FAILED.store(true, Ordering::Relaxed);
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
