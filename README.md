# jcdc

**English** | [简体中文](README.zh.md)

[![CI](https://github.com/ejfkdev/jcdc/actions/workflows/ci.yml/badge.svg)](https://github.com/ejfkdev/jcdc/actions/workflows/ci.yml)
[![Release](https://img.shields.io/github/v/release/ejfkdev/jcdc)](https://github.com/ejfkdev/jcdc/releases)
[![License: MIT](https://img.shields.io/badge/license-MIT-blue.svg)](LICENSE)

A Java class file decompiler written in Rust — turns `.class` files from any
JDK (class file version 45 / Java 1.1 through 70 / Java 26) back into
readable, **recompilable** Java source. Design studied from
fernflower/Vineflower, garlic, CFR, Procyon and Krakatau (research notes in
[`docs/ARCHITECTURE_NOTES.md`](docs/ARCHITECTURE_NOTES.md)); the code is a
fresh Rust implementation.

## Highlights

- **Full-era coverage** — Java 1.1 → 26 bytecode, including `invokedynamic`
  (lambda / string-concat / switch-pattern desugaring), records, sealed
  classes, try-with-resources, enums, generics re-witnessing, inner/local/
  anonymous class reconstruction, and `synchronized` recovery.
- **Verified at scale** — across a 21-release JDK corpus (630 source
  families): **100% of decompiled families recompile**, with run-level output
  equality on the behavioral suite and zero run-mismatches; full `rt.jar`
  (12,609 classes) renders panic-free and byte-deterministically on both
  structurizer pipelines.
- **Fast** — whole `rt.jar` in ~7 s and JDK 26 `java.base` in ~3 s (18-core),
  under 600 MB peak RSS; parallel by default with deterministic,
  schedule-independent output.
- **Faithful control flow** — loops/conditions/switch/try-catch-finally
  structuring with per-arrival shared-tail copies; source-exact
  short-circuit (`&&`/`||`) and `assert` idiom recovery.

## Performance

Whole-SDK benchmarks on two workloads — every class in **Java 8's `rt.jar`**
(20,413 class entries → 12,609 emitted compilation units) and **Java 26's
`java.base`** module (7,422 class entries → ~3,400 units, extracted with
`jimage`). Host: Apple M5 Pro (18 cores, 48 GB), macOS. All Java tools run on
the same JVM (OpenJDK 26) with a uniform `-Xmx8g` heap; each tool gets one
`/usr/bin/time -l` run (wall time + peak RSS) after jcdc has warmed the page
cache. Reproduce with [`scripts/bench.sh`](scripts/bench.sh).

**Workload 1 — `rt.jar` (JDK 8, 12,609 units):**

| Tool | Wall time | Peak RSS | Units emitted |
|---|---:|---:|---:|
| **jcdc** (parallel — default, 1 worker/core) | **7.4 s** | **594 MB** | 12,609 |
| jcdc (`JCDC_THREADS=1`, single-threaded) | 23.0 s | 461 MB | 12,609 |
| Vineflower 1.11.1 | 39.9 s | 8,434 MB | 12,609 |
| CFR 0.152 | 53.0 s | 4,318 MB | 12,609 |
| Procyon 0.6.0 | 99.4 s | 2,252 MB | 12,586 |
| fernflower (JetBrains) | 190.5 s | 2,770 MB | 12,609 |

**Workload 2 — `java.base` (JDK 26, modern bytecode):**

| Tool | Wall time | Peak RSS | Units emitted |
|---|---:|---:|---:|
| **jcdc** (parallel — default) | **2.9 s** | **216 MB** | 3,383 |
| jcdc (`JCDC_THREADS=1`, single-threaded) | 9.7 s | 153 MB | 3,383 |
| CFR 0.152 | 20.5 s | 2,145 MB | 3,386 |
| Vineflower 1.11.1 † | 41.5 s | 10,236 MB | 3,383 |
| fernflower (JetBrains) | 51.9 s | 2,549 MB | 3,383 |
| Procyon 0.6.0 | 79.3 s | 3,474 MB | 3,386 |

† Vineflower **OOMs at `-Xmx8g` on the JDK 26 workload** (zero files
written); the row above is its `-Xmx16g` retry.

Even single-threaded, jcdc is the fastest or near-fastest tool on both
workloads while using **153–594 MB peak RSS against 2.1–10.2 GB** for the
JVM tools (~4×–67× less); with the default parallel pipeline it is ~7×
faster than the next-fastest tool (CFR) on JDK 26 and ~5–26× faster than
every JVM tool on `rt.jar`. Emitted-unit counts differ slightly between
tools: jcdc folds `$`-named hidden classes into their family file (and
emits `module-info.java`), while Procyon skips `package-info` files (−23 on
`rt.jar`). (jcdc runs with `-cp <jar>` for full type context; the JVM tools
resolve from the input jar itself.)

## Install

**Homebrew** (macOS Apple silicon / Intel, and Linux amd64/arm64):

```sh
brew install ejfkdev/tap/jcdc
```

**crates.io** (any platform with Rust; also installs the `dbg2`/`dbg3`
debug helpers):

```sh
cargo install jcdc --locked
```

**Prebuilt binaries** from **[Releases](https://github.com/ejfkdev/jcdc/releases)** —
raw executables (no archives) for **Linux / Windows / macOS × amd64 / arm64**
(Apple silicon included; Linux & Windows UPX-compressed where supported,
macOS stripped-only since UPX has no Mach-O support), plus `SHA256SUMS.txt`.

**From source:**

```sh
git clone https://github.com/ejfkdev/jcdc && cd jcdc
cargo build --release        # binary: target/release/jcdc
```

## Usage

```sh
jcdc Foo.class                       # print decompiled source to stdout
jcdc -o Foo.java Foo.class           # write to one file
jcdc -o out/ Foo.class               # out/<package>/Foo.java
jcdc -cp rt.jar pkg/ -o out/         # whole directory tree, structure kept
jcdc -o out/ app.jar                 # whole jar
jcdc classes/                        # default: sibling "classes-dec/" dir
jcdc --synthetic Foo.class           # include synthetic/bridge members
```

| Option | Description |
|---|---|
| `-o, --output <path>` | output file, directory (package structure preserved), or `-` to force stdout |
| `-cp, --classpath <p>` | colon-separated class/jar/dir list for cross-type resolution (generics, varargs, nesting) |
| `--synthetic` | emit synthetic/bridge members (hidden by default) |
| `-h, --help` / `-V, --version` | help / version (`help` and `version` subcommands also work) |

Invalid invocations print the error followed by the full help and exit 2.

## Workspace layout

```
crates/classfile    class-file binary parsing (constant pool, attributes,
                    instruction decode; versions 45–70)
crates/jvm          ClassPool (cross-type resolution), generic Signature parsing
crates/decompiler   the decompiler core:
  builder.rs          operand-stack simulation → Expr/Stmt (indy lambdas,
                      string concat, varargs, monitors)
  method.rs           fixpoint passes: merge-slot vars, diamond folding
                      (ternaries), type inference, booleanization, slot
                      splitting, generic cast recovery, TWR/finally pruning
  structure.rs        CFG structuring: loops/conds/switch/try/sync regions,
                      shared-tail copy-walks, parked-chain routing
  convert.rs          Region → Stmt trees (break/continue/label resolution)
  classdec.rs         class-level emission: nested-class taxonomy, anonymous
                      inlining, enum-switch/assert recovery, access$ bridges
  emit.rs             Java source printer (precedence parens, short names)
  varalloc.rs         LVT/LVTT-driven variable tables
crates/cli          the jcdc binary (+ dbg2/dbg3 debug helpers)
config/versions.toml  per-class-version feature switches (new JDK = new entry)
corpus/               verification corpus (features suite + JDK manifest)
scripts/verify.py     the verification pipeline (features / corpus modes)
```

## Verification

Source-text equality is **not** the bar — semantic equivalence is:

1. `python3 scripts/verify.py features` — compile each feature file with its
   era's javac → run → decompile → recompile → re-run → exact stdout/rc diff.
   Green on releases 6/7/8/9/11/17/21/26.
2. `python3 scripts/verify.py corpus` — real JDK source families compiled per
   era → decompiled → `--patch-module` recompiled → `javap` method-level
   bytecode comparison + run-mismatch detection. Last full sweep: 21
   releases, 617/617 recompiled, 0 run-mismatches.
3. `rt.jar` smoke: all 12,609 classes rendered on both pipelines, zero
   panics, byte-deterministic.

Details in [`docs/VERIFICATION.md`](docs/VERIFICATION.md) and
[`QUALITY_REPORT.md`](QUALITY_REPORT.md).

## Debugging

`JCDC_PRINT=<method>`, `JCDC_PRINT_TREE=1`,
`JCDC_DBG_IF/LOOP/MERGE/GOTO/ANON/SCFOLD=1` (structuring traces),
`JCDC_THREADS=1` (sequential rendering), `JCDC_SLOW_LOG=<ms>` (per-class
timing). Helper binaries: `dbg2 <class> <method>[#n]`, `dbg3 <class>`.

## License

[MIT](LICENSE)
