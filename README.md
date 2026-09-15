# jcdc

**English** | [简体中文](README.zh.md)

[![CI](https://github.com/ejfkdev/jcdc/actions/workflows/ci.yml/badge.svg)](https://github.com/ejfkdev/jcdc/actions/workflows/ci.yml)
[![Release](https://img.shields.io/github/v/release/ejfkdev/jcdc)](https://github.com/ejfkdev/jcdc/releases)
[![License: MIT](https://img.shields.io/badge/license-MIT-blue.svg)](LICENSE)
[![Built with ZCode](https://img.shields.io/badge/Built%20with%20ZCode-000000.svg?style=flat&logo=data:image/svg%2bxml;base64,PHN2ZyB4bWxucz0iaHR0cDovL3d3dy53My5vcmcvMjAwMC9zdmciIHdpZHRoPSIxMTgiIGhlaWdodD0iMTAwIiB2aWV3Qm94PSIwIDAgMjU2IDIxOCI+PHBhdGggZmlsbD0iI2ZmZmZmZiIgZD0iTTEzNC40IDAuMTMwMTUyTDExNi40OCAyNS42MDIyQzExMy42NjUgMjkuNTY5OSAxMDkuMDU0IDMyLjAwMTkgMTA0LjA2NCAzMi4wMDE5SDYuMzk5OVYwQzYuMzk5OSAwLjEzMDE0OSAxMzQuNCAwLjEzMDE1MiAxMzQuNCAwLjEzMDE1MloiLz48cGF0aCBmaWxsPSIjZmZmZmZmIiBkPSJNMjU2IDAuMTMwMTI3TDEwMi40MDEgMjE3LjczMkgwTDE1My41OTkgMC4xMzAxMjdIMjU2WiIvPjxwYXRoIGZpbGw9IiNmZmZmZmYiIGQ9Ik0xMjEuNjAxIDIxNy43MzJMMTM5LjY1IDE5Mi4xMzRDMTQyLjQ2NSAxODguMTY2IDE0Ny4wNzYgMTg1LjczNCAxNTIuMDY3IDE4NS43MzRIMjQ5LjYwNFYyMTcuNzM2SDEyMS42MDFWMjE3LjczMloiLz48L3N2Zz4=)](https://zcode.z.ai/)

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
- **Fast** — whole `rt.jar` in ~7 s and the entire JDK 26 runtime image
  (27,855 classes) in ~12 s (18-core), under 900 MB peak RSS; parallel by
  default with deterministic, schedule-independent output.
- **Faithful control flow** — loops/conditions/switch/try-catch-finally
  structuring with per-arrival shared-tail copies; source-exact
  short-circuit (`&&`/`||`) and `assert` idiom recovery.

## Performance

Whole-SDK benchmarks on two workloads — every class in **Java 8's `rt.jar`**
(20,413 class entries → 12,609 emitted units) and **every class of the newest
JDK, Java 26**. (JDK 9+ has no `rt.jar`: the boot classpath became the module
image `lib/modules`, so workload 2 is that image's complete class set — all
68 modules, 27,855 entries → 15,231 units — extracted with `jimage`.) Host:
Apple M5 Pro (18 cores, 48 GB), macOS. All Java tools run on the same JVM
(OpenJDK 26) with a uniform `-Xmx8g` heap; each tool gets one
`/usr/bin/time -l` run (wall time + peak RSS) after jcdc has warmed the page
cache. Reproduce with [`scripts/bench.sh`](scripts/bench.sh).

**Workload 1 — `rt.jar` (JDK 8, 12,609 units):**

| Tool | Wall time | Peak RSS | Units emitted |
|---|---:|---:|---:|
| **jcdc** (parallel — default, 1 worker/core) | **6.8 s** | **599 MB** | 12,609 |
| jcdc (`JCDC_THREADS=1`, single-threaded) | 23.3 s | 503 MB | 12,609 |
| Vineflower 1.11.1 | 26.2 s | 8,710 MB | 12,609 |
| CFR 0.152 | 59.4 s | 4,831 MB | 12,609 |
| Procyon 0.6.0 | 113.1 s | 4,377 MB | 12,586 |
| fernflower (JetBrains) | 196.8 s | 2,760 MB | 12,609 |

**Workload 2 — JDK 26 runtime image (`lib/modules`, 15,231 units):**

| Tool | Wall time | Peak RSS | Units emitted |
|---|---:|---:|---:|
| **jcdc** (parallel — default) | **11.9 s** | **801 MB** | 15,231 |
| jcdc (`JCDC_THREADS=1`, single-threaded) | 72.3 s | 591 MB | 15,231 |
| CFR 0.152 | 175.8 s | 8,146 MB | 15,235 |
| fernflower (JetBrains) | 513.1 s | 4,485 MB | 15,231 |
| Procyon 0.6.0 | 789.4 s | 4,343 MB | 15,233 |
| Vineflower 1.11.1 † | > 40 min (capped) | 16,964 MB | 0 |

† Vineflower **cannot finish this workload**: at `-Xmx8g` and `-Xmx16g` it
exhausts the heap (hundreds of caught per-class `OutOfMemoryError`s, nothing
written even after 48 min at 16g); at `-Xmx32g` it was still running when
capped at 40 min (16.9 GB peak RSS, `Java heap space` errors, zero files
written). It does finish the core module alone (`java.base`, 7,422 entries)
with a 16g heap in 41.5 s — still slower than jcdc's whole-image run.

Even single-threaded, jcdc is the fastest tool on both workloads, and its
whole-run peak RSS (**503–801 MB against 2.8–17 GB** for the JVM tools,
3.4×–34× less) is smaller than any of them. With the default parallel
pipeline it is ~3.9× faster than Vineflower, ~8.8× faster than CFR, ~17×
faster than Procyon and ~29× faster than fernflower on `rt.jar`, and ~15×
(CFR) / ~43× (fernflower) / ~66× (Procyon) faster on the JDK 26 image.
Emitted-unit counts differ slightly between tools: jcdc folds `$`-named
hidden classes into their family file (and emits `module-info.java`), while
Procyon skips `package-info` files (−23 on `rt.jar`). (jcdc runs with
`-cp <jar>` for full type context; the JVM tools resolve from the input jar
itself.)

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
