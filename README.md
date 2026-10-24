# jcdc

**English** | [简体中文](README.zh.md)

[![CI](https://github.com/ejfkdev/jcdc/actions/workflows/ci.yml/badge.svg)](https://github.com/ejfkdev/jcdc/actions/workflows/ci.yml)
[![Release](https://img.shields.io/github/v/release/ejfkdev/jcdc)](https://github.com/ejfkdev/jcdc/releases)
[![License: MIT](https://img.shields.io/badge/license-MIT-blue.svg)](LICENSE)
[![Built with ZCode](https://img.shields.io/badge/Built%20with%20ZCode-000000.svg?style=flat&logo=data:image/svg%2bxml;base64,PHN2ZyB4bWxucz0iaHR0cDovL3d3dy53My5vcmcvMjAwMC9zdmciIHdpZHRoPSIxMTgiIGhlaWdodD0iMTAwIiB2aWV3Qm94PSIwIDAgMjU2IDIxOCI+PHBhdGggZmlsbD0iI2ZmZmZmZiIgZD0iTTEzNC40IDAuMTMwMTUyTDExNi40OCAyNS42MDIyQzExMy42NjUgMjkuNTY5OSAxMDkuMDU0IDMyLjAwMTkgMTA0LjA2NCAzMi4wMDE5SDYuMzk5OVYwQzYuMzk5OSAwLjEzMDE0OSAxMzQuNCAwLjEzMDE1MiAxMzQuNCAwLjEzMDE1MloiLz48cGF0aCBmaWxsPSIjZmZmZmZmIiBkPSJNMjU2IDAuMTMwMTI3TDEwMi40MDEgMjE3LjczMkgwTDE1My41OTkgMC4xMzAxMjdIMjU2WiIvPjxwYXRoIGZpbGw9IiNmZmZmZmYiIGQ9Ik0xMjEuNjAxIDIxNy43MzJMMTM5LjY1IDE5Mi4xMzRDMTQyLjQ2NSAxODguMTY2IDE0Ny4wNzYgMTg1LjczNCAxNTIuMDY3IDE4NS43MzRIMjQ5LjYwNFYyMTcuNzM2SDEyMS42MDFWMjE3LjczMloiLz48L3N2Zz4=)](https://zcode.z.ai/)

A Java class file decompiler written in Rust — turns `.class` files from any
JDK (class file version 45 / Java 1.1 through 72 / Java 28) back into
readable, **recompilable** Java source. Design studied from
fernflower/Vineflower, garlic, CFR, Procyon and Krakatau (research notes in
[`docs/ARCHITECTURE_NOTES.md`](docs/ARCHITECTURE_NOTES.md)); the code is a
fresh Rust implementation.

## Highlights

- **Full-era coverage** — Java 1.1 → 28 bytecode, including `invokedynamic`
  (lambda / string-concat / switch-pattern desugaring), records, sealed
  classes, try-with-resources, enums, generics re-witnessing, inner/local/
  anonymous class reconstruction, and `synchronized` recovery.
- **Verified at scale** — compile → decompile → recompile → run equality on
  the features suite for **every JDK release from 6 to 28**, plus a 630-family
  source corpus in which **100% of decompiled families recompile** with zero
  run-mismatches; full `rt.jar` (12,609 classes) renders panic-free and
  byte-deterministically on both structurizer pipelines.
- **Fast** — whole `rt.jar` in ~3.6 s and the entire Java 28 runtime image
  (27,766 classes) in ~6.2 s on 18 cores, under 1 GB peak RSS (458–945 MB);
  parallel by default with deterministic, schedule-independent output.
- **Faithful control flow** — loops/conditions/switch/try-catch-finally
  structuring with per-arrival shared-tail copies; source-exact
  short-circuit (`&&`/`||`) and `assert` idiom recovery.

## Performance

Whole-SDK benchmarks on two workloads — every class in **Java 8's `rt.jar`**
(20,413 class entries → 12,609 emitted units) and **every class of the newest
JDK, Java 28 (early access)**. (JDK 9+ has no `rt.jar`: the boot classpath
became the module image `lib/modules`, so workload 2 is that image's complete
class set — all 68 modules, 27,766 entries → 15,039 units — extracted with
`jimage`.) Host: Apple M5 Pro (18 cores, 48 GB), macOS. All Java tools run on
the same JVM (OpenJDK 27) with a uniform `-Xmx8g` heap; each tool gets one
`/usr/bin/time -l` run (wall time + peak RSS) after jcdc has warmed the page
cache. Reproduce with [`scripts/bench.sh`](scripts/bench.sh).

**Workload 1 — `rt.jar` (JDK 8, 12,609 units):**

| Tool | Wall time | Peak RSS | Units emitted |
|---|---:|---:|---:|
| **jcdc** (parallel — default, 1 worker/core) | **3.6 s** | **684 MB** | 12,609 |
| jcdc (`JCDC_THREADS=1`, single-threaded) | 12.0 s | 458 MB | 12,609 |
| Vineflower 1.11.1 | 24.7 s | 8,633 MB | 12,609 |
| CFR 0.152 | 51.9 s | 4,516 MB | 12,609 |
| Procyon 0.6.0 | 108.8 s | 2,218 MB | 12,586 |
| fernflower (JetBrains) | 208.6 s | 2,639 MB | 12,609 |

**Workload 2 — Java 28 runtime image (`lib/modules`, 15,039 units):**

| Tool | Wall time | Peak RSS | Units emitted |
|---|---:|---:|---:|
| **jcdc** (parallel — default) | **6.2 s** | **945 MB** | 15,039 |
| jcdc (`JCDC_THREADS=1`, single-threaded) | 31.6 s | 568 MB | 15,039 |
| CFR 0.152 | 144.7 s | 8,245 MB | 15,012 |
| fernflower (JetBrains) | 497.5 s | 5,108 MB | 15,039 |
| Procyon 0.6.0 | 725.2 s | 6,232 MB | 15,011 |
| Vineflower 1.11.1 † | capped at 300 s | 8,707 MB | 0 |

† Vineflower **cannot finish this workload**, which is why `scripts/bench.sh`
climbs a heap ladder (8 g → 16 g → 32 g): at **8 g** it catches 194 per-class
`Java heap space` errors and writes no file in 300 s; at **16 g** the heap
holds but it still writes nothing in 7 minutes (≥ 9 GB RSS); a previous **32 g**
probe on a same-size image was still running at the 40-minute cap (16.9 GB
peak, zero files). It does finish the core module alone (`java.base`, 7,422
entries) with a 16 g heap in 41.5 s — still slower than jcdc's whole-image
run.

Even **single-threaded**, jcdc finishes both workloads faster than every JVM
tool here (12.0 s vs Vineflower's 24.7 s on `rt.jar`), and its whole-run peak
RSS (**458–945 MB** against **2.2–8.7 GB** for the JVM tools) is 2.3×–19×
smaller. With its default parallel pipeline it is ~6.8× faster than
Vineflower, ~14× CFR, ~30× Procyon and ~57× fernflower on `rt.jar`, and
~23× (CFR) / ~80× (fernflower) / ~117× (Procyon) faster on the Java 28
image. Emitted-unit counts differ slightly between tools: jcdc folds `$`-named
hidden classes into their family file (and emits `module-info.java`), while
Procyon skips `package-info` files (−23 on `rt.jar`). (jcdc runs with
`-cp <jar>` for full type context; the JVM tools resolve from the input jar
itself.)

Times move a few tens of percent between sessions on this machine; the rows in
each table are from one run (2026-10-24, mimalloc-based jcdc), so the ratios
are what matters.

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

**From source**: the decompiler core lives in its own repo
([jdc-core](https://github.com/ejfkdev/jdc-core), shared with future
Java-family front-ends) and is a *sibling* path dependency — clone both
side by side:

```sh
git clone https://github.com/ejfkdev/jdc-core
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

The machine-neutral half of the decompiler — IR, CFG structuring, statement
conversion, Java emission — lives in **[jdc-core](https://github.com/ejfkdev/jdc-core)**
(a sibling repo, shared with future Java-family front-ends: the class-file
front-end below is one front-end, a DEX one would be another).

```
crates/classfile    class-file binary parsing (constant pool, attributes,
                    instruction decode; versions 45–72)
crates/jvm          ClassPool (cross-type resolution), generic Signature parsing
crates/decompiler   the class-file front-end + its JVM idioms:
  builder.rs          operand-stack simulation → Expr/Stmt (indy lambdas,
                      string concat, varargs, monitors)
  method.rs           fixpoint passes: merge-slot vars, diamond folding
                      (ternaries), type inference, booleanization, slot
                      splitting, generic cast recovery, TWR/finally pruning
  classdec.rs         class-level emission: nested-class taxonomy, anonymous
                      inlining, enum-switch/assert recovery, access$ bridges
  jvmctx.rs           the Ctx implementation: the core's only view of this
                      front-end (types, nesting, signatures, lambda bodies)
  varalloc.rs         LVT/LVTT-driven variable tables
                      (structuring, Region→Stmt conversion and the Java
                      printer live in jdc-core now — see ../jdc-core/src/
                      structure.rs, sese.rs, convert.rs, emit.rs)
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
