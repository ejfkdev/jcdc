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
- **Fast** — whole `rt.jar` in ~6 s (18-core), ~430 MB peak RSS; parallel by
  default with deterministic, schedule-independent output.
- **Faithful control flow** — loops/conditions/switch/try-catch-finally
  structuring with per-arrival shared-tail copies; source-exact
  short-circuit (`&&`/`||`) and `assert` idiom recovery.

## Install

Download a prebuilt binary from **[Releases](https://github.com/ejfkdev/jcdc/releases)** —
raw executables (no archives) for **Linux / Windows / macOS × amd64 / arm64**
(Apple silicon included; Linux & Windows UPX-compressed where supported,
macOS stripped-only since UPX has no Mach-O support), plus `SHA256SUMS.txt`.
Or build from source:

```sh
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
