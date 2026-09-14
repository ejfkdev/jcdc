# jcdc

[![CI](https://github.com/ejfkdev/jcdc/actions/workflows/ci.yml/badge.svg)](https://github.com/ejfkdev/jcdc/actions/workflows/ci.yml)
[![Release](https://img.shields.io/github/v/release/ejfkdev/jcdc)](https://github.com/ejfkdev/jcdc/releases)
[![License](https://img.shields.io/badge/license-MIT%20OR%20Apache--2.0-blue.svg)](#license--许可证)

A Java class file decompiler written in Rust — turns `.class` files from any
JDK (class file version 45 / Java 1.1 through 70 / Java 26) back into readable,
**recompilable** Java source. Design studied from fernflower/Vineflower,
garlic, CFR, Procyon and Krakatau (research notes in
[`docs/ARCHITECTURE_NOTES.md`](docs/ARCHITECTURE_NOTES.md)); the code is a
fresh Rust implementation.

用 Rust 编写的 Java class 文件反编译器——把任意 JDK（class 文件主版本 45 /
Java 1.1 至 70 / Java 26）编译出的 `.class` 文件还原为可读、**可重编译**的
Java 源码。设计参考了 fernflower/Vineflower、garlic、CFR、Procyon、Krakatau
等开源反编译器（研究笔记见 [`docs/ARCHITECTURE_NOTES.md`](docs/ARCHITECTURE_NOTES.md)），
代码为全新 Rust 实现。

---

## English

### Highlights

- **Full-era coverage** — Java 1.1 → 26 bytecode, including `invokedynamic`
  (lambda / string-concat / switch-pattern desugaring), records, sealed
  classes, try-with-resources, enums, generics re-witnessing, inner/local/
  anonymous class reconstruction, and `synchronized` recovery.
- **Verified at scale** — across a 21-release JDK corpus (630 source
  families): **100% of decompiled families recompile**, with run-level output
  equality on the behavioral suite and zero run-mismatches; full `rt.jar`
  (12,609 classes) renders panic-free on both structurizer pipelines.
- **Fast** — whole `rt.jar` in ~6 s (18-core), ~430 MB peak RSS, parallel by
  default with deterministic, schedule-independent output.
- **Faithful control flow** — loops/conditions/switch/try-catch-finally
  structuring with per-arrival shared-tail copies; source-exact short-circuit
  (`&&`/`||`) and `assert` idiom recovery.

### Install

Download a prebuilt binary (Linux / Windows compressed with UPX, macOS arm64 &
amd64) from **[Releases](https://github.com/ejfkdev/jcdc/releases)**, or build
from source:

```sh
cargo build --release        # binary: target/release/jcdc
```

### Usage

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

### Workspace layout

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

### Verification

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

### Debugging

`JCDC_PRINT=<method>`, `JCDC_PRINT_TREE=1`,
`JCDC_DBG_IF/LOOP/MERGE/GOTO/ANON/SCFOLD=1` (structuring traces),
`JCDC_THREADS=1` (sequential rendering), `JCDC_SLOW_LOG=<ms>` (per-class
timing). Helper binaries: `dbg2 <class> <method>[#n]`, `dbg3 <class>`.

---

## 中文

### 特性

- **全版本覆盖**——Java 1.1 → 26 字节码，含 `invokedynamic`（lambda /
  字符串拼接 / switch-pattern 脱糖还原）、record、sealed、
  try-with-resources、枚举、泛型见证还原、内部/局部/匿名类重建、
  `synchronized` 域恢复。
- **大规模验证**——21 个 JDK 版本、630 个源码族的语料：**反编译产物
  100% 可重编译**，行为套件运行级输出全等、零 run-mismatch；完整
  `rt.jar`（12,609 个类）在双结构化管线下零 panic 渲染。
- **快**——18 核机器上整包 `rt.jar` 约 6 秒、峰值内存约 430MB；默认并行
  且输出与调度无关（确定性）。
- **控制流忠实**——循环/条件/switch/try-catch-finally 结构化 + per-arrival
  共享尾拷贝；短路（`&&`/`||`）与 `assert` 习语源码级还原。

### 安装

从 **[Releases](https://github.com/ejfkdev/jcdc/releases)** 下载预编译二进制
（Linux / Windows 经 UPX 压缩，macOS arm64 与 amd64），或源码构建：

```sh
cargo build --release        # 产物: target/release/jcdc
```

### 使用

```sh
jcdc Foo.class                       # 反编译输出到 stdout
jcdc -o Foo.java Foo.class           # 输出到单个文件
jcdc -o out/ Foo.class               # out/<包路径>/Foo.java
jcdc -cp rt.jar pkg/ -o out/         # 整目录树，保持包结构
jcdc -o out/ app.jar                 # 整 jar
jcdc classes/                        # 缺省输出到平级 classes-dec/ 目录
jcdc --synthetic Foo.class           # 包含 synthetic/bridge 成员
```

| 选项 | 说明 |
|---|---|
| `-o, --output <path>` | 输出文件、目录（保持包结构）、或 `-` 强制 stdout |
| `-cp, --classpath <p>` | 冒号分隔的 class/jar/目录列表，用于跨类型解析（泛型、varargs、嵌套判定） |
| `--synthetic` | 输出 synthetic/bridge 成员（默认隐藏） |
| `-h, --help` / `-V, --version` | 帮助 / 版本（也支持 `help`、`version` 子命令） |

### Workspace 结构

```
crates/classfile    class 文件二进制解析（常量池、属性、指令解码；45–70 全版本）
crates/jvm          ClassPool（跨类型解析池）、泛型 Signature 解析
crates/decompiler   反编译核心：
  builder.rs          操作数栈模拟 → Expr/Stmt（indy lambda、字符串拼接、
                      varargs、monitor 指令）
  method.rs           跨块定点迭代：merge 栈变量、钻石折叠（三元还原）、类型
                      推断、布尔化、槽位拆分、泛型 cast 还原、TWR/finally 修剪
  structure.rs        CFG 结构化：循环/条件/switch/try/sync 域、共享尾拷贝、
                      parked-chain 路由
  convert.rs          Region → Stmt 树（break/continue/label 消解）
  classdec.rs         类级输出：嵌套类分类、匿名类内联、枚举 switch/assert
                      还原、access$ 桥内联
  emit.rs             Java 源码 Printer（优先级括号、import/短名）
  varalloc.rs         LVT/LVTT 驱动的变量表
crates/cli          jcdc 主程序（+ dbg2/dbg3 调试辅助）
config/versions.toml  按 class 主版本的特性开关（新 JDK 只需追加条目）
corpus/               验证语料（features 套件 + JDK 下载清单）
scripts/verify.py     验证管线（features / corpus 两种模式）
```

### 验证方法

验收标准不是与原始源码逐行一致，而是**语义等价**：

1. `python3 scripts/verify.py features`——每个特性文件用对应年代 javac
   编译 → 运行 → 反编译 → 重编译 → 再运行 → stdout/rc 精确 diff。
   release 6/7/8/9/11/17/21/26 全部通过。
2. `python3 scripts/verify.py corpus`——真实 JDK 源码族按年代编译 →
   反编译 → `--patch-module` 重编译 → `javap` 方法级字节码对比 +
   运行差异检测。最近全量：21 个版本 617/617 重编译、0 run-mismatch。
3. `rt.jar` 冒烟：12,609 个类双管线渲染、零 panic、逐字节确定。

详见 [`docs/VERIFICATION.md`](docs/VERIFICATION.md) 与
[`QUALITY_REPORT.md`](QUALITY_REPORT.md)。

### 调试

`JCDC_PRINT=<method>`、`JCDC_PRINT_TREE=1`、
`JCDC_DBG_IF/LOOP/MERGE/GOTO/ANON/SCFOLD=1`（结构化过程跟踪）、
`JCDC_THREADS=1`（顺序渲染）、`JCDC_SLOW_LOG=<ms>`（逐类计时）。
辅助二进制：`dbg2 <class> <method>[#n]`、`dbg3 <class>`。

---

## License / 许可证

MIT OR Apache-2.0
