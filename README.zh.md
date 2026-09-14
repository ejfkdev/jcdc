# jcdc

[English](README.md) | **简体中文**

[![CI](https://github.com/ejfkdev/jcdc/actions/workflows/ci.yml/badge.svg)](https://github.com/ejfkdev/jcdc/actions/workflows/ci.yml)
[![Release](https://img.shields.io/github/v/release/ejfkdev/jcdc)](https://github.com/ejfkdev/jcdc/releases)
[![License: MIT](https://img.shields.io/badge/license-MIT-blue.svg)](LICENSE)

用 Rust 编写的 Java class 文件反编译器——把任意 JDK（class 文件主版本 45 /
Java 1.1 至 70 / Java 26）编译出的 `.class` 文件还原为可读、**可重编译**的
Java 源码。设计参考了 fernflower/Vineflower、garlic、CFR、Procyon、Krakatau
等开源反编译器（研究笔记见 [`docs/ARCHITECTURE_NOTES.md`](docs/ARCHITECTURE_NOTES.md)），
代码为全新 Rust 实现。

## 特性

- **全版本覆盖**——Java 1.1 → 26 字节码，含 `invokedynamic`（lambda /
  字符串拼接 / switch-pattern 脱糖还原）、record、sealed、
  try-with-resources、枚举、泛型见证还原、内部/局部/匿名类重建、
  `synchronized` 域恢复。
- **大规模验证**——21 个 JDK 版本、630 个源码族的语料：**反编译产物
  100% 可重编译**，行为套件运行级输出全等、零 run-mismatch；完整
  `rt.jar`（12,609 个类）在双结构化管线下零 panic、逐字节确定。
- **快**——18 核机器上整包 `rt.jar` 约 6 秒、峰值内存约 430MB；默认并行
  且输出与调度无关（确定性）。
- **控制流忠实**——循环/条件/switch/try-catch-finally 结构化 + per-arrival
  共享尾拷贝；短路（`&&`/`||`）与 `assert` 习语源码级还原。

## 性能对比

整包 SDK 基准：Java 8 `rt.jar` 全量 class（20,413 个 class 条目 → 12,609 个
编译单元），Apple M5 Pro（18 核 / 48GB）/ macOS。Java 工具统一跑在同一 JVM
（OpenJDK 26，`-Xmx8g`）；jcdc 先跑预热页缓存，之后每个工具 `/usr/bin/time -l`
计时一次。复现脚本：[`scripts/bench.sh`](scripts/bench.sh)。

| 工具 | 墙钟时间 | 峰值内存 | 产出文件 |
|---|---:|---:|---:|
| **jcdc**（并行——默认，每核 1 worker） | **6.5 秒** | **618 MB** | 12,609 |
| jcdc（`JCDC_THREADS=1` 单线程） | 22.6 秒 | 467 MB | 12,609 |
| Vineflower 1.11.1 | 23.6 秒 | 8,631 MB | 12,609 |
| CFR 0.152 | 53.9 秒 | 4,911 MB | 12,609 |
| Procyon 0.6.0 | 105.9 秒 | 4,279 MB | 12,586 |

即便单线程，jcdc 的墙钟时间也与最快的 JVM 反编译器持平，而峰值内存只有其
**约 1/18**；默认并行管线下比 Vineflower 快约 3.6 倍、比 CFR 快约 8 倍、比
Procyon 快约 16 倍。（jcdc 带 `-cp rt.jar` 提供完整类型上下文；Java 工具从
输入 jar 自行解析。）

## 安装

**Homebrew**（macOS 苹果 M 芯片 / Intel，以及 Linux amd64/arm64）：

```sh
brew install ejfkdev/tap/jcdc
```

**crates.io**（任何装有 Rust 的平台；会一并安装 `dbg2`/`dbg3` 调试辅助工具）：

```sh
cargo install jcdc --locked
```

**预编译二进制**：从 **[Releases](https://github.com/ejfkdev/jcdc/releases)**
下载——**Linux / Windows / macOS × amd64 / arm64** 六平台裸可执行文件
（不打压缩包；含苹果 M 芯片；Linux/Windows 支持的平台经 UPX 压缩，macOS
因 UPX 不支持 Mach-O 仅剥离符号），另附 `SHA256SUMS.txt` 校验和。

**源码构建：**

```sh
git clone https://github.com/ejfkdev/jcdc && cd jcdc
cargo build --release        # 产物: target/release/jcdc
```

## 使用

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

非法调用会先打印错误、再输出完整帮助，退出码 2。

## Workspace 结构

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

## 验证方法

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

## 调试

`JCDC_PRINT=<method>`、`JCDC_PRINT_TREE=1`、
`JCDC_DBG_IF/LOOP/MERGE/GOTO/ANON/SCFOLD=1`（结构化过程跟踪）、
`JCDC_THREADS=1`（顺序渲染）、`JCDC_SLOW_LOG=<ms>`（逐类计时）。
辅助二进制：`dbg2 <class> <method>[#n]`、`dbg3 <class>`。

## 许可证

[MIT](LICENSE)
