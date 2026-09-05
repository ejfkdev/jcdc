# jcdc — Java class 文件反编译器（Rust）

把任意 JDK 版本（class 文件主版本 45 / Java 1.1 至 70 / Java 26）编译出的
`.class` 文件反编译回可读、可重编译的 Java 源码。

设计参考了 fernflower/Vineflower、garlic、CFR、Procyon、Krakatau 等开源反编译器
（研究笔记见 `docs/ARCHITECTURE_NOTES.md`），但代码为全新 Rust 实现。

## 使用

```sh
cargo build --release

# 单个 class → stdout
./target/release/jcdc Foo.class

# 目录 / jar → 输出目录（自动跳过已在池中的嵌套类，由外层类一并输出）
./target/release/jcdc classes-dir -o out/
./target/release/jcdc app.jar -o out/

# 类型解析 classpath（泛型还原、varargs、内部类判定等需要看到相关类）
./target/release/jcdc -cp jdk/lib/rt.jar:. Foo.class -o out/
```

选项：

| 选项 | 说明 |
|---|---|
| `-o, --output <dir>` | 输出目录；单 class 且未指定时打印到 stdout |
| `-cp, --classpath <p>` | 冒号分隔的 class/jar/目录列表，用于跨类型解析 |
| `--synthetic` | 输出 synthetic/bridge 成员（默认隐藏） |

调试环境变量：`JCDC_PRINT=<method>`（打印单个方法源码）、
`JCDC_PRINT_TREE=1`（打印 Stmt 树）、`JCDC_DBG_IF/LOOP/MERGE/GOTO/ANON=1`
（结构化过程跟踪）。辅助二进制：`dbg2 <class> <method>[#n]`、`dbg3 <class>`。

## Workspace 结构

```
crates/
  classfile/    class 文件二进制解析（常量池、属性、指令解码；45–70 全版本）
  jvm/          ClassPool（跨类型解析池）、PoolClass、JavaType/泛型 Signature 解析
  decompiler/   反编译核心：
    builder.rs    基本块内操作数栈模拟 → Expr/Stmt（含 indy lambda/字符串拼接、
                  varargs 展开、监控指令）
    method.rs     跨块定点迭代：merge 栈变量、钻石折叠（三元还原）、类型推断、
                  布尔化、槽位复用拆分、泛型 cast 还原、TWR/finally 修剪
    structure.rs  CFG 结构化：循环/条件/switch/try-catch-finally/synchronized 域，
                  共享尾复制（copy-walk）、appendix 折叠
    convert.rs    Region → Stmt 树（break/continue/label 解析、RawGoto 消解）
    classdec.rs   类级输出：嵌套类分类（成员/局部/匿名/lambda/枚举/record）、
                  匿名类内联、access$ 桥内联、内部类构造器伪参数剥离、
                  枚举 switch 还原、assert 还原
    emit.rs       Java 源码 Printer（优先级括号、import/短名、布尔/字符常量修正）
    varalloc.rs   LVT/LVTT 驱动的变量表
  cli/          jcdc 主程序 + 调试工具
config/versions.toml   按 class 主版本的特性开关（新 JDK 只需追加条目）
corpus/
  jdks/         已下载的历史 JDK（6–26，每个小版本最新补丁）
  jdk-sources/  对应 src.zip 解包源码（回归语料）
  features/src/ 特性验证套件源码（按语言特性分文件）
scripts/verify.py    验证管线（见下）
```

## 验证方法

反编译结果不要求与原始源码逐行一致，验收标准是**语义等价**：

1. **features 模式**（`python3 scripts/verify.py features`）：
   每个特性文件用对应 release 的 javac 编译 → 运行记录 stdout →
   jcdc 反编译 → 重编译 → 再运行 → diff stdout。
   目前 release 6/7/8/9/11/17/21/26 全部通过（编译 + 运行语义一致）。
2. **corpus 模式**（`python3 scripts/verify.py corpus --jdks 8,17,26`）：
   取真实 JDK 源码族（java.util、java.lang、java.security 等）用该版本
   javac 编译 → 反编译 → `--patch-module` 重编译 → javap 对比方法字节码。
   jdk6/7/8 前 12 个源码族全部可重编译（9/9、11/11、10/10）；
   字节码级差异集中在 javac 版本间代码生成差异（语义等价即视为通过）。
   详见 `docs/VERIFICATION.md`。
3. **冒烟**：rt.jar 全量 12608 个类批量反编译，无 panic / 死循环 / 失败。

近期修复的深水区结构化问题（详见 `docs/VERIFICATION.md`）：循环内
try-return 的异常边丢失（`SecureRandom.getInstanceStrong`）、多块循环条件
折叠（`Random.internalNextLong` 的 `while(a||b)`、`internalNextInt` 的复合
do-while）、super/this 构造器实参精确定型（`Reference$ReferenceHandler` 的
boolean）、switch 全贯穿返回时剪除不可达尾 return
（`DirectMethodHandle.shouldBeInitialized`）、宽合并变量不被 slot-reuse 拆分
（`DirectMethodHandle.make` 各 case 共用同一 `stack0`），以及 `walk` 递归
深度护栏（keytool `doCommands` 等超大方法不再挂死）。

已知限制（jdk9–26 整 `--patch-module` 闭包重编译的残余阻塞项，详见
`docs/VERIFICATION.md`；features 语义套件不受影响，全绿）：
- 复合条件 `if(A||B) then` 的 follow 误判致方法尾重复/守卫链展平
  （`Integer.toString`/`IntegerCache`/`StringUTF16`）——真后支配过滤修复
  会引发个别方法反编译挂死，已回退；
- 泛型方法实参的裸 cast/捕获还原（`List.sort` 的 `Arrays.sort(a,(Comparator)c)`）；
- 共享尾复制致 final 二次赋值（`sun.security.util.Debug`）、循环重结构化
  残留游离 `break`（`Class.toGenericString`）；
- 少数共享尾场景输出 `stack` 变量而非三元表达式（可编译，仅观感差异）。



## 版本兼容策略

不同 class 版本的差异集中在：

- **字节码形态**：jsr/ret（≤50）、StackMapTable（≥50）、invokedynamic
  （≥51，lambda/字符串拼接）、NestHost（≥55，取代 access$ 桥）、
  record/sealed（≥60）。
- **javac 代码生成习惯**：try-with-resources 的 J7 形态与 J11 形态、
  finally 复制模式、字符串拼接（StringBuilder vs StringConcatFactory）、
  内部类构造器 marker 参数（≤ JDK10）、flexible constructors（≥ JDK25 语义）。

`config/versions.toml` 按 class 主版本声明特性开关；处理逻辑本身全版本复用，
仅在模式匹配处按特性分支（如 TWR 的 J7/J11 两套匹配器）。
