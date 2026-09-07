# jcdc 验证方法与结果

验收标准（用户约定）：反编译输出不要求与原始源码逐行一致，**语义等价**即可。
本仓库用三层验证逼近该标准，全部可由 `scripts/verify.py` 复现。

## 1. features 模式 — 运行语义等价（最强标准）

```sh
python3 scripts/verify.py features                # 全部 release
python3 scripts/verify.py features --releases 8,17,26
```

流程：`corpus/features/src/feat/*.java` 每个特性文件

1. 用对应 release 的 javac 编译（`--release N`；jdk6/7 用其自带 javac，
   JDK6 在 Rosetta 下会 segfault，改用 `java -Xint -cp ... com.sun.tools.javac.Main`）；
2. 运行原始类，记录 stdout；
3. `jcdc` 反编译 → 得到 Java 源码；
4. 重新编译反编译产物；
5. 运行重编译类，diff stdout。

判定：重编译成功 且 stdout 完全一致。覆盖的特性文件按 release 划分
（Legacy6/Legacy7、ControlFlow、Exceptions、Generics、InnerClasses、
LambdaStream、TwrSync、RecordsSealed、Modern26 等），涵盖：
jsr/ret、增强 for、协变返回、枚举、泛型桥、内部/匿名/局部类、lambda、
方法引用、字符串拼接 indy、try-with-resources（J7/J11 两种形态）、
synchronized、assert、record、sealed、switch 表达式、var、文本块等。

## 2. corpus 模式 — 真实 JDK 源码回归

```sh
python3 scripts/verify.py corpus --jdks 8,17,26 --limit 12 [--keep]
```

流程：从各 JDK 的 `src.zip` 取自包含源码族（java.util AbstractCollection
家族、Base64、Hashtable、java.lang.Class/Character、java.security.KeyStore
等），用该版本 javac（`-g`，必要时 `--patch-module`）编译 →
反编译整个族 → `--patch-module java.base=decomp` 重编译 →
`javap -p -c` 逐方法对比字节码。

判定分两档：
- **recompile ok**（硬标准）：反编译产物必须能通过该时代 javac 重编译；
- **bytecode equal**（软标准，仅统计）：javac 跨版本代码生成有差异
  （如三元/钻石的栈布局、TWR 脚手架），字节码不完全一致但语义等价
  属预期，不计为失败。

## 3. 冒烟 — 规模与健壮性

```sh
find /tmp/buf -name '*.class' | xargs -P 8 -n 40 jcdc
```

5528 个类（JDK 自身 + 常见库）批量反编译：要求零 panic、零挂死、零失败。

## 平台类路径

corpus/features 管线在反编译时为 jcdc 传入时代匹配的平台类（jdk8 用自带
`rt.jar`，jdk9+ 用对应 JDK 的 `jmods/java.base.jmod` 与 `jdk.unsupported.jmod`，
jmod 内 `classes/` 前缀由 ClassPool 剥离），用于泛型 Signature、varargs、
内部类等跨类型解析。家族/嵌套类枚举只认「主输入源」（输入目录/文件），
classpath 上的类仅作参考，不会把异版本的嵌套类泄漏进反编译产物。

9+ 的重编译采用 `--patch-module java.base=<decomp>:<该版本完整源码树>`，
decomp 在前（反编译产物优先），完整源码树兜底解析 sun.util.spi、
jdk.internal asm 等 java.base 内部依赖——与原始编译的解析方式一致。

## JDK 语料

`corpus/jdks/` 含 jdk6–jdk26（每个小版本最新补丁版；macOS aarch64/x64，
旧版本经 Rosetta）。`corpus/jdk-sources/` 为对应 `src.zip` 解包。
下载/安装记录见 `corpus/jdks/MANIFEST.json`。

## 当前状态（2026-09）

- features：release 6/7/8/9/11/17/21/26 全部 `recompile_ok=true` 且运行
  输出一致（用户验收标准：语义等价）。此前 r6 Legacy6 尾换行 flake 已证实
  为字节一致的捕获抖动，本轮未复现。
- 冒烟：rt.jar 全量反编译 12135 个 .java，零 panic、零错误、零挂死；超大
  方法（keytool `Main.doCommands`，数万行）经 `walk` 递归深度护栏不再挂死。
- 单测：`cargo test` 39 项全绿。
- corpus（真实 JDK 源码重编译）：jdk6/7/8 源码族全量重编译通过；jdk9–26
  的 java.util 源码族在整 `--patch-module` 闭包重编译时仍被若干深水区结构化
  问题阻塞（见下「已知限制」）。注意重编译是 per-family 全或无的批量编译，
  闭包中单个类不可编译即令该版本 12 族全部记 0，是比语义等价更严的压力测试。
- 字节码级一致率（javap 对比）：差异几乎全部来自 javac 跨版本代码生成差异
  与栈变量形态（语义等价，features 运行验证覆盖）。

### 本轮修复的深水区问题

| # | 版本 / 类·方法 | 根因 | 解法 |
|---|---|---|---|
| 1 | 9/11 `SecureRandom.getInstanceStrong` | 循环内 try-return 的异常边丢失：循环成员可达性只走正常 succ，两分支皆 return 的 try 块被判为循环出口，整个 try/catch 被提出循环 | `structure_loop` 成员可达性改走异常边（`exc_edges` 放宽为 overlap 语义，覆盖尾 return 落在 range 边界的保护块）；保护成员的尾 return/throw 保留为循环成员 |
| 2 | 9/11 `Random.internalNextLong` | 多块循环条件 `while(a\|\|b)` 编译成两块串联测试，循环头直接后继均非出口，`classify_loop` 退化为 `while(true)` + 空 if，丢失出口成死循环 | `classify_loop` 识别「fall 侧为纯条件延续块（无语句、其 taken 为循环出口、fall 回体）」，折叠为 `while(a \|\| !b) body` |
| 4 | 26 `Reference$ReferenceHandler` | super/this 构造器实参按「参数个数」匹配重载，`Thread` 有多个等长构造器时选错，boolean 实参 `iconst_0` 被输出成 int `0` | super/this 实参改用 methodref 精确描述符 `desc.args` 直接定型（`0`→`false`、`0L` 等） |
| 5 | 26 `DirectMethodHandle.shouldBeInitialized` | switch 各 case 落空贯穿到返回的 default 时，方法尾 `return` 不可达却未剪枝，javac 报「无法访问的语句」 | `stmt_terminates` 支持 switch：有 default 且**所有** case 入口均终止（break 判为不终止）才判终止，`prune_unreachable` 据此剪不可达尾；「所有」条件避免 `makeImpl` 的 case9 break 到共享尾 return 时被误剪成「缺少返回语句」 |
| 6 | 9/11 `Random.internalNextInt` | 复合条件 do-while（`do{..}while(a\|\|b); return r;`）的两块条件被还原成 do-while 体内 `if(a)continue; if(b)continue; else return r;`，循环后缺尾 `return`，javac 报「缺少返回语句」 | `extract_compound_do_while`：先展平嵌套序列块，识别尾部「连续 `if(ci)continue` + 末 `if(cN)continue else exit`」运行，折叠为 `do{body}while(c1\|\|..\|\|cN); exit`（self-loop 与 goto 两条 classify 路径都接入） |
| 7 | 26 `DirectMethodHandle.make` | switch 各 case 把结果存入同一合并变量后 break 到共享尾 `return`；slot-reuse 拆分 pass 把该宽合并变量按各 case 的具体类型（Special/Interface/DMH）顺序拆成 3 个变量，尾部 `return` 只读到 default 的那个 → 其余 case 返回未赋值/错误值 | `handle_assign`：宽合并变量（`wide_stack_vars`，跨互斥分支接收不同类型、已 join 为 Object）**不参与** slot-reuse 拆分，保持单一身份；各 case 赋同一 `stack0`，尾 `return (DMH) stack0` 正确 |


健壮性：`walk` 增加递归深度护栏（256 层），超大方法（如 keytool
`doCommands`）的共享尾递归不再导致挂死/栈溢出，退化为局部 goto 仍可编译。

### 已知限制（jdk9–26 整闭包重编译的残余阻塞项）

corpus 的整 `--patch-module` 闭包重编译是「全或无」的批量编译：闭包内任一
类不可编译即令该版本全部族记 0。本轮修复后，各版本的阻塞点已逐层后移
（jdk9/11 越过 SecureRandom/Random，jdk26 越过 DirectMethodHandle.make/
shouldBeInitialized/Reference），暴露出更深层的残余问题：

- **复合条件 `if(A||B) then` 的 follow 误判**（jdk17/21 首要阻塞）：
  `immediate_postdom` 用「最近公共后代」（min BFS 距离）近似直接后支配者，
  会把 then 体（它本身也是 entry 的一个后继、BFS 自距离 0）误当 follow，
  导致方法尾重复（`Integer.toString`/`IntegerCache.<clinit>`，后者还令 final
  字段疑似二次赋值）或守卫链展平（`StringUTF16.replace`）。
  **第一性原理**：follow 的正确定义是 entry 的直接后支配者；近似在不对称
  分支（短路条件）下必错。**彻底修复的障碍（已在 git `rewrite-structurer`
  分支系统验证）**：把 follow 改成真后支配者后，整条结构化管线失效——六种
  实现都未能交付：①完整后支配树（哨兵虚出口 + 反向 CHK，O(n²)×每 COND，巨方法
  卡死）②真后支配旁路过滤 ③仅拒绝「后继即候选」（含 self-loop 与 ≤300 块
  门控）④③ + walk 主循环护栏收紧到 O(universe)（消除挂死但 features 全 release
  重编译失败）⑤完整后支配树 + 共享尾复制改走有界 `copy_walk`（COPY_DEPTH=4）
  ——解决了挂死，却仍令 features 全 8 release `recompile_ok=false`：逐方法定位
  发现唯一报错是 `未定义的标签 L{n}`，真后支配 follow 改道后嵌套循环里
  break-to-outer 的**跳转目标块从「外层循环记录的 exit」漂移到「循环内某个 if
  汇合块」**，`resolve_goto` 既匹配不到 `loops[i].exits`、该块又不再是
  `if_follows`，退化成 `RawGoto(block)`；printer 把 `Stmt::Goto(id)` 印成
  `break L{id};` 而配套 `pending_labels` 标签发射是**死代码从未实现**，且前向
  break 的标签在 Java 里本必须**外围包裹**该 break——故非法。⑥**混合方案**
  （≤300 块用精确后支配树、精确 ipdom 为虚出口即分支发散时回退 BFS 最近汇合 +
  resolve_goto 增补「流向某外层循环 exit 即 break 之」+ 有界共享尾）——**features
  全 8 release 转绿**（重编译+运行一致，6 修复保留，`Legacy6.loops` 的
  break-outer 正确带标签），但**全 rt.jar 冒烟过不去**：一是精确后支配树是
  O(n²)/scope，比 BFS 慢约 15×（media/sound 包 15s vs <1s），复杂类单方法即
  >120s，整 jar 实际跑不完；二是把 walk 主循环护栏从 10 万收紧到
  `64×universe+1024`（合法 walk 每块只 claim 一次=O(n)，故不误伤 features，
  实测 features 仍全绿）后，发散虽被 bound，O(n²) 慢仍在。且 corpus 阻塞只是
  **平移**未消除（jdk9/11 移到 `Provider.java` 缺返回、jdk26 仍是
  `Class.toGenericString` 游离 break、jdk17/21 仍 `IntegerCache`）。⑥ 已提交在
  `rewrite-structurer` 分支（`JCDC_RW` 门控，默认关；含 visit-cap，commit
  a3598aa6），**不可作为默认发布**。**结论**：BFS「最近汇合」follow 语义是整条
  下游（`classify_loop`、`extract_compound_do_while`、`convert` 的
  break/continue/标签归约）赖以成立的承重假设；真后支配 follow 无法增量并入，
  混合方案能让 features 绿却过不了全量冒烟（慢 + 残余发散）。彻底修复必须把
  `walk` + `convert` + 循环分类一起按 SESE/支配树区域分解
  **从零重写**成对任意合法 follow 都单调收敛的结构（非补丁、非门控混合），工作量
  与回归风险都很大，属跨会话专项。当前 master **保留近似 + 记录为限制**：
  `Integer.toString` 冗余但可编译；`IntegerCache`/`StringUTF16` 仍为 jdk17/21
  阻塞。已验证稳定基线在 master（代码 commit b5d0a7f）。

### SESE 从零重写进展（`rewrite-sese` 分支，`JCDC_SESE` 门控，默认关）

按上述结论，已把结构化器按 SESE/支配树区域分解**从零重写**为
`crates/decompiler/src/sese.rs`（每块经 `consumed` 集 + `reachable_within`
恰好结构化一次；真后支配 follow；自然循环来自回边）。里程碑 3 的三个提交：

- **5e336542** 异常边循环成员：try-in-loop 的 handler 回边经异常边纳入循环
  成员（`exc_preds`），成员回溯止于 header，body 递归期同步 `loops_stack`
  → 修复 `SecureRandom.getInstanceStrong`（try 不再被甩出循环）。
- **f305b23c** 共享尾 follow：`convergent_merge`（从所有分支/case 目标
  **前向**可达、不在 stop、未 consumed 的最近块）在 ipdom=None 时作 follow；
  前向可达**不穿越** `loop_stack` 中的 header（仅经回边/下一轮迭代可达的合流
  不算）→ 修复 `Legacy6`（`if(a==2&&b==2)break outer` 的共享尾）、`EnumSwitch`
  （循环内 switch 的共享 `++i` 尾）、`ControlFlow.nestedLoops`（不误造跨
  `continue` 的 follow）。`stop-entry-Goto`：区域 ENTRY 即 stop 块时发
  `Goto{entry}`→break/continue，而非空分支丢失出口。
- **108bda02** try-finally 尾 return：try body 经内联/复制的 finally 副本到达
  尾 return，`reachable_within`（仅常规 succ）会漏掉它 → 放宽 loop-top break
  与 try 后 `next`，结构化未 consumed、在 universe、非 stop 的前向尾块
  → 修复 `Exceptions.nestedTry`（finally 后的 `return sb.toString()`）。

- **step 4（cf17817a）循环成员/出口三分离 + 支配守卫**：
  ① 成员收集只认**真回边**（`u→h` 且 h 支配 u；此前任何入边都算，
  `Integer.toString` 的 pre-loop 守卫块 blk10→header 把整个外围链吞进成员集）；
  ② `exits`（全成员出边）只用于 **break 归约**（resolve_goto 找最外层含目标
  的循环 → 带标签 break），循环后续用 **natural_follow（header 自身出口）**
  ——此前 `exits.first()` 可能是 body 内 if 跳去的远处 early-return，续走检查
  失败静默丢尾（Integer post-while 尾丢失的真正根因）；do-while（底测环，
  header 无外出边）回退到全成员出口；③ convergent_merge 拒绝**真支配另一
  目标**的候选（祖先汇合=fixup 块，`if(A||B) fixup;` 形态保持 follow=None →
  分支自然走 + copy_walk 复制，与 walk 同形）。
- **step 5（22fa2570）cm 守卫补全 + 纯 continue 分支 + 自 break 丢弃**：
  ④ cm 再拒「自身是分支目标且被**兄弟目标**严格支配」的候选（fixup 支配
  subtree 头：选头会孤立 fixup → `radix=10` 前多出无条件 subtree）；
  ⑤ `reaches_within` 不穿越 stop 块，且**起点在 stop 中的分支视为离开区域**
  （C2 经 fixup-stop 一跳"到达"subtree 的伪汇合）；⑥ consumed 检查里指向
  循环 header 的 Goto **无条件发射**（此前 parts 为空时塌缩成 Empty ——
  `StringUTF16.codePointCount` 两个 `continue` 全丢、循环尾无条件执行）；
  ⑦ convert：`extract_compound_do_while` 提出的 exit 若是循环**自身无名
  break** 则丢弃（do-while 条件假已出口，环外重发 break 是游离语句/编译错；
  walk 与 SESE 同享此修复）。
- **step 6（sibling-target 优先）多块条件链**：jdk8 `Random.internalNextInt`
  （fix-⑥ 目标）在 SESE 回退——旋转自环 header（body+c1 融合、自回边）+
  第二测试块 c2 构成多块条件链；两个 cond 的 cm 候选都被支配守卫（各自
  正确地）拒绝 → follow=None → 测试嵌套成 If → `extract_trailing_do_while`
  在内层 if/else 上误触发 → 环外游离 `break`/`continue` + 丢 `return r`。
  修复：cm 在通用扫描前**优先兄弟分支目标**——若某 target 被其余所有
  target 前向可达，它就是条件链的下一测试块（H1 分支的汇合就是 H2 本身），
  选它把循环体摊平成 `if(c1)continue; if(c2)continue; else exit;` ——恰是
  `extract_compound_do_while`/CLASSIFY2 折叠消费的形状（walk 侧机器无需改）。
  Legacy6 不受影响（其 fall 目标即共享尾，兄弟可达它 → 兄弟不是汇合）。
  `internalNextInt` 现与 walk **逐字节一致**（do-while 折叠 `||` 条件 + return）。

**当前 SESE 状态（step 5 后）**：features **全 release 全绿**（r8/9/11/17/21/26，
56/56，SESE 与 walk 双路都绿）；cargo test 39 绿；`Integer.toString(int,radix)`
达 walk 形态（else-if 链 + 单 `radix=10` + 完整复制子树，全路径 return，语义
精确；3 份复制 vs walk 2 份——按平价标准可接受）；`codePointCount` 三份复制
均保留 `continue`；`doWhile`/`Legacy6`/`nestedLoops`/`EnumSwitch` 与 walk 同形；
`internalNextLong` = walk 减两处冗余 return；jdk8 `internalNextInt` 与 walk
逐字节一致（step 6）；`SecureRandom` try-in-loop 正确。
**corpus 定点：SESE 修复了三个 walk 基线阻塞**——jdk26 `Class.toGenericString`
（游离 break → 干净 do-while）、jdk11/17 `Integer$IntegerCache`（walk 无条件
分配语义错 → SESE archived 分支 `return;`（static-init 内合法）跳过分配，
每路径恰好一次 final 赋值，可编译且语义精确）、`StringUTF16.codePointCount`
（walk 语义对，SESE 曾丢 continue，现修复）。

**final 字段共享尾复制家族——已修复（aa6ab069，walk/SESE 双路共享）**：
`inline_terminator`/RawGoto `term_copy` 会把共享 return/throw 尾块的语句复制到
每个到达点（对纯 return 正确：`if (t || explode()) return 1;` 两支都保留
return 1）。但尾块若先给 **final 字段**赋值再 return（`sun.security.util.Debug`
`<clinit>`：`hexDigits = ...toCharArray(); return;` 是三个分支的汇合），复制即
final 二次赋值 → javac「可能已被赋值」编译错（walk 2 份 / SESE 3 份，长期共同
阻塞）。修复：把本类 final 字段名集合（`pc.cf.fields` access flags）传入
Converter，`stmts_write_final()` 命中时禁止内联/复制 → Goto 走 resolve_goto
按自然流省略，尾块只结构化一次。验证：Debug `hexDigits =` 双路各 1 次；
IntegerCache(jdk8) `cache =` 1 次；jdk8+jdk26 `Integer.toString` 完整 walk 形态；
features 56/56 双路绿；cargo test 绿。仍共同阻塞：`List.sort` 裸 cast
（root cause D，泛型还原，与结构化器无关）、RawGoto 未定义标签家族
（walk 60 / SESE 43，见上文量化；`Pattern.clazz` 环体中部 hub 为不可约形状）。

**后续三个双路共享修复（corpus 家族级重编译暴露，walk/SESE 同受益）**：
- **a9eceec7 anon-inline walker 覆盖缺口**：`walk_stmt_anon` 的 `_ => {}`
  静默跳过 `Stmt::Labeled` 体与 Assert/TernaryValue/MonitorEnter/Exit 表达式
  ——标签块内的匿名类 `new` 永不内联，印成非法的 `new Outer.1(args)`/
  `new 3(args)`（jdk9+ `URLClassPath` 家族，**阻塞所有 jdk11/17 corpus 家族
  批量重编译**，双路同坏）。修复后 URLClassPath 全类零 raw-digit-new。
- **diamond fold root 豁免**（method.rs `try_diamond_fold` clean 守卫）：
  折叠此前要求整个区域无任何被引用赋值——**包括 root 自身**；但两个
  结构化器的 fold-collapse 都会原地发射 root 的语句（`Basic{root}`），
  root 赋值从不丢失。过严守卫拒绝了所有「header 块兼做 setup 赋值」的
  clinit 钻石（`props=...; DEBUG = prop!=null`），回退到 stack-var：
  `int stack0; if(..)stack0=0 else stack0=1; DEBUG=stack0;`——int 赋给
  boolean 字段（不可编译）+ 错误结构化的 `||` 链恒存 1（语义错）。
  修复后 rt.jar 含 int/long stack-var 声明的文件 **587 → 25（-96%）**，
  URLClassPath clinit 折叠为精确布尔表达式。
- **c0d59f87 不可达共享尾修剪**：`stmt_terminates` 不识别 JLS 14.21 无限
  循环（无 break 的 `while(true)`/`do..while(true)`/`for(;;)`），共享
  return 尾被复制进各分支后，原尾留在「两支皆 return/永旋」的 if/else
  之后 → javac「无法访问的语句」（jdk11/26 `String.split` 家族，双路同坏）。
  补 While/DoWhile/For 臂（字面 true 条件 + 保守 contains_break 检查）。
  String.java/URLClassPath.java 现通过家族重编译；剩余闭包错误为泛型/
  捕获（Class.java 三元 cast、WeakHashMap CAP#1、ObjectInputStream
  Enum.valueOf——root cause D 同族）与常量定型（Unsafe boolean→byte、
  JarFile ctor int 参数）、重载消歧（ObjectInputFilter doPrivileged）。

**SESE 侧 try-in-switch 修复（c39a3f06）**：SESE 调 `structure_switch`/
`copy_walk` 时 active 传空——保护段完全落在 switch case 内部的 try 组
永远无法在 case walk 里触发（walk 的组检查只匹配 active 表），case 被裸
结构化、handler 被孤儿化：jdk17 `URL$DefaultFactory.createURLStreamHandler`
的反射 try 丢失 → 「未报告的异常错误」（SESE 侧 jdk11/17 corpus 家族阻塞，
`Provider.java` 同因）。修复：按 walk 同款过滤器构造 `top_groups` 并传入
两个子构建器。已验证输出与 walk 同形（try/catch 完整）。

**泛型/lambda 两共享修复（classdec/emit，双路受益）**：
① 泛型返回方法的**擦除 cast 剥离**：Signature 返回为泛型（`T[]` 等）时，
bytecode checkcast 到擦除类型的 cast 在 return 位置是非法源文（Object[]
不能转 T[]）；当内层表达式已携带泛型源类型（G 型局部/字段/调用、泛型调用、
泛型数组上的 `clone()`——由 return 目标定型的 poly 表达式）则剥掉 cast。
`Class.getEnumConstants` 现与 JDK 源码逐字一致。② **lambda SAM 参数对齐**：
impl 方法签名 =（captures..., SAM 参数...），旧对齐只接受等长（无捕获），
任何带捕获的 lambda 印成 `(x0,x1) -> {..k..v..}`（未定义符号；
`ConcurrentMap.replaceAll`）。改取 impl 参数名的**尾部 SAM 切片**。

**corpus 家族级现状（jdk11 Provider 家族 4309 类闭包重编译）**：上述修复
逐个消除了 URLClassPath(anon)/String.split(unreachable)/Unsafe(bool2byte)/
Debug(final)/Class.getEnumConstants/ObjectInputStream.valueOf/
WeakHashMap.CAP#1/ConcurrentMap.replaceAll 各层错误；剩余 ~100 错误散布
~10 文件（ClassSpecializer 匿名派生类名 `Factory$1Var` 引用无声明、
Enum.getDeclaringClass 泛型三元 witness、ObjectInputFilter doPrivileged
重载歧义、FileSystem/Module/Package 等待逐个归因）——多家族长尾，属跨会话
专项（root cause D 亲族），walk/SESE 共同。

**clinit/嵌套类家族四连修（classdec/emit/method，双路共享）**：
- **hoist_clinit_returns**：static 初始化器里的裸 `return;` 是编译错
  （「返回外部方法」），但反编译 clinit 遍地都是——共享尾 RETURN 被复制进
  各分支 + javac 旋转断言脱糖（`if(AD) return; else if(c) return; else
  throw;`）用 return 表达「跳过剩余初始化」。原 strip 只剥块尾 return。
  新 pass：先在**原始树**上剪除 definite-exit 语句后的死代码（重复的共享
  尾，否则 final 字段二次赋值），再**先改写后递归**：含裸 return 的语句
  若有后继，退出分支剥掉 return（rest 不进入），落空分支/缺失 else 接收
  rest。`Integer$IntegerCache` clinit 现与源码语义精确一致（archived 分支
  恰好一次 final 赋值并跳过分配；null/oversize 路径各持一份分配副本），
  **jdk17/21 IntegerCache 基线阻塞修复**；Integer.java 家族 0 错误。
- **局部类 `$NName` 分类**：数字开头的嵌套简名此前一律按匿名类内联；但
  javac 把方法内**局部类**编码为 `Outer$1Name`（数字+标识符）——有名字、
  被签名/强转/泛型引用。改为：纯数字=匿名（new 处内联）；数字+标识符=
  Local（剥前缀，在使用点声明 `class Name`）；printer shorten 同步输出
  剥前缀简名（原来印 `ClassSpecializer$Factory$1Var` 二进制名→找不到符号；
  现 38 处引用→0，该文件错误 ~50→~19）。
- **内部类断言字段**：javac 给非静态内部类也合成 static final
  `$assertionsDisabled`，但 16 前源级禁止内部类静态成员（「内部类中的静态
  声明非法」）；有 this$0 的类改发实例 final 字段。
- **泛型返回 witness**（witness_generic_returns）：Signature 返回含类型
  变量而 return 表达式是通配参数化（`Class<?>`）或裸擦除时，包一层
  `(Class<E>)` 非受检 cast——`Enum.getDeclaringClass` 的 poly 三元 javac
  直接拒绝（bytecode 无 checkcast 可依）。

**剩余 corpus 闭包长尾**（jdk11 Provider 家族为样本，双路共同，多为
root cause D 亲族，待后续专项）：ClassSpecializer `Var` 构造器签名/初始化
自引用（~19）、ForkJoinTask VarHandle 签名多态在大 patch 下退化（9，单文件
+srcroot 可编译、全家族失败——疑似依赖类错误降级符号所致）、BoundMethodHandle
valueOf 泛型（8）、Spliterator tryAdvance 重载歧义（6）、WeakHashMap/
ConcurrentHashMap CAP#1 捕获转换（7）、URI int→boolean（2）、
ObjectInputFilter doPrivileged 歧义、Module$1DummyModuleInfo 命名。

**step 6 后全量冒烟**：rt.jar 12608 文件 / 0 panic / 0 error / 0 hang /
exit=0，888s（~14.8min，约为 walk ~10min 的 1.5×；step 4/5 的守卫剪枝使
其比 step 3 时的 ~19min 更快）。**最终二进制（aa6ab069）双路冒烟**：
SESE 12608/0/0/exit=0/1029s，walk 12608/0/0/exit=0/1031s——同机同负载下
两路等速（此前 1.5× 差值主要为机器负载噪声）；Debug `hexDigits` 双路
冒烟产物各恰 1 次赋值；未定义标签计数不变（walk 60 / SESE 43，见下）。

**未定义标签家族的量化**（新证据，walk/SESE 全量对比，精确正则扫描
`break L<n>`/`continue L<n>` 无对应 `L<n>:` 定义）：walk **60** 个文件、
SESE **43** 个、共同 26、walk-only 34（SESE 修复）、SESE-only 17。根源是
RawGoto 兜底：`resolve_goto` 无法把跳转归约为 break/continue/fallthrough
时 printer 把 `Stmt::Goto(blockid)` 印成 `break L<blockid>`，而标签从未
发射（pending_labels 死代码）。典型：`Pattern.clazz` 的**环体中部汇合块**
（所有 case-break 与自环出口汇入 blk39，其流经增量块回到环顶）——jump
目标既非 header（非 continue）也不在 exits（非 break）→ RawGoto；walk
（break L37）与 SESE（break L39）**同样失败**，属两结构化器共同的
「非结构化跳转」深水区家族；冒烟只测 jcdc 自身错误，不测可重编译性，
故该家族此前从未被量化。SESE 净值更优（43<60），翻转门槛不含此项，
但两路都值得后续专项（复活标签发射或 hub 区域化）。

**门控状态**：里程碑 3 全部完成——① try-in-loop 异常边；② finally/TWR 平价；
③ 共享尾复合-if（Integer.toString walk 平价 + IntegerCache 语义修复 +
internalNextInt walk 逐字节一致）。SESE 现「不劣于 walk 且修复三个 corpus
定点阻塞（toGenericString/IntegerCache/codePointCount）」；剩余共同阻塞
（Debug final-copy、List.sort 泛型 root cause D）非 SESE 特有。翻转默认为
SESE 的剩余门槛：corpus **家族级重编译**证据（进行中，releases 11/17/26）
与冒烟速度取舍（1.5× walk）。




- **泛型方法实参的捕获/裸类型还原**（jdk11 `List.sort`）：原始
  `Arrays.sort(a, (Comparator) c)` 的裸 cast 被 javac 擦除（bytecode 无
  checkcast），反编译丢失该 cast，重编译时 `Comparator<? super E>` 无法匹配
  泛型 `Arrays.<T>sort(T[],Comparator<? super T>)` 而报 CAP#1。完整修复需
  泛型方法签名解析 + 捕获转换判定（裸 cast 何时必需），属泛型还原深水区。
- **共享尾复制致 final 二次赋值**（jdk9 `sun.security.util.Debug`）：方法尾
  赋值被复制进某分支，final 字段 `hexDigits` 出现两处赋值。
- **循环重结构化残留游离 `break`**（jdk26 `Class.toGenericString`）：原
  `while(component.isArray())` 被并入 if/else，else 分支尾留一个不在任何
  loop/switch 内的 `break`。

这些同属「条件/循环/switch 的共享尾与 follow 结构化」「泛型还原」两类深水
区，是下一步收敛方向；**features 语义套件不受影响（全 release 全绿）**，
冒烟（rt.jar 全量）零 panic/零挂死。


## 调试开关

| 环境变量 | 作用 |
|---|---|
| `JCDC_PRINT=<m[#n]>` | 打印指定方法反编译源码 |
| `JCDC_PRINT_TREE=1` | 打印 Stmt 树 |
| `JCDC_DBG_IF=1` | 条件/跟随块结构化跟踪 |
| `JCDC_DBG_LOOP=1` | 循环成员/分类跟踪 |
| `JCDC_DBG_MERGE=1` | 定点 merge 变量类型跟踪 |
| `JCDC_DBG_GOTO=1` | Goto 消解跟踪 |
| `JCDC_DBG_TWR=1` | TWR J7 匹配跟踪 |
| `JCDC_DBG_ANON=1` | 匿名类内联跟踪 |
| `JCDC_DBG_HOIST=1` | 声明提升跟踪 |
| `JCDC_DBG_BLOCKS=1` | 基本块构建/转换跟踪 |


## 2026-09-06 晚：家族普查驱动的长尾收敛（rewrite-sese 98f8f296..HEAD，21+ 修复提交）

方法论（本轮引擎，已验证高效）：
1. **家族普查**：单源文件 `javac --release N --patch-module java.base=srcroot -d orig`
   （隐式编译拉全闭包）→ `jcdc -cp jdk8-rt.jar orig -o dec` → 全量重编译
   **必须 `-Xmaxerrs 10000`**（默认 100 上限会掩盖分布）。基线→现状：
   jdk11 ForkJoinTask 闭包 1111→338；jdk17 SunJCE 闭包 1020→374；
   jdk26 WeakHashMap 闭包 1759→974。
2. **corpus 首阻塞迭代**：`verify.py corpus --jdks 11,17,26 --limit 10` 每路
   约 6 分钟（并非小时级）；每 JDK 的 10 个家族共享同一首阻塞文件（javac
   全或无 + 相同 java/util 闭包）。修一个→重跑→下一层。层级推进：
   vJ Hashtable/WeakHashMap-nonsealed → vK Collections 通配 cast 语法 →
   vL Hashtable Entry<> diamond → vN LinkedHashMap this$0 / String ctor 折叠 /
   Collection T[] → vP Set.copyOf 擦除 cast / HashIterator arg0 →
   vQ ClassValue diamond / ObjectInputFilter lambda 捕获 →
   vS System PrintStream bool / Enum arg0 → vU ObjectStreamClass 标签 /
   FilterOutputStream 重复 catch → vV/vW Long-Integer clinit final 双赋值。
   SESE 每一层都严格不劣于 walk（相同或更晚的首阻塞）。

本轮修复族（详见各提交信息）：JVMS 2.9 签名多态 cast（闭集名单，非 pool
注解——corpus -cp 是 jdk8 rt.jar 无 VarHandle）；泛型 new 的 diamond 还原
（cast 下丢弃合成泛型 cast、通配实参退 raw）；non-sealed 仅直接超类；
typevar/三元返回见证；SESE 逃逸分支共享终结符 follow 拒绝 + 显式 goto 入
stop 的发射；限定 this 两段名（防继承成员类型遮蔽）；局部类声明提升至方法
顶块（捕获定义后/首引用前；lambda 体内局部类经 EXTERN_DECL 于 pass 期抽取
到外层，方法级作用域快照恢复）；局部类真实构造器（合成捕获参数按字节码
putfield 隐藏；Signature 省略前导 this$0 与**尾部 val$** 的对齐重建）；
char/boolean 字面量渲染（ret_char/ret_byte/ret_short、NewArray 元素类型、
booleanize 窄化常量）；TWR 资源护栏（体内再赋值/null 初始化拒绝）；
构造器委托折叠（裸赋值叶子/块包 if 链/尾部兜底 this(...)）；泛型方法实参
raw-cast 见证（仅通配参数化实参）；歧义重载 lambda 实参 raw SAM cast
（doPrivileged）；见证类型参数界违反拒绝（Collections.min）；擦除 cast
剥除仅限内层擦除相等（Set.copyOf 真实下转保留）；walk_stmt_subst 补
Labeled/Assert/TernaryValue/Monitor 覆盖；成员类字段初始化经构造器 putfield
映射捕获参数（arg0 家族归零，含槽位级 outer-param 重写）；clinit 调用见证
（doPrivileged in clinit）；lambda SAM bool/char 返回渲染；clinit 跳过返回
保护（strip 仅顶层，hoist 依赖分支内 return 标记——Long/Integer cache 双
赋值修复）；共享 final 终结符复制恢复（副本各带 return，路径不相交）；
live_merge follow 回收（≥2 活分支、目标优先、兄弟完成度过滤——switch-in-loop
增量块 follow、ObjectStreamClass case 边界与 break 还原）。

**剩余深水区**（已归档，跨会话专项）：
- varalloc 槽位合并错型：ResourceBundle 字符串 switch 临时变量与 Iterator
  槽位冲突（16）、Calendar catch 参数并入 switch 赋值变量（11）、
  ProxyGenerator foreach 降级临时变量类型错（13）、CharPredicates
  stackNNN 泄露为 `Object 不是函数接口`（jdk17，21）、AnnotationReader
  stackNNN 数组存储泄露（jdk26，42）。
- SESE try-in-loop 拷贝：getInheritableMethod 循环展平、catch 内复制丢失
  try 包装（copy_walk active-groups 扩展已写入待验证）；FilterOutputStream
  旧式 suppressed 模式重复 catch(Throwable)（多范围异常表重建）。
- Pattern 丢外层 for(;;)（switch 环游 hub，7 处未定义标签）。
- 泛型尾：无法转换 ~130（root cause D 残余）、Gatherers Downstream CAP
  方法引用、ReferencePipeline StatelessOp `this,this` 重复实参（pre-existing）。

## 2026-09-07 凌晨：普查驱动的第二轮收敛（rewrite-sese，46+ 修复提交）

普查轨迹（SESE 路，`/tmp/census_run.sh`，错误=可编译性）：
jdk11 352→236，jdk17 398→271，jdk26 929→468→(pattern-break 待测)。
features 56/56 双路 + cargo test 39/39 每次提交后全绿。

本轮修复家族（详见各 commit message）：
- **qualified-new via-super**：jdk21+ javac 不再给仅转发 outer 的内部类生成
  this$0 字段（WeakHashMap 三个 iterator），emit 的 is_member_inner 改为
  字段检查 + outer_param_via_super 检查，调用点还原 `Outer.this.new Inner()`。
- **SESE absorbed-tail**：structure_try 吸收的组尾 areturn 不得再被 after-try
  延续搜索选中复制（ObjectStreamClass.getDeclaredSUID 重复 return；顺带治愈
  FilterOutputStream.close 重复 catch）。
- **finally dedupe 增强**：trailing_rethrow_var 识别分支化 rethrow
  （if/else 双支 throw 同一变量）；内联副本比较用 alpha 归一化（变量 id 按
  遍历序重映射 + 去掉无值尾 return/throw）——FilterOutputStream.close 还原
  真 finally。
- **loop-wins-over-group**：块既是循环头又是 try 组起点且回边在保护区外时
  先结构循环（ClassValue.getFromHashMap `for(;;){try}catch retry`——SESE
  3 倍展开/walk 静默丢环，缺返回语句）。
- **switch follow 放宽**：循环头在 walk 位于该循环之外时可作分支/switch
  follow（loop_stack 守卫替代 loop_headers 守卫——Subject.populateSet 循环
  被复制进每个 case）；copied 区域新增 switch_stop_confluence（全体活 case
  共同逃逸的 stop 块作 break 解析锚点——Calendar catch 副本 case 贯穿）。
- **witness/推断家族**：witness_generic_returns 跳过 lambda 臂（多义条件
  standalone 化非法）、同擦除异参数化、子类擦除（super+interface 链）、
  已带显式 type_args 的调用；gate 放宽至任意参数化返回；泛型调用返回位置
  永不加擦除 cast（cast 语境饿死推断——Gatherer.finisher），优先显式
  witness，失败时按目标形态选择裸调用（参数化类返回）或 typevar cast
  （ArrayList.toArray `(T[]) copyOf`）；带 diamond new 实参的调用保持裸式
  （Stream.toList）；field-init 合成 cast 跳过泛型调用初始化器
  （ProtectionDomain cache——cast 冻结外层调用、内层 diamond 推成
  <Object,Object> 后 cast 不可转换）；throw 位置 checkcast 擦除重定型为
  throws 类型变量 + 裸 throw 合成 `(T) t`（Optional.orElseThrow /
  ForkJoinTask.uncheckedThrow）。
- **varalloc 家族**：gap 收集仅 STORE 前向归因（LOAD 读的是更早的 gap
  临时值——ForkJoinTask.exec `return rex`）；LVT 同名同描述符但 LVTT 签名
  不同的区段不合并（Subject pI Iterator<Principal>/<Object>）；同名区段
  跨活性间隙不合并（ResourceBundle 字符串 switch int 索引被并进 String v）；
  combine_types 具体类型 join 出的 plain-Object LUB 具粘性（不再被后续
  KeyStore 证据"恢复"）；split_walk 记录谱系具体类型，unknown→concrete
  且曾携带不同具体类型时分裂，并把分裂前变量窄化为首个具体类型
  （KeyStore var6_80 Iterator/KeyStore 双谱系各自成型）。
- **booleanize**：int 形参位/数组维度/数组下标保持 int 形态
  （`out.write(v ? 1 : 0)`）；数值父下多义臂 boolify 后重包裹 `? 1 : 0`
  （Invokers INARG_LIMIT）；int 数组存 boolean 由 cast_generic_locals 重
  包裹（Calendar.readObject）。
- **builder dup-mark**：plain dup 的幸存原件被 store 消费时内联为
  `x = e` 赋值表达式——仅限参数槽（LambdaForm Name ctor `this(.., arguments
  = copyOf(..))` 灵活构造器）；局部槽内联会重塑条件表达式、破坏下游折叠
  （+850 回归，已用参数守卫回退）。dup 幸存件上的 requireNonNull+pop 是
  javac 隐式空检查，不成语句（ClassSpecializer Var ctor super 前 this 引用）。
  标记为逐块 thread-local，所有 pop 点清理（陈旧标记曾大面积误伤）。
- **局部类**：anon 体内声明拼接在方法顶块（ANON_TOP_BLOCK 认领——
  ClassSpecializer Factory$1$1Var 先用后宣）；class-literal 引用触发声明
  发射且计入先用后宣重排（Module.DummyModuleInfo）；record 保留 implements
  （CleanupAction implements Runnable）；this(..) 委托构造器不再被当作
  canonical 跳过（VMStorage 3 参构造器）；enum values/valueOf 按描述符
  过滤（Tag.valueOf(byte) 保留）；enum 常量同元数构造器按实参兼容性打分
  （KnownOIDs (String,String,boolean) 不被 varargs 遮蔽）。
- **其他**：匿名类 new 位丢弃未存储的首位 outer 参数（jdk21+ ctor
  requireNonNull+pop 无 this$0 字段）；捕获局部变量的提升声明省略
  `= null`（仅限 anon-ctor-arg 捕获；lambda 捕获走快照通道需要默认值保
  定值赋值——ObjectInputFilter patternFilter3 反例）；catch 变量重写以
  首次槽位再赋值为界（Calendar createCalendar 共享尾部被染成异常变量）；
  assert 条件经 expr_bool 发射（assert 0 → assert false）；byte/short/char
  目标的 int 条件式补窄化 cast（MemberName 常量变量内联后失去 byte 性）；
  varargs 展开的窄数组常量按分量类型重 cast（PKCS9Attribute (byte) 22）；
  typeSwitch（模式 switch）恢复时为每个带标签 case 与 default 补 break
  （模式贯穿非法）。

**回归教训**（两次被普查当场抓获）：cast 到参数化目标会冻结泛型调用推断
（HashMap.newHashMap → Map<Object,Object> 不可转换——19 错）；局部槽
dup 内联重塑条件破坏循环折叠（+850 错）。守则：改发射/推断策略必须跑
三 JDK 普查对比，必要时 prev-commit dec 树重编译做逐文件错误差分。

**剩余深水区**：找不到符号（jdk26 Gatherers/ClassPrinterImpl——泛型尾）、
Object 非函数接口 27（`stackN = sink::accept` 方法引用落入 Object 栈合并
变量，需按使用点函数接口定型）、CHM comparableClassFor 共享尾 return null
被复制进循环条件（预先存在的 foreach+共享终结符 bug）、jdk11 局部类构造器
参数名 arg4/LVT 脱节（ClassSpecializer$Factory$1Var prev）、Pattern 丢
for(;;) 悬空标签、AnnotationReader stackNNN、Gatherers Downstream CAP。

### 2026-09-07 深夜下半场（局部类机器大修，普查 223/231/413 → 158/169/244 附近）

引擎不变：三 JDK 家族普查 → 修最大错误家族 → features 56/56 双路 + cargo
test 39/39 → 提交 → 重跑普查。本段共 17 个 fix commit，全部围绕"局部类/
匿名类发射机器"与"擦除 cast 毒性"两条主线：

1. **兄弟局部类声明丢失**：emit_local_class_decl 排空 ANON_HOIST 中同
   EnclosingMethod 的声明并置于自身之前（Gatherers.mapConcurrent 的
   MapConcurrentTask 只被 State 体内引用，原先彻底丢失，19 错）；插入位
   扫描同时看 ClassDecl 文本提及（局部类作用域自声明起）。
2. **多站点声明重定位**：EXTERN_REDECL 记录第二次提及，fix_lambda_captures
   尾部把声明移到方法顶（Composite.impl State 被 SESE 复制尾在 if 链后再次
   引用——声明困在分支里）；位置计算用 captures 定义锚点（PairBox：声明必
   须在 c1Supplier.. 定义之后）；local_class_captures 对同名兄弟取并集
   （Gatherers 有四个 State）。
3. **同 arity 构造器选择**：analyze_anon_ctor 在多个同参数构造器中选"直接
   存 capture"的那个；委托构造器跟随 this(..) 链收割 capture，pure-forward
   门（声明参数兼作 capture 源时保留在 kept args）；prune_local_ctor_
   delegation 按目标构造器被剥离的 capture 位剪委托实参；ctor_capture_
   params 同样跟随委托（打印签名与调用点保持一致）。
4. **局部 record**：类 Signature 存在时渲染 `record Name<TP>(components)
   implements ..`（sig_header 的 `extends Record` 非法；组件未声明；new 站
   点撞 0 参构造器——classfile Util 三个 record 全灭 10→4）。
5. **Holder 型局部类**：仅被静态成员访问提及（Holder.INSTANCE）也发射声
   明；16+ 类文件的局部类 <clinit> 以 static 块发射。
6. **assert 字段三联**：$assertionsDisabled 在匿名/局部体内保留为实例
   final 字段；顶层类在常量池引用合成兄弟 holder（接口 ConstantGroup$1）
   时自declare；引用一律裸名（Object. 前缀的 holder 引用不可解析）。
7. **nest-based this$0**：无字段的内部类 outer_this_map 合成 this$0→
   Outer.this 映射（CallArranger/COWArrayList）；lambda impl 体补 outer-
   this 替换（ProxyGenerator 13 错）。
8. **分支复制捕获**：capture 定义只存在于复制尾分支时，提升为块首 blank
   声明+分支内赋值，类声明落在首个提及前（DoublePipeline FlatMap/fastPath
   12 错）；重定位对已存在声明幂等。
9. **擦除 cast 毒性**：raw-cast witness 仅在其它实参以具体类型钉住共享推
   断变量时发射（Arrays.sort(a,c) 保留 (Comparator) c；toMap(keyMapper,
   valueMapper) 裸传保推断链）；strip_selftype_checkcasts 丢弃自类型泛型
   返回（BaseStream.onClose():S）后的 checkcast Owner——裸 cast 会毒化整
   条泛型链（Files.find 的 entry→Object）。
10. **嵌套匿名外层成员**：render_captures 的 this$N→Raw("this") 改为不可
    见标记（打印为无主名——词法解析到外层匿名成员；实参位保留 this）
    （KeyStore Builder getCalled/oldException 11 错）。
11. **窄类型渲染**：char/boolean/byte/short 目标的 plain 赋值按目标渲染
    （xml Parser mESt char 状态机 15×2 错）；局部类 new 站点经
    LOCAL_CLASS_INTERNALS 查内部名走 typed ctor args（Qchar 39→'\''）；
    boolean==int 栈合并等式以 !=0 归一（VirtualThread assert）；方法返回
    位 lambda 按签名 ret 补 SAM 返回 witness（castingIdentity (R) i）。
12. **合并 new 初始化**：非构造器方法里经栈合并变量到达的 invokespecial
    <init> 在 INIT 位折叠（死 raw 孪生赋值删除、孪生变量改指已初始化对
    象）——InflaterInputStream `super(stack233)` 变回 throw new
    ZipException(msg)（显式构造器位置家族，-33）。
13. **静态上下文类型变量 cast 禁令**：static 方法/clinit 内禁止引用类级
    类型变量的参数 cast（未替换的字段签名参数化泄漏 (ReferenceKey<K>)）。
14. **ClassReader 重名变量**：disambiguate_nested_locals 的重命名候选避
    开"任何变量曾占用过的名字"（vt 重命名是全局的，同名多站点声明会在
    仍然相互包围的作用域里撞车，asm ClassReader 12 错）。

**回归教训（新增两条）**：返回位 diamond 参数 cast 普查 +35（cast 冻结
推断的老病，已回滚，ReferencedKeyMap 由 raw-new+擦除 cast 路径治愈）；
声明重定位/hoist 必须幂等——匿名 walk 在一次发射里跑多遍，第二遍的
demote/hoist 会吃掉第一遍的 blank 声明。

**剩余深水区**（普查 ~571 后）：Gatherers type-args 恢复（Integrator.of
方法引用 witness、defaultFinisher 比较上下文 witness）、SESE 悬空标签/
外部中断/空 then 无条件 throw（语义）、FloatingDecimal !ssign!=45 布尔化
错树、匿名构造器内联 super() 形状（SplitConstantPool/ProcessBuilder）、
Optional.map 链 witness（ClassPrinterImpl）、Object 栈合并变量推断尾。
