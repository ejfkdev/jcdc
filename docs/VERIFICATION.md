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
