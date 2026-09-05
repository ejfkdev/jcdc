# jcdc 架构笔记：class → java 反编译器设计参考

> 研究对象：
> - **garlic**（C 实现，含 dalvik 复用层）：`/Users/e/Documents/github/java-decompile/garlic/src/`
>   - 核心目录：`jvm/`（JVM 字节码前端）、`decompiler/`（后端中立的 IR/CFG/表达式/输出）、`analyzer/`、`parser/class/`（class 文件解析）
> - **Vineflower**（Java 实现，Fernflower 的现代 fork）：`/Users/e/Documents/github/java-decompile/Vineflower/vineflower/src/org/jetbrains/java/decompiler/`
>   - 核心包：`main/`（驱动 + ClassWriter）、`main/rels/`（类级关系处理）、`struct/`（class 文件结构模型）、`code/` + `code/cfg/`（指令与 CFG）、`modules/decompiler/`（结构化 + 表达式 + 变量）、`modules/decompiler/exps|stats|sforms|vars|flow|decompose/`、`util/`（TextBuffer 等）
>
> 本文所有路径均相对上述两个根目录，引用格式 `包/文件:符号`。目标读者：准备用 Rust 从零实现 jcdc 的开发者。

---

## 0. 两种总体架构对比（先建立直觉）

| 维度 | Vineflower | garlic |
|---|---|---|
| 核心策略 | **结构化分析**：CFG → 递归域分解（dominator/postdominator）→ Statement 树 → 在 Statement 树上做表达式折叠与模式重写 | **指令级重写**：每条指令先生成一个表达式（大多是 `stackVar = rhs` 形式），再用几十个定点迭代 pass 折叠、内联、识别循环/分支，最后构建 node 树输出 |
| 中间表示 | `Exprent` 表达式树 + `Statement` 控制流树（两层） | 单一 `jd_exp` 表达式森林 + `jd_node` 语法树（表达式即语句） |
| 栈处理 | 在基本块内直接模拟栈（`ExprProcessor.processBlock`），跨块用"栈变量" `VarExprent(index≥10000)` + SSA 版本化，再内联 | 全程 worklist 栈模拟（`jvm_simulator.c`），每个栈值分配 `jd_var`（stack_var），指令翻译成对 stack_var 的赋值，再靠 `inline_variables` 系列 pass 消除 |
| 异常处理 | 先在 CFG 层清洗异常表（ExceptionDeobfuscator），finally 在结构化前用 `FinallyProcessor` 以**指令级比较**去复制 | 先建异常块 CFG，识别 handler 范围、扁平化、合并 try/catch/finally 范围，finally 复制用**指令序列反向比对** nop 掉（`jvm_exception.c:reverse_compare_instruction`） |
| 类型推断 | `VarTypeProcessor` + `VarDefinitionHelper.populateTypeBounds` + 各 Exprent 的 `getExprType/getInferredExprType/checkExprTypeBounds` 全链路 | 简单前向传播：`jvm_type_analyse.c`（int 隐藏类型 boolean/byte/char/short 修正）+ LVT/描述符 |
| 跨类信息 | `StructContext`（全局类池，含 library）支撑泛型推断、TWR、switch-on-enum、内部类 | 基本单类独立反编译；jar 级只处理 inner/anonymous 类归属（`jar/jar.c`），无父类成员解析 |
| 输出 | `TextBuffer`（带 token/字节码映射/换行组 reformat）+ `ImportCollector` + `ClassWriter` | 直接 `fprintf` 到 FILE（`expression_writter.c:writter_for_class`），import 用 trie 收集 |
| 可移植性 | 逻辑最全，但依赖大量 Java 生态习惯（ThreadLocal 上下文、VBStyleCollection） | 代码底层、无外部依赖，pass 顺序一目了然，最适合 Rust 移植时当"骨架" |

**给 jcdc 的总建议**：用 garlic 的"单遍管线 + 显式 pass 列表"作为骨架组织代码，用 Vineflower 的算法细节（域分解结构化、finally 指令比对、switch/enum/lambda/concat 模式、泛型与类型推断、TextBuffer/import 输出）填充每个 pass 的正确实现。

---

## 1. 整体管线

### 1.1 Vineflower 管线

入口链：`main/decompiler/ConsoleDecompiler.java`（CLI）→ `main/Fernflower.java` → `struct/StructContext` → `main/ClassesProcessor`。

```
Fernflower(saver, props, logger)
 ├─ StructContext(provider, saver, this)      # 收集所有输入空间(jar/dir/file)，懒加载 StructClass
 ├─ ClassesProcessor(structContext)
 ├─ DecompilerContext(properties, ...)        # ThreadLocal 全局上下文：importCollector/varProcessor/counter/structContext
 └─ (可选) IdentifierConverter.rename()       # 混淆重命名模式

Fernflower.decompileContext()
 └─ classProcessor.loadClasses(renamer)       # 阶段A：建 ClassNode 树
 └─ structContext.saveContext()               # 对每个 unit：processClass(cl) + getClassContent(cl) 写结果

阶段A：ClassesProcessor.loadClasses          (main/ClassesProcessor.java:92)
 输入：所有 own StructClass
 处理：
   1. 去重（同名类只保留第一个）
   2. 对每个类读 InnerClasses 属性 → mapInnerClasses: innerName → {simpleName, type(ANONYMOUS/LOCAL/MEMBER), accessFlags, enclosingName}
      - type 判定：simpleNameIdx==0 → ANONYMOUS；outerNameIdx==0 → LOCAL；否则 MEMBER；
        再用被嵌套类自己的 EnclosingMethod 属性修正（有 methodName → LOCAL）
   3. 非 inner 的类建 ClassNode(Type.ROOT)，存 mapRootClasses
   4. 从 ROOT 出发 DFS，把 InnerClasses 里记录的嵌套类挂到 node.nested（设置 simpleName/type/access；
      ANONYMOUS 时清 static、算 anonymousClassType=第一个接口或父类；LOCAL 时只保留 ABSTRACT|FINAL(16+ 再加 INTERFACE|ENUM)）
   5. isAnonymous() 校验：父类只能是 Object/单接口、外围类中对它的引用只能是一次 new（检查 checkcast/instanceof/getstatic 等指令）
 输出：ClassNode 森林（ROOT → nested MEMBER/LOCAL/ANONYMOUS）

阶段B：ClassesProcessor.processClass(cl)      (main/ClassesProcessor.java:442)
 输入：一个 ROOT StructClass
 处理（顺序重要）：
   1. new ImportCollector(root)；DecompilerContext.startClass(...)
   2. package-info / module-info 特判（不跑后续，输出时单独处理）
   3. new LambdaProcessor().processClass(root)          # 扫描 invokedynamic+LambdaMetafactory，为每个 lambda 建 ClassNode(Type.LAMBDA) 挂进 nested
   4. addClassNameToImport(root, importCollector)       # 内部类简单名注册为隐式 import
   5. initWrappers(root, spec)                          # 递归：先初始化"应提前"的嵌套类(合成 switchmap/$assertionsDisabled 容器类，见 shouldInitEarly)，
                                                        # 再 new ClassWrapper(node).init(spec)，最后其余 nested
   6. new NestedClassProcessor().processClass(root, root)  # 局部/匿名类：解析 this$0/外围变量捕获(见 §4.5)
   7. new NestedMemberAccess().propagateMemberAccess(root) # 消除 access$000 等合成桥接方法调用
 输出：每个 ClassNode 带 ClassWrapper（含所有 MethodWrapper{RootStatement root, VarProcessor}、字段初始化器表）

阶段C：ClassesProcessor.writeClass(cl, buffer) (main/ClassesProcessor.java:489)
   1. ClassWriter.writeClass(root, classBuffer, 0)   # 生成类体
   2. classBuffer.reformat()                          # 按 NewlineGroup 做超长行折行
   3. writer.writeClassHeader(cl, buffer, importCollector)  # package + import 前缀
   4. buffer.append(classBuffer)；字节码→源码行映射(BytecodeSourceMapper)
```

`ClassWrapper.init`（main/rels/ClassWrapper.java:52）＝**类级反编译主体**：对每个 `StructMethod`：
1. `MethodDescriptor.parseDescriptor` + `new VarProcessor(mt, md)`；
2. 若 `mt.containsCode()` → `MethodProcessor.codeToJava(classStruct, mt, md, varProc, spec)`（可带超时线程，超时 `Thread.stop`，失败记录 `decompileError` 并 dump dot）；否则只给参数排布变量名（this + 参数按 stackSize 占 slot）；
3. 产出 `MethodWrapper(root, varProc, mt, classStruct, counter)` 存入 `methods`（key = name+descriptor）；
4. 成功后：`varProc.refreshVarNames(字段名集合)`（避免变量名撞字段名），`USE_DEBUG_VAR_NAMES` 时用 LocalVariableTable 设置参数名。

**方法级管线 `MethodProcessor.codeToJava`**（main/rels/MethodProcessor.java:87）——全项目最核心函数，阶段如下（每步都记 `DecompileRecord` 便于调试 dump）：

```
1  mt.expandData(cl)                        # 懒解析 Code 属性 → FullInstructionSequence（指令列表+异常表）
2  graph = new ControlFlowGraph(seq)        # 基本块划分+连边+异常边+jsr子程序边 (§3a)
3  DeadCodeHelper.removeDeadBlocks(graph)
4  if version.hasJsr() || FORCE_JSR_INLINE: graph.inlineJsr(cl, mt)   # jsr/ret 内联展开(复制子程序块)
5  DeadCodeHelper.connectDummyExitBlock(graph); removeGotos(graph)
6  ExceptionDeobfuscator.removeCircularRanges / restorePopRanges / removeEmptyRanges
   DeadCodeHelper.extendSynchronizedRangeToMonitorexit (Kotlin/Scala 特例)
   DeadCodeHelper.incorporateValueReturns
   ExceptionDeobfuscator.insertEmptyExceptionHandlerBlocks
   DeadCodeHelper.mergeBasicBlocks           # 单前驱单后继且异常范围一致 → 合并 (§3a)
   if hasObfuscatedExceptions: handleMultipleEntryExceptionRanges + insertDummyExceptionHandlerBlocks
7  root = DomHelper.parseGraph(graph, mt, 0) # CFG → Statement 树（结构化，§3c）
8  FinallyProcessor 循环:
     while fProc.iterateGraph(cl, mt, root, graph):   # 找到一个 catch-all 是 finally → 验证复制体/插信号量 → 改 CFG
        root = DomHelper.parseGraph(graph, mt, ++n)    # 重新结构化
9  DomHelper.buildSynchronized(root)          # monitorenter + CatchAll(monitor exit) → SynchronizedStatement
   DomHelper.removeSynchronizedHandler(root)
10 SequenceHelper.condenseSequences(root)     # 压平嵌套 Sequence、删空语句
   ClearStructHelper.clearStatements(root)
11 ExprProcessor proc.processStatement(root, cl)   # 字节码 → Exprent（栈模拟，§3b）
   SequenceHelper.condenseSequences(root)
12 do { StackVarsProcessor.simplifyStackVars(root, mt, cl)   # SSA/SSAU 稀疏版本化 + 栈变量内联
        varProc.setVarVersions(root) } while (new PPandMMHelper(varProc).findPPandMM(root))  # ++/-- 识别
   PPandMMHelper.inlinePPIandMMIIf(root)
13 if version.hasIndyStringConcat(): ConcatenationHelper.simplifyStringConcat(root)   # §4.2
14 AssertProcessor.buildAssertions(root)      # §4.8
15 主循环 while(true)（任一 pass 返回 changed 就 continue 重来）:
     LabelHelper.cleanUpEdges(root)
     if hasLoops: 内层 merge 循环 {
        EliminateLoopsHelper.eliminateLoops      # 消除冗余嵌套循环(外层循环无用则解开)
        MergeHelper.enhanceLoops                 # INFINITE→WHILE→FOR_EACH/FOR；DO_WHILE (§3c)
        LoopExtractHelper.extractLoops           # 把循环里"仅执行一次的前置块"提出去 / 多入口循环整理
        IfHelper.mergeAllIfs                     # &&、||、else-if、三元、if 重排 (§3c)
     }
     StackVarsProcessor.simplifyStackVars; varProc.setVarVersions
     LabelHelper.identifyLabels(root)            # break/continue 边定级
     SecondaryFunctionsHelper.identifySecondaryFunctions  # 布尔化简(x==true)、位运算→算术等二级函数
     IntersectionCastProcessor.makeIntersectionCasts      # 接口交叉类型 cast
     if hasIfPatternMatching: IfPatternMatchProcessor.matchInstanceof  # instanceof 模式匹配 (16+)
     if hasSwitch: SwitchPatternMatchProcessor.processPatternMatching; SwitchExpressionHelper.processSwitchExpressions
     if hasTryCatch: TryHelper.enhanceTryStats(root, cl)  # try-with-resources + 合并相邻 try (§4.9)
     InlineSingleBlockHelper.inlineSingleBlocks
     if hasLoops: MergeHelper.makeDoWhileLoops / condenseInfiniteLoopsWithReturn
     if !isInitializer: ExitHelper.condenseExits(root)    # 多 return 收拢、if-return 化简
     else break
16 收尾（不再循环）:
   SwitchHelper.simplifySwitches(root, mt, root)   # switch-on-enum(switchmap 还原) + switch-on-string (§4.3/4.4)
   ExitHelper.adjustReturnType / removeRedundantReturns
   SecondaryFunctionsHelper.identifySecondaryFunctions（再跑一次）
   SynchronizedHelper.cleanSynchronizedVar / insertSink
   varProc.setVarDefinitions(root)                 # VarDefinitionHelper：变量声明位置/合并/命名 (§3e)
   SecondaryFunctionsHelper.updateAssignments
   LabelHelper.hideDefaultSwitchEdges; GenericsProcessor.qualifyChains; ExprProcessor.canonicalizeCasts
   LabelHelper.replaceContinueWithBreak(root)      # 必须最后：破坏 statement 结构一致性
   ExprProcessor.markExprOddities(root)            # 标记残留 monitor/unknown 变量 → 输出注释
17 mt.releaseResources(); return root
```

阶段D（回到 `ClassWriter.invokeProcessors`，main/ClassWriter.java:75）——**写出前的类级后处理**：
- 每个方法再跑一次 `SwitchHelper.simplifySwitches`（eclipse 风格 switchmap 需要整个类都反编译完）+ `IfHelper.prettifyIfs`；
- `InitializerProcessor.extractInitializers/hideInitalizers`：把 `<clinit>`/构造器里对字段的赋值抽成 `staticFieldInitializers`/`dynamicFieldInitializers`（字段声明处的 `= init`），并隐藏空构造器/空 super()；
- `ClassReference14Processor`（Java 1.4 的 `class$java$lang$String` 合成类还原为 `X.class`）；
- `EnumProcessor.clearEnum`：隐藏 `values()/valueOf(String)/$VALUES` 字段 + 构造器里的 `Enum.<init>(name, ordinal)` 调用（§4.4）；
- `RecordHelper.fixupCanonicalConstructor`（紧凑构造器识别）。

阶段E：`ClassWriter.writeClass(node, buffer, indent)`（main/ClassWriter.java:373）输出（§6）。

### 1.2 garlic 管线

入口：`garlic.c:main` → 按 magic 分派（class/jar/dex/apk/elf）。class 文件路径：`run_for_jvm_class` → `parser/class/metadata.c:parse_class_file`（解析出 `jclass_file`，内含 `jsource_file *jfile` 高层模型）→ `jvm/jvm_decompile.c:jvm_analyse_class_file`。

```
jvm_analyse_class_file_inside(jf)            # jvm/jvm_decompile.c:73
 1. jf->fname/pname/sname                     # 类全名/包名/简单名
 2. jvm_init_ins_fn / jvm_init_method_fn      # 装入指令/方法判定函数表（前端抽象：JVM 与 Dalvik 共用后端）
 3. jvm_collect_descriptor(jf)                # 常量池描述符缓存
 4. jvm_fields(jf)                            # 字段模型 jd_field（access/type/name）
 5. jvm_methods(jf)                           # 逐方法反编译（跳过 lambda 体方法，lambda 在调用点内联展开）
 6. jvm_signatures(jf)                        # 类/字段/方法的 Signature 属性
 7. class_create_definations(jf)              # 生成类/字段/方法声明字符串（access flags + 泛型）
 8. jvm_annotations(jf)                       # 注解渲染为字符串
 9. optimize_enum_class(jf)                   # enum: 隐藏 values/valueOf/$VALUES、<clinit> 常量聚合 (§4.4)
10. class_create_blocks(jf)                   # 建类级 jd_node 树：CLASS_ROOT→[PACKAGE_IMPORT, CLASS→[FIELD, METHOD...]]
jvm_analyse_class_file → writter_for_class(jf, NULL)   # 输出到 stdout/文件
```

**方法级管线** `jvm/jvm_method.c:jvm_method`：

```
jvm_method(jc, m, jm)
 1. jvm_method_init                            # jvm_method.c:465
    a. init_method_instructions                # 线性扫描解码指令: jd_ins{code,offset,idx,param,prev/next,
                                               #   pushed/popped 数(invoke/multianewarray/wide 动态计算),
                                               #   uses/defs bitset(load/store 的 slot)}，建 offset→idx 哈希
    b. init_jvm_instruction_graph              # 每条指令 targets/jumps/comings:
                                               #   条件跳转→[target,next]；table/lookupswitch→default+所有 case(含 padding 处理)；
                                               #   goto/goto_w；return/athrow 无后继；jsr/ret → method_mark_unsupport(直接放弃)
    c. init_method_exception_table             # jd_exc: start/end/handler pc → offset/idx（try_end 取 end_pc 前一条指令）
 2. jvm_rename_goto2return                     # goto→return 的归一化 (jvm_ins.c:103)
 3. jvm_method_exception_edge                  # jvm/jvm_exception.c:174，异常结构恢复（详见 §3d）:
      cfg_create(m)                            # 建 CFG + 支配树
      identify_exception_handler_block_end     # 用支配集求 handler 块结束位置 → closed_exceptions
      cleanup_full_exception_table             # 删空/重复项
      clear_dominator_tree; copy_exceptions_closed2cfg; cfg_create(m)   # 重建
      identify_finally_excpetion_handler_block_end
      flatten_exceptions                       # 把交叠/相邻的 try 范围合并、finally 归组 → mix_exceptions{try,catches[],finally}
      inline_finally_block                     # finally 复制体识别：指令级反向比对，nop 掉 try/catch 尾部复制 (reverse_compare_instruction)
      pullin_block_jump_into_exception_try_block
 4. jvm_simulator(m)                           # jvm/jvm_simulator.c:410，栈模拟 + SSA:
      sform_prepare_for_local_variable         # use/def bitset + 活跃变量数据流迭代 (ssa.c)
      jvm_method_enter_stack                   # this + 参数按描述符放 local_vars（long/double 占两 slot）
      worklist: queue_push(第一条指令)
      while pop(ins): jvm_ins_cb
        - jvm_fill_watch_successors            # 后继 = 块内 next / 块尾 out 边目标(跳过回边) / 异常 handler 入口
        - jvm_run_instruction_action           # 计算 stack_out = f(stack_in)；dup/swap/pop 有特殊 action；
                                               #   store/load 更新 local_vars（类型或名字变化→视为新变量!）；
                                               #   每个 push 的值绑定 stack_var（jvm_stack_var_defination）
        - jvm_fill_visit_queue                 # 后继 stack_in==NULL 才入队（handler 入口注入"异常对象"栈）
      mark_unreachable_instruction
      sform_for_local_variable                 # 支配边界插 φ + 重命名(SSA) + φ 参数与栈值合并
      sform_for_stack_variable                 # 跨块栈值统一（把前驱块尾的 stack_var 替换为汇合点的）
 5. cfg_remove_exception_block                 # 把 EXCEPTION 块边替换为到 handler 正常块的边（异常块使命已完成）
 6. optimize_jvm_method(m)                     # jvm/jvm_optimizer.c:37 —— 表达式化 + 全部重写 pass（顺序即架构）:
      instruction_to_expression                # 每条指令 → 一个 jd_exp（§3b）；invokedynamic → follow_lambda + identify_string_concat
      jvm_fix_type                             # 应用 int 隐藏类型修正 (jvm_type_analyse.c)
      negative_if_expression; nop_empty_expression; inline_variables; identify_cmp_after_if
      optimize_enum_constructor                # nop 掉 enum 构造器里的 Enum.<init>
      create_node_tree                         # root + 每个基本块一个 BASIC_BLOCK node + EXCEPTION/TRY/CATCH/FINALLY node 树
      do {  # 定点迭代
        identify_logical_operations            # if-if 钻石 → && / ||  (expression_logical.c)
        identify_reverse_logical_operation
        identify_initialize                    # new+dup+invokespecial<init> → INITIALIZE 表达式 (expression_new.c)
        identify_ternary_operator              # 三元 (expression_ternary.c)
        identify_assignment_chain / identify_define_stack_variable_chain / identify_assignment_chain_store
        identify_logical_with_assignment       # b = cond1 && cond2
        identify_ternary_operator_in_condition
        identify_array_initialize              # new T[n] + n×aastore → T[]{...}
        inline_variables                       # stack_var 内联（核心消栈手段）
      } while (changed)
      inline_variables_round2                  # def_count==1 的宽松内联
      identify_assignment                      # a=b 且 b 为局部变量 → 复制传播式合并
      identify_loop                            # 循环识别：自身在支配边界中 → header；回收回边可达块 (expression_loop.c)
      identify_branches                        # if/else-if/else、switch/case 节点化 (expression_branches.c)
      identify_if_break_or_if_continue
      identify_synchronized                    # monitorenter + EXCEPTION(finally=monitorexit) → SYNCHRONIZED 节点
      optimize_goto_expression                 # goto → break/continue/删除 (expression_goto.c)
      analyse_local_variables                  # 变量重命名+作用域+声明位置 (expression_local_variable.c, §3e)
      copy_propagation_of_dup_local_variable
      identify_loop_type                       # for/do-while/while/infinite 分类 (expression_loop_type.c)
      remove_empty_if_else_of_method; nop_node_last_return
      setup_expression_node_param              # 给 if/while/catch/synchronized 节点装配条件表达式 param_exp
      optimize_exception_block
```

输出：`decompiler/expression_writter.c:writter_for_class` 递归遍历类 node 树，按节点类型（IF/SWITCH/CASE/WHILE/DO_WHILE/FOR/LOOP/CATCH/SYNCHRONIZED/...）打印；表达式打印走 `decompiler/transformer/transformer.c:expression_to_stream` 的大 switch，分派到 50 个 `transformer/*.c`。

---

## 2. class 文件解析要点

### 2.1 结构总览

`magic(0xCAFEBABE) minor u2 major u2 constant_pool access u2 this u2 super u2 interfaces[] fields[] methods[] attributes[]`。
- Vineflower：`struct/StructClass.create`（struct/StructClass.java:54）；常量池 `struct/consts/ConstantPool.java`；成员 `StructField/StructMethod extends StructMember`（属性表 `Map<Key<?>,Object>`，Key 常量集中在 `struct/attr/StructGeneralAttribute.java:21-45`）。
- garlic：`parser/class/metadata.c:parse_class`；结构体在 `parser/class/class_structure.h`（`jclass_file/jcp_info/jattr/jmethod/jfield` + 每种属性的 `jattr_*`）；属性分派表 `metadata.c:548-580`（28 个已知属性，未知属性按 length 跳过）。

### 2.2 必须处理的属性清单（两边并集）

| 属性 | 位置 | 内容/用途 | 参考实现 |
|---|---|---|---|
| Code | method | max_stack/max_locals/code[]/exception_table[]/子属性 | Vineflower `struct/attr/StructCodeAttribute.java`（**懒解析**：把 code+exception 原始字节存下，`StructMethod.expandData` 时才解码指令，省内存）；garlic `parse_attr_code` |
| StackMapTable | Code 子属性 | 类型校验帧。反编译**不需要**逐帧使用（garlic 自己模拟栈；Vineflower 也用 DataPoint/InstructionImpact 模拟），但解析时必须能正确跳过/读取（frame_type 分支多：same/same_locals_1_stack/append/full 等，garlic `parse_attr_stack_map_table` 完整实现可参考） |
| LineNumberTable | Code 子属性 | 字节码→源码行；用于输出原始行号注释/字节码映射 | `StructLineNumberTableAttribute` |
| LocalVariableTable / LocalVariableTypeTable | Code 子属性 | 调试名+描述符/泛型签名，按 [start_pc, start_pc+length) 区间绑定 slot | `StructLocalVariableTableAttribute`（`getVarName(index, offset)` 区间查询）；garlic `jvm_type_analyse.c:match_local_variable`（**注意匹配条件是 `next_ins->offset == start_pc`**，即 store 之后第一条指令的偏移） |
| Exceptions | method | throws 列表（无 Signature 时输出 throws 用） | `StructExceptionsAttribute` |
| Signature | class/field/method | 泛型签名（§5） | `StructGenericSignatureAttribute` + `struct/gen/generics/GenericMain` |
| InnerClasses | class | 条目 {inner_class_info, outer_class_info, inner_name, inner_class_access_flags}；**嵌套类树的唯一可靠来源**；simpleName==null → 匿名；outer==null 且 simpleName!=null → 局部类 | `StructInnerClassesAttribute`；garlic `parse_attr_inner_classes` |
| EnclosingMethod | class | {class_index, method_index}；局部类/匿名类的外围方法；method_index==0 表示在字段初始化器/静态块中 | `StructEnclosingMethodAttribute` |
| BootstrapMethods | class | bsm 数组 {bootstrap_method_ref(MethodHandle), bootstrap_arguments[]}；invokedynamic/condy 解析必需 | `StructBootstrapMethodsAttribute`；garlic `jvm_lambda.c:get_bootstrap_method_attr` |
| NestHost / NestMembers | class (55+) | nest 访问控制；影响私有成员访问桥接是否需要还原。注意 Vineflower 只解析 NestHost（StructGeneralAttribute.java:46 标注 NestMembers 为 TODO），garlic 两者都解析（metadata.c 的 parse_attr_nest_host/nest_members） | `StructNestHostAttribute` |
| Record | class (60+) | components[] {name_index, descriptor_index, attributes(含 Signature/注解)} | `StructRecordAttribute` → `StructRecordComponent` |
| PermittedSubclasses | class (61+) | 允许子类列表 → sealed/permits | `StructPermittedSubclassesAttribute` |
| AnnotationDefault | method(注解成员) | element_value 默认值 | `StructAnnDefaultAttribute` |
| RuntimeVisible/InvisibleAnnotations、…ParameterAnnotations、…TypeAnnotations | 全部 | 注解渲染；TypeAnnotations 带 target_type/target_info/type_path（复杂，可后置） | `StructAnnotationAttribute/StructAnnotationParameterAttribute/StructTypeAnnotationAttribute`；garlic `jvm_annotation.c`（渲染成字符串挂在 jd_annotation.str） |
| ConstantValue | field | static final 基本型/String 常量（字段初始化器缺失时的兜底） | `StructConstantValueAttribute`；ClassWriter.writeField 用它 |
| MethodParameters | method | 参数名+flags（无 LVT 时的参数名来源） | `StructMethodParametersAttribute` |
| Module / ModulePackages / ModuleMainClass | module-info (53+) | 模块描述（requires/exports/opens/uses/provides） | `StructModuleAttribute` + `ClassWriter.moduleInfoToJava/writeModuleInfoBody` |
| Synthetic / Deprecated / SourceFile / SourceDebugExtension | 各处 | 合成标记（隐藏成员判断）、弃用注释、源文件名 | 略 |

### 2.3 解析的坑（务必逐条处理）

1. **CONSTANT_Utf8 是 modified UTF-8**：`0xC0 0x80` 表示 NUL，增补字符用代理对的双 3 字节编码。Vineflower 直接用 `DataInputStream.readUTF()`（ConstantPool.java:41）天然正确；Rust 里**不能**用 `String::from_utf8`，要么手写 modified-UTF8 解码转 Rust `String`（代理对→`char` 需组合），要么存字节+按需转。
2. **Long/Double 占两个常量池 slot**：`CONSTANT_Long/Double` 后面那个 index 不可用。Vineflower：`pool.add(null); i++`（ConstantPool.java:52-61）。garlic 常量池同样处理。取值时必须容忍空洞。
3. **常量池两阶段解析**：第一遍只读原始 index，第二/三/四遍再 resolve 引用（Class/String/MethodType/NameAndType → Fieldref/Methodref/InvokeDynamic/Dynamic → MethodHandle），因为前向引用普遍存在。Vineflower 用三个 `BitSet nextPass[3]` 分趟 resolve——Rust 里就是 `resolve(&mut pool)` 多趟循环。
4. **jsr/ret（major ≤ 50，即 Java 6 及以前）**：老 finally 用子程序实现。
   - garlic：直接 `method_mark_unsupport`（jvm_method.c:442）放弃该方法；
   - Vineflower：完整内联——`ControlFlowGraph.setSubroutineEdges`（用 jsr 栈 DFS 把 ret 块连到 jsr 的下一块）→ `processJsr`（求每个 jsr 的 range；range 相交时 `splitJsrRange` **复制**公共块）→ `removeJsr`（用 `DataPoint`+`InstructionImpact.stepTypes` 模拟栈类型，删掉 jsr/ret 指令和针对 returnAddress 的 astore/pop）。
   - jcdc 建议：至少实现"遇到 jsr/ret 标记方法不可反编译并输出注释"，内联可作为二期。
5. **wide 前缀**：`wide` 后跟 iload/istore/…/ret 时操作数是 u2，跟 iinc 时是 u2+u2（总参数长：普通 3、iinc 5）。garlic `caculate_param_length`（jvm_method.c:280）；Vineflower 在解码时直接把 wide 版本折叠成普通 opcode + u2 操作数（StructMethod.java:126,225）。`wide goto/jsr` 不存在，`goto_w/jsr_w` 是独立 opcode（4 字节偏移）。
6. **tableswitch/lookupswitch 4 字节对齐 padding**：操作数从 `(4 - (offset+1) % 4) % 4` 的 padding 之后开始。garlic `jvm_switch_padding(ins->offset)`；解码后所有 jump offset 都是**相对本 switch 指令自身 offset** 的有符号 s4。Vineflower 把 default+destinations 全部转成指令下标存进 `SwitchInstruction`。
7. **invokedynamic 操作数是 4 字节**（u2 index + 2 个必须为 0 的字节）；`invokeinterface` 是 u2+count+0 共 4 字节；Java 6 以前 invokedynamic 未定义（`bytecodeVersion.hasInvokeDynamic()` 分支，StructMethod.java:220）。
8. **简写指令归一化**：`iconst_m1..iconst_5`、`iload_0..aload_3`、`istore_0..astore_3`、`ldc vs ldc_w`、`goto vs goto_w`、`bipush/sipush`。Vineflower 在解析期统一映射到基础 opcode + 显式操作数（`opr_iconst/opr_loadstore/opcs_load/opcs_store` 表，StructMethod.java:62-65,135-147）——**强烈建议 jcdc 照做**，后续所有 pass 只面对 ~60 个规范 opcode。
9. **指令组(group)**：Vineflower 给每条指令标 `GROUP_GENERAL/JUMP/SWITCH/RETURN/INVOCATION/FIELDACCESS`（`code/Instruction.java`、`code/CodeConstants.java`），CFG 构建只看 group，干净利落。
10. **异常表 end_pc 是排他边界**：try 区间是 [start_pc, end_pc)，转指令下标时 end 取"最后一条被保护指令"（garlic `init_method_exception_table` 取 `try_end_idx-1`；Vineflower `findStartInstructions` 把 `handler.to()` 也标为块起点，range 用块 id 区间 [from.id, to.id) 表达）。
11. **access flags 的语境差异**：同一个 0x1000 在 class 是 SYNTHETIC、在 method 也是 SYNTHETIC，但 0x0020 在 class 是 SUPER/ACC_SUPER（**不要输出成 synchronized**）、在 method 是 SYNCHRONIZED、在 field 是 0（volatile 是 0x0040）。inner_classes 属性里的 flags 是"源码级"修饰符（可以没有 SUPER）。两边都定义了完整常量表（garlic `class_structure.h:7-49`，Vineflower `code/CodeConstants.java`）。
12. **类版本 → 特性开关**（Vineflower `code/BytecodeVersion.java`，jcdc 应原样照抄这张表）：
    - 45 (1.0.2)～48 (1.4)：可能 jsr/ret（≤50）；48-：`has14ClassReferences`（`class$` 合成类）；45.0-45.2 `predatesJava`；
    - 49 (5)：enum（`hasEnums`，ACC_ENUM 合法）；
    - 50 (6)：StackMapTable 可选；jsr 上限；
    - 51 (7)：invokedynamic 正式可用（`hasInvokeDynamic`）；
    - 52 (8)：lambda（`hasLambdas`）、接口 default/static 方法、方法参数名属性常见；
    - 53 (9)：indy 字符串拼接（`hasIndyStringConcat`）、module-info（ACC_MODULE 0x8000 + Module 属性）、接口私有方法、NestHost 尚未（55）；
    - 55 (11)：nest-based access（NestHost/NestMembers）、新版 try-with-resources 字节码（`hasNewTryWithResources`，资源变量 dup 模式变化）；
    - 59 (15)：sealed 预览（minor==65535）、record 预览、隐藏类；
    - 60 (16)：record 正式、sealed 预览、instanceof 模式匹配（`hasIfPatternMatching`）、switch 表达式正式（`hasSwitchExpressions`）、局部 enum/接口（`hasLocalEnumsAndInterfaces`）；
    - 61 (17)：sealed 正式（`hasSealedClasses`=previewReleased(15,17)）、switch 模式匹配预览；
    - 65 (21)：switch 模式匹配正式（`hasSwitchPatternMatch`=previewReleased(17,21)）、record 模式（`hasRecordPatternMatching`）；
    - **预览特性判定**：`minor == 65535 (PREVIEW)` 且 major ≥ 预览起始版本。66=Java22、67=Java23（Vineflower 常量止于 MAJOR_21=65，jcdc 需自行延伸，逻辑不变）。
13. **module-info.class**：`cl.hasModifier(ACC_MODULE) && cl.hasAttribute(ATTRIBUTE_MODULE)` → 走 `ClassWriter.moduleInfoToJava`（requires/transitive/exports/opens/to/uses/provides/with），不建方法体。`package-info.class`：synthetic + simpleName=="package-info" → 只输出注解 + package 声明。
14. **重复方法/损坏文件容错**：Vineflower 对重复 method key 打 warning 后继续（StructClass.create）；属性解析失败不应中断整个类。反编译器必须"永不崩溃"：每个方法独立 try/catch，失败输出 `/* $VF: Unable to decompile */` + 原始字节码 dump（`ClassWriter.dumpError/collectBytecode`）。

---

## 3. 方法反编译核心

### 3a. 基本块划分与 CFG 构建

**Vineflower**（`code/cfg/ControlFlowGraph.java`，输入 `FullInstructionSequence`=指令数组+ExceptionTable）：

```
buildBlocks(seq):
  states = findStartInstructions(seq)     # short[] 位图，标 1 = 块起点
    # 起点集合：指令0；每个异常 handler 的 from/handler/to；
    # 每条 GROUP_JUMP 的 destination 与其下一条；GROUP_SWITCH 的 default+全部 case 目标与其下一条；
    # GROUP_RETURN(return/athrow/ret) 的下一条
  createBasicBlocks(states, seq)
    # 顺序扫描，遇 states[i]==1 开新 BasicBlock(++counter)；
    # 指令拷入 block.seq，记录 instrOldOffsets（原始字节码偏移，用于行号映射/指令比对）；
    # mapInstrBlocks: 指令下标→块；额外建一个空 dummy last 块（所有 return 的前汇点）
  connectBlocks(mapInstrBlocks)
    # 按块尾指令 group：
    #   JUMP: addSuccessor(dest块)；canFallThrough(条件跳转) 再 addSuccessor(下一块)
    #         —— 后继表顺序约定：条件跳转目标在前、fallthrough 在后（后续 IfStatement 依赖!）
    #   SWITCH: 先 default 块，再各 case 块（SwitchStatement 依赖此顺序）
    #   RETURN: last.addPredecessor(block)（ret 例外）
    #   GENERAL/INVOCATION/FIELDACCESS: addSuccessor(下一块)
  setExceptionEdges(seq, mapInstrBlocks)
    # 每个 ExceptionHandler(from,to,handler,type)：
    #   key=from.id:to.id:handle.id 去重合并（同范围多类型 → range.addExceptionType，multi-catch 基础）
    #   protectedRange=[from.id, to.id) 的每个块 addSuccessorException(handler块)
    #   生成 ExceptionRangeCFG{protectedRange, handler, exceptionTypes(null=catch-all/finally)}
  setSubroutineEdges()   # jsr/ret 配对（§2.3-4）
```

辅助：`BasicBlock`（code/cfg/BasicBlock.java）字段：id、seq、succs/preds、succExceptions/predExceptions、mark、instrOldOffsets、`getOldOffset(i)`。`getReversePostOrder()` 用显式双栈迭代 DFS（succs+succExceptions 合并遍历）。`DeadCodeHelper.mergeBasicBlocks`（modules/code/DeadCodeHelper.java）：`succs==1 && next.preds==1 && next.predExceptions空 && next!=first && 两块在每个异常 range 中同进同出 && 尾指令不是 switch` → 合并指令序列。

**garlic**（`decompiler/control_flow.c:cfg_create`）：
- 块类型 5 种：`JD_BB_ENTER(id=0)/EXIT(1)/EXCEPTION_EXIT(2)/NORMAL(从3起)/EXCEPTION`（每条异常表项一个 EXCEPTION 块，存 `jd_eblock{try_start/end_offset, handler_start/end_offset, type=CATCH|FINALLY(catch_type==0)}`）。
- NORMAL 块切分（`cfg_create_normal_blocks`）：扫描指令，**当前指令的 closest_exception_of(offset) 与下一条不同**（进出 try 范围）、或 `is_block_end(ins)`（跳转/return/athrow）、或 `is_block_start(next)`（被跳转/handler 起点）→ 断开。比 Vineflower 多了"异常上下文变化"这一维（因为它把异常块当 CFG 节点用）。
- 连边：`cfg_link_normal_block`（enter→首块；return/末尾→exit；athrow 无常规后继；否则按 `end_ins->targets` 连）＋ `cfg_link_exception_block`（NORMAL 块 → 覆盖它的最近 EXCEPTION 块（try_start 最大/范围最小优先），EXCEPTION 块 → 其 handler 起始 NORMAL 块、父异常块、最近 finally 块；athrow 且不在任何 try 内 → EXCEPTION_EXIT）。
- 支配树（`decompiler/dominator_tree.c`）：经典迭代数据流——`dominator_tree()` 反复 pre_order 遍历，`compute_dominator_cb` 对每个块取所有已访问前驱的"共同支配者"（`same_dom_block` 沿 idom 链求交），直到不动点；随后建 `dom_children`、算支配边界 `dominance_frontier`（标准 DF 递归：out 边中 idom≠self 的目标 + 子块 DF 上提）；`compute_dominates_block(b)` 按需物化 b 的支配集合（循环/switch 识别用）。
- SCC：`decompiler/scc.c:compute_scc`（Tarjan），用于识别强连通分量（循环嵌套分析）。

**jcdc 建议**：采用 Vineflower 的 CFG 形态（异常不进常规边，只作 `succExceptions` + range 对象），块切分条件加上 garlic 的"异常上下文变化"点；支配树用简单迭代法即可（方法级 CFG 很小），或直接用 Lengauer-Tarjan。保留 `old_offsets` 映射（调试输出/finally 比对/行号都需要）。

### 3b. 表达式构建（栈模拟 → 表达式树）

**Vineflower 的 Exprent 体系**（`modules/decompiler/exps/`）。基类 `Exprent`：字段 `type(枚举见下)/bytecode(BitSet 原始偏移)/parent`；核心虚方法：`copy()`（深拷贝，到处在用）、`getExprType()`、`getInferredExprType(upperBound)`（泛型推断版）、`checkExprTypeBounds()`（返回 CheckTypesResult：赋值上下界约束，喂给 VarTypeProcessor）、`toJava(indent)`、`getAllExprents()`、`replaceExprent(old,new)`、`processSforms(...)`（SSA 遍访钩子）、`addBytecodeOffsets`。Type 枚举：`ANNOTATION, ARRAY, ASSERT, ASSIGNMENT, CONST, EXIT, FIELD, FUNCTION, IF, INVOCATION, MONITOR, NEW, PATTERN, SWITCH, SWITCH_HEAD, VAR, YIELD, OTHER`。

完整清单与字段：

| 类 | 字段 | 说明 |
|---|---|---|
| `ConstExprent` | `ConstType(VarType), value(Object: Integer/Long/Float/Double/String/...), booleanConst推断` | 字面量。`adjustConstType(fieldType)` 按上下文收窄（int→byte/char/short/boolean）；`convertStringToJava` 转义；char 常量输出 `'x'`；浮点格式化为 Java 字面量（`1.0f/1.0d/NaN/Infinity`）；String 走常量池。类型推断：new ConstExprent(int) 默认 INT，被赋给 byte 变量/参数时 adjust |
| `VarExprent` | `index(slot 或 ≥STACK_BASE=10000 的栈变量), version(SSA), VarType, varProcessor, isStack, isDefinition, LVT(LocalVariable 调试信息), boundType, final 状态` | 局部变量/栈临时量。`getVarVersionPair()=(index,version)` 是全系统变量身份标识 |
| `AssignmentExprent` | `left(dest), right(source), condType(=,+=,...)` | 赋值；也用来表达"栈变量定义" |
| `FunctionExprent` | `FunctionType(见下), lstOperands, implicitType` | 一元/二元运算。FunctionType 枚举带 `(arity, operator字符串, precedence, castType)`：ADD/SUB/MUL/DIV/REM/SHL/SHR/USHR/AND/OR/XOR(prec 2-4)、BIT_NOT/BOOL_NOT/NEG(1)、I2L..I2S(15 个窄化/宽化转换，输出为 cast)、CAST、INSTANCEOF(6)、ARRAY_LENGTH、IMM/MMI/IPP/PPI(前后缀 ++/--)、TERNARY(12)、LCMP/FCMPL/FCMPG/DCMPL/DCMPG(内部占位，最终应被 IfExprent 吃掉)、EQ/NE(6)/LT/GE/GT/LE(5)、BOOLEAN_AND(10)/BOOLEAN_OR(11)、STR_CONCAT(3, "+")。**这张 precedence 表就是输出加括号的依据** |
| `IfExprent` | `Type(EQ,NE,LT,GE,GT,LE,ICMPEQ..ACMPNE,NULL,NONNULL), condition(Exprent)` | if 条件。构建时取指令语义的 **negative**（`func5[opcode-ifeq].getNegative()`）：ifeq 跳走=假，所以记录的 condition 是"顺序执行的条件"即 `x != 0`。`negateIf()` 翻转 |
| `FieldExprent` | `LinkConstant(classname/elementname/descriptor), instance(null=static), isStatic, 泛型 QualifierChain` | 字段访问 |
| `InvocationExprent` | `functype(GENERAL/INIT/SPECIAL/DYNAMIC), classname, name, stringDescriptor, descriptor(MethodDescriptor), instance, lstParameters, isStatic, bootstrapMethod+bootstrapArguments(indy), invokeDynamicClassSuffix(lambda 键), genericArgs/genericsMap, boxing 状态, syntheticNullCheck` | 方法调用。构造时**直接从模拟栈弹出参数**（`InvocationExprent(opcode, cn, bsm, bsmArgs, stack, offsets)`）。toJava 处理：lambda 节点(`isLambda`)、方法引用(`isMethodReference`→`X::m`)、匿名类(`isAnonymous`→`new I(){...}`)、enum 构造、 boxing/unboxing 隐藏、`<init>` 渲染为 `super()/this()/new`、varargs 参数展开 |
| `NewExprent` | `NewType(VarType), lstDimensions, lstArrayElements(new T[]{a,b}), constructor(InvocationExprent), directAnonymous, enumConst, wasLazyCondy` | new/anewarray/newarray/multianewarray。`isLambda/isAnonymous/isMethodReference` 通过 ClassNode 查表（`ClassesProcessor.mapRootClasses` 里 `##Lambda_x_y` 键）。toJava：匿名类 → `ClassWriter.classLambdaToJava/writeClass`；数组初始化 → `{...}` |
| `ArrayExprent` | `array(Exprent), index(Exprent), ArrayType(VarType)` | `a[i]` |
| `ExitExprent` | `Type(RETURN/THROW), value, retType, methodDescriptor` | return/athrow |
| `SwitchHeadExprent` | `value(选择子), caseValues(List<List<Exprent>> 每 case 可多值)` | switch 头。真实 case 值由 SwitchHelper 后期从 switchmap/字符串模式还原 |
| `SwitchExprent` | `selector(VarExprent), caseValues, caseStatements, defaultDestination` | 整个 switch 的表达式封装（switch 表达式/yield 支持） |
| `MonitorExprent` | `Type(ENTER/EXIT), monitor(Exprent), remove 标志` | monitorenter/exit |
| `AssertExprent` | `lstParameters(条件, 消息)` | assert 语句 |
| `YieldExprent` | `value` | switch 表达式 yield |
| `AnnotationExprent/TypeAnnotation` | 注解渲染 | |
| `PatternExprent/Pattern` | 模式匹配（instanceof/record/switch 模式） | 16+/21+ |

**栈模拟核心 `ExprProcessor.processBlock`**（modules/decompiler/ExprProcessor.java:203）：
- 状态：`PrimitiveExprsList{ListStack<Exprent> stack, List<Exprent> exprlist}`——**stack 里放的是 VarExprent（栈变量引用），exprlist 是块内语句序列**。
- 关键手法 `pushEx`（:615）：任何产生值的指令，先构造 rhs Exprent，然后：
  ```
  varindex = STACK_BASE + stack.size()          # 10000+depth，栈槽→虚拟变量号
  var = VarExprent(varindex, rhs.getExprType(), isStack=true)
  exprlist.add(AssignmentExprent(var, rhs))     # 语句:  <stackN> = rhs
  stack.push(var.copy())                        # 栈上只放变量引用
  ```
  即：**每条指令的产物先落成一个显式栈变量赋值**，块间通过复制 stack（`data.copyStack()`，DFS 传播，catch 块从 `collectCatchVars` 预置的异常变量开始）传递。真正的"折叠成表达式树"发生在后面 `StackVarsProcessor.simplifyStackVars`（用 SSA 版本判断 `stackN` 只有一个 use → 把 AssignmentExprent 的 rhs 直接替换进 use 处，删除赋值），多 use 的栈变量保留为局部变量（`define_stack_var` 风格）。
- dup 家族：`insertByOffsetEx(offset, stack, exprlist, copyoffset)` 通过"弹出-重编号-再压入"模拟 dup_x1/dup_x2/dup2_x1/dup2_x2/swap（按 `getExprType().stackSize` 区分类目 1/2 值），每个被搬动的值都产生新的栈变量赋值——这保证了任意 dup 模式（包括 `new/dup/invokespecial` 字段链、`a[i++]`、`synchronized` 的 dup）都能正确展开。
- 特殊指令：
  - `iinc` → `AssignmentExprent(var, FunctionExprent(ADD/SUB, [var.copy(), const]))`（后续 PPandMMHelper 可能变 `i += n`/`i++`）；
  - `checkcast/instanceof` → 先 push `ConstExprent(类型)` 再建 `FunctionExprent(CAST/INSTANCEOF)`（**类型作为第二操作数**入栈的巧妙编码）；
  - `if*` → `exprlist.add(new IfExprent(negatedType, stack))`（弹 1-2 个值）；
  - `tableswitch/lookupswitch` → `exprlist.add(new SwitchHeadExprent(stack.pop()))`；
  - `return/athrow` → ExitExprent；`monitorenter/exit` → MonitorExprent（EXIT 若 `stat.isRemovableMonitorexit()` 标 remove）；
  - `pop` → 弹栈；若上一条恰是"赋值=getClass()/Objects.requireNonNull 调用"（编译器合成的空检查 `DUP; ... POP` 模式）→ 标 `setSyntheticNullCheck()` 输出时隐藏；
  - `pop2` → 按栈顶 stackSize 弹 1 或 2 个；
  - `invokedynamic` → InvocationExprent（带 bsm），lambda/concat/condy 分别由 LambdaProcessor/ConcatenationHelper/CondyHelper 后处理；
  - `ldc CONSTANT_Dynamic` → CondyHelper.simplifyCondy（condy 折叠为 cast+常量/方法引用）。
- `processStatement`：`FlattenStatementsHelper.buildDirectGraph(root)` 把 Statement 树压成 `DirectGraph`（DirectNode=一段 exprents 列表 + REGULAR/EXCEPTION 边；catch/finally 的头块单独成 node），然后 DFS：`mapData[node] = 前驱的 stack 拷贝`，逐块 `processBlock`，块结果写回 `BasicBlockStatement.setExprents`。

**garlic 的对应机制**：
- 模拟发生在**表达式构建之前**（`jvm_simulator.c`），每条 `jd_ins` 得到 `stack_in/stack_out`（`jd_stack{depth, vals[], local_vars[]}`，值是 `jd_val{type, data(cname/val), ins, name, stack_var}`）；每个 push 的值分配全局唯一 `jd_var`（stack_var，含 def_count/use_count/dupped_count/store_count 引用计数）。
- `instruction_to_expression`（jvm/jvm_expression_builder.c:1406）：**每条指令一个 jd_exp**，绝大多数是 `ASSIGNMENT{left=LVALUE(stack_var), right=<操作表达式>}`：
  - 常量 → right=CONST；load → right=LOCAL_VARIABLE(jd_val)；算术 → right=OPERATOR{op, [lhs(stack_in[1]), rhs(stack_in[0])]}；
  - invoke → INVOKE{class/method/descriptor, args[](从 stack_in 弹出，instance 放最后)，void 或后面紧跟 pop 时不包 assignment}；
  - store → STORE{[LOCAL_VARIABLE(slot 当前 jd_val), STACK_VAR]}（不包 assignment，因为它本身就是"语句"）；
  - if → IF{offset(目标), expression=OPERATOR(比较)}；ifeq/ifne 且栈值被判定为 boolean → 直接 `!x`/`x`（`stack_val_is_boolean`）；
  - switch → SWITCH{default_offset, targets[{offset,ikey}], selector}；goto → GOTO{goto_offset}；return/athrow/monitorenter/exit/newarray/arraylength/a?load/a?store/get|put(field|static)/iinc/neg/cast(i2l..checkcast)/instanceof/cmp(LCMP 家族→COMPARE assignment)/new(→UNINITIALIZE，稍后与 invokespecial 合并成 INITIALIZE)/dup(→仅增加 dupped_count，无独立表达式)/pop(→EMPTY，且若前一条是 load 则 nop 掉)/swap(EMPTY)。
- 消栈 = `inline_variables`（expression_inline.c）：`stack_var_can_inline(var)`（def==1 且 use==1 且未 dup）时，把 `LHS = rhs` 中 RHS 就地替换到后续表达式里所有引用 LHS 的 STACK_VAR 位置，def_count 归零则整条 nop；`inline_variables_round2` 放宽到 def==1（多 use 也内联，复制 rhs）。**dupped_count>0 的（如 new 的 dup、i++ 的 dup 模式）不允许内联**——这就是 garlic 版的"栈变量保留"。
- `expression_chain.c:identify_assignment_chain`：处理 `a = b = c`（dup 链）；`expression_assign.c:identify_assignment`：`x = y`（y 局部变量）→ 后续 y 全部替换为 x（局部变量复制传播）；`expression_copy_propgation.c` 处理 dup 出的局部变量。

**ConstExprent 类型推断要点**（Vineflower ConstExprent.java）：`new ConstExprent(int)` 的 ConstType 初始为 INT；`adjustConstType(targetType)` 在目标为 BYTE/CHAR/SHORT/BOOLEAN 且值在范围内时收窄；输出时 boolean 常量来自 `iconst_0/1` 且上下文类型为 boolean（`VARTYPE_BOOLEAN`）→ `false/true`；char → `'c'`（含转义）；long 加 `L`；float/double 用最短可逆表示 + `f/d` 后缀；String 用 `convertStringToJava` 做 `\n \t \" \\ \uxxxx` 转义（非 ASCII 按选项）。garlic 对应逻辑在 `transformer/const.c` + `jd_val.data->primitive`。

### 3c. 控制流结构化

**Vineflower：两层结构化**

第一层（CFG→Statement 树）`modules/decompiler/decompose/DomHelper.java`：

```
parseGraph(graph, mt):
  root = graphToStatement(graph)
    # 每个 BasicBlock → BasicBlockStatement；全部装入 GeneralStatement(first=首块)；
    # CFG 边 → StatEdge：目标是 first → TYPE_CONTINUE(闭包=general)；源在 finallyExits → TYPE_FINALLYEXIT(→DummyExit)；
    # 目标是 dummy last → TYPE_BREAK(→DummyExit)；其余 TYPE_REGULAR；异常边 → TYPE_EXCEPTION(带 exceptionTypes)
    # root = RootStatement(general, dummyExit)
  processStatement(root, ...) 递归:
    loop {
      findSimpleStatements(general):           # 由内向外（post-reverse-post-order 排序保证）
        for st in general.getPostReversePostOrderList():
          result = detectStatement(st)         # 依序尝试:
            DoStatement.isHead(st)             # 自环边(REGULAR 且 dest==head)，或 continueSet 含自身 basichead → 循环(INFINITE)
            SwitchStatement.isHead(st)         # st 是 BasicBlockStatement 且 lastBasicType==SWITCH
                                               #   且 DecHelper.isChoiceStatement(st, lst) 找到 post + 分支集合
            IfStatement.isHead(st)             # lastBasicType==IF；regedges<2 直接成；否则 isChoiceStatement
            SequenceStatement.isHead2Block(st) # st 的唯一 REGULAR 后继 s：s 只有一个前驱 → Seq(st,s)
            CatchStatement.isHead(st)          # st 的异常后继 handlers 集非空(getUniquePredExceptions:
                                               #   handler 的所有异常前驱都在集合里)，各 handler 尾都常规流向同一个 next(或无后继)，
                                               #   DecHelper.checkStatementExceptions 通过 → Catch(head, next, handlers)
            CatchAllStatement.isHead(st)       # 恰一个 handler、edge.getExceptions()==null(catch-all/finally 候选)、
                                               #   handler 无常规后继或后继非常规、非 monitorEnter → CatchAll(head, handler)
          if result: stat.collapseNodesToStatement(result)  # 把成员块折叠成单节点，重连所有边(内部边消失，
                                                            # 跨界边改挂到新 statement；labelEdges/break/continue 提升)
      if general 只剩一个节点 → 完成，replaceStatement 上提
      stat = findGeneralStatement(general):    # 找可独立分解的子图
        # 用扩展后支配集(FastExtendedPostdominanceHelper)或 calcPostDominators(SCC+数据流)求 head→post 对；
        # 从 head 沿 REGULAR 边 BFS 收集 setNodes（不越过 post），期间收集异常 handler，
        #   handler 的加入条件：其全部异常前驱 ⊆ setNodes（保证 try 完整）；
        # 校验：setPreds(外部前驱)为空、checkSynchronizedCompleteness(monitorEnter 块的后继必须在集合内)
        # → new GeneralStatement(head, setNodes, post) 并 collapseNodesToStatement
      processStatement(stat, ...) 递归分解子图
    }
    # 不可约图：IrreducibleCFGDeobfuscator.splitIrreducibleNode —— 找多入口头块，复制一份消除多入口（最多5次）
  LabelHelper.lowContinueLabels; SequenceHelper.condenseSequences; root.buildMonitorFlags
  buildSynchronized(root):
    # Sequence 中 [monitorEnter 块, CatchAll] 相邻，且 CatchAll.head 以 monitorExit/athrow 结尾(或无出口/finally 化)，
    # 且 handler 含 monitorExit → 删 monitorexit、摘掉头块、组 SynchronizedStatement(head, body=ca.first, handler)
```

Statement 类型全集（`modules/decompiler/stats/`）：`RootStatement`(first+dummyExit)、`BasicBlockStatement`(BasicBlock+exprents)、`SequenceStatement`(stats 线性表)、`GeneralStatement`(未分解占位)、`IfStatement`(first/ifstat/elsestat/ifedge/elseedge/negated/iftype/post + headexprent=[IfExprent])、`DoStatement`(first + looptype INFINITE/DO_WHILE/WHILE/FOR/FOR_EACH + initExprent/conditionExprent/incExprent 三槽)、`SwitchStatement`(headexprent=[SwitchHeadExprent] + caseValues/caseEdges/defaultEdge + caseStatements)、`CatchStatement`(first + handlers[] + vars[](catch 参数 VarExprent) + resources[](TWR))、`CatchAllStatement`(first + handler + isFinally + monitor(信号量变量))、`SynchronizedStatement`(first=head + body + handler)、`DummyExitStatement`。
`StatEdge`（modules/decompiler/StatEdge.java）：`type(REGULAR=1/EXCEPTION=2/BREAK=4/CONTINUE=8/FINALLYEXIT=32), source, destination, closure(拥有该边的最外层 statement——label 归属), exceptions(List<String>)`。Statement 通用字段：`stats/first/parent/post/exprents(仅叶)/varDefinitions/labelEdges/continueSet/lastBasicType(GENERAL/IF/SWITCH)/isMonitorEnter/containsMonitorExit`。

第二层（Statement 精化）在主循环（§1.1 步 15）：

- **if/else 合并 `IfHelper`**（modules/decompiler/IfHelper.java）。`IfNode.build` 把 if 的四种出边（if 体、else 体、if 边、else 边的去向）归类为 DIRECT/INDIRECT/NONE，然后依序尝试：
  - `collapseIfIf`：`if(c1){if(c2){A}}` → `if(c1&&c2){A}`（内层 if 的 else 与外层 else 汇合到同一点；条件用 `FunctionExprent(BOOLEAN_AND)` 连接，字节码序 c1,c2）；
  - `collapseIfElse`：`if(c1){...}else{if(c2)...}` 变形合并（||）；
  - `collapseElse`：else 链整理（else{if→else-if 提升}）；
  - `collapseTernary`：钻石形 `if(c1){ if(c2) goto A; goto B } else { if(c3) goto A; goto B }` 且 A/B 均为 INDIRECT（break 到同一汇点）→ `c1 ? c2 : c3`（支持 inverted：ifBranch 的 inner/successor 与 elseBranch 交叉相等时取反）；
  - `ifElseChainDenesting`、`reorderIf`（if 体是直落、else 体是跳转 → 交换分支并 negate，使代码布局贴近源码顺序，`swapBranches`）。
- **循环 `MergeHelper`**（modules/decompiler/MergeHelper.java）：
  - `matchWhile(stat)`：循环 first 是 `IfStatement(IFTYPE_IF, ifstat==null)` 且 ifedge 通向循环外（`isDirectPath(stat, dest)`）或可加 break（`addContinueOrBreak`）→ WHILE，条件=**取反**的 if 条件（因为 if 是"跳出"判断）；elseEdge 出路版本则不取反；然后把空 if 从体内删除、ifedge 提升为循环的出边。
  - `matchDoWhile`（在 `makeDoWhileLoops` 阶段跑，避免破坏 for 识别）：循环**最后一个**语句是 IFTYPE_IF 且 ifedge=TYPE_BREAK、elseedge=TYPE_CONTINUE(closure==stat)（或反过来/双 continue 特例）→ DO_WHILE，条件按需 negate；要求 continue 前驱只有该 if。
  - `matchFor(stat)`：WHILE 循环，取体内最后一个 direct data 块末条表达式（AssignmentExprent/FunctionExprent，即 `i++` 类 inc），再向循环**前面的兄弟块**找 init（末条 AssignmentExprent），检查：inc 中变量在循环内先被使用、init 变量出现在条件或 inc 中、循环体非"只剩 inc"、无 continue 前驱残留 → `looptype=FOR; setInitExprent/setIncExprent`（表达式从原块移除）。
  - `matchForEach(stat)`（增强 for，两种模式）：
    - **Iterator 模式**：pre 块末条 `it = X.iterator()`（`isIteratorCall`：invokeinterface/virtual `iterator()Ljava/util/Iterator;`，排除 java/util/stream）；循环条件 `it.hasNext()`；体首条 `e = it.next()`（或 unbox 包装）；iterator 变量在循环内无其它引用、元素变量循环前未用循环后未用 → `FOR_EACH: for (T e : X)`，initExprent=元素变量，incExprent=X（被迭代表达式）。
    - **数组模式**：pre 末两条 `i = 0; len = arr.length`（FunctionExprent ARRAY_LENGTH），体首条 `e = arr[i]`（ArrayExprent），体末条 `i++`（IPP/PPI）→ `for (T e : arr)`。
  - `EliminateLoopsHelper.eliminateLoops`：嵌套循环中外层"退化"（体内无 continue、入口唯一等）时解开外层。`LoopExtractHelper.extractLoops`：把循环头部只执行一次的块外提、处理"循环+前置块"合并。
- **switch**：`SwitchStatement` 构造时把 head 的 REGULAR 后继按"default 在前"的顺序与 case 值对齐（`SwitchInstruction.getDestinations/getDefaultDestination`），case 值先记为原始 int 常量；多前驱的 case 目标用 `DecHelper.isChoiceStatement` 校验（所有分支必须汇合到唯一 post）。**switch-on-enum/string 的还原在 SwitchHelper（§4.3/4.4）**；case 穿透（fallthrough）通过"case 块无常规后继、直接落入下一 case"表达；`LabelHelper.hideDefaultSwitchEdges` 隐藏空 default。switch 表达式（16+）：`SwitchExpressionHelper.processSwitchExpressions` 把"所有 case 都 yield/return 到同一栈变量"的 switch 折叠成 `SwitchExprent`。
- **try-catch-finally**：
  - catch：CatchStatement 携带 `vars[]`（每个 handler 一个异常参数 VarExprent，类型=exceptionTypes；multi-catch 由 ExceptionRangeCFG 合并的同 range 多类型表达，输出 `catch (A | B e)`）；
  - finally 候选=CatchAllStatement(isFinally=false 初始)；**FinallyProcessor 判定与去复制**见 §3d；
  - `TryHelper.enhanceTryStats`：TWR 识别（§4.9）+ `mergeTry`（相邻/嵌套且资源相同的 try-with-resources 合并）；
  - try 体与 catch 的顺序输出由 CatchStatement.toJava 处理（first → 各 handler → finally）。
- **break/continue/label**：`LabelHelper`。`cleanUpEdges`（删冗余边）、`identifyLabels`（每条 BREAK/CONTINUE 边计算 `closure`=能包含它的最小 statement；跨越多层 → 需要 label）、`lowContinueLabels/lowClosures`（把 closure 下压到最内层可行 statement）、`replaceContinueWithBreak`（最后一步：`continue L` 若目标是循环尾 → 改 `break` 内层 + 结构调整）。输出时 `labelN:` 前缀（Statement.toJava `isLabeled()`）。

**garlic 的结构化**（对照）：
- 循环识别 `expression_loop.c:identify_loops_recursive`：**header 判据 = `block.frontier 包含 block 自身`**（支配边界自环 → 回边头）。然后：
  - `find_loop_content`：从 header 沿 in 边反向 DFS，只收 header 支配的块（自然循环）；
  - `find_loop_condition`：检查循环 first/last 块尾是否 IF 表达式，且其 true/false 目标恰好一个在循环内一个在外；pre-condition（first 块且块内只有这一条表达式）→ while 型；post-condition（last 块）→ do-while 型；`can_write_condition` 还要求没有其它块跳进条件目标（`count_jumps==0`）；
  - `find_loop_exit_blocks`：exit_to_blocks（单入边出口）与 exit_block（多入边汇点）；
  - 无条件块（混淆器产物）时的三种兜底：`loop_content_with_exit_block(s)/loop_content_with_preheader`；
  - `loop_to_node` 把循环块挂到 LOOP 节点（parent 用 `parent_of_loop` 上找到能包含所有块的最近祖先）。
- 循环分型 `expression_loop_type.c:identify_loop_type`：先试 **for**（`loop_to_for_structure`：条件表达式中提取被写变量集合 `get_expression_for_loop`，在 pre-header 块从后往前找"写了条件中变量"的 STORE/PUT_FIELD/PUT_STATIC 作 init，在循环尾找 IINC/OPERATOR/PUT_* 作 increment，都 nop 掉原位置），再 **do-while**（post_condition），再 **while**（pre_condition），否则 **infinite**（`while(true)`）。
- if/switch 节点化 `expression_branches.c`：`identify_if_branches`——if 表达式所在块为 start_block，true_block=跳转目标块、false_block=顺序块；对两者分别要求 `basic_block_is_single_enter`（除 start 外无其它活前驱）才收进分支（用 `compute_dominates_block` 的支配集圈定范围）；jump 目标是 continue/break（`node_is_continue_or_break`）则不收。之后 `identify_else_if_of_method`（IF_TRUE 子节点只含一个 IF → 提升为 ELSE_IF 兄弟）、`identify_else_of_method`、`remove_single_false_node`（空 else 删除+条件取反）。switch：`identify_switch_branches` 按 targets 分组建 CASE 节点（同目标多 key → fallthrough case 合并），default 特殊处理。
- &&/|| `expression_logical.c:identify_logical_operations`：钻石模式 `if(c1) → next块也是 if(c2)，两个 if 的 true/false 目标交叉汇合到同两点` → 合并成 LOGICAL_AND/OR（`make_logic_not` 提供条件取反：EQ↔NE、LT↔GE、AND↔OR、否则包 LOGICAL_NOT）。
- 三元 `expression_ternary.c`、break/continue `expression_goto.c`（goto 目标在循环头之前/之后 → continue/break；`identify_if_break_or_if_continue` 生成 `if (c) break;` 形式的 IF_BREAK 表达式）。

**jcdc 建议**：结构化选 Vineflower 的"域分解 + isHead 模式检测"方案（鲁棒性远好于纯区间法，天然处理不可约图/混淆代码），但把 detectStatement 的六种模式作为独立纯函数实现，便于测试。garlic 的"表达式级循环分型"（for 三段识别）比 Vineflower 的更简单直观，可作为 MatchFor 的简化替代参考。

### 3d. finally 复制模式的识别与合并

Java 编译器把 finally 体复制到：try 正常出口、每个 catch 出口、以及一个 catch-all handler（异常路径：存异常→跑 finally→athrow）。所以一个 `try{A} catch(E e){B} finally{F}` 会生成 3+ 份 F。

**Vineflower `FinallyProcessor`**（modules/decompiler/FinallyProcessor.java，在结构化后、表达式化前，对 CFG+CatchAllStatement 操作）：
```
iterateGraph: 找到 parent 是 CatchAllStatement(非 finally 已确认) 的 first
  handler 首指令分类 firstcode: 0=直接athrow? 1=pop;athrow 2=astore;...;athrow（存异常变量）3=空 finally
  getFinallyInformation: 遍历 DirectGraph 收集 mapLast{try 的各出口块 → 是否以"跳到 handler 同款 finally 复制体"结尾}
  verifyFinallyEx(graph, fstat, record):
    # try 块的每个"侧出口" startBlocks（后继不在 try 内、非 dummy exit）
    # 对每个 start 调 compareSubgraphsEx(graph, start, catchBlocks, first, finallytype, mapLast):
    #   从 start 和 handler-first 同步 BFS，逐块调 compareBasicBlocksEx → equalInstructions 逐指令比较：
    #     - astore/iload 等 slot 可不同（用 lstStoreVars 记录 slot 映射对齐）
    #     - goto 目标只要"同为区域出口"即可
    #   得到 Area{start, sample(复制体块集), next(汇点), sideExits}
    # 所有 Area 的 sideExits 必须一致
  验证通过 → deleteArea 删除所有复制体（把 start 直连 next，复制块从异常 range 摘除），fin.setFinally(true)
  验证失败 → insertSemaphore: 生成 int 信号量变量 s；try 入口 s=1，方法头 s=0；handler 里 if(s==0) 才执行 finally
             → 输出带 /* $VF: semaphore */ 的合法代码（保语义优先）
  CatchAllStatement.isFinally=true 后由 ClassWriter/Statement.toJava 输出 finally 块；
  monitor 变量（synchronized 的 catch-all）由 DomHelper.buildSynchronized 抢先处理，不进 finally 流程
```
`equalInstructions`（:898）细节：opcode 必须相同；操作数按类型比较——常量/池索引相等；`isOpcVar`（load/store/iinc/ret）允许 slot 不同但记录映射；跳转目标比较"在同一 Area 中的相对位置"。

**garlic `inline_finally_block`**（jvm/jvm_exception.c:158 + decompiler/exception.c）：
- 前置：`flatten_exceptions` 已把异常表整理成 `mix_exception{try_range, catches[], finally_range}`（finally=catch_type==0 的项；同一 try 的多个 catch 归组；`remove_duplicate_finally_for_catch_block/narrow_finally_block_near_catch_exception/fix_overlapping_*` 等十来个清洗函数处理交叠范围）。
- `reverse_compare_instruction`：对每个 finally 范围 [fs, fe]，与 try 正常出口尾部 [ts, te] **从后往前**逐指令 `jvm_ins_compares`（opcode+关键操作数，slot 允许映射差异）比对；若匹配长度==finally 指令数 → try 尾部这段是复制体 → `nop_instructions` 全部 nop 掉；对每个 catch 范围同样比对并 nop。
- 差异：garlic 在**指令层**比对（表达式化之前），Vineflower 在**基本块图**层比对（能处理复制体中间有分支的复杂 finally）。

**jcdc 建议**：实现 Vineflower 风格的块级比对（更通用），保留"比对失败→信号量"兜底；范围清洗（交叠 try、共享 handler、嵌套 finally）参考 garlic `exception.c` 的函数清单逐条实现，那里覆盖了实际混淆/老编译器产生的绝大多数畸形异常表。

### 3e. 局部变量：slot → 变量映射

问题本质：一个 slot 在不同程序点可能是**不同源变量**（编译器复用 slot）；一个源变量也可能跨 slot（罕见）。

**Vineflower**：
1. **SSA 版本化**（`modules/decompiler/sforms/`）：`SFormsConstructor.splitVariables(root, mt)` 在 DirectGraph 上做稀疏 SSA：
   - 每个 DirectNode 维护 `SFormsFastMapDirect varmap: slot → FastSparseSet<version>`；入口块初始化参数（`initParameter`，this+params 各得 version 1，long/double 占两 slot 但只建一个变量）；
   - 写（AssignmentExprent 左值是 VarExprent）→ `getNextFreeVersion` 新版本，varmap 置单值；读 → `varRead`：若当前 map 中该 slot 只有一个版本 → 直接 `setVersion`；多版本（汇合点）→ `varReadMultipleVersions`：**新建一个版本作 φ**，`phi[(slot,newVer)] = 输入版本集`（SSAConstructorSparseEx），或 SSAU 变体建 phantom 节点+读边（`SSAUConstructorSparseEx`，用于栈变量内联判定，带 `VarVersionsGraph`）；
   - 块间传播 `mergeInVarMaps`：多前驱取并集，迭代到不动点（worklist `updated`）；catch 块入口特殊（`setCatchMaps`：异常变量新版本）。
   - φ 的作用：**同一 slot 的两个版本若无 φ 连接 → 是两个不同变量**；有 φ → 同一变量的不同赋值。
2. **StackVarsProcessor.simplifyStackVars**：基于 SSAU 图判断栈变量（index≥10000）能否内联（`isVersionToBeReplaced`：唯一读、无 φ 分歧、不在 protected range 跨块等），把 `stackN = rhs` 消掉、rhs 代入读点；不能内联的降级为普通局部变量。
3. **VarProcessor**（modules/decompiler/vars/VarProcessor.java）：持 `mapVarNames/mapVarTypes(Map<VarVersionPair,...>)`、`VarNamesCollector`、thisVars、syntheticSemaphores。`setVarVersions(root)` = 重跑 SSA 定版本；`getFreeName` 生成 `varN`/`varN_M`。
4. **VarTypeProcessor**（vars/VarTypeProcessor.java）：从方法描述符、`checkExprTypeBounds` 收集的约束（赋值两边、参数位置）求每个 VarVersionPair 的最小上界类型（`getCommonSupertype`），处理 int↔byte/char/short/boolean、null↔对象、数组。
5. **VarDefinitionHelper.setVarDefinitions**（vars/VarDefinitionHelper.java:155）：
   - 对每个"需要显式声明"的变量（`mapVarDefStatements`: 变量首次定义所在 statement）：for-init/for-each 特判；否则 `findFirstBlock(stat, index)` 找首个含该变量的块，把首个 `var = ...` 赋值标记 `setDefinition(true)`（输出 `T var = ...`）；找不到赋值则插入裸 `VarExprent(definition=true)`（输出 `T var;`）到合适位置；
   - `mergeVars`：**同一 slot 不同版本的合并**——若两个版本间是直接赋值传递（`x1 = x0`）且生命周期不重叠/可统一命名，则 `remapVar` 把 (slot,v2) 重映射为 (slot,v1)，消除编译器产生的冗余变量；类型合并用 `getMergedType`；
   - `propagateLVTs`：把 LocalVariableTable 的名字/类型按 (index, 首次定义 offset ∈ LVT 区间) 挂到 VarExprent（`VarExprent.setLVT/getDebugName`）；
   - `setNonFinal`、`remapClashingNames`（同名冲突加后缀）。
6. 命名：无 LVT 时 `VarNamesCollector.getFreeName(index)` → `var1/var2...`；有 LVT 用调试名；参数名优先 MethodParameters/LVT；避免与字段名、外围类捕获名冲突（`ClassWrapper.init` 尾部 refreshVarNames；lambda 变量与外围方法变量对齐在 `NestedClassProcessor.setLambdaVars`）。

**garlic**：
- slot 的"变量身份"由模拟期的 `jd_val` 决定：`jvm_run_store_local_variable`——store 时若 slot 无值 → 新建 `jd_val` 放 `local_vars[slot]`；若有值且**类型相同、类名相同、LVT 名字相同** → 沿用（同一变量再赋值）；否则（类型变/类名变/LVT 名字变）→ **新建另一个 jd_val 顶替该 slot**（即认定 slot 复用为不同变量）。读点 `jvm_run_load_local_variable` 直接引用当前 slot 的 jd_val。
- 变量名：LVT/LVTT 命中（`jvm_has_debug/jvm_debug`，name_type=DEBUG）优先；否则 `stack_val_name` 按类型生成 `i0/str0/l0/dbl0/...`，类名生成 `lowerLastWord` 或 `xxxVarN`（`expression_local_variable.c:gen_variable_name`）。
- 声明位置：`analyse_local_variables`（expression_local_variable.c:166）：`variables_scope` 为每个非参数、非 catch 参数的变量名收集 [首次 store, 最后 store/use] 表达式区间和 stores bitset；`variables_declaration`：若首次 store 与最后使用在同一节点或"祖先兄弟"关系 → 首次 store 处就地声明（`declarations` bitset，STORE 输出时带类型前缀）；否则找两者最近公共祖先节点，`insert_declaration_to` 插入独立 DECLARATION 表达式（`T name;`），并避开 else-if/catch/finally/case 子节点边界。
- 同 slot 不同区间不同变量 → 天然由"不同 jd_val + 不同 name"表达；SSA φ（`ssa.c`）用于跨块合并名字/stack_var（`sform_local_variable_phi_node_dfs_copies` 把 φ 参数侧的 jd_val 名字与 stack_var 统一）。

**jcdc 建议**：采用 Vineflower 的 (slot, version) 身份 + φ 图 + mergeVars 方案（正确性最好），LVT 名字按区间绑定到版本；声明放置算法用 Vineflower 的 setVarDefinitions + garlic 的"公共祖先插声明"兜底。

---

## 4. 特殊构造的还原

### 4.1 Lambda 与方法引用（invokedynamic + LambdaMetafactory）

字节码形态：`invokedynamic #idx` → 常量池 `CONSTANT_InvokeDynamic{bootstrap_method_attr_index, name_and_type}` → `BootstrapMethods[i] = {MethodHandle → LambdaMetafactory.metafactory/altMetafactory, args=[MethodType(samMethodType), MethodHandle(implMethod), MethodType(instantiatedMethodType)]}`。

**Vineflower**：
- 识别（main/rels/LambdaProcessor.java）：类版本 ≥52 且有 BootstrapMethods；bsm ref 的 classname==`java/lang/invoke/LambdaMetafactory` 且 name∈{metafactory, altMetafactory} → 该 bsm 索引进 lambdaMethods 位图。扫描所有指令找 `invokedynamic` 且 `invoke_dynamic.index1`（bsm 索引）命中 → 建 `ClassNode(Type.LAMBDA)`：
  - `lambdaInformation{content_class_name/method_name/method_descriptor/method_invocation_type(=MethodHandle.reference_kind), method_name(sam 名), method_descriptor}`；
  - **方法引用判定** `is_method_reference = 内容类 != 当前类 || 内容方法非 synthetic`（javac 为 lambda 体生成的 `lambda$foo$0` 是 synthetic；用户已有方法被引用则非 synthetic）；
  - 捕获参数 = invokedynamic 的调用参数（静态捕获）；lambda 节点的 simpleName = `外层类##Lambda_bsmIdx_cpIdx`，注册进 mapRootClasses。
- 输出（InvocationExprent.toJava + ClassWriter.classLambdaToJava/methodLambdaToJava）：
  - `is_method_reference` → `X::m`（静态/构造器 `X::new`；实例接收者形式 `expr::m`——instance 表达式在前）；
  - 否则 lambda：单表达式体（内容方法只有一条 return/throw）→ `(a, b) -> expr` 或 `a -> expr`；块体 → `(a, b) -> { ... }`；参数名取自内容方法的 VarProcessor（NestedClassProcessor.setLambdaVars 把外围方法中捕获变量名映射进 lambda，保证一致）；无参 `() ->`；单参数可省括号（按选项）。
  - 泛型：用 samMethodType/instantiatedMethodType 对内容方法签名做类型替换后输出。
- 匿名类 vs lambda：`NewExprent.isLambda()`（ClassNode LAMBDA）与 `isAnonymous()`（ANONYMOUS）分路输出。

**garlic**（jvm/jvm_lambda.c + jvm_expression_builder.c:follow_lambda）：
- `identify_lambda_expression`：同款判定（LambdaMetafactory.metafactory/altMetafactory + bsm args≥3 + args[1] 是 MethodHandle）→ `jd_lambda{exp, target_method(jd_method_sig{kind, class_name, name, descriptor})}`。
- `follow_lambda`：若目标方法就在**当前类**（按名字+描述符索引匹配）→ 立即递归 `jvm_method` 反编译目标方法体，`build_lambda_expression` 把 INVOKE 表达式改写为 `JD_EXPRESSION_LAMBDA{method(已反编译), lambda, descriptor, is_static(kind==6)}`；目标方法标记 `METHOD_STATE_LAMBDA`（类级输出时跳过）。
- 输出（transformer/lambda.c）：`method==NULL`（外部类方法引用）→ `Class::name` 或 `arg0::name`（kind 非 static 时接收者是第一个参数）；synthetic 方法（lambda 体）→ `(p0, p1) -> { <递归输出方法体> }`；非 synthetic 且 instance → `arg0::name`。
- **字符串拼接 indy**（jvm_lambda.c:identify_string_concat_expression）：bsm 是 `StringConcatFactory.makeConcatWithConstants/makeConcat` → 解析 recipe：`num_bootstrap_arguments==1` 时 args[0] 是 recipe 字符串，`\x01`=动态参数占位、`\x02`=常量占位（常量在后续 bsm args）；逐段生成 `JD_EXPRESSION_STRING_CONCAT{list}`，输出 `a + "lit" + b`。

**Vineflower concat**（ConcatenationHelper，§3b 已述）：java9+ indy recipe 解析（TAG_ARG='\u0001'、TAG_CONST='\u0002'，makeConcat 无 recipe 时全 \x01）+ java8 `StringBuilder.append` 链收缩（`isAppendConcat`：`sb.append(x)` 链 + `toString()` + `new StringBuilder(...)`），统一折叠为 `FunctionExprent(STR_CONCAT)` 左结合链；前两个操作数若无 String 则补 `""` 常量（保证 `1+2+"x"` 语义正确——实际上按字节码顺序拼接天然正确，补 "" 是为了纯对象相加场景）。

### 4.2 switch on String

javac 模式：`switch(s)` 编译为两级——第一级 `switch(s.hashCode())`：每个 case 是 `if (s.equals("lit")) tmp = k;`（hash 冲突时是 else-if 链），default 不落赋值；第二级 `switch(tmp)`：k → 原 case 体。

**Vineflower `SwitchHelper.trySimplifyStringSwitch`**（modules/decompiler/SwitchHelper.java:219 + 内部 StringSwitch 匹配器 :1023-1114）识别四种形态（record 类型）：
- `Split`：第一个 switch 的唯一 REGULAR 后继是第二个 SwitchStatement；
- `InlineSplit`：第二个 switch 内联在第一个的 default 目标；
- `NullableSplit`（J17 preview 风格）：外层 `if (s != null) {switch1} else {tmp = -1}` + 第二 switch（-1 → null case）；
- `Merged`：单 switch，case 体直接是 `equals` 判断 + return/break（eclipse 风格/简单情形）。
校验 `isValid`：第一 switch 头必须是 `s.hashCode()` InvocationExprent；每个 case（含 else-if 链）是 `if (s.equals("lit")) { tmp = k; }` 或 `if (...) break;`（k 与第二 switch 的 case 值对应）；中间变量 tmp 只被这两个 switch 使用（`findSyntheticDupVar/removeSyntheticDupVar` 处理编译器 dup 出的临时变量）。
还原：第二 switch 的选择子换成 `s`；case 值从 `getStringSwitchCaseMap`（tmp=k → "lit"）反查替换；NullableSplit 加 `null` case；删除第一 switch、中间赋值、包裹 if。

**garlic**：**未实现**字符串 switch 还原（grep 无 hashCode）——`jd_exp_switch` 只保留 int key。jcdc 应按 Vineflower 的 Split/Merged 两种主形态实现。

### 4.3 switch on Enum

javac 模式：外部类（或合成类 `Outer$1`）持有 `static final int[] $SwitchMap$pkg$Enum`，其 `<clinit>` 中 `$SwitchMap[Enum.C.ordinal()] = k`；调用点 `switch($SwitchMap[e.ordinal()])`。

**Vineflower `SwitchHelper.simplify`**（:40）：
1. switch 头是 `ArrayExprent(arr=FieldExprent($SwitchMap...) 或 InvocationExprent(合成类的 $values 风格方法), index=InvocationExprent(e.ordinal()))`；
2. 取持有类的 `<clinit>` 的 MethodWrapper（`shouldInitEarly` 保证这类合成类**先于**外围类反编译），遍历其中 `arr[Enum.C.ordinal()] = k` 赋值建 `mapping: k → FieldExprent(Enum.C)`（Kotlin 变体：先赋局部变量再赋字段，用 `getAssignmentsOfWithinOneStatement` 跟踪）；
3. 用 mapping 替换 caseValues（找不到的 k：-1 → null case（J21 nullable enum switch），或 tableswitch 空洞 → 复制邻近 key；仍失败 → 输出 `$VF: Unable to simplify switch on enum` 注释并放弃）；
4. 选择子替换为 `e`（ordinal 调用的 instance）；若中间变量只剩这一处引用则删除其赋值；
5. `simplifySwitchOnEnumJ21`：Java 21 直接 `switch(e){case C ->}` 编译形态的处理。
注意该 pass 跑两次：主循环后一次 + `ClassWriter.invokeProcessors` 里类级再跑一次（依赖类已全部反编译）。

**garlic**：`expression_enum.c` 只做枚举类本身的还原，switch-on-enum 未实现（case 输出原始 int）。

### 4.4 Enum 类还原

**Vineflower**：
- `EnumProcessor.clearEnum`：隐藏 `values()[]E`、`valueOf(String)E`、synthetic `[LE;` 字段（$VALUES）；每个 `<init>` 首条若是 `Enum.<init>(name, ordinal)`（`Statements.isInvocationInitConstructor` 沿类链确认）→ 删除。
- `InitializerProcessor.extractStaticInitializers`：`<clinit>` 中 `CONST = new E("CONST", i, args...) {body}` 形式的 putstatic → 抽成字段的 `staticFieldInitializers`；ClassWriter.writeField 对 ACC_ENUM 字段输出 `NewExprent(setEnumConst(true))` → `CONST(args...) { body },`（枚举常量列表，最后一个 `;`），并把构造参数里的 `"CONST", i` 两个合成前缀参数跳过（`appendParamList` 的 isEnum mask）。
- 枚举构造器输出时隐藏 name/ordinal 两参数（writeMethodParameterHeader isEnum 分支）。

**garlic**（expression_enum.c）：`optimize_enum_fields`（隐藏 $VALUES 与 `public static final E X` 常量字段）、`optimize_enum_methods`（隐藏 values/valueOf/$values）、`optimize_enum_statics`（`<clinit>` 里 `putstatic X = INITIALIZE(E, ["X", i, ...args])` 序列聚合成一个 `JD_EXPRESSION_ENUM{list of {name, args}}`，最后一条保留为输出锚点；`list->len>2` 时输出 `NAME(args[2..])`，否则 `NAME`）、`optimize_enum_constructor`（nop 掉构造器里的 `<init>` 调用即 Enum.super）。输出即 `A, B(1, "x"), C;` 形式。

### 4.5 内部类 / 匿名类 / 局部类

**Vineflower**：
- InnerClasses 属性缺失/损坏时的推断（ClassesProcessor.loadClasses + `isAnonymous`）：
  - 类型判定链：simpleName==null → ANONYMOUS；有 EnclosingMethod(methodName!=null) → LOCAL；否则 MEMBER；
  - 匿名类校验 `isAnonymous(cl, enclosingCl)`：只能有一个"源"（单接口或单父类且父类为 Object）；扫描外围类（限定 EnclosingMethod 指明的方法）所有指令，对该类的引用只允许**一次** `new/anewarray/multianewarray`；出现 checkcast/instanceof/getstatic/putstatic 引用或多次 new → 降级为 LOCAL；
  - `VALIDATE_INNER_CLASSES_NAMES` 选项：MEMBER 类必须满足 `innerName == enclosingName + '$' + simpleName`，否则剔除（防混淆器伪造 InnerClasses）。
- 构造器捕获分析（main/rels/NestedClassProcessor.java）：
  - `getMaskLocalVars(wrapper)`：对匿名/局部类的构造器，用 DirectGraph 分析"参数 i 存入 synthetic final 字段 f"（`getEnclosingVarField`：找 `this.f = param` 模式，f 判定 `possiblySyntheticField`=private+final(+synthetic) 且名字形如 `this$0/val$xxx`）→ 得到 mask（哪些构造参数是外围实例/捕获变量）；
  - `insertLocalVars`：外围类调用点 `new Inner(a, b, captured)` → 按 mask 把参数分为 enclosing this、捕获变量；捕获变量重命名对齐（外围方法中的变量名 → 匿名类中 `val$name` 去掉前缀），要求外围变量 effectively final；
  - `insertNestedClass`：InnerClasses 缺失时，按 `EnclosingMethod` 属性/构造器 `this$0` 类型/名字 `Outer$1` 模式把类挂回正确父节点（`checkNotFoundClasses`）；
  - `setLocalClassDefinition`：局部类定义点=外围方法中 `new X(...)` 出现处，声明输出在该语句前。
- `NestedMemberAccess.propagateMemberAccess`：识别 `access$000/100/200...`（静态合成桥：get/set field、invoke）→ 调用点直接改写为字段访问/方法调用，桥方法隐藏；Java 11+ nest-based access 时这些桥不存在，直接放行私有跨类访问。
- 输出：MEMBER 类在 writeClass 里按 nested 递归输出在类体内；ANONYMOUS 在 `new` 表达式处内联类体（NewExprent.toJava → ClassWriter.writeClass(node, buf, indent) 带 anonymousClassType）；LOCAL 在定义语句处输出 `class X { ... }`。

**garlic**：jar 级预处理（jar/jar.c）：扫描 jar 条目，按名字 `Outer$Inner`/`Outer$1` 建 `jd_jar_entry{is_inner, is_anoymous, parent, inner_classes[], anoymous_classes[]}` 树；反编译外围类时遇到 `invokespecial Outer$1.<init>` → `build_anonymous_expression`（jvm_expression_builder.c:226）：目标类是 synthetic + 名字在外围类的匿名/内部列表中 → 递归反编译该类（`jar_entry_anonymous_analyse`），INVOKE 改写为 `JD_EXPRESSION_ANONYMOUS{cname=接口或父类, jfile=已反编译类}`，输出 `new I(args) { ...类体... }`，并把该条目从待输出列表移除。**单 class 文件（无 jar 上下文）时匿名类无法内联**（build_anonymous_expression 直接 return）。InnerClasses 属性 garlic 解析了但主要用于访问标志；this$0 推断未实现。

### 4.6 Record（60+）

**Vineflower**：`StructRecordAttribute` → `StructRecordComponent{name, descriptor, signature, attributes}`；
- 类定义：`record Name(components) extends/implements`（writeClassDefinition :715-773，components 由 `RecordHelper.appendRecordComponents` 输出，含泛型/注解/varargs 末组件）；record 隐式 final+static（局部场景）；不输出 `extends java.lang.Record`；
- 隐藏合成成员：`RecordHelper.isHiddenRecordMethod`——`toString()/equals(Object)/hashCode()` 若方法体是"单条 return InvocationExprent(ObjectMethods)"（invokedynamic ObjectMethods bootstrap 或超类调用）则隐藏；字段与 component 一一对应则隐藏（isHiddenRecordField）；
- 紧凑构造器：`fixupCanonicalConstructor/isCompactCanonicalConstructor`——规范构造器体若无 `this.f = p` 赋值序列（被 javac 自动补全）→ 输出 `Name(components) { body }` 紧凑形式。

**garlic**：解析了 Record 属性（metadata.c:1254）但未见输出端还原。jcdc 按 Vineflower 实现。

### 4.7 Sealed（59 预览 / 61 正式）

**Vineflower**：`StructPermittedSubclassesAttribute` → 类定义前缀 `sealed`/`non-sealed`（writeClassDefinition :668-670,725-728：有 PermittedSubclasses 且非空 → sealed + `permits A, B`（appendFQClassNames）；无该属性但**父类/父接口是 sealed**（`isSuperClassSealed` 沿层次查，版本 ≥ hasSealedClasses）且自身非 final → `non-sealed`）。enum 不加 sealed 修饰。

### 4.8 Assert

模式：`if (!$assertionsDisabled) { if (!cond) throw new AssertionError(msg); }`，`$assertionsDisabled` 是类合成 static final boolean 字段，`<clinit>` 里 `= !E.class.desiredAssertionStatus()`。

**Vineflower `AssertProcessor`**（modules/decompiler/AssertProcessor.java）：
- `getHoldingClass`：从 ClassNode 的 nested 中找"合成类只含 `<clinit>` + 若干 Z 字段"（ClassesProcessor.shouldInitEarly 提前反编译它），或直接当前类；key=`$assertionsDisabled`；
- `buildAssertions(root)`：找到该字段的 putstatic（在 `<clinit>`）→ 记 holding class；`replaceAssertions` 遍历语句：IfStatement 条件是 `!field`（`isAssertionField`：getstatic 该字段 + BOOL_NOT，或 `field == true/false` 变体）且 if/else 体是 `throw new AssertionError(...)`（`isAssertionError`：ExitExprent THROW ← InvocationExprent INIT of java/lang/AssertionError）→ 组装 `AssertExprent(cond, msg)`；
- `getAssertionExprent` 处理三种形态：throw 在 if 体（cond 取反）、throw 在 else 体（cond 原样）、**赋值断言** `if (!$AD) { boolean b = cond; if (!b) throw ...; }`（res.assignment，把 b 的定义并入 assert 条件）；
- `cleanInterfaceStaticInitializer`：接口的 `<clinit>` 只剩该字段赋值时整个隐藏。
- 输出：`assert cond;` / `assert cond : msg;`。

**garlic**（expression_assert.c）：节点级模式——外层 IF 的首表达式条件含 `$assertionsDisabled`（`if_expression_is_assert` 检查 GET_STATIC/PUT_STATIC 名字），IF_FALSE 子节点里有内层 IF 且其 false 分支是 `athrow(new AssertionError())` → 外层 if 表达式改写为 `JD_EXPRESSION_ASSERT`（data=内层条件），删除两层节点；`<clinit>` 里的 `$assertionsDisabled = ...` putstatic nop 掉。

### 4.9 synchronized

模式：`monitorenter; try { body; monitorexit; } catch(any) { monitorexit; athrow; }`。

**Vineflower**：DomHelper.buildSynchronized（§3c）在结构化阶段把 `[monitorEnter 块] + CatchAll(handler 含 monitorExit)` 组为 SynchronizedStatement；`markMonitorexitDead` 把体内/handler 中的 monitorexit 标死（ExprProcessor 遇到 `stat.isRemovableMonitorexit()` 时 MonitorExprent.setRemove → 不输出）；`removeSynchronizedHandler` 删掉 handler 子结构；`SynchronizedHelper.cleanSynchronizedVar`（monitor 对象是临时栈变量时内联）、`insertSink`（表达式形式的 monitor 赋回）。输出 `synchronized (obj) { ... }`。Kotlin/Scala 缺失 monitorexit 的 synchronized 范围由 `DeadCodeHelper.extendSynchronizedRangeToMonitorexit` 在 CFG 层修补。

**garlic**（expression_synchronized.c:identify_synchronized）：EXCEPTION 节点前一条有效表达式是 MONITOR_ENTER 且该节点有 FINALLY 子节点 → 删除 finally 子节点、递归 nop 掉 try 内所有 MONITOR_EXIT、把 TRY 节点改为 `JD_NODE_SYNCHRONIZED`（param_exp=monitor 对象）。

### 4.10 try-with-resources

**J7/J8 模式**：`try { R r = ...; body } finally { if (r != null) r.close(); }`（异常路径还嵌套 if-throw-suppressed）。Vineflower `TryWithResourcesProcessor.makeTryWithResource(CatchAllStatement)`（:24）：handler 恰好两语句、first 是 `if (r != null) { if (...) r.close(); } else { r.close(); }` 双 if 结构（J8 完整形态）→ 提取 `isCloseable`（invokevirtual/interface `close()V`，且 receiver 实现 AutoCloseable——需要类路径）→ 找资源定义（`findResourceDef`：try 前的 `r = new/init` 赋值）→ 资源表达式移入 `CatchStatement.resources`，删除 finally 结构。
**J11+ 模式**（`makeTryWithResourceJ11`，:107）：javac 11 生成 `catch (Throwable t) { r.addSuppressed... }` 或直接在 catch 里 `r.close()`，资源变量 dup 方式不同；识别 CatchStatement 的 handler 尾部 close 调用 + null 检查变体（nullable 资源）。
`TryHelper.mergeTry`：嵌套 TWR（`try (a; b)` javac 会编译成嵌套 try）合并为单条多资源；资源赋值右值是 null 常量时 `fixResourceAssignment` 从前置块找回真实初始化。

**garlic**：未实现 TWR（finally 保留原样输出）。

### 4.11 do-while vs while vs for 区分

- Vineflower：结构化后循环一律先是 INFINITE；`matchWhile`（首块是"跳出型 if"）→ WHILE；`makeDoWhileLoops` 在主循环**最后**跑（注释明言"必须最后，否则会破坏 for 的形成"）：尾部"条件回跳 if"（ifedge=BREAK & elseedge=CONTINUE 或对称形态）→ DO_WHILE；WHILE 再经 `matchForEach/matchFor` 升级为 FOR_EACH/FOR（§3c）。判据本质：**条件在体前=while、体后=do-while**；both（首尾都有 if）时以 while 优先（do-while 的 continue 前驱检查 `set.remove(last); !set.isEmpty()` 排除多回跳）。
- garlic：`identify_loop_type` 顺序 for → do-while → while → infinite；`is_post_condition`（条件在 last 块）+ `can_write_condition`（无其它入口跳入条件块）决定 do-while；`count_jumps(loop, true_target, last_exp)==0` 保证出口唯一。

### 4.12 其它模式速查

- **`new` 三段式**：`new C; dup; invokespecial C.<init>` → Vineflower 在 ExprProcessor 中 NewExprent 先入栈，`<init>` 调用时被 InvocationExprent(INIT) 吸收（NewExprent.setConstructor），最终 `NewExprent.toJava` 输出 `new C(args)`；garlic `identify_initialize`（UNINITIALIZE + 后续 consumes 同一 stack_var 的 invokespecial → INITIALIZE）。
- **数组初始化器**：`new T[n]{...}`：Vineflower NewExprent.lstArrayElements（`InitializerProcessor`/SimplifyExprentsHelper 收集连续 aastore）；garlic `identify_array_initialize`。
- **`++/--`**：Vineflower PPandMMHelper（`x = x + 1` 且 x 无其它干涉 → IPP/PPI；`a[i++]` 形态经 dup 模式识别）；garlic IINC 直接映射 `iinc_type pre/post`。
- **boxing/unboxing 隐藏**：InvocationExprent.isBoxingCall/isUnboxingCall（`Integer.valueOf(I)`/`intValue()` 等）+ `markUsingBoxingResult`，输出时按上下文省略（SecondaryFunctionsHelper 亦参与）。
- **`x.class`**：Java 1.4 `class$java$lang$String` 静态合成字段 → ClassReference14Processor；1.5+ `ldc Ljava/lang/Class;` 常量直接输出。
- **接口 default/static/private 方法**：无需特殊还原（直接输出方法体）；注意 9+ 接口私有方法、ACC_STATIC 在接口中的合法性按版本放宽。
- **varargs 还原**：方法 ACC_VARARGS(0x0080) 且末参数 arrayDim>0 → 输出 `T... name`（ClassWriter:1435-1460：取组件类型 + `...`；generic 签名时 `GenericMethodDescriptor` 末参数同样处理）；调用点：InvocationExprent.appendParamList 中若实参数组是"数组初始化器"形态则摊平为逗号参数，否则输出 `new T[]{...}`/原数组变量（必要时 cast `(T[])`）。
- **桥接方法**：ACC_BRIDGE(0x0040)+ACC_SYNTHETIC → 默认隐藏（ClassWriter 按选项）。
- **condy（CONSTANT_Dynamic，55+）**：CondyHelper.simplifyCondy。

---

## 5. 类型与泛型

### 5.1 描述符与类型系统

- 字段/方法描述符解析：Vineflower `struct/gen/FieldDescriptor.parseDescriptor`、`MethodDescriptor.parseDescriptor`（`(params)ret`，params 逐个 `VarType.parse`）；garlic `decompiler/descriptor.c:descriptor_tokenizer/expand_descriptor`（jd_descriptor{list(参数类型串), str_return, index}）。
- **VarType**（struct/gen/VarType.java）：`(CodeType type, int arrayDim, String value)`。CodeType：BYTE/CHAR/DOUBLE/FLOAT/INT/LONG/SHORT/BOOLEAN/NULL/OBJECT/VOID/**UNKNOWN**/**GENVAR**/BYTECHAR/SHORTCHAR（后两个是"可能是 byte 或 char"的合并态，类型推断中间结果）。派生属性：`typeFamily(TypeFamily)`、`stackSize`（long/double=2 其余 1，用于 slot 占位）、`isGeneric`（GenericType 子类）。`resizeArrayDim/defineObjectType/getCommonSupertype`（格：int 族最小上界、对象类用 StructContext.findCommonAncestor）。
- **GenericType extends VarType**（struct/gen/generics/GenericType.java）：`parent(外层类类型，嵌套泛型), arguments(List<VarType>), wildcard(WILDCARD_EXTENDS/SUPER/UNBOUND/NO)`。`parse(signature)` 递归下降解析签名字符串：`[...`数组、`T<name>;` 类型变量、`L<pkg/Class<args>.Inner<args>;` 类类型（**内部类泛型的 `.` 分隔外层链**要特殊处理）、`*`/`+X`/`-X` 通配符、基本类型单字符。

### 5.2 Signature 属性语法（JVMS §4.7.9.1）

```
ClassSignature:  [FormalTypeParameters] SuperclassSignature {SuperinterfaceSignature}
FormalTypeParameters: '<' FormalTypeParameter+ '>'
FormalTypeParameter: Identifier [':' FieldTypeSignature] {':' FieldTypeSignature}   # 第一个是 extends bound，其余是 interface bounds
MethodSignature: [FormalTypeParameters] '(' {FieldTypeSignature} ')' Result {ExceptionType}
FieldSignature:  FieldTypeSignature
FieldTypeSignature: ClassTypeSignature | ArrayTypeSignature | TypeVariableSignature
ClassTypeSignature: 'L' [PackageSpecifier] SimpleClassTypeSignature {ClassTypeSignatureSuffix} ';'
SimpleClassTypeSignature: Identifier [TypeArguments]
TypeArguments: '<' TypeArgument+ '>'   TypeArgument: ['+'|'-'] FieldTypeSignature | '*'
Result: FieldTypeSignature | 'V'
ExceptionType: '^' (ClassTypeSignature | TypeVariableSignature)
```

- Vineflower 解析器：`GenericMain.parseClassSignature/parseMethodSignature/parseFieldSignature/parseFormalParameters` + `GenericType.getNextType`（按括号深度切一个完整类型 token）。产物：`GenericClassDescriptor{fparameters, fbounds, superclass, superinterfaces, genericType}`、`GenericMethodDescriptor{fparameters, fparameterbounds, parameterTypes, returnType, exceptionTypes}`、`GenericFieldDescriptor{type}`。**解析失败仅 warn 并回退描述符类型**（永不崩溃）。
- garlic 解析器：`decompiler/signature.c`（type_sig AST：class_signature/method_sig/field_type_sig{type=简单类/数组/通配/类型变量, path(内部类链), wildcard{super/extends bound}}），输出端 `field_type_sig_to_s/formal_type_parameters_to_s/interfaces_to_s` 渲染 `List<? extends X>`、`<T extends A & B>` 等。
- 使用规则：
  1. 类/字段/方法有 Signature → 优先用泛型类型输出（`ClassWriter.getFieldTypeData`、`writeMethodParameterHeader` 用 GenericMethodDescriptor）；
  2. **校验一致性**：签名参数个数必须与描述符一致（garlic `create_method_defination` 显式检查 `sig->parameter_types->size == desc->list->size`，enum 构造器减 2；不一致回退原始描述符）——混淆器/编译器 bug 常产生坏签名；Vineflower 用 `GenericsChecker`（struct/gen/generics/GenericsChecker.java）验证泛型参数数量匹配，不匹配则整体丢弃泛型；
  3. 原始类型 vs 泛型类型：擦除后一致时输出泛型；表达式层 `GenericsProcessor.qualifyChains`（modules/decompiler/GenericsProcessor.java）在链式调用中传播泛型实参（`InvocationExprent.genericArgs/genericsMap` + `getInferredExprType(upperBound)`：用方法声明签名 + 接收者类型做替换求实例化类型），失败回退擦除类型并可能加 cast。

### 5.3 表达式中的类型推断

- **整数常量提升/收窄**：iconst/bipush/sipush 产生 INT 常量；赋给 byte/short/char/boolean 目标（变量类型、字段描述符、参数描述符、返回类型、数组元素类型 bastore/castore/sastore、ireturn 目标类型）时 `ConstExprent.adjustConstType` 收窄并按目标类型打印（char → `'a'`）。
- **int 隐藏类型**（boolean/byte/char/short 在栈上都是 int）：
  - Vineflower：来源优先级 = LVT 描述符 > 字段/参数/返回描述符 > 指令形态（baload→BYTE 等）> 常量上下文；`VarTypeProcessor.process`（vars/VarTypeProcessor.java）用 CheckTypesResult（各 Exprent.checkExprTypeBounds 产生的"下界/上界"约束，如赋值 right 的类型是 left 的下界）+ `VarType.getCommonSupertype` 求每个 (slot,version) 的最终类型；BYTECHAR/SHORTCHAR 表达不确定态，最后按使用点裁决。
  - garlic：`jvm_int_type_analyze`（jvm/jvm_type_analyse.c:73）在模拟期逐指令修正：ireturn 返回类型非 int、invoke 参数描述符是 Z/B/C/S、putfield/putstatic 字段是 Z/B/C/S、xastore、istore 到已知窄类型局部变量 → `add_stack_val_type` 记录，`jvm_fix_type` 统一回写 jd_val 的 cname。
- **null 类型**：aconst_null → VarType.VARTYPE_NULL；参与 getCommonSupertype 时被任意对象类型吸收；输出 `null` 无需 cast（除非歧义重载）。
- **cast 插入**：赋值/传参/返回处表达式类型 ≠ 目标类型且非安全 widening → `ExprProcessor.getCastedExprent` 包 `FunctionExprent(CAST)`；`canonicalizeCasts` 去重嵌套同类型 cast；checkcast 指令产生的显式 CAST 保留（除非冗余：目标类型已知一致时可删，见 SimplifyExprentsHelper）。

---

## 6. 输出 / 打印

### 6.1 Vineflower

- **TextBuffer**（util/TextBuffer.java）：StringBuilder 包装 + 三个增值能力：
  1. `appendBytecodeMapping(BitSet)`：记录源码偏移 → 原始字节码偏移（配合 BytecodeMappingTracer/BytecodeSourceMapper 输出行号映射，IDE 导航用）；
  2. token 流（util/token/*）：标识符/字面量/注释打标，支持重命名一致性与语法高亮导出（jcdc 可省）；
  3. **NewlineGroup reformat**：`pushNewlineGroup(indent, extra)/appendPossibleNewline/popNewlineGroup` 标记"可折行点"（长参数列表、长条件），全文生成后 `reformat()` 递归检查组内最长行超过 `PREFERRED_LINE_LENGTH`（默认 160）才把 possible-newline 替换为真实换行+缩进，并同步修正字节码映射偏移（offsetMapping）。
- **缩进**：`appendIndent(indent)` = INDENT_STRING（默认 3 空格，可配）× indent；每个 toJava(indent) 自带。
- **运算符优先级**：`FunctionType.precedence`（§3b 表）。规则：`Exprent.getPrecedence()`；二元输出时若操作数 precedence > 自己的 → 加括号（FunctionExprent.toJava 里 wrapOperandString 比较；CAST 特殊：`((T) x).f` 需要外层括号时用 appendInstCast/encloseWithParens）。赋值表达式作右值时加括号。三元/布尔运算按表。
- **import 收集**（main/collectors/ImportCollector.java）：
  - `getShortName(fullName, imported)`：查 ClassNode（内部类 → `Outer.Inner` 形式；匿名 → `<unrepresentable>`）；不在 map 的类按包名规则：`java.lang.*`、同包、当前类内部类 → 免 import 直接用简单名；冲突（同简单名不同包，`collectConflictingShortNames` 预扫描 nested 与常用名）→ 保留全限定名；否则登记 `mapSimpleNames: simple → full` 并返回简单名；
  - 字段名遮蔽：类层次中所有字段名集合 `setFieldNames`，简单名撞字段名 → 用全限定（getShortNameInClassContext）；
  - `writeImports`：排序输出 `import a.b.C;`（选项 REMOVE_IMPORTS 可全用 FQN）；嵌套类 import 用 `Outer.Inner`；
  - `appendCastTypeName/appendTypeName`（TextBuffer 上的扩展，ClassWriter/TextUtil）统一走 ImportCollector。
- **类输出顺序**（ClassWriter.writeClass）：javadoc/注解 → 类声明（modifiers 顺序由 MODIFIERS map 固定：public/protected/private/abstract/static/final/sealed/non-sealed/strictfp + class/interface/enum/record/@interface）→ 类型参数 `<T extends ...>` → extends（record/enum 省略 java.lang.Record/java.lang.Enum）→ implements → permits → `{` → 枚举常量 → 字段 → 构造器/方法 → 嵌套类 → `}`。方法输出：注解、modifiers（接口中省略冗余 public/abstract，按 CLASS_ALLOWED/EXCLUDED 位掩码）、泛型形参、返回类型、名字、参数（varargs/注解/名字）、throws、体或 `;`。

### 6.2 garlic

- 无缓冲抽象，直接 `fprintf(FILE*)`；缩进 `get_node_ident(node)`（node 深度 × 4 空格）；import 用 trie（`class_import` 排除 java/lang、同包、基本类型；`trie_leaf_to_stream` 输出）；package 行 `/`→`.`。表达式→字符串双通道：`exp_to_s`（返回 string，用于嵌套拼接）与 `exp_*_to_stream`（直接写流，用于语句级）——Rust 里统一用 `String` 或 `fmt::Write` 即可，不需要双通道。
- **括号处理较弱**：靠 transformer 里手写括号（如 operator.c 对子表达式恒加括号或按 op 判断），没有系统 precedence 表——jcdc 应采用 Vineflower 的 precedence 方案。

---

## 7. 类间依赖（为什么需要 ClassPool）

**Vineflower `StructContext`**（struct/StructContext.java）＝全局类池：
- `classes: Map<qualifiedName, StructClass>`（ConcurrentHashMap，**懒加载**：`getClass(name)` miss 时从 units/legacy provider `tryLoadClass`；own（要输出的）与 library（只解析不输出）分开，`badlyPlacedClasses` 处理路径与包名不符的类）；
- 关键查询：
  - `instanceOf(valclass, refclass)`：沿 superClass 链 + 接口递归判断（**接口默认方法、abstract 判定、AutoCloseable(TWR)、Iterable(foreach) 检查都靠它**）；
  - `findCommonAncestor(a, b)`：类型推断求最小上界（`VarType.getCommonSupertype` 的对象分支）；
  - `getClass(name).getMethod(name, desc)/getMethodRecursive`：成员解析——`StructClass.getMethodRecursive(name, descriptor)` 沿父类链找方法（用于 `Statements.isInvocationInitConstructor`（Enum.<init> 判定）、record ObjectMethods、boxing 调用识别、泛型方法签名查找 `InvocationExprent.getInferredExprType` 中 `hierarchy` 的构建）；
  - `loadAbstractMetadata`：从外部载入 abstract 参数名元数据（可选）。
- 用途汇总（哪些 pass 需要池）：泛型推断（父类/接口签名）、TWR（AutoCloseable）、switch-on-enum（**另一个类**的 `<clinit>` switchmap）、内部类/匿名类（外围类的字节码扫描）、lambda 内容方法（同类，但经 mapRootClasses）、`Objects.requireNonNull` 等 JDK API 模式识别、类层次相关 cast 消除（SimplifyExprentsHelper 判断 cast 是否冗余：目标类型是表达式类型的祖先 → 删）。
- **INCLUDE_ENTIRE_CLASSPATH / INCLUDE_JAVA_RUNTIME 选项**：把 JDK（JrtFinder 读 jrt-fs 或 modules 镜像）加入池，显著提高泛型/TWR 还原率——jcdc 应支持"附带 classpath"输入。

**成员解析细节**（对应 CFR 的 getMemberBySignature 概念）：Vineflower 没有单一入口，而是 `StructClass.getField(name,desc)/getMethod(key)`（VBStyleCollection 以 `name + ' ' + descriptor` 为 key，`InterpreterUtil.makeUniqueKey`）+ `getMethodRecursive` 向上遍历；调用点解析在 `InvocationExprent.getDesc()`（拿 StructMethod 做泛型/描述符校验）与 `ExprUtil`。jcdc 建议实现统一的 `resolve_member(class, name, desc, kind) → Option<MemberRef>`，先本类、再父类链、再接口（含 default 方法冲突时的 JLS 规则可简化为"最先找到"）。

**garlic**：无类池。跨类信息仅 jar 条目表（inner/anonymous 归属）+ 常量池里的类名/描述符字符串。后果：无法做泛型链推断、TWR、switch-on-enum 还原、cast 冗余消除；这也是它输出质量低于 Vineflower 的主要原因之一。**jcdc 必须做类池**（哪怕只索引签名不存字节码：HashMap<ClassName, ClassMeta{flags, super, interfaces, fields[], methods[], signature}>，库类懒解析）。

---

## 8. 对 Rust 实现的建议

### 8.1 数据结构

- **Arena + index 为主，Rc 少用**：
  - 指令：`Vec<Instr>` + `InstrId(u32)`（解码后不变，天然 arena）；每指令 `old_offset: u32, opcode: OpCode(规范化的枚举), operands: SmallVec<[i32;4]>, group: InstrGroup`。
  - 基本块：`Vec<BasicBlock>`，边用 `Vec<BlockId>`（succs/preds/succ_exceptions）+ 单独的 `Vec<ExceptionRange{from,to,handler,types:Option<Vec<ClassNameId>>}>`。CFG 频繁改边（merge/inline finally），用 id 而非引用可以避免生命周期地狱。
  - 表达式树：这是最需要 Rc/arena 权衡的地方。Vineflower 到处 `copy()`/`replaceExprent`（结构共享少、改写多）→ Rust 建议 `ExprentId` + `Arena<Exprent>`，`Exprent` 子节点存 id；`copy()` = 深拷贝到新 id（ arena 分配便宜）；`replace(old,new)` = 父节点字段改 id。避免 `Rc<RefCell>` 的循环引用与 borrow 冲突（parent 指针用裸 id 回指）。
  - Statement 树：同样 arena + id；`stats: Vec<StatId>, first/post/parent: StatId`。边 `StatEdge{kind, source, dest, closure: StatId, exceptions}` 存全局 `Vec<StatEdge>` + 每 statement 的 succ/pred 边 id 列表（Vineflower 的 mapSuccEdges 按类型分桶可直接照搬）。
  - 变量：`(slot: u16, version: u32)` 作 VarVersionPair（Copy + Hash），全局 `VarProcessor` 结构持 name/type map。
  - 字符串/类名：`StringInterner` → `Sym(u32)`，类名统一内部形式（`a/b/C`），比较/哈希全用 Sym。
- **上下文**：不要学 Vineflower 的 ThreadLocal 静态上下文；定义 `struct Ctx<'a>{ pool: &'a ClassPool, opts: &'a Options, imports: ImportCollector, counters: Counters, logger }` 显式传参（或用 thread-local 只在并行按类反编译时各自持有）。
- **错误策略**：每方法 `Result<RootStat, DecompileError>`；失败输出注释 + javap 风格字节码 dump（照抄 Vineflower 的容错输出，反编译器口碑取决于失败时的表现）。

### 8.2 阶段取舍（可直接照搬 / 可简化 / 可后置）

**照搬（正确性关键）**：
1. class 解析 + 常量池两阶段 resolve + 属性表（§2）；指令规范化（iconst_x→bipush 等）；
2. CFG 构建（findStartInstructions/connectBlocks/exception ranges/dummy exit/mergeBasicBlocks）；
3. DomHelper 结构化全套（含 GeneralStatement 子图分解、IrreducibleCFGDeobfuscator、扩展后支配）——这是 Vineflower 相对其它开源反编译器最大的护城河，自创算法风险极高；
4. FinallyProcessor（指令级 equalInstructions + Area 删除 + semaphore 兜底）；
5. ExprProcessor 栈模拟 + 栈变量（STACK_BASE 技巧）+ SSA 稀疏版本化 + StackVarsProcessor 内联；
6. SwitchHelper（enum switchmap + string switch 四形态）、ConcatenationHelper（indy recipe + StringBuilder 链）、AssertProcessor、LambdaProcessor、EnumProcessor、InitializerProcessor、TryWithResourcesProcessor；
7. VarDefinitionHelper（声明放置 + mergeVars + LVT 传播）；
8. ImportCollector + precedence 输出。

**可简化（一期）**：
- jsr/ret 内联：Java 6- 才需要；先做"检测到 → 方法降级输出字节码注释"（garlic 策略），二期补 Vineflower 的 splitJsrRange；
- 泛型链推断（GenericsProcessor/getInferredExprType）：先输出擦除类型 + Signature 直译（类/字段/方法声明处用泛型，表达式内部不推断），二期补；
- 模式匹配（16+/21+ 的 instanceof pattern、switch pattern、record pattern）：整个 IfPatternMatchProcessor/SwitchPatternMatchProcessor 后置；
- switch 表达式/yield（SwitchExpressionHelper）后置；
- TypeAnnotations、token 流、字节码→行号映射、NewlineGroup reformat：后置（先固定缩进 4 空格 + 简单行宽）；
- 混淆对抗（IrreducibleCFG、ExceptionDeobfuscator 的 handleMultipleEntry、deobfuscator 包）：保留骨架但可容忍降级输出；
- 变量命名美化：先用 `var{slot}_{version}` + LVT 名，garlic 的按类型命名（str0/i0）可选。

**架构建议**：
- pass 组织学 garlic：`fn decompile_method(...) -> RootStat` 内显式顺序调用 + 主循环 `loop { let mut changed = false; changed |= pass_x(...); if !changed { break } }`；每个 pass 是纯函数 `(root: &mut Arena<Stat>, ctx) -> bool`，便于单测（Vineflower 的 testData 目录有海量对照用例可借用：`Vineflower/vineflower/testData`）；
- 双表示调试：学 Vineflower 的 DecompileRecord/DotExporter，每个 pass 后可 dump（dot + 文本），这是此类项目调试的生命线；
- 并行：按类并行（类池只读共享，ImportCollector/输出 per-class），Vineflower 的 ThreadLocal 上下文在 Rust 中换成 per-task Ctx 即可；
- 测试基线：先跑通 javac 生成的常见模式（用 JDK 自己的类库做语料），再上混淆样本。

---

## 9. garlic src/jvm 与 src/decompiler 文件清单（Rust 移植索引）

### src/jvm/（JVM 前端：把 jclass_file + 字节码变成后端 IR）

| 文件 | 职责 |
|---|---|
| `jvm_decompile.c/h` | 类级管线入口 `jvm_analyse_class_file(_inside)`；装填指令/方法判定函数表（前端-后端解耦的 vtable） |
| `jvm_class.c/h` | 类级模型构建：Signature 收集（类/字段/方法）、access flags → 修饰符字符串、字段模型 `jvm_fields` |
| `jvm_method.c/h` | 方法级入口 `jvm_method`；指令解码 `init_method_instructions`（含 wide/invoke/multianewarray/switch padding 的参数长与 push/pop 数计算）、跳转图 `init_jvm_instruction_graph`、异常表 `init_method_exception_table`、access flags 输出、table/lookupswitch 目标解析 |
| `jvm_ins.c/h` | 指令分类谓词库（is_return/is_goto/is_conditional_jump/is_store/is_load/is_switch/is_compare/is_block_start/end…）、操作数提取（slot/offset）、指令模式匹配 `match_instruction_patten`、`jvm_rename_goto2return` |
| `jvm_ins_helper.h` | 更细的 inline 谓词（is_xiload/is_boolean_const/is_wide/is_multianewarray/switch padding 计算等） |
| `jvm_ins_action.c` | dup/dup_x1/dup_x2/dup2/dup2_x1/dup2_x2/swap/pop/pop2 的栈搬运实现（`build_jvm_ins_*_action`），及各类指令的 stack_out 填充 |
| `jvm_simulator.c/h` | 抽象解释主循环 `jvm_simulator`：worklist 传播 stack_in/stack_out、局部变量槽管理（store/load 时变量身份判定）、handler 入口注入异常对象栈、栈变量(stack_var)分配、调用 sform（SSA） |
| `jvm_expression_builder.c/h` | `instruction_to_expression`：每条指令 → jd_exp 的大 switch（const/load/store/算术/cast/cmp/if/switch/goto/invoke/new/field/array/monitor/return/athrow/dup/pop…）；匿名类识别 `build_anonymous_expression`；lambda 挂接 `follow_lambda/build_lambda_expression` |
| `jvm_optimizer.c/h` | 方法级优化 pass 的总调度 `optimize_jvm_method`（§1.2 的完整 pass 顺序清单在此） |
| `jvm_exception.c/h` | `jvm_method_exception_edge`：CFG 两遍构建 + handler 范围识别 + 异常表清洗 + `inline_finally_block`（finally 复制体的指令级反向比对删除 `reverse_compare_instruction`） |
| `jvm_lambda.c/h` | invokedynamic 解析：BootstrapMethods 读取、LambdaMetafactory 判定、目标 MethodHandle → jd_method_sig；StringConcatFactory recipe 解析 `identify_string_concat_expression`（\x01/\x02 占位符） |
| `jvm_type_analyse.c/h` | int 隐藏类型修正 `jvm_int_type_analyze/jvm_fix_type`（返回/参数/字段/xastore/istore 上下文的 boolean/byte/char/short 推断）；LVT/LVTT 调试信息匹配（`match_local_variable/jvm_debug`） |
| `jvm_descriptor.c/h` | 常量池描述符 → jd_descriptor 缓存（jvm_descriptor） |
| `jvm_annotation.c/h` | 类/字段/方法/参数注解 → 可打印字符串（含 element_value 各 tag 的渲染） |

### src/decompiler/（后端中立核心：dalvik 也复用）

| 文件 | 职责 |
|---|---|
| `structure.h` | **全部核心数据结构**：jd_ins/jd_exp(60+ 表达式类型枚举)/jd_var/jd_val/jd_stack/jd_bblock(nblock/eblock 联合体)/jd_edge/jd_node(20+ 节点类型)/jd_loop/jd_switch/jd_if_branch/jd_mix_exception/jd_method/jsource_file |
| `control_flow.c/h` | CFG 构建 `cfg_create`（normal 块按"异常上下文/块边界"切分、exception 块、enter/exit/exception_exit 哑块、连边规则）、块查询（by_id/offset/contains_idx）、异常块降级 `cfg_remove_exception_block`、块复制 `dup_basic_block`、SCC 声明 |
| `dominator_tree.c/h` | 迭代法支配树 + 支配边界 + `compute_dominates_block`（按需支配集）、dominates 判定 |
| `scc.c/h` | Tarjan 强连通分量 |
| `exception.c/h` | 异常表清洗大全：handler 结束识别（支配集连续块）、同 handler try 合并、交叠 try/try、try/handler 修正、finally 归组 `flatten_exceptions` → mix_exceptions{try,catches,finally}、重复 finally 删除、`pullin_block_jump_into_exception_try_block` |
| `ssa.c/h` | 局部变量 use/def/活跃性/到达定义数据流 + 支配边界插 φ + SSA 重命名（counter+stack 经典算法）+ φ 侧栈值合并；栈变量跨块统一 `sform_stack_variable_insert_phi_v2` |
| `stack.c/h` | jd_stack/jd_val 工具：克隆、方法入口栈（this+参数按描述符布槽，long/double 双槽）、栈变量命名 `stack_val_name`、按 idx/ins 查 var |
| `instruction.c/h` | 指令级工具（nop/unreachable/copy 标记、块起止判定辅助） |
| `descriptor.c/h` | 描述符 tokenizer/展开、descriptor→类型枚举 |
| `signature.c/h` | 泛型签名解析（class/method/field signature → type_sig AST）与渲染（`field_type_sig_to_s` 等） |
| `klass.c/h` | 类名工具（simple/package/array 名）、import trie、类/字段/方法声明字符串生成、类级 node 树 `class_create_blocks` |
| `method.c/h` | 方法声明字符串（有/无 Signature 两路、enum 构造器 -2 参数特判）、lambda 形参表 `create_lambda_defination` |
| `field.c/h` | 字段标记（hide/assert 字段） |
| `expression.c/h` | jd_exp 工具（类型谓词 exp_is_*、nop/empty 标记、取表达式 by idx/offset） |
| `expression_node.c/h` | node 树构建 `create_node_tree`（root/basic-block/exception 节点、按包含关系挂接、排序）与查询（ancestor/contains/scope） |
| `expression_node_param.c/h` | 给 IF/WHILE/DO_WHILE/FOR/CATCH/SYNCHRONIZED 节点装配 param_exp（条件/monitor 对象/异常变量） |
| `expression_branches.c` | if/else-if/else/switch-case 识别与节点化（`identify_branches`，§3c） |
| `expression_loop.c` | 循环识别（支配边界自环 header、自然循环体回收、条件块/出口块分析）`identify_loop` |
| `expression_loop_type.c` | for/do-while/while/infinite 分型 `identify_loop_type`（§3c） |
| `expression_if.c` | 条件取反 `negative_if_expression`、布尔条件化简、if-break/if-continue |
| `expression_logical.c` | &&/|| 钻石合并、反向逻辑、cmp-after-if（lcmp+fcmp 模式并入条件） |
| `expression_ternary.c` | 三元表达式识别（块级 + 条件内） |
| `expression_new.c` | new+dup+invokespecial → INITIALIZE；数组初始化器识别 |
| `expression_array.c` | `new T[]{a,b,...}` 聚合 |
| `expression_assign.c` | `x=y` 局部变量赋值合并（复制传播） |
| `expression_chain.c` | 赋值链 `a=b=c`、栈变量定义链、链式 store |
| `expression_inline.c` | 栈变量内联 `inline_variables`（def/use/dup 计数判定）+ round2 宽松内联 |
| `expression_copy_propgation.c` | dup 出的局部变量复制传播 |
| `expression_goto.c` | goto → break/continue/删除（`optimize_goto_expression`，目标与循环/case 关系分析） |
| `expression_return.c` | 末尾冗余 return nop |
| `expression_assert.c` | $assertionsDisabled 双层 if 模式 → ASSERT（§4.8） |
| `expression_enum.c` | enum 类还原（字段/方法隐藏、<clinit> 常量聚合，§4.4） |
| `expression_synchronized.c` | monitorenter + finally(monitorexit) → SYNCHRONIZED 节点（§4.9） |
| `expression_exception.c` | 异常块输出优化、空 catch 体识别、synchronized 变量整理 |
| `expression_local_variable.c` | 变量重命名/作用域/声明位置（§3e garlic 侧） |
| `expression_inner_class.c/h` | **空文件（预留占位）**，内部类逻辑实际在 jar/jar.c 与 jvm_expression_builder.c 的匿名类识别里 |
| `expression_remove_useless.c/h` | 无用表达式清理 |
| `expression_analyse.c/h` | 方法级类型分析入口 |
| `expression_visitor.c/h` | 表达式树遍历器（收集 stack_var/local_variable 引用、for 循环变量集） |
| `expression_writter.c/h` | **输出器**：类 node 树递归打印 `writter_for_class`（package/import/注解/字段/方法/if/switch/case/loop/catch/synchronized 各 write_* 函数）、调试打印（表达式+SSA+CFG dump） |
| `transformer/transformer.c/h` | 表达式打印总分派 `exp_to_s/expression_to_stream` |
| `transformer/*.c`（48 个） | 每种表达式类型的 `exp_<kind>_to_s` + `exp_<kind>_to_stream` 打印器：const/local_variable/stack_var/stack_value/lvalue/operator/single_operator/single_list/compare(在 operator 内)/assignment/assignment_chain/store/declaration/define_stack_var/invoke{static,virtual,special,interface,dynamic}/lambda/anonymous/get_field/put_field/get_static/put_static/new_array/array_load/array_store/arraylength/uninitialize/initialize(instanceof 也在)/cast/iinc/if/if_break/switch/goto/return/ternary/logic_not/athrow/monitorenter/monitorexit/str_concat/enum/assert/loop{while,do_while,for}/local_variable/const 等 |

### src/analyzer/（注意：**与 JVM 反编译无关**）

`jd_analyzer.c/jd_string_analyzer.h/jd_api_matcher.c/h` 是 **DEX/APK 字符串与 API 行为分析**（URL/crypto/设备标识/权限字符串标记、API 调用图分类），服务于 garlic 的安卓分析模式；jcdc 不需要移植。

---

## 10. Vineflower 版本兼容处理速查

**版本常量**（code/BytecodeVersion.java:101-122）：`PREVIEW=65535(minor)`；`MAJOR_1_0_2=45, MAJOR_1_2=46, MAJOR_1_3=47, MAJOR_1_4=48, MAJOR_5=49, MAJOR_6=50, MAJOR_7=51, MAJOR_8=52, MAJOR_9=53, MAJOR_10=54, MAJOR_11=55, MAJOR_12=56, MAJOR_13=57, MAJOR_14=58, MAJOR_15=59, MAJOR_16=60, MAJOR_17=61, MAJOR_18=62, MAJOR_19=63, MAJOR_20=64, MAJOR_21=65`。（66/67=Java22/23 需自行延伸。）

**特性谓词 → 使用点**：

| 谓词 | 版本条件 | 使用位置/行为分支 |
|---|---|---|
| `predatesJava()` | major≤45 && minor≤2 | 极老文件容错 |
| `hasJsr()` | major≤50 | MethodProcessor:107 → `graph.inlineJsr`（jsr/ret 内联） |
| `has14ClassReferences()` | major≤48 | ClassWriter.invokeProcessors → ClassReference14Processor（`class$` 合成字段 → `X.class`） |
| `hasEnums()` | major≥49 | enum 相关还原的前提 |
| `hasOverride()` | major≥49 | @Override 输出策略 |
| `hasInvokeDynamic()` | major≥51 | StructMethod.parseBytecode:220（invokedynamic 按 4 字节解码，否则按无效指令）；ExprProcessor:487（低版本忽略 indy） |
| `hasLambdas()` | major≥52 | LambdaProcessor.processClass 提前 return（不扫 lambda） |
| `hasIndyStringConcat()` | major≥53 | MethodProcessor:253 → ConcatenationHelper.simplifyStringConcat（否则只走 StringBuilder 链收缩） |
| module-info | major≥53 && ACC_MODULE && Module 属性 | ClassesProcessor.processClass:449 特判；ClassWriter.moduleInfoToJava/writeModuleInfoBody（requires/exports/opens/uses/provides） |
| 接口私有方法 | major≥53 | 无显式分支（正常方法输出；ACC_PRIVATE 在接口中合法化由版本隐含） |
| `hasNewTryWithResources()` | major≥55 | TryHelper.makeTryWithResourceRec：J11 形态 `makeTryWithResourceJ11(CatchStatement)` vs J7/8 形态 `makeTryWithResource(CatchAllStatement+finally)` |
| nest-based access | major≥55 | Vineflower 仅解析 NestHost 属性（NestMembers 为 TODO）；NestedMemberAccess 对 access$ 桥的消除在低版本生效，55+ 通常无桥 |
| `hasSealedClasses()` | major≥61，或 major≥59 且 minor==PREVIEW | ClassWriter:668-670 sealed/non-sealed/permits 输出；isSuperClassSealed 检查 |
| record | major≥60（属性存在即处理） | StructRecordAttribute/StructRecordComponent；ClassWriter:715+ record 声明；RecordHelper 隐藏合成成员/紧凑构造器 |
| `hasLocalEnumsAndInterfaces()` | major≥60 | ClassesProcessor:334 局部类允许 ACC_INTERFACE/ACC_ENUM（LOCAL 类 access 掩码放宽） |
| `hasIfPatternMatching()` | major≥60 | MethodProcessor:337 → IfPatternMatchProcessor.matchInstanceof（instanceof 模式变量） |
| `hasSwitchExpressions()` | major≥60 | SwitchExpressionHelper（yield/箭头 switch） |
| `hasSwitchPatternMatch()` | major≥65，或 major≥61 且 minor==PREVIEW（previewReleased(17,21)） | SwitchPatternMatchProcessor.processPatternMatching（case 模式/guard/穷尽性） |
| `hasRecordPatternMatching()` | major≥65 | record 解构模式（PatternExprent） |
| nullable enum switch | J21 形态 | SwitchHelper.simplifySwitchOnEnumJ21 + case -1 → null |

**匿名/局部类标志修正也依赖版本**：ANONYMOUS 去 ACC_STATIC（编译器 bug 容错）；LOCAL 仅保留 ABSTRACT|FINAL（16+ 再加 INTERFACE|ENUM|（enum 时 STATIC））——ClassesProcessor.loadClasses:317-341。

---

## 附：jcdc 推荐的最小可行管线（MVP）

```
parse_class(字节) -> ClassFile{pool(两阶段resolve), fields, methods, attrs}
ClassPool(懒加载索引: 自己+classpath)
per class:
  build_class_node_tree(InnerClasses/EnclosingMethod/名字模式)
  collect_lambdas(BootstrapMethods)
  per method:
    decode_instructions(规范化+group) -> CFG(块/边/异常range/dummy exit) -> merge_blocks
    clean_exceptions(循环range/空range/多入口)
    structure(DomHelper 六模式 + 不可约分裂) -> Statement 树
    finally(指令比对去复制 | semaphore) ; synchronized 识别
    flatten -> DirectGraph -> 栈模拟建 Exprent(栈变量)
    SSA 版本化 -> 内联栈变量 -> ++/--
    indy concat / assert
    主循环{ loops(while/foreach/for/dowhile), if 合并(&&/||/else-if/三元), labels,
             secondary functions, try 增强(TWR), inline single blocks, exit 收拢 }
    switch 还原(enum switchmap / string) ; return 调整 ; 变量定义/命名/LVT
  类级: 初始化器抽取, enum 清理, record 修正, access$ 消除, 嵌套类变量捕获
write: ClassWriter(TextBuffer 简化版) + ImportCollector + precedence 括号
```

失败兜底（任何阶段 panic/Err）：输出 `// $jcdc: failed` + 原始方法 javap 风格 dump，继续下一个方法。
