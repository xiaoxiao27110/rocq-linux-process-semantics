# ARM64 模型差分测试结论（主会话复核版）

> `REPORT.md` 由测试程序自动生成，其中的"分桶"标签是**按测试类别硬编码**的，不代表根因，以本文件为准。
> 原始逐例数据：容器内 `/workspace/difftest/mismatches.tsv`（每条不一致一行）。

## 测试方法
- 参照对象：Apple M4 真机（aarch64 Linux 容器内原生执行），对照手写的 Coq 模型 `theories/Riscv/{Decode,Sem,Instr}.v`（导出为 OCaml）。
- 共 298,000 例：T1 为 5 万个随机 32 位指令字；T2/T3 为各指令类定向生成，并混入边界值；T4 为非对齐访存。

## 发现并已修复的模型缺陷
| # | 缺陷 | 性质 | 修复 |
|---|---|---|---|
| 1 | 32 位版 REV64、32 位版 SMADDL/SMSUBL/SMULH/UMADDL/UMSUBL/UMULH、DP3 中 op54≠0、SMULH/UMULH 中 o0=1 被当作合法指令 | 解码过宽（真机 SIGILL，模型照常执行） | Decode.v 收紧 |
| 2 | STPSW（opc=01, L=0），size∈{2,3} 且 opc=11 的访存编码 | 同上 | Decode.v 收紧 |
| 3 | **PRFM/PRFUM 被当作 64 位有符号加载**（会覆盖 Rt，地址不合法时还会误报出错） | 语义错误 | 改为 NOP，覆盖立即数、非缩放立即数、寄存器偏移、literal 四种形式 |
| 4 | **STLR 被解码成 STXR**、LDAR 被解码成 LDXR（o2 位未检查）；LDXP/STXP 被当成单寄存器形式（o1 位未检查） | 语义错误（编译器生成的 C/C++ 原子操作常用 LDAR/STLR） | LDAR/STLR 改为普通加载/存储；o1=1 以及 ARMv8.1 的 LDLAR 不解码（按出错处理） |
| 5 | BR/BLR/RET 只检查了 opc 的 2 位，ERET/DRPS/PAC 分支变体会被误认成 BR/BLR；op2/op3/op4 未检查 | 解码过宽 | 4 位 opc 加上全部固定字段 |
| 6 | 位域/EXTR 的 N≠sf、sf=0 时移位≥32、ADD/SUB 移位类型为 11、扩展寄存器形式中 imm3>4、ADC 中 bits[15:10]≠0、CCMP 中 S=0/o2/o3、CSEL 中 S=1、DP1/DP2 中 S=1 或未分配 opcode、SVC/BRK 中 op2≠0、HINT/屏障中 Rt≠31 | 解码过宽（ARMv8.0 未分配） | Decode.v 收紧 |
| 7 | 带写回且 Rn=Rt、LDP 中 Rt=Rt2、STXR 中 Rs∈{Rt,Rn}（CONSTRAINED UNPREDICTABLE，M4 的处理是 SIGILL） | 模型说能执行，真机可能直接崩 | 不解码（按出错处理）。编译器不会生成这类编码，按出错处理没有代价 |
| 8 | CLREX 被当作 NOP（实际会清除独占监视器） | 语义错误 | 不解码（按出错处理） |
| 9 | 缺少 LDR (literal)，包括 W/X、LDRSW 和 PRFM literal（编译器常用） | 不完整 | 新增构造子 `A64_LoadLiteral` |

## 最终结果（修复后）
| 类别 | 数量 | 说明 |
|---|---|---|
| 完全一致 | 283,488 | |
| **严重（模型接受、真机 SIGILL）** | **0** | |
| 语义不一致 | 357 | **全部是测试框架造成的假差异**，见下 |
| 模型未实现（安全方向，会按出错处理） | 1,427 | SIMD/FP（含 FP/SIMD 寄存器的 ldr/str/ldp）、ARMv8.1+（LSE 原子、LDLAR、LDAPUR、STLUR、PAC、BF16）、CRC32（v8.0 中为可选扩展），以及 v8.0 的 LDTR/LDNP/STNP/LDXP/STXP |
| 对齐差异 | 12,728 | M4 允许非对齐访存，模型按"D2000 严格自然对齐"处理（见遗留问题 1） |

357 例假差异的构成：
- 347 例：随机地址的**存储**指令在真机上访问到未映射的页，触发 SIGSEGV。指令级模型没有页表，内存是否已映射由进程级的 `RiscvSemantics` / `Run` 检查，所以模型这一层报 EDone 属于预期行为。
- 10 例：随机远跳转的 B/BL 落进了测试程序**自身已映射的代码**，真机又继续执行了别的指令。

## 回归
- `LinuxProcessSem`、`EquivalenceDefinition` 全部重新编译通过。
- tinyxml2/xmltest 的 `Images`/`Statements`/`Characterise`/`Arm64Verify.v` 重新编译通过（500 步具体执行没有遇到 fault 或 unmodeled）。

## 遗留问题
1. **对齐假设需要在 D2000 上实测**：在 ARMv8 Linux 用户态下，普通内存的非对齐访问通常是允许的（SCTLR_EL1.A=0）。如果 D2000 也是这样，模型对普通 LDR/STR 的严格对齐检查就会**过严**。方向是安全的，但会把实际不会崩溃的程序判成出错。不过独占访存、acquire/release 指令在架构上始终要求对齐，这一部分是正确的。
2. 测试框架仍有少量情况没有自动排除（见上面 357 例），需要后续改进；此外它偶尔会遇到 ld.so 断言崩溃，重跑即可。
3. 以上结论都基于 M4 对照 ARMv8.0 规范。和 D2000 真机之间的差异（风险二）还没有测试。
