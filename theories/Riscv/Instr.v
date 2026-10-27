(** * Instr: ARMv8.0-A (AArch64 / Phytium D2000) instruction AST
    (preserving legacy RV64 constructors for Common proof-library compatibility). *)

From LinuxProcessSemantics.Riscv Require Import Prelude.

(** Integer register-register ops. *)
Inductive aluop : Type :=
| ALU_ADD | ALU_SUB | ALU_SLL | ALU_SLT | ALU_SLTU
| ALU_XOR | ALU_SRL | ALU_SRA | ALU_OR | ALU_AND.

(** Multiply/divide ops. *)
Inductive mulop : Type :=
| M_MUL | M_MULH | M_MULHSU | M_MULHU
| M_DIV | M_DIVU | M_REM | M_REMU.

Inductive branch_cond : Type :=
| BC_EQ | BC_NE | BC_LT | BC_GE | BC_LTU | BC_GEU.

(** Memory access sizes, in bytes. *)
Inductive msize : Type := SZ1 | SZ2 | SZ4 | SZ8.

(** A extension. *)
Inductive amoop : Type :=
| AMO_SWAP | AMO_ADD | AMO_XOR | AMO_AND | AMO_OR
| AMO_MIN | AMO_MAX | AMO_MINU | AMO_MAXU.

Inductive awidth : Type := AW | AD.

(** Zicsr. *)
Inductive csrop : Type := CSR_RW | CSR_RS | CSR_RC.

(** F/D formats and op groups. *)
Inductive ffmt : Type := FMT_S | FMT_D.
Inductive fariop : Type := F_ADD | F_SUB | F_MUL | F_DIV.
Inductive fmaop : Type := F_MADD | F_MSUB | F_NMSUB | F_NMADD.
Inductive fsgnop : Type := F_SGNJ | F_SGNJN | F_SGNJX.
Inductive fminmaxop : Type := F_MIN | F_MAX.
Inductive fcmpop : Type := F_EQ | F_LT | F_LE.
Inductive fcvt_ty : Type := FC_W | FC_WU | FC_L | FC_LU | FC_S | FC_D.
Inductive fmvdir : Type := FMV_X_F | FMV_F_X.

Inductive instr : Type :=
(* ---- ARMv8.0-A (AArch64) instructions ---- *)
| A64_AddSubImm (sf is_sub setflags : bool) (rd rn : reg) (imm : word)
| A64_LogicalImm (sf : bool) (opc : bv 2) (rd rn : reg) (bmask : word)
| A64_MoveWide (sf : bool) (opc : bv 2) (rd : reg) (imm16 : bv 16) (hw : bv 2)
| A64_Adr (is_page : bool) (rd : reg) (imm : word)
| A64_LoadLiteral (sz : msize) (is_signed : bool) (rt : reg) (offset : word)  (* LDR (literal) W/X, LDRSW (literal) *)
| A64_Bitfield (sf : bool) (opc : bv 2) (rd rn : reg) (immr imms : bv 6)
| A64_Extract (sf : bool) (rd rn rm : reg) (imms : bv 6)
| A64_AddSubShifted (sf is_sub setflags : bool) (shift_ty : bv 2) (rd rn rm : reg) (imm6 : bv 6)
| A64_AddSubExtended (sf is_sub setflags : bool) (option_ty : bv 3) (rd rn rm : reg) (imm3 : bv 3)
| A64_AddSubCarry (sf is_sub setflags : bool) (rd rn rm : reg)
| A64_LogicalShifted (sf : bool) (opc : bv 2) (inv_rm : bool) (shift_ty : bv 2) (rd rn rm : reg) (imm6 : bv 6)
| A64_CondSelect (sf op o2 : bool) (cond : bv 4) (rd rn rm : reg)
| A64_CondCompare (sf is_sub is_imm : bool) (cond : bv 4) (rn rm_or_imm : reg) (nzcv_imm : bv 4)
| A64_DataProc2 (sf : bool) (opcode : bv 6) (rd rn rm : reg)
| A64_DataProc1 (sf : bool) (opcode : bv 6) (rd rn : reg)
| A64_DataProc3 (sf : bool) (op54 : bv 2) (op31 : bv 3) (o0 : bool) (rd rn rm ra : reg)
| A64_BImm (is_link : bool) (offset : word)
| A64_BReg (op : bv 2) (rn : reg)
| A64_BCond (cond : bv 4) (offset : word)
| A64_CBZ (sf is_nz : bool) (rt : reg) (offset : word)
| A64_TBZ (is_nz : bool) (rt : reg) (bit_pos : bv 6) (offset : word)
| A64_LoadStoreImm (sz : msize) (is_load is_signed simm_64 wback postindex : bool) (rt rn : reg) (offset : word)
| A64_LoadStoreReg (sz : msize) (is_load is_signed simm_64 : bool) (option_ty : bv 3) (s_scale : bool) (rt rn rm : reg)
| A64_LoadStorePair (sz : msize) (is_load is_signed wback postindex : bool) (rt rt2 rn : reg) (offset : word)
| A64_LoadStoreExcl (sz : msize) (is_load : bool) (rs rt rn : reg)
| A64_Nop
| A64_MrsTpidr (rt : reg)
| A64_MsrTpidr (rt : reg)
| A64_Svc (imm16 : bv 16)
| A64_Brk (imm16 : bv 16)
| A64_Udf (imm16 : bv 16)
(* ---- Legacy constructors kept for Common proof-library compatibility ---- *)
| Lui (rd : reg) (imm : bv 20)
| Auipc (rd : reg) (imm : bv 20)
| Jal (rd : reg) (imm : bv 21)
| Jalr (rd rs1 : reg) (imm : bv 12)
| Branch (c : branch_cond) (rs1 rs2 : reg) (imm : bv 13)
| Load (sz : msize) (signed : bool) (rd rs1 : reg) (imm : bv 12)
| Store (sz : msize) (rs1 rs2 : reg) (imm : bv 12)
| OpImm (op : aluop) (rd rs1 : reg) (imm : bv 12)
| ShiftImm (op : aluop) (rd rs1 : reg) (shamt : bv 6)
| Op (op : aluop) (rd rs1 rs2 : reg)
| OpImm32 (rd rs1 : reg) (imm : bv 12)
| ShiftImm32 (op : aluop) (rd rs1 : reg) (shamt : bv 5)
| Op32 (op : aluop) (rd rs1 rs2 : reg)
| Fence (fm : bv 4) (pred succ : bv 4) (rd rs1 : reg)
| FenceI (rd rs1 : reg) (imm : bv 12)
| Ecall
| Ebreak
| Mul (op : mulop) (rd rs1 rs2 : reg)
| Mul32 (op : mulop) (rd rs1 rs2 : reg)
| Lr (w : awidth) (aq rl : bool) (rd rs1 : reg)
| Sc (w : awidth) (aq rl : bool) (rd rs1 rs2 : reg)
| Amo (op : amoop) (w : awidth) (aq rl : bool) (rd rs1 rs2 : reg)
| Csr (op : csrop) (rd rs1 : reg) (csr : bv 12)
| CsrI (op : csrop) (rd : reg) (uimm : bv 5) (csr : bv 12)
| FLoad (fmt : ffmt) (rd rs1 : reg) (imm : bv 12)
| FStore (fmt : ffmt) (rs1 rs2 : reg) (imm : bv 12)
| Fma (op : fmaop) (fmt : ffmt) (rd rs1 rs2 rs3 : reg) (rm : bv 3)
| Fari (op : fariop) (fmt : ffmt) (rd rs1 rs2 : reg) (rm : bv 3)
| Fsqrt (fmt : ffmt) (rd rs1 : reg) (rm : bv 3)
| Fsgnj (op : fsgnop) (fmt : ffmt) (rd rs1 rs2 : reg)
| Fminmax (op : fminmaxop) (fmt : ffmt) (rd rs1 rs2 : reg)
| Fcmp (op : fcmpop) (fmt : ffmt) (rd rs1 rs2 : reg)
| Fcvt (dst src : fcvt_ty) (rd rs1 : reg) (rm : bv 3)
| Fmv (dir : fmvdir) (fmt : ffmt) (rd rs1 : reg)
| Fclass (fmt : ffmt) (rd rs1 : reg).

Definition msize_bytes (sz : msize) : Z :=
  match sz with SZ1 => 1 | SZ2 => 2 | SZ4 => 4 | SZ8 => 8 end.
