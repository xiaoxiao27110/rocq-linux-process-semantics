(** * DecodeC: ARMv8.0-A (AArch64) top-level instruction decoder wrapper.
    In ARM64 all instructions are fixed 32-bit (4 bytes). *)

From Stdlib Require Import ZArith Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode.

Local Open Scope Z_scope.

Definition decode_any (w : bv 32) : option (instr * Z) :=
  match decode w with
  | Some i => Some (i, 4%Z)
  | None => None
  end.

(** Architecturally permanently undefined instruction in ARMv8.0-A:
    UDF #imm16 (bits [31:16] = 0x0000). *)
Definition is_defined_illegal (w : bv 32) : bool :=
  Z.eqb (bv_unsigned (bits 16 16 w)) 0.
