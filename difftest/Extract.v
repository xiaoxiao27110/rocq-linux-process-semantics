Require Import Coq.extraction.ExtrOcamlBasic.
Require Import Coq.extraction.ExtrOcamlZBigInt.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.

Require Extraction.

Extraction "arm64_model.ml"
  decode
  decode_any
  is_defined_illegal
  exec
  step
  msize_bytes
  bv_key
  tget
  tset
  c_regs
  c_fregs
  c_pc
  c_fcsr
  c_resv
  Core
  rget_sp
  rget_xzr
  rset_sp
  rset_xzr
  fget
  fset
  get_n
  get_z
  get_c
  get_v
  set_nzcv.
