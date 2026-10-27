(** * Decode: the ARMv8.0-A (AArch64 / Phytium D2000) 32-bit instruction decoder. *)

From Stdlib Require Import ZArith NArith Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.

Local Open Scope Z_scope.
Local Open Scope bool_scope.

(** Decode ARM64 logical immediate bitmask from (sf, N, immr, imms). *)
Definition decode_bitmask (sf n_bit : bool) (immr imms : Z) : option word :=
  let '(esize, len) :=
    if n_bit then
      if sf then (64, imms + 1) else (0, 0)
    else if imms <? 32 then (32, imms + 1)
    else if imms <? 48 then (16, imms - 32 + 1)
    else if imms <? 56 then (8, imms - 48 + 1)
    else if imms <? 60 then (4, imms - 56 + 1)
    else if imms <? 62 then (2, imms - 60 + 1)
    else (0, 0) in
  if (esize =? 0) || (len <=? 0) || (esize <=? len) then None
  else
    let welem := Z.ones len in
    let r := immr mod esize in
    let rot :=
      if r =? 0 then welem
      else Z.lor (Z.shiftr welem r)
                 (Z.land (Z.shiftl welem (esize - r)) (Z.ones esize)) in
    let v1 := if esize <=? 2  then Z.lor rot (Z.shiftl rot 2) else rot in
    let v2 := if esize <=? 4  then Z.lor v1 (Z.shiftl v1 4) else v1 in
    let v3 := if esize <=? 8  then Z.lor v2 (Z.shiftl v2 8) else v2 in
    let v4 := if esize <=? 16 then Z.lor v3 (Z.shiftl v3 16) else v3 in
    let v5 := if esize <=? 32 then Z.lor v4 (Z.shiftl v4 32) else v4 in
    let res := if sf then v5 else Z.land v5 (Z.ones 32) in
    Some (Z_to_bv 64 res).

Definition decode (w : bv 32) : option instr :=
  let rd := bits 0 5 w in
  let rn := bits 5 5 w in
  let rm := bits 16 5 w in
  let rt := bits 0 5 w in
  let sf := bit 31 w in
  (* 1. PC-relative addressing: ADR / ADRP (bits[28:24] = 10000) *)
  if bv_unsigned (bits 24 5 w) =? 16 then
    let is_page := bit 31 w in
    let immlo := bits 29 2 w in
    let immhi := bits 5 19 w in
    let imm21 := bv_concat 21 immhi immlo in
    let imm :=
      if is_page then sext 64 (bv_concat 33 imm21 (Z_to_bv 12 0))
      else sext 64 imm21 in
    Some (A64_Adr is_page rd imm)
  (* 2. Add/subtract (immediate): bits[28:23] = 100010 *)
  else if bv_unsigned (bits 23 6 w) =? 34 then
    let is_sub := bit 30 w in
    let setflags := bit 29 w in
    let sh := bit 22 w in
    let imm12 := bits 10 12 w in
    let imm :=
      if sh then zext 64 (bv_concat 24 imm12 (Z_to_bv 12 0))
      else zext 64 imm12 in
    Some (A64_AddSubImm sf is_sub setflags rd rn imm)
  (* 3. Logical (immediate): bits[28:23] = 100100 *)
  else if bv_unsigned (bits 23 6 w) =? 36 then
    let opc := bits 29 2 w in
    let n_bit := bit 22 w in
    let immr := bits 16 6 w in
    let imms := bits 10 6 w in
    match decode_bitmask sf n_bit (bv_unsigned immr) (bv_unsigned imms) with
    | Some bmask => Some (A64_LogicalImm sf opc rd rn bmask)
    | None => None
    end
  (* 4. Move wide (immediate): bits[28:23] = 100101 *)
  else if bv_unsigned (bits 23 6 w) =? 37 then
    let opc := bits 29 2 w in
    let hw := bits 21 2 w in
    let imm16 := bits 5 16 w in
    if negb sf && bit 22 w then None
    else if bv_unsigned opc =? 1 then None
    else Some (A64_MoveWide sf opc rd imm16 hw)
  (* 5. Bitfield: bits[28:23] = 100110 *)
  else if bv_unsigned (bits 23 6 w) =? 38 then
    let opc := bits 29 2 w in
    let immr := bits 16 6 w in
    let imms := bits 10 6 w in
    (* N (bit 22) must equal sf; with sf = 0, immr<5> and imms<5> must be 0. *)
    if bv_unsigned opc =? 3 then None
    else if negb (Bool.eqb (bit 22 w) sf) then None
    else if negb sf && ((32 <=? bv_unsigned immr) || (32 <=? bv_unsigned imms)) then None
    else Some (A64_Bitfield sf opc rd rn immr imms)
  (* 6. Extract: bits[28:23] = 100111 *)
  else if bv_unsigned (bits 23 6 w) =? 39 then
    let imms := bits 10 6 w in
    (* op21 (bits 30:29) = 00, o0 (bit 21) = 0, N = sf, and sf = 0 needs imms < 32. *)
    if negb (bv_unsigned (bits 29 2 w) =? 0) || bit 21 w then None
    else if negb (Bool.eqb (bit 22 w) sf) then None
    else if negb sf && (32 <=? bv_unsigned imms) then None
    else Some (A64_Extract sf rd rn rm imms)
  (* 7. Unconditional branch (immediate): B / BL (bits[30:26] = 00101) *)
  else if bv_unsigned (bits 26 5 w) =? 5 then
    let is_link := bit 31 w in
    let imm26 := bits 0 26 w in
    let offset := sext 64 (bv_concat 28 imm26 (Z_to_bv 2 0)) in
    Some (A64_BImm is_link offset)
  (* 8. Compare and branch: CBZ / CBNZ (bits[30:25] = 011010) *)
  else if bv_unsigned (bits 25 6 w) =? 26 then
    let is_nz := bit 24 w in
    let imm19 := bits 5 19 w in
    let offset := sext 64 (bv_concat 21 imm19 (Z_to_bv 2 0)) in
    Some (A64_CBZ sf is_nz rt offset)
  (* 9. Test and branch: TBZ / TBNZ (bits[30:25] = 011011) *)
  else if bv_unsigned (bits 25 6 w) =? 27 then
    let is_nz := bit 24 w in
    let bit_pos := bv_concat 6 (bits 31 1 w) (bits 19 5 w) in
    let imm14 := bits 5 14 w in
    let offset := sext 64 (bv_concat 16 imm14 (Z_to_bv 2 0)) in
    Some (A64_TBZ is_nz rt bit_pos offset)
  (* 10. Conditional branch: B.cond (bits[31:24] = 01010100, bit[4] = 0) *)
  else if (bv_unsigned (bits 24 8 w) =? 0x54) && negb (bit 4 w) then
    let imm19 := bits 5 19 w in
    let cond := bits 0 4 w in
    let offset := sext 64 (bv_concat 21 imm19 (Z_to_bv 2 0)) in
    Some (A64_BCond cond offset)
  (* 11a. Exception generation: SVC / BRK (bits[31:24] = 11010100) *)
  else if bv_unsigned (bits 24 8 w) =? 0xd4 then
    let opc := bv_unsigned (bits 21 3 w) in
    let imm16 := bits 5 16 w in
    let ll := bv_unsigned (bits 0 2 w) in
    if negb (bv_unsigned (bits 2 3 w) =? 0) then None   (* op2 must be 000 *)
    else if (opc =? 0) && (ll =? 1) then Some (A64_Svc imm16)
    else if (opc =? 1) && (ll =? 0) then Some (A64_Brk imm16)
    else None
  (* 11b. System / Hints / Barriers / TPIDR_EL0: bits[31:24] = 11010101 *)
  else if bv_unsigned (bits 24 8 w) =? 0xd5 then
    let top27 := bv_unsigned (bits 5 27 w) in
    if top27 =? 0x6a9de82 then Some (A64_MrsTpidr rt)      (* mrs Xt, tpidr_el0 *)
    else if top27 =? 0x6a8de82 then Some (A64_MsrTpidr rt) (* msr tpidr_el0, Xt *)
    else
      let top20 := bv_unsigned (bits 12 20 w) in
      let op2 := bv_unsigned (bits 5 3 w) in
      (* HINT space (every CRm:op2, unallocated hints execute as NOP in
         ARMv8.0) and the DSB / DMB / ISB barriers, all with Rt = 11111.
         CLREX (op2 = 010) is NOT a NOP — it clears the exclusive monitor —
         and is left undecoded (fail closed). *)
      if negb (bv_unsigned rt =? 31) then None
      else if top20 =? 0xd5032 then Some A64_Nop
      else if (top20 =? 0xd5033) && ((op2 =? 4) || (op2 =? 5) || (op2 =? 6)) then Some A64_Nop
      else None
  (* 11c. Unconditional branch (register): BR / BLR / RET (bits[31:25] = 1101011) *)
  else if bv_unsigned (bits 25 7 w) =? 0x6b then
    let op := bits 21 2 w in
    (* opc (bits 24:21) in {BR, BLR, RET}; op2 = 11111, op3 = 000000, op4 = 00000
       (anything else is ERET / DRPS / the ARMv8.3 pointer-auth forms or unallocated). *)
    if (bv_unsigned (bits 21 4 w) <=? 2) && (bv_unsigned (bits 16 5 w) =? 31)
       && (bv_unsigned (bits 10 6 w) =? 0) && (bv_unsigned (bits 0 5 w) =? 0)
    then Some (A64_BReg op rn) else None
  (* 12a. Logical (shifted register): bits[28:24] = 01010 *)
  else if bv_unsigned (bits 24 5 w) =? 10 then
    let opc := bits 29 2 w in
    let shift_ty := bits 22 2 w in
    let inv_rm := bit 21 w in
    let imm6 := bits 10 6 w in
    if negb sf && (32 <=? bv_unsigned imm6) then None
    else Some (A64_LogicalShifted sf opc inv_rm shift_ty rd rn rm imm6)
  (* 12b. Add/subtract (shifted or extended register): bits[28:24] = 01011 *)
  else if bv_unsigned (bits 24 5 w) =? 11 then
    let is_sub := bit 30 w in
    let setflags := bit 29 w in
    if negb (bit 21 w) then
      let shift_ty := bits 22 2 w in
      let imm6 := bits 10 6 w in
      if bv_unsigned shift_ty =? 3 then None
      else if negb sf && (32 <=? bv_unsigned imm6) then None
      else Some (A64_AddSubShifted sf is_sub setflags shift_ty rd rn rm imm6)
    else
      let option_ty := bits 13 3 w in
      let imm3 := bits 10 3 w in
      if negb (bv_unsigned (bits 22 2 w) =? 0) then None
      else if 4 <? bv_unsigned imm3 then None
      else Some (A64_AddSubExtended sf is_sub setflags option_ty rd rn rm imm3)
  (* 12c. Add/subtract (with carry): bits[28:21] = 11010000 *)
  else if bv_unsigned (bits 21 8 w) =? 208 then
    let is_sub := bit 30 w in
    let setflags := bit 29 w in
    if negb (bv_unsigned (bits 10 6 w) =? 0) then None
    else Some (A64_AddSubCarry sf is_sub setflags rd rn rm)
  (* 12d. Conditional compare: bits[28:21] = 11010010 *)
  else if bv_unsigned (bits 21 8 w) =? 210 then
    let is_sub := bit 30 w in
    let is_imm := bit 11 w in
    let cond := bits 12 4 w in
    let nzcv_imm := bits 0 4 w in
    (* S = 1, o2 (bit 10) = 0, o3 (bit 4) = 0. *)
    if negb (bit 29 w) || bit 10 w || bit 4 w then None
    else Some (A64_CondCompare sf is_sub is_imm cond rn rm nzcv_imm)
  (* 12e. Conditional select: bits[28:21] = 11010100 *)
  else if bv_unsigned (bits 21 8 w) =? 212 then
    let op := bit 30 w in
    let cond := bits 12 4 w in
    let o2 := bit 10 w in
    (* S = 0, op2<1> (bit 11) = 0. *)
    if bit 29 w || bit 11 w then None
    else Some (A64_CondSelect sf op o2 cond rd rn rm)
  (* 12f. Data-processing (2-source & 1-source): bits[28:21] = 11010110 *)
  else if bv_unsigned (bits 21 8 w) =? 214 then
    let opcode := bits 10 6 w in
    let op := bv_unsigned opcode in
    if bit 29 w then None   (* S = 1 is unallocated *)
    else if negb (bit 30 w) then
      (* UDIV SDIV LSLV LSRV ASRV RORV; CRC32 (optional in ARMv8.0) is not modeled. *)
      if (op =? 2) || (op =? 3) || ((8 <=? op) && (op <=? 11))
      then Some (A64_DataProc2 sf opcode rd rn rm) else None
    else
      (* opcode2 (bits 20:16) = 0; RBIT REV16 REV/REV32 REV(64, sf = 1 only) CLZ CLS. *)
      if negb (bv_unsigned (bits 16 5 w) =? 0) then None
      else if 5 <? op then None
      else if (op =? 3) && negb sf then None
      else Some (A64_DataProc1 sf opcode rd rn)
  (* 12g. Data-processing (3-source): bits[28:24] = 11011 *)
  else if bv_unsigned (bits 24 5 w) =? 27 then
    let op54 := bits 29 2 w in
    let op31 := bits 21 3 w in
    let o0 := bit 15 w in
    let ra := bits 10 5 w in
    let o31 := bv_unsigned op31 in
    (* op54 = 00; op31 = 000 (MADD/MSUB, any sf) or 001/010/101/110 with sf = 1,
       and SMULH / UMULH (010 / 110) need o0 = 0. *)
    if negb (bv_unsigned op54 =? 0) then None
    else if (o31 =? 3) || (o31 =? 4) || (o31 =? 7) then None
    else if negb (o31 =? 0) && negb sf then None
    else if ((o31 =? 2) || (o31 =? 6)) && o0 then None
    else Some (A64_DataProc3 sf op54 op31 o0 rd rn rm ra)
  (* 12h. Load register (literal): bits[29:27] = 011, bits[25:24] = 00.
     opc 00 LDR Wt, 01 LDR Xt, 10 LDRSW, 11 PRFM (a hint: NOP).  V = 1 (SIMD/FP) is not decoded. *)
  else if (bv_unsigned (bits 27 3 w) =? 3) && (bv_unsigned (bits 24 2 w) =? 0) then
    let opc := bv_unsigned (bits 30 2 w) in
    let offset := sext 64 (bv_concat 21 (bits 5 19 w) (Z_to_bv 2 0)) in
    if bit 26 w then None
    else if opc =? 0 then Some (A64_LoadLiteral SZ4 false rt offset)
    else if opc =? 1 then Some (A64_LoadLiteral SZ8 false rt offset)
    else if opc =? 2 then Some (A64_LoadLiteral SZ4 true rt offset)
    else Some A64_Nop
  (* 13a. Load/store register pair: LDP / STP / LDPSW (bits[29:25] = 10100, bit[26] = 0) *)
  else if (bv_unsigned (bits 25 5 w) =? 20) && negb (bit 26 w) then
    let opc := bv_unsigned (bits 30 2 w) in
    let mode := bv_unsigned (bits 23 2 w) in
    let is_load := bit 22 w in
    (* opc = 01 is LDPSW, a load only: there is no STPSW. *)
    let wb := (mode =? 1) || (mode =? 3) in
    let t := bv_unsigned rt in
    let t2 := bv_unsigned (bits 10 5 w) in
    let n := bv_unsigned rn in
    if (opc =? 3) || (mode =? 0) || ((opc =? 1) && negb is_load) then None
    (* CONSTRAINED UNPREDICTABLE, which a core may resolve as UNDEFINED (Apple
       M4 does): a load with Rt = Rt2, or writeback with Rn (not SP) equal to
       Rt or Rt2.  Fail closed. *)
    else if is_load && (t =? t2) then None
    else if wb && negb (n =? 31) && ((n =? t) || (n =? t2)) then None
    else
      let imm7 := bits 15 7 w in
      let rt2 := bits 10 5 w in
      let sz := if opc =? 2 then SZ8 else SZ4 in
      let is_signed := (opc =? 1) in
      let shift := if opc =? 2 then 3 else 2 in
      let offset := Z_to_bv 64 (Z.shiftl (bv_signed imm7) shift) in
      let wback := (mode =? 1) || (mode =? 3) in
      let postindex := (mode =? 1) in
      Some (A64_LoadStorePair sz is_load is_signed wback postindex rt rt2 rn offset)
  (* 13b. Load/store register (immediate & register offset): bits[29:27] = 111, bit[26] = 0 *)
  else if (bv_unsigned (bits 27 3 w) =? 7) && negb (bit 26 w) then
    let size_bits := bv_unsigned (bits 30 2 w) in
    let opc := bv_unsigned (bits 22 2 w) in
    let sz :=
      match size_bits with
      | 0 => SZ1 | 1 => SZ2 | 2 => SZ4 | _ => SZ8
      end in
    let is_load := negb (opc =? 0) in
    let is_signed := (opc =? 2) || (opc =? 3) in
    let simm_64 := (opc =? 2) in
    (* size = 11, opc = 10 is PRFM: a hint that neither touches a register nor
       faults, so it executes as a NOP.  size in {10, 11} with opc = 11 is
       unallocated. *)
    let is_prfm := (size_bits =? 3) && (opc =? 2) in
    if bit 25 w then None   (* bit 25 = 1 is the data-processing (register) group *)
    else if (2 <=? size_bits) && (opc =? 3) then None
    else if bit 24 w then
      let imm12 := bits 10 12 w in
      let offset := Z_to_bv 64 (Z.shiftl (bv_unsigned imm12) size_bits) in
      if is_prfm then Some A64_Nop
      else Some (A64_LoadStoreImm sz is_load is_signed simm_64 false false rt rn offset)
    else if negb (bit 21 w) then
      let m2 := bv_unsigned (bits 10 2 w) in
      if m2 =? 2 then None
      else if is_prfm then (if m2 =? 0 then Some A64_Nop else None)   (* PRFUM; no writeback forms *)
      else
        let imm9 := bits 12 9 w in
        let offset := sext 64 imm9 in
        let wback := (m2 =? 1) || (m2 =? 3) in
        let postindex := (m2 =? 1) in
        (* writeback with Rn (not SP) = Rt is CONSTRAINED UNPREDICTABLE: fail closed *)
        if wback && negb (bv_unsigned rn =? 31) && (bv_unsigned rn =? bv_unsigned rt) then None
        else Some (A64_LoadStoreImm sz is_load is_signed simm_64 wback postindex rt rn offset)
    else if bv_unsigned (bits 10 2 w) =? 2 then
      let option_ty := bits 13 3 w in
      let s_scale := bit 12 w in
      (* option<1> must be 1 (UXTW, LSL/UXTX, SXTW, SXTX). *)
      if negb (bit 14 w) then None
      else if is_prfm then Some A64_Nop
      else Some (A64_LoadStoreReg sz is_load is_signed simm_64 option_ty s_scale rt rn rm)
    else None
  (* 13c. Load/store exclusive: LDXR / LDAXR / STXR / STLXR (bits[29:24] = 001000) *)
  else if bv_unsigned (bits 24 6 w) =? 8 then
    let size_bits := bv_unsigned (bits 30 2 w) in
    let sz :=
      match size_bits with
      | 0 => SZ1 | 1 => SZ2 | 2 => SZ4 | _ => SZ8
      end in
    let is_load := bit 22 w in
    let rs := bits 16 5 w in
    (* o2 = bit 23, o1 = bit 21, o0 = bit 15.
       o2 = 0, o1 = 0: LDXR / LDAXR / STXR / STLXR.
       o2 = 1, o1 = 0, o0 = 1: LDAR / STLR, a plain (single-copy atomic) load or
         store; ordering is invisible to a single-threaded model.
       o1 = 1 (LDXP / STXP / CASP) and o2 = 1, o0 = 0 (LDLAR / STLLR, ARMv8.1)
       are not decoded. *)
    if bit 21 w then None
    (* a store-exclusive with Rs = Rt or Rs = Rn (not SP) is CONSTRAINED UNPREDICTABLE *)
    else if negb (bit 23 w) then
      if negb is_load && ((bv_unsigned rs =? bv_unsigned rt)
                          || (negb (bv_unsigned rn =? 31) && (bv_unsigned rs =? bv_unsigned rn)))
      then None
      else Some (A64_LoadStoreExcl sz is_load rs rt rn)
    else if bit 15 w then Some (A64_LoadStoreImm sz is_load false false false false rt rn (Z_to_bv 64 0))
    else None
  (* 14. UDF #imm16: bits[31:16] = 0 *)
  else if bv_unsigned (bits 16 16 w) =? 0 then
    Some (A64_Udf (bits 0 16 w))
  else None.
