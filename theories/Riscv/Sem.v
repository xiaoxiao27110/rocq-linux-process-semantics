(** * Sem: ARMv8.0-A (AArch64 / Phytium D2000) & legacy RV64 semantics, as a first-order effect tree. *)

From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.

(** ** Pure helpers *)

Definition w0 : word := Z_to_bv 64 0.
Definition w1 : word := Z_to_bv 64 1.
Definition low32 (v : word) : bv 32 := bv_extract 0 32 v.
Definition is_x0 (r : reg) : bool := Z.eqb (bv_unsigned r) 0.
Definition is_r31 (r : reg) : bool := Z.eqb (bv_unsigned r) 31.

Definition alu {n : N} (shmask : Z) (op : aluop) (a b : bv n) : bv n :=
  match op with
  | ALU_ADD => a + b
  | ALU_SUB => a - b
  | ALU_SLL => a ≪ bv_and b (Z_to_bv n shmask)
  | ALU_SLT => if bv_lts a b then Z_to_bv n 1 else Z_to_bv n 0
  | ALU_SLTU => if bv_ltu a b then Z_to_bv n 1 else Z_to_bv n 0
  | ALU_XOR => bv_xor a b
  | ALU_SRL => a ≫ bv_and b (Z_to_bv n shmask)
  | ALU_SRA => bv_ashiftr a (bv_and b (Z_to_bv n shmask))
  | ALU_OR => bv_or a b
  | ALU_AND => bv_and a b
  end.

Definition alu64 : aluop → word → word → word := alu 63.
Definition alu32 : aluop → bv 32 → bv 32 → bv 32 := alu 31.

Definition branch_taken (c : branch_cond) (a b : word) : bool :=
  match c with
  | BC_EQ => bv_eqb a b
  | BC_NE => negb (bv_eqb a b)
  | BC_LT => bv_lts a b
  | BC_GE => negb (bv_lts a b)
  | BC_LTU => bv_ltu a b
  | BC_GEU => negb (bv_ltu a b)
  end.

Definition mul_div {n : N} (op : mulop) (a b : bv n) : bv n :=
  let div0 := Z.eqb (bv_unsigned b) 0 in
  match op with
  | M_MUL => a * b
  | M_MULH => bv_mulhss a b
  | M_MULHSU => bv_mulhsu a b
  | M_MULHU => bv_mulhuu a b
  | M_DIV => if div0 then Z_to_bv n (-1) else bv_quots a b
  | M_DIVU => if div0 then Z_to_bv n (-1) else bv_divu a b
  | M_REM => if div0 then a else bv_rems a b
  | M_REMU => if div0 then a else bv_modu a b
  end.

Definition amo_bytes (wd : awidth) : Z :=
  match wd with AW => 4 | AD => 8 end.

Definition amo_aligned (wd : awidth) (a : word) : bool :=
  Z.eqb (bv_unsigned a mod amo_bytes wd) 0.

(** Phytium D2000 strict natural alignment check for memory accesses. *)
Definition mem_aligned (sz : msize) (a : word) : bool :=
  Z.eqb (bv_unsigned a mod msize_bytes sz) 0.

Definition amo_val {n : N} (op : amoop) (old src : bv n) : bv n :=
  match op with
  | AMO_SWAP => src
  | AMO_ADD => old + src
  | AMO_XOR => bv_xor old src
  | AMO_AND => bv_and old src
  | AMO_OR => bv_or old src
  | AMO_MIN => if bv_lts old src then old else src
  | AMO_MAX => if bv_lts old src then src else old
  | AMO_MINU => if bv_ltu old src then old else src
  | AMO_MAXU => if bv_ltu old src then src else old
  end.

Definition csr_read_only (csr : bv 12) : bool :=
  Z.eqb (Z.land (Z.shiftr (bv_unsigned csr) 10) 3) 3.

Definition csr_write_illegal (writes : bool) (csr : bv 12) : bool :=
  (writes && csr_read_only csr)%bool.

Definition csr_slice (csr : bv 12) : option (Z * Z) :=
  let c := bv_unsigned csr in
  if Z.eqb c 1 then Some (0%Z, 5%Z)
  else if Z.eqb c 2 then Some (5%Z, 3%Z)
  else if Z.eqb c 3 then Some (0%Z, 8%Z)
  else None.

Lemma csr_read_only_unimplemented : forall csr : bv 12,
  csr_read_only csr = true -> csr_slice csr = None.
Proof.
  intros csr H. unfold csr_slice. cbv zeta.
  unfold csr_read_only in H.
  destruct (Z.eqb_spec (bv_unsigned csr) 1) as [E|_].
  { rewrite E in H. cbn in H. discriminate. }
  destruct (Z.eqb_spec (bv_unsigned csr) 2) as [E|_].
  { rewrite E in H. cbn in H. discriminate. }
  destruct (Z.eqb_spec (bv_unsigned csr) 3) as [E|_].
  { rewrite E in H. cbn in H. discriminate. }
  reflexivity.
Qed.

Definition slice_get (f : bv 32) (lo len : Z) : word :=
  Z_to_bv 64 (Z.land (Z.shiftr (bv_unsigned f) lo) (Z.ones len)).

Definition slice_set (f : bv 32) (lo len : Z) (v : word) : bv 32 :=
  let mask := Z.shiftl (Z.ones len) lo in
  Z_to_bv 32 (Z.lor (Z.land (bv_unsigned f) (Z.lnot mask))
                    (Z.land (Z.shiftl (bv_unsigned v) lo) mask)).

Definition nan_box (v : bv 32) : word := bv_concat 64 (Z_to_bv 32 (-1)) v.

Definition unbox_s (v : word) : bv 32 :=
  if Z.eqb (bv_unsigned (bv_extract 32 32 v)) (Z.ones 32)
  then low32 v
  else Z_to_bv 32 0x7fc00000.

Definition sgnj_val {n : N} (op : fsgnop) (a b : bv n) : bv n :=
  let sa := bit (n - 1) a in
  let sb := bit (n - 1) b in
  let s := match op with
           | F_SGNJ => sb
           | F_SGNJN => negb sb
           | F_SGNJX => xorb sa sb
           end in
  bv_concat n (Z_to_bv 1 (if s then 1 else 0)) (bv_extract 0 (n - 1) a).

(** ** Core state *)

Record core := Core {
  c_regs : bvmap 5 word;
  c_fregs : bvmap 5 word;
  c_pc : word;
  c_fcsr : bv 32;
  c_resv : option word;
}.

Definition with_regs f (c : core) :=
  Core (f (c_regs c)) (c_fregs c) (c_pc c) (c_fcsr c) (c_resv c).
Definition with_fregs f (c : core) :=
  Core (c_regs c) (f (c_fregs c)) (c_pc c) (c_fcsr c) (c_resv c).
Definition with_pc (v : word) (c : core) :=
  Core (c_regs c) (c_fregs c) v (c_fcsr c) (c_resv c).
Definition with_fcsr (v : bv 32) (c : core) :=
  Core (c_regs c) (c_fregs c) (c_pc c) v (c_resv c).
Definition with_resv (v : option word) (c : core) :=
  Core (c_regs c) (c_fregs c) (c_pc c) (c_fcsr c) v.

Definition reg_get (rm : bvmap 5 word) (r : reg) : word :=
  match bvmap_get r rm with Some v => v | None => w0 end.

(** Legacy RV64 x0-hardwired accessors (kept for Common compatibility). *)
Definition rget (c : core) (r : reg) : word :=
  if is_x0 r then w0 else reg_get (c_regs c) r.
Definition rset (r : reg) (v : word) (c : core) : core :=
  if is_x0 r then c else with_regs (bvmap_set r v) c.

(** ARMv8.0-A register accessors:
    - Key 0..30 = X0..X30
    - Key 31 = SP in stack/base/add-sub-imm instructions, or XZR (0) in general operands
    - Writing with sf = false (32-bit W register) zero-extends to 64 bits. *)
Definition mask_sf (sf : bool) (v : word) : word :=
  if sf then v else zext 64 (low32 v).

Definition rget_sp (c : core) (r : reg) (sf : bool) : word :=
  mask_sf sf (reg_get (c_regs c) r).

Definition rget_xzr (c : core) (r : reg) (sf : bool) : word :=
  if is_r31 r then w0 else mask_sf sf (reg_get (c_regs c) r).

Definition rset_sp (r : reg) (sf : bool) (v : word) (c : core) : core :=
  with_regs (bvmap_set r (mask_sf sf v)) c.

Definition rset_xzr (r : reg) (sf : bool) (v : word) (c : core) : core :=
  if is_r31 r then c else with_regs (bvmap_set r (mask_sf sf v)) c.

Definition fget (c : core) (r : reg) : word := reg_get (c_fregs c) r.
Definition fset (r : reg) (v : word) (c : core) : core :=
  with_fregs (bvmap_set r v) c.

(** ** ARMv8.0-A NZCV condition flags (stored in c_fcsr[3:0]) & ALU helpers *)

Definition set_nzcv (n_fl z_fl c_fl v_fl : bool) (c : core) : core :=
  let bits :=
    Z.lor (if n_fl then 8%Z else 0%Z)
      (Z.lor (if z_fl then 4%Z else 0%Z)
        (Z.lor (if c_fl then 2%Z else 0%Z)
               (if v_fl then 1%Z else 0%Z))) in
  with_fcsr (Z_to_bv 32 bits) c.

Definition get_n (c : core) : bool := Z.testbit (bv_unsigned (c_fcsr c)) 3.
Definition get_z (c : core) : bool := Z.testbit (bv_unsigned (c_fcsr c)) 2.
Definition get_c (c : core) : bool := Z.testbit (bv_unsigned (c_fcsr c)) 1.
Definition get_v (c : core) : bool := Z.testbit (bv_unsigned (c_fcsr c)) 0.

Definition condition_holds (cond : bv 4) (c : core) : bool :=
  let u := bv_unsigned cond in
  let hi := Z.shiftr u 1 in
  let base :=
    if Z.eqb hi 0 then get_z c
    else if Z.eqb hi 1 then get_c c
    else if Z.eqb hi 2 then get_n c
    else if Z.eqb hi 3 then get_v c
    else if Z.eqb hi 4 then andb (get_c c) (negb (get_z c))
    else if Z.eqb hi 5 then Bool.eqb (get_n c) (get_v c)
    else if Z.eqb hi 6 then andb (Bool.eqb (get_n c) (get_v c)) (negb (get_z c))
    else true in
  if andb (Z.testbit u 0) (negb (Z.eqb hi 7)) then negb base else base.

Definition add_with_carry (sf : bool) (x y : word) (carry_in : bool)
    : word * (bool * bool * bool * bool) :=
  let w := if sf then 64%Z else 32%Z in
  let ux := Z.land (bv_unsigned x) (Z.ones w) in
  let uy := Z.land (bv_unsigned y) (Z.ones w) in
  let sx := if Z.testbit ux (w - 1) then (ux - Z.shiftl 1 w)%Z else ux in
  let sy := if Z.testbit uy (w - 1) then (uy - Z.shiftl 1 w)%Z else uy in
  let cin := if carry_in then 1%Z else 0%Z in
  let usum := (ux + uy + cin)%Z in
  let ssum := (sx + sy + cin)%Z in
  let ures := Z.land usum (Z.ones w) in
  let sres := if Z.testbit ures (w - 1) then (ures - Z.shiftl 1 w)%Z else ures in
  let n_fl := Z.testbit ures (w - 1) in
  let z_fl := Z.eqb ures 0 in
  let c_fl := negb (Z.eqb ures usum) in
  let v_fl := negb (Z.eqb sres ssum) in
  (Z_to_bv 64 ures, (n_fl, z_fl, c_fl, v_fl)).

Definition not_sf (sf : bool) (v : word) : word :=
  let w := if sf then 64%Z else 32%Z in
  Z_to_bv 64 (Z.land (Z.lnot (bv_unsigned v)) (Z.ones w)).

Definition shift_reg (sf : bool) (shift_ty : bv 2) (v : word) (amt : Z) : word :=
  let w := if sf then 64%Z else 32%Z in
  let sh := Z.modulo amt w in
  let u := Z.land (bv_unsigned v) (Z.ones w) in
  let s := if Z.testbit u (w - 1) then (u - Z.shiftl 1 w)%Z else u in
  let st := bv_unsigned shift_ty in
  if Z.eqb st 0 then
    Z_to_bv 64 (Z.land (Z.shiftl u sh) (Z.ones w))
  else if Z.eqb st 1 then
    Z_to_bv 64 (Z.shiftr u sh)
  else if Z.eqb st 2 then
    Z_to_bv 64 (Z.land (Z.shiftr s sh) (Z.ones w))
  else
    if Z.eqb sh 0 then Z_to_bv 64 u
    else Z_to_bv 64 (Z.land (Z.lor (Z.shiftr u sh) (Z.shiftl u (w - sh))) (Z.ones w)).

Definition extend_reg (sf : bool) (opt : bv 3) (sh : Z) (v : word) : word :=
  let w := if sf then 64%Z else 32%Z in
  let u := bv_unsigned v in
  let lo2 := Z.land (bv_unsigned opt) 3 in
  let ebits :=
    if Z.eqb lo2 0 then 8%Z
    else if Z.eqb lo2 1 then 16%Z
    else if Z.eqb lo2 2 then 32%Z
    else 64%Z in
  let is_signed := Z.testbit (bv_unsigned opt) 2 in
  let masked := Z.land u (Z.ones ebits) in
  let ext :=
    if is_signed then
      (if Z.testbit masked (ebits - 1) then (masked - Z.shiftl 1 ebits)%Z else masked)
    else masked in
  Z_to_bv 64 (Z.land (Z.shiftl ext sh) (Z.ones w)).

Definition exec_bitfield (sf : bool) (opc : bv 2) (src_w dst_w : word)
    (immr imms : bv 6) : word :=
  let w := if sf then 64%Z else 32%Z in
  let r := bv_unsigned immr in
  let s := bv_unsigned imms in
  let src := Z.land (bv_unsigned src_w) (Z.ones w) in
  let dst := Z.land (bv_unsigned dst_w) (Z.ones w) in
  let op := bv_unsigned opc in
  if Z.geb s r then
    let len := (s - r + 1)%Z in
    let extracted := Z.land (Z.shiftr src r) (Z.ones len) in
    if Z.eqb op 2 then Z_to_bv 64 extracted
    else if Z.eqb op 0 then
      let sgn := Z.testbit extracted (len - 1) in
      Z_to_bv 64 (Z.land (if sgn then Z.lor extracted (Z.shiftl (Z.ones (w - len)) len)
                          else extracted) (Z.ones w))
    else
      Z_to_bv 64 (Z.land (Z.lor (Z.land dst (Z.lnot (Z.ones len))) extracted) (Z.ones w))
  else
    let len := (s + 1)%Z in
    let pos := (w - r)%Z in
    let extracted := Z.land src (Z.ones len) in
    let shifted := Z.land (Z.shiftl extracted pos) (Z.ones w) in
    if Z.eqb op 2 then Z_to_bv 64 shifted
    else if Z.eqb op 0 then
      let sgn := Z.testbit extracted (len - 1) in
      let top_len := (w - (pos + len))%Z in
      Z_to_bv 64 (Z.land (if sgn then Z.lor shifted (Z.shiftl (Z.ones top_len) (pos + len))
                          else shifted) (Z.ones w))
    else
      let mask := Z.shiftl (Z.ones len) pos in
      Z_to_bv 64 (Z.land (Z.lor (Z.land dst (Z.lnot mask)) shifted) (Z.ones w)).

Fixpoint clz_loop (n : nat) (bit_idx : Z) (u : Z) : Z :=
  match n with
  | O => 0%Z
  | S n' =>
      if Z.testbit u bit_idx then 0%Z
      else (1 + clz_loop n' (bit_idx - 1) u)%Z
  end.

Fixpoint rbit_loop (n : nat) (u acc : Z) : Z :=
  match n with
  | O => acc
  | S n' =>
      rbit_loop n' (Z.shiftr u 1) (Z.lor (Z.shiftl acc 1) (Z.land u 1))
  end.

Definition rev16_word (sf : bool) (v : word) : word :=
  let u := bv_unsigned v in
  let b0 := Z.land u 255 in
  let b1 := Z.land (Z.shiftr u 8) 255 in
  let b2 := Z.land (Z.shiftr u 16) 255 in
  let b3 := Z.land (Z.shiftr u 24) 255 in
  let lo := Z.lor (Z.shiftl b0 8) (Z.lor b1 (Z.lor (Z.shiftl b2 24) (Z.shiftl b3 16))) in
  if negb sf then Z_to_bv 64 lo
  else
    let b4 := Z.land (Z.shiftr u 32) 255 in
    let b5 := Z.land (Z.shiftr u 40) 255 in
    let b6 := Z.land (Z.shiftr u 48) 255 in
    let b7 := Z.land (Z.shiftr u 56) 255 in
    let hi := Z.lor (Z.shiftl b4 8) (Z.lor b5 (Z.lor (Z.shiftl b6 24) (Z.shiftl b7 16))) in
    Z_to_bv 64 (Z.lor lo (Z.shiftl hi 32)).

Definition rev32_word (sf : bool) (v : word) : word :=
  let u := bv_unsigned v in
  let b0 := Z.land u 255 in
  let b1 := Z.land (Z.shiftr u 8) 255 in
  let b2 := Z.land (Z.shiftr u 16) 255 in
  let b3 := Z.land (Z.shiftr u 24) 255 in
  let lo := Z.lor (Z.shiftl b0 24) (Z.lor (Z.shiftl b1 16) (Z.lor (Z.shiftl b2 8) b3)) in
  if negb sf then Z_to_bv 64 lo
  else
    let b4 := Z.land (Z.shiftr u 32) 255 in
    let b5 := Z.land (Z.shiftr u 40) 255 in
    let b6 := Z.land (Z.shiftr u 48) 255 in
    let b7 := Z.land (Z.shiftr u 56) 255 in
    let hi := Z.lor (Z.shiftl b4 24) (Z.lor (Z.shiftl b5 16) (Z.lor (Z.shiftl b6 8) b7)) in
    Z_to_bv 64 (Z.lor lo (Z.shiftl hi 32)).

Definition rev64_word (v : word) : word :=
  let u := bv_unsigned v in
  let b0 := Z.land u 255 in
  let b1 := Z.land (Z.shiftr u 8) 255 in
  let b2 := Z.land (Z.shiftr u 16) 255 in
  let b3 := Z.land (Z.shiftr u 24) 255 in
  let b4 := Z.land (Z.shiftr u 32) 255 in
  let b5 := Z.land (Z.shiftr u 40) 255 in
  let b6 := Z.land (Z.shiftr u 48) 255 in
  let b7 := Z.land (Z.shiftr u 56) 255 in
  Z_to_bv 64
    (Z.lor (Z.shiftl b0 56)
      (Z.lor (Z.shiftl b1 48)
        (Z.lor (Z.shiftl b2 40)
          (Z.lor (Z.shiftl b3 32)
            (Z.lor (Z.shiftl b4 24)
              (Z.lor (Z.shiftl b5 16)
                (Z.lor (Z.shiftl b6 8) b7))))))).

(** ** Legacy FP register file helpers *)

Definition frm_of (c : core) : Z :=
  Z.land (Z.shiftr (bv_unsigned (c_fcsr c)) 5) 7.

Definition inval_resv (a : word) (c : core) : core :=
  match c_resv c with
  | Some r =>
      if Z.eqb (bv_unsigned r) (bv_unsigned a) then with_resv None c else c
  | None => c
  end.

(** ** The effect tree *)

Inductive eff : Type :=
| EDone (c : core)
| EIllegal (c : core)
| EDefinedIllegal (c : core)
| EEcall (c : core)
| EEbreak (c : core)
| EFault (c : core)
| ELoad (n : N) (a : word) (k : bv n → eff)
| EStore (n : N) (a : word) (v : bv n) (k : eff).

Definition load_val (sz : msize) (sgn : bool) (a : word) (k : word → eff) : eff :=
  match sz with
  | SZ1 => ELoad 8 a (λ v, k (if sgn then sext 64 v else zext 64 v))
  | SZ2 => ELoad 16 a (λ v, k (if sgn then sext 64 v else zext 64 v))
  | SZ4 => ELoad 32 a (λ v, k (if sgn then sext 64 v else zext 64 v))
  | SZ8 => ELoad 64 a k
  end.

Definition store_val (sz : msize) (a : word) (v : word) (k : eff) : eff :=
  match sz with
  | SZ1 => EStore 8 a (bv_extract 0 8 v) k
  | SZ2 => EStore 16 a (bv_extract 0 16 v) k
  | SZ4 => EStore 32 a (low32 v) k
  | SZ8 => EStore 64 a v k
  end.

Definition load_a64 (sz : msize) (is_signed simm_64 : bool) (a : word) (k : word → eff) : eff :=
  let post (v : word) : word :=
    if is_signed then
      if simm_64 then v else zext 64 (low32 v)
    else v in
  load_val sz is_signed a (λ v, k (post v)).

Definition exec_csr (op : csrop) (rd : reg) (operand : word)
    (writes : bool) (csr : bv 12) (c : core) : eff :=
  match csr_slice csr with
  | None => EIllegal c
  | Some (lo, len) =>
      let f := c_fcsr c in
      let old := slice_get f lo len in
      let newv :=
        match op with
        | CSR_RW => operand
        | CSR_RS => bv_or old operand
        | CSR_RC => bv_and old (bv_not operand)
        end in
      EDone (rset rd old
               (if writes then with_fcsr (slice_set f lo len newv) c else c))
  end.

(** ** The semantics *)

Definition exec (sz : word) (i : instr) (c : core) : eff :=
  let pc := c_pc c in
  let npc := pc + sz in
  let cn := with_pc npc c in
  match i with
  (* ---- ARMv8.0-A (AArch64 / Phytium D2000) instructions ---- *)
  | A64_AddSubImm sf is_sub setflags rd rn imm =>
      let x := rget_sp c rn sf in
      let y := if is_sub then not_sf sf imm else mask_sf sf imm in
      let '(res, (nf, zf, cf, vf)) := add_with_carry sf x y is_sub in
      let c1 := if setflags then set_nzcv nf zf cf vf cn else cn in
      let c2 := if setflags then rset_xzr rd sf res c1 else rset_sp rd sf res c1 in
      EDone c2

  | A64_LogicalImm sf opc rd rn bmask =>
      let x := rget_xzr c rn sf in
      let y := mask_sf sf bmask in
      let op := bv_unsigned opc in
      let res :=
        if Z.eqb op 0 then bv_and x y
        else if Z.eqb op 1 then bv_or x y
        else if Z.eqb op 2 then bv_xor x y
        else bv_and x y in
      let res_m := mask_sf sf res in
      let w := if sf then 64%Z else 32%Z in
      let c1 :=
        if Z.eqb op 3 then
          set_nzcv (Z.testbit (bv_unsigned res_m) (w - 1))
                   (Z.eqb (bv_unsigned res_m) 0) false false cn
        else cn in
      let c2 := if Z.eqb op 3 then rset_xzr rd sf res_m c1 else rset_sp rd sf res_m c1 in
      EDone c2

  | A64_MoveWide sf opc rd imm16 hw =>
      let pos := (bv_unsigned hw * 16)%Z in
      let imm_u := Z.shiftl (bv_unsigned imm16) pos in
      let op := bv_unsigned opc in
      let w := if sf then 64%Z else 32%Z in
      let res :=
        if Z.eqb op 0 then (* MOVN *)
          Z_to_bv 64 (Z.land (Z.lnot imm_u) (Z.ones w))
        else if Z.eqb op 2 then (* MOVZ *)
          Z_to_bv 64 (Z.land imm_u (Z.ones w))
        else (* MOVK *)
          let old := bv_unsigned (rget_xzr c rd sf) in
          let mask := Z.shiftl (Z.ones 16) pos in
          Z_to_bv 64 (Z.land (Z.lor (Z.land old (Z.lnot mask)) imm_u) (Z.ones w)) in
      EDone (rset_xzr rd sf res cn)

  | A64_Adr is_page rd imm =>
      let base := if is_page then bv_and pc (Z_to_bv 64 (-4096)) else pc in
      EDone (rset_xzr rd true (base + imm) cn)

  | A64_Bitfield sf opc rd rn immr imms =>
      let res := exec_bitfield sf opc (rget_xzr c rn sf) (rget_xzr c rd sf) immr imms in
      EDone (rset_xzr rd sf res cn)

  | A64_Extract sf rd rn rm imms =>
      let w := if sf then 64%Z else 32%Z in
      let lsb := bv_unsigned imms in
      let hi := Z.land (bv_unsigned (rget_xzr c rn sf)) (Z.ones w) in
      let lo := Z.land (bv_unsigned (rget_xzr c rm sf)) (Z.ones w) in
      let pair := Z.lor (Z.shiftl hi w) lo in
      let res := Z_to_bv 64 (Z.land (Z.shiftr pair lsb) (Z.ones w)) in
      EDone (rset_xzr rd sf res cn)

  | A64_AddSubShifted sf is_sub setflags shift_ty rd rn rm imm6 =>
      let x := rget_xzr c rn sf in
      let m := shift_reg sf shift_ty (rget_xzr c rm sf) (bv_unsigned imm6) in
      let y := if is_sub then not_sf sf m else m in
      let '(res, (nf, zf, cf, vf)) := add_with_carry sf x y is_sub in
      let c1 := if setflags then set_nzcv nf zf cf vf cn else cn in
      EDone (rset_xzr rd sf res c1)

  | A64_AddSubExtended sf is_sub setflags option_ty rd rn rm imm3 =>
      let x := rget_sp c rn sf in
      let m := extend_reg sf option_ty (bv_unsigned imm3) (rget_xzr c rm true) in
      let y := if is_sub then not_sf sf m else m in
      let '(res, (nf, zf, cf, vf)) := add_with_carry sf x y is_sub in
      let c1 := if setflags then set_nzcv nf zf cf vf cn else cn in
      let c2 := if setflags then rset_xzr rd sf res c1 else rset_sp rd sf res c1 in
      EDone c2

  | A64_AddSubCarry sf is_sub setflags rd rn rm =>
      let x := rget_xzr c rn sf in
      let m := rget_xzr c rm sf in
      let y := if is_sub then not_sf sf m else m in
      let '(res, (nf, zf, cf, vf)) := add_with_carry sf x y (get_c c) in
      let c1 := if setflags then set_nzcv nf zf cf vf cn else cn in
      EDone (rset_xzr rd sf res c1)

  | A64_LogicalShifted sf opc inv_rm shift_ty rd rn rm imm6 =>
      let x := rget_xzr c rn sf in
      let m0 := shift_reg sf shift_ty (rget_xzr c rm sf) (bv_unsigned imm6) in
      let y := if inv_rm then not_sf sf m0 else m0 in
      let op := bv_unsigned opc in
      let res :=
        if Z.eqb op 0 then bv_and x y
        else if Z.eqb op 1 then bv_or x y
        else if Z.eqb op 2 then bv_xor x y
        else bv_and x y in
      let res_m := mask_sf sf res in
      let w := if sf then 64%Z else 32%Z in
      let c1 :=
        if Z.eqb op 3 then
          set_nzcv (Z.testbit (bv_unsigned res_m) (w - 1))
                   (Z.eqb (bv_unsigned res_m) 0) false false cn
        else cn in
      EDone (rset_xzr rd sf res_m c1)

  | A64_CondSelect sf op o2 cond rd rn rm =>
      let res :=
        if condition_holds cond c then
          rget_xzr c rn sf
        else
          let m := rget_xzr c rm sf in
          let m1 := if op then not_sf sf m else m in
          let m2 := if o2 then mask_sf sf (m1 + w1) else m1 in
          m2 in
      EDone (rset_xzr rd sf res cn)

  | A64_CondCompare sf is_sub is_imm cond rn rm_or_imm nzcv_imm =>
      if condition_holds cond c then
        let x := rget_xzr c rn sf in
        let m := if is_imm then zext 64 rm_or_imm else rget_xzr c rm_or_imm sf in
        let y := if is_sub then not_sf sf m else m in
        let '(_, (nf, zf, cf, vf)) := add_with_carry sf x y is_sub in
        EDone (set_nzcv nf zf cf vf cn)
      else
        let u := bv_unsigned nzcv_imm in
        EDone (set_nzcv (Z.testbit u 3) (Z.testbit u 2) (Z.testbit u 1) (Z.testbit u 0) cn)

  | A64_DataProc2 sf opcode rd rn rm =>
      let x := rget_xzr c rn sf in
      let y := rget_xzr c rm sf in
      let op := bv_unsigned opcode in
      if Z.eqb op 2 then (* UDIV *)
        let res :=
          if Z.eqb (bv_unsigned y) 0 then w0
          else if sf then bv_divu x y else zext 64 (bv_divu (low32 x) (low32 y)) in
        EDone (rset_xzr rd sf res cn)
      else if Z.eqb op 3 then (* SDIV *)
        let res :=
          if Z.eqb (bv_unsigned y) 0 then w0
          else if sf then bv_quots x y else zext 64 (bv_quots (low32 x) (low32 y)) in
        EDone (rset_xzr rd sf res cn)
      else if Z.eqb op 8 then (* LSLV *)
        EDone (rset_xzr rd sf (shift_reg sf (Z_to_bv 2 0) x (bv_unsigned y)) cn)
      else if Z.eqb op 9 then (* LSRV *)
        EDone (rset_xzr rd sf (shift_reg sf (Z_to_bv 2 1) x (bv_unsigned y)) cn)
      else if Z.eqb op 10 then (* ASRV *)
        EDone (rset_xzr rd sf (shift_reg sf (Z_to_bv 2 2) x (bv_unsigned y)) cn)
      else if Z.eqb op 11 then (* RORV *)
        EDone (rset_xzr rd sf (shift_reg sf (Z_to_bv 2 3) x (bv_unsigned y)) cn)
      else EIllegal cn

  | A64_DataProc1 sf opcode rd rn =>
      let x := rget_xzr c rn sf in
      let u := bv_unsigned x in
      let op := bv_unsigned opcode in
      let w_nat := if sf then 64%nat else 32%nat in
      let w_z := if sf then 64%Z else 32%Z in
      if Z.eqb op 0 then (* RBIT *)
        EDone (rset_xzr rd sf (Z_to_bv 64 (rbit_loop w_nat u 0)) cn)
      else if Z.eqb op 1 then (* REV16 *)
        EDone (rset_xzr rd sf (rev16_word sf x) cn)
      else if Z.eqb op 2 then (* REV32 *)
        EDone (rset_xzr rd sf (rev32_word sf x) cn)
      else if Z.eqb op 3 then (* REV64 *)
        EDone (rset_xzr rd sf (rev64_word x) cn)
      else if Z.eqb op 4 then (* CLZ *)
        EDone (rset_xzr rd sf (Z_to_bv 64 (clz_loop w_nat (w_z - 1) u)) cn)
      else if Z.eqb op 5 then (* CLS *)
        let top := Z.testbit u (w_z - 1) in
        let inv := if top then Z.land (Z.lnot u) (Z.ones w_z) else u in
        EDone (rset_xzr rd sf (Z_to_bv 64 (clz_loop ( Nat.pred w_nat) (w_z - 2) inv)) cn)
      else EIllegal cn

  | A64_DataProc3 sf op54 op31 o0 rd rn rm ra =>
      let o31 := bv_unsigned op31 in
      if Z.eqb o31 0 then (* MADD / MSUB *)
        let n := rget_xzr c rn sf in
        let m := rget_xzr c rm sf in
        let a := rget_xzr c ra sf in
        let prod := n * m in
        let res := if o0 then a - prod else a + prod in
        EDone (rset_xzr rd sf res cn)
      else if Z.eqb o31 1 then (* SMADDL / SMSUBL *)
        let n := sext 64 (low32 (rget_xzr c rn false)) in
        let m := sext 64 (low32 (rget_xzr c rm false)) in
        let a := rget_xzr c ra true in
        let prod := n * m in
        let res := if o0 then a - prod else a + prod in
        EDone (rset_xzr rd true res cn)
      else if Z.eqb o31 2 then (* SMULH *)
        let n := rget_xzr c rn true in
        let m := rget_xzr c rm true in
        EDone (rset_xzr rd true (bv_mulhss n m) cn)
      else if Z.eqb o31 5 then (* UMADDL / UMSUBL *)
        let n := rget_xzr c rn false in
        let m := rget_xzr c rm false in
        let a := rget_xzr c ra true in
        let prod := n * m in
        let res := if o0 then a - prod else a + prod in
        EDone (rset_xzr rd true res cn)
      else if Z.eqb o31 6 then (* UMULH *)
        let n := rget_xzr c rn true in
        let m := rget_xzr c rm true in
        EDone (rset_xzr rd true (bv_mulhuu n m) cn)
      else EIllegal cn

  | A64_BImm is_link offset =>
      let target := pc + offset in
      let c1 := with_pc target c in
      let c2 := if is_link then rset_xzr (Z_to_bv 5 30) true npc c1 else c1 in
      EDone c2

  | A64_BReg op rn =>
      let target := rget_xzr c rn true in
      let c1 := with_pc target c in
      let c2 :=
        if Z.eqb (bv_unsigned op) 1 then
          rset_xzr (Z_to_bv 5 30) true npc c1
        else c1 in
      EDone c2

  | A64_BCond cond offset =>
      let target := if condition_holds cond c then pc + offset else npc in
      EDone (with_pc target c)

  | A64_CBZ sf is_nz rt offset =>
      let v := rget_xzr c rt sf in
      let is_z := Z.eqb (bv_unsigned v) 0 in
      let taken := if is_nz then negb is_z else is_z in
      EDone (with_pc (if taken then pc + offset else npc) c)

  | A64_TBZ is_nz rt bit_pos offset =>
      let v := rget_xzr c rt true in
      let b := Z.testbit (bv_unsigned v) (bv_unsigned bit_pos) in
      let taken := if is_nz then b else negb b in
      EDone (with_pc (if taken then pc + offset else npc) c)

  | A64_LoadStoreImm msz is_load is_signed simm_64 wback postindex rt rn offset =>
      let base := rget_sp c rn true in
      let wb_addr := base + offset in
      let addr := if postindex then base else wb_addr in
      if negb (mem_aligned msz addr) then EFault c
      else
      let c_wb := if wback then rset_sp rn true wb_addr cn else cn in
      if is_load then
        let dst_sf := if is_signed then simm_64 else match msz with SZ8 => true | _ => false end in
        load_a64 msz is_signed simm_64 addr (λ v, EDone (rset_xzr rt dst_sf v c_wb))
      else
        let v := rget_xzr c rt true in
        store_val msz addr v (EDone (inval_resv addr c_wb))

  | A64_LoadStoreReg msz is_load is_signed simm_64 option_ty s_scale rt rn rm =>
      let base := rget_sp c rn true in
      let sh :=
        if s_scale then
          match msz with SZ1 => 0%Z | SZ2 => 1%Z | SZ4 => 2%Z | SZ8 => 3%Z end
        else 0%Z in
      let off := extend_reg true option_ty sh (rget_xzr c rm true) in
      let addr := base + off in
      if negb (mem_aligned msz addr) then EFault c
      else if is_load then
        let dst_sf := if is_signed then simm_64 else match msz with SZ8 => true | _ => false end in
        load_a64 msz is_signed simm_64 addr (λ v, EDone (rset_xzr rt dst_sf v cn))
      else
        let v := rget_xzr c rt true in
        store_val msz addr v (EDone (inval_resv addr cn))

  | A64_LoadStorePair msz is_load is_signed wback postindex rt rt2 rn offset =>
      let base := rget_sp c rn true in
      let wb_addr := base + offset in
      let addr1 := if postindex then base else wb_addr in
      let step_sz := Z_to_bv 64 (msize_bytes msz) in
      let addr2 := addr1 + step_sz in
      if negb (andb (mem_aligned msz addr1) (mem_aligned msz addr2)) then EFault c
      else
      let c_wb := if wback then rset_sp rn true wb_addr cn else cn in
      if is_load then
        let dst_sf := if is_signed then true else match msz with SZ8 => true | _ => false end in
        load_a64 msz is_signed true addr1 (λ v1,
          load_a64 msz is_signed true addr2 (λ v2,
            EDone (rset_xzr rt2 dst_sf v2 (rset_xzr rt dst_sf v1 c_wb))))
      else
        let v1 := rget_xzr c rt true in
        let v2 := rget_xzr c rt2 true in
        store_val msz addr1 v1
          (store_val msz addr2 v2
            (EDone (inval_resv addr2 (inval_resv addr1 c_wb))))

  | A64_LoadStoreExcl msz is_load rs rt rn =>
      let addr := rget_sp c rn true in
      if negb (mem_aligned msz addr) then EFault c
      else if is_load then
        let dst_sf := match msz with SZ8 => true | _ => false end in
        load_val msz false addr (λ v,
          EDone (with_resv (Some addr) (rset_xzr rt dst_sf v cn)))
      else
        let ok := match c_resv c with
                  | Some r => Z.eqb (bv_unsigned r) (bv_unsigned addr)
                  | None => false
                  end in
        let c1 := with_resv None cn in
        if ok then
          store_val msz addr (rget_xzr c rt true)
            (EDone (rset_xzr rs false w0 c1))
        else
          EDone (rset_xzr rs false w1 c1)

  | A64_Nop => EDone cn

  | A64_MrsTpidr rt =>
      EDone (rset_xzr rt true (fget c (Z_to_bv 5 0)) cn)

  | A64_MsrTpidr rt =>
      EDone (fset (Z_to_bv 5 0) (rget_xzr c rt true) cn)

  | A64_Svc _ => EEcall cn

  | A64_Brk _ => EDefinedIllegal c

  | A64_Udf _ => EDefinedIllegal c

  (* ---- Legacy RV64 instructions (kept for Common compatibility) ---- *)
  | Lui rd imm =>
      EDone (rset rd (sext 64 (bv_concat 32 imm (Z_to_bv 12 0))) cn)
  | Auipc rd imm =>
      EDone (rset rd (pc + sext 64 (bv_concat 32 imm (Z_to_bv 12 0))) cn)
  | Jal rd imm =>
      EDone (rset rd npc (with_pc (pc + sext 64 imm) c))
  | Jalr rd rs1 imm =>
      let a := rget c rs1 in
      EDone (rset rd npc (with_pc (bv_and (a + sext 64 imm) (bv_not w1)) c))
  | Branch bc rs1 rs2 imm =>
      EDone (with_pc (if branch_taken bc (rget c rs1) (rget c rs2)
                      then pc + sext 64 imm else npc) c)
  | Load msz sgn rd rs1 imm =>
      load_val msz sgn (rget c rs1 + sext 64 imm)
        (λ v, EDone (rset rd v cn))
  | Store msz rs1 rs2 imm =>
      let a := rget c rs1 + sext 64 imm in
      store_val msz a (rget c rs2) (EDone (inval_resv a cn))
  | OpImm op rd rs1 imm =>
      EDone (rset rd (alu64 op (rget c rs1) (sext 64 imm)) cn)
  | ShiftImm op rd rs1 shamt =>
      EDone (rset rd (alu64 op (rget c rs1) (zext 64 shamt)) cn)
  | Op op rd rs1 rs2 =>
      EDone (rset rd (alu64 op (rget c rs1) (rget c rs2)) cn)
  | OpImm32 rd rs1 imm =>
      EDone (rset rd (sext 64 (alu32 ALU_ADD (low32 (rget c rs1)) (sext 32 imm))) cn)
  | ShiftImm32 op rd rs1 shamt =>
      EDone (rset rd (sext 64 (alu32 op (low32 (rget c rs1)) (zext 32 shamt))) cn)
  | Op32 op rd rs1 rs2 =>
      EDone (rset rd (sext 64 (alu32 op (low32 (rget c rs1)) (low32 (rget c rs2)))) cn)
  | Fence _ _ _ _ _ | FenceI _ _ _ =>
      EDone cn
  | Ecall => EEcall cn
  | Ebreak => EEbreak cn
  | Mul op rd rs1 rs2 =>
      EDone (rset rd (mul_div op (rget c rs1) (rget c rs2)) cn)
  | Mul32 op rd rs1 rs2 =>
      EDone (rset rd (sext 64 (mul_div op (low32 (rget c rs1)) (low32 (rget c rs2)))) cn)
  | Lr wd _ _ rd rs1 =>
      let a := rget c rs1 in
      if negb (amo_aligned wd a) then EFault c
      else match wd with
      | AW => ELoad 32 a (λ v,
                EDone (with_resv (Some a) (rset rd (sext 64 v) cn)))
      | AD => ELoad 64 a (λ v,
                EDone (with_resv (Some a) (rset rd v cn)))
      end
  | Sc wd _ _ rd rs1 rs2 =>
      let a := rget c rs1 in
      if negb (amo_aligned wd a) then EFault c
      else
      let ok := match c_resv c with
                | Some r => Z.eqb (bv_unsigned r) (bv_unsigned a)
                | None => false
                end in
      let c1 := with_resv None cn in
      if ok then
        (match wd with
         | AW => EStore 32 a (low32 (rget c rs2))
         | AD => EStore 64 a (rget c rs2)
         end) (EDone (rset rd w0 c1))
      else EDone (rset rd w1 c1)
  | Amo op wd _ _ rd rs1 rs2 =>
      let a := rget c rs1 in
      if negb (amo_aligned wd a) then EFault c
      else
      let src := rget c rs2 in
      let c1 := inval_resv a cn in
      match wd with
      | AW => ELoad 32 a (λ old,
                EStore 32 a (amo_val op old (low32 src))
                  (EDone (rset rd (sext 64 old) c1)))
      | AD => ELoad 64 a (λ old,
                EStore 64 a (amo_val op old src)
                  (EDone (rset rd old c1)))
      end
  | Csr op rd rs1 csr =>
      let writes := match op with CSR_RW => true | _ => negb (is_x0 rs1) end in
      if csr_write_illegal writes csr then EDefinedIllegal c
      else exec_csr op rd (rget c rs1) writes csr cn
  | CsrI op rd uimm csr =>
      let writes :=
        match op with
        | CSR_RW => true
        | _ => negb (Z.eqb (bv_unsigned uimm) 0)
        end in
      if csr_write_illegal writes csr then EDefinedIllegal c
      else exec_csr op rd (zext 64 uimm) writes csr cn
  | FLoad fmt rd rs1 imm =>
      let a := rget c rs1 + sext 64 imm in
      match fmt with
      | FMT_S => ELoad 32 a (λ v, EDone (fset rd (nan_box v) cn))
      | FMT_D => ELoad 64 a (λ v, EDone (fset rd v cn))
      end
  | FStore fmt rs1 rs2 imm =>
      let a := rget c rs1 + sext 64 imm in
      let v := fget c rs2 in
      (match fmt with
       | FMT_S => EStore 32 a (low32 v)
       | FMT_D => EStore 64 a v
       end) (EDone (inval_resv a cn))
  | Fmv dir fmt rd rs1 =>
      EDone match dir, fmt with
            | FMV_X_F, FMT_S => rset rd (sext 64 (low32 (fget c rs1))) cn
            | FMV_X_F, FMT_D => rset rd (fget c rs1) cn
            | FMV_F_X, FMT_S => fset rd (nan_box (low32 (rget c rs1))) cn
            | FMV_F_X, FMT_D => fset rd (rget c rs1) cn
            end
  | Fsgnj op fmt rd rs1 rs2 =>
      let a := fget c rs1 in
      let b := fget c rs2 in
      EDone match fmt with
            | FMT_S => fset rd (nan_box (sgnj_val op (unbox_s a) (unbox_s b))) cn
            | FMT_D => fset rd (sgnj_val op a b) cn
            end
  | Fari _ _ _ _ _ _
  | Fsqrt _ _ _ _
  | Fma _ _ _ _ _ _ _
  | Fminmax _ _ _ _ _
  | Fcmp _ _ _ _ _
  | Fclass _ _ _
  | Fcvt _ _ _ _ _ => EIllegal cn
  end.

Definition step (decode_any : bv 32 → option (instr * Z)) (c : core) : eff :=
  ELoad 32 (c_pc c) (λ w32,
    match decode_any w32 with
    | Some (i, isz) => exec (Z_to_bv 64 isz) i c
    | None => EIllegal c
    end).
