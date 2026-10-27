From Coq.Numbers.Cyclic.Int63 Require Import PrimInt63 Uint63.
From Coq.Array Require Export PArray.

Notation char63 := Uint63.int (only parsing).
Definition string : Type := PArray.array char63.
Definition length (s : string) : Uint63.int := PArray.length s.
Definition get (s : string) (i : Uint63.int) : char63 := PArray.get s i.
Definition max_length : Uint63.int := PArray.max_length.
