(** * Decoding: Sail's [encdec_backwards] on the instruction words emitted by the encoder

    Each lemma takes a 32-bit word given by the values of its fields (as
    [Z]) and evaluates [ext_decode] symbolically.  The guards of the other
    instructions tried before the matching one are refuted by [bsolve]. *)

From stdpp Require Import base bitvector.definitions.
From SailStdpp Require Import Base ConcurrencyInterfaceV2.
From Riscv Require Import rv64d_types rv64d.
From GaletteSail Require Export Mem.
From Stdlib Require Import Lia.
Import ListNotations.

Local Open Scope Z_scope.

(** ** Instruction formats, as numbers *)

Definition encR (f7 rs2 rs1 f3 rd opc : Z) : Z :=
  opc + 2 ^ 7 * rd + 2 ^ 12 * f3 + 2 ^ 15 * rs1 + 2 ^ 20 * rs2 + 2 ^ 25 * f7.

Definition reg5 (r : Z) : Prop := 0 <= r < 32.

Ltac dec_finish :=
  apply ev_ret_eq; repeat f_equal; apply bv_eq; zsolve.

Section Decode.

Variable s : SailState.
Hypothesis Hinv : agree ctrl cfg (regs s).

Lemma decode_ADD w rd rs1 rs2 :
  reg5 rd -> reg5 rs1 -> reg5 rs2 -> bv_unsigned w = encR 0 rs2 rs1 0 rd 0x33 ->
  ~ (rd = 0 /\ rs1 = 0 /\ 2 <= rs2 <= 5) ->
  runX (ext_decode w) s =
  Some (inl (RTYPE (Regidx (Z_to_bv 5 rs2), Regidx (Z_to_bv 5 rs1), Regidx (Z_to_bv 5 rd), ADD)), s).
Proof.
  unfold reg5, encR. intros Hrd Hrs1 Hrs2 Hw Hntl.
  Ltac ev_val_hook ::= ev_val_agree.
  Ltac ev_hook ::= ev_ctrl.
  ev. dec_finish.
Qed.

End Decode.
