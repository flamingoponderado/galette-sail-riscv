(** * The integer register file of the Sail model

    Sail keeps [x1]..[x31] as 31 separate registers and reads them with
    [rX], a 32-way case analysis on the register number.  [gpr] and
    [set_gpr] give the same access by number, and [rX_spec]/[wX_spec]
    evaluate [rX]/[wX] for a symbolic register number. *)

From stdpp Require Import base bitvector.definitions.
From SailStdpp Require Import Base ConcurrencyInterfaceV2.
From Riscv Require Import rv64d_types rv64d.
From GaletteSail Require Export Config.
From Stdlib Require Import Lia.

Local Open Scope Z_scope.

Definition xreg (i : Z) : option register_bitvector_64 :=
  match i with
  | 1 => Some x1 | 2 => Some x2 | 3 => Some x3 | 4 => Some x4 | 5 => Some x5 | 6 => Some x6
  | 7 => Some x7 | 8 => Some x8 | 9 => Some x9 | 10 => Some x10 | 11 => Some x11
  | 12 => Some x12 | 13 => Some x13 | 14 => Some x14 | 15 => Some x15 | 16 => Some x16
  | 17 => Some x17 | 18 => Some x18 | 19 => Some x19 | 20 => Some x20 | 21 => Some x21
  | 22 => Some x22 | 23 => Some x23 | 24 => Some x24 | 25 => Some x25 | 26 => Some x26
  | 27 => Some x27 | 28 => Some x28 | 29 => Some x29 | 30 => Some x30 | 31 => Some x31
  | _ => None
  end.

(** Register [i] ([x0] reads as zero). *)
Definition gpr (rf : regfile) (i : Z) : mword 64 :=
  match xreg i with Some x => rd rf x | None => zero_reg end.

(** Write register [i] (writes to [x0] are dropped). *)
Definition set_gpr (rf : regfile) (i : Z) (v : mword 64) : regfile :=
  match xreg i with Some x => upd_reg rf x v | None => rf end.

Definition is_gpr (r : register) : bool :=
  match r with
  | R_bitvector_64 r' =>
      match r' with
      | x1 | x2 | x3 | x4 | x5 | x6 | x7 | x8 | x9 | x10 | x11 | x12 | x13 | x14 | x15 | x16
      | x17 | x18 | x19 | x20 | x21 | x22 | x23 | x24 | x25 | x26 | x27 | x28 | x29 | x30
      | x31 => true
      | _ => false
      end
  | _ => false
  end.

Lemma xreg_gpr i x : xreg i = Some x -> is_gpr (R_bitvector_64 x) = true.
Proof.
  unfold xreg. destruct i as [|p|p]; try discriminate.
  repeat (destruct p as [p|p|]; try discriminate); intros [= <-]; reflexivity.
Qed.

Lemma rd_set_gpr_other rf i v r : is_gpr r = false -> rd (set_gpr rf i v) r = rd rf r.
Proof.
  intros Hr. unfold set_gpr. destruct (xreg i) as [x|] eqn:E; [|reflexivity].
  apply rd_upd_other. intros <-. apply xreg_gpr in E. congruence.
Qed.

Lemma agree_set_gpr rf i v : agree ctrl cfg rf -> agree ctrl cfg (set_gpr rf i v).
Proof.
  intros H. unfold set_gpr. destruct (xreg i) as [x|] eqn:E; [|exact H].
  apply agree_upd_data; [exact H|].
  apply xreg_gpr in E. revert E. destruct x; cbn; congruence.
Qed.

Lemma gpr_set_gpr rf i j v :
  0 <= i < 32 -> 0 <= j < 32 ->
  gpr (set_gpr rf i v) j = if (j =? 0) then zero_reg else if (i =? j) then v else gpr rf j.
Proof.
  intros Hi Hj. unfold gpr, set_gpr.
  assert (Hx : forall k, 0 <= k < 32 -> (k = 0 /\ xreg k = None) \/ (k <> 0 /\ exists x, xreg k = Some x)).
  { intros k Hk. assert (k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/
      k = 9 \/ k = 10 \/ k = 11 \/ k = 12 \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17 \/
      k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 \/ k = 24 \/ k = 25 \/ k = 26 \/
      k = 27 \/ k = 28 \/ k = 29 \/ k = 30 \/ k = 31) by lia.
    repeat match goal with H : _ \/ _ |- _ => destruct H as [->|H] end; subst;
      first [left; split; reflexivity | right; split; [discriminate|eexists; reflexivity]]. }
  destruct (Z.eqb_spec j 0) as [->|Hj0].
  - destruct (xreg i); reflexivity.
  - destruct (Hx j Hj) as [[? _]|[_ [y Hy]]]; [contradiction|]. rewrite Hy.
    destruct (Z.eqb_spec i j) as [<-|Hij].
    + rewrite Hy. exact (rd_upd_same rf (R_bitvector_64 y) v).
    + destruct (xreg i) as [x|] eqn:Ex; [|reflexivity].
      refine (rd_upd_other rf (R_bitvector_64 x) (R_bitvector_64 y) v _). intros [= ->].
      apply Hij. clear -Hi Hj Ex Hy.
      assert (i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7 \/ i = 8 \/
        i = 9 \/ i = 10 \/ i = 11 \/ i = 12 \/ i = 13 \/ i = 14 \/ i = 15 \/ i = 16 \/ i = 17 \/
        i = 18 \/ i = 19 \/ i = 20 \/ i = 21 \/ i = 22 \/ i = 23 \/ i = 24 \/ i = 25 \/ i = 26 \/
        i = 27 \/ i = 28 \/ i = 29 \/ i = 30 \/ i = 31) as Hi' by lia.
      assert (j = 0 \/ j = 1 \/ j = 2 \/ j = 3 \/ j = 4 \/ j = 5 \/ j = 6 \/ j = 7 \/ j = 8 \/
        j = 9 \/ j = 10 \/ j = 11 \/ j = 12 \/ j = 13 \/ j = 14 \/ j = 15 \/ j = 16 \/ j = 17 \/
        j = 18 \/ j = 19 \/ j = 20 \/ j = 21 \/ j = 22 \/ j = 23 \/ j = 24 \/ j = 25 \/ j = 26 \/
        j = 27 \/ j = 28 \/ j = 29 \/ j = 30 \/ j = 31) as Hj' by lia.
      repeat match goal with H : _ \/ _ |- _ => destruct H as [->|H] end; subst;
        cbn in Ex, Hy; congruence.
Qed.

Local Ltac regcases r :=
  assert (r = 0 \/ r = 1 \/ r = 2 \/ r = 3 \/ r = 4 \/ r = 5 \/ r = 6 \/ r = 7 \/ r = 8 \/
    r = 9 \/ r = 10 \/ r = 11 \/ r = 12 \/ r = 13 \/ r = 14 \/ r = 15 \/ r = 16 \/ r = 17 \/
    r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/
    r = 27 \/ r = 28 \/ r = 29 \/ r = 30 \/ r = 31) by lia;
  repeat match goal with H : _ \/ _ |- _ => destruct H as [->|H] end; subst.

Lemma rX_spec r s : 0 <= r < 32 -> runX (rX (Regno r)) s = Some (inl (gpr (regs s) r), s).
Proof. intros Hr. regcases r; reflexivity. Qed.

Lemma wX_spec r v s : 0 <= r < 32 ->
  runX (wX (Regno r) v) s = Some (inl tt, mkSailState (set_gpr (regs s) r v) (mem s)).
Proof. intros Hr. destruct s. regcases r; reflexivity. Qed.

Lemma uint_bv5 (i : mword 5) : 0 <= uint i < 32.
Proof. rewrite uint_spec. pose proof (bv_unsigned_in_range _ i). unfold bv_modulus in *. cbn in *. lia. Qed.

Lemma rX_bits_spec i s : runX (rX_bits (Regidx i)) s = Some (inl (gpr (regs s) (uint i)), s).
Proof. apply rX_spec, uint_bv5. Qed.

Lemma wX_bits_spec i v s :
  runX (wX_bits (Regidx i) v) s = Some (inl tt, mkSailState (set_gpr (regs s) (uint i) v) (mem s)).
Proof. apply wX_spec, uint_bv5. Qed.

(** ** Default hooks of the evaluator *)

Ltac ev_val_agree :=
  match goal with
  | H : agree ctrl cfg (regs ?s) |- context [rd (regs ?s) ?r] => rewrite <- (H r eq_refl)
  end.

Ltac ev_gpr :=
  lazymatch goal with
  | |- runX (rX_bits (Regidx ?i)) ?s = _ => apply rX_bits_spec
  | |- runX (wX_bits (Regidx ?i) ?v) ?s = _ => apply wX_bits_spec
  end.

(** A call whose result is a hypothesis. *)
Ltac ev_hyp :=
  match goal with
  | H : runX ?P ?s = _ |- runX ?P ?s = _ => apply H
  end.

Ltac solve_agree_extra ::= apply agree_set_gpr.
Ltac ev_val_hook ::= ev_val_agree.
Ltac ev_hook ::= first [ ev_ctrl | ev_gpr | ev_hyp ].
