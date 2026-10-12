(** * Between L3's words and Sail's bit vectors

    Galette's HOL words ([words.word n], a natural number below [2^n]) and
    stdpp's bit vectors ([bv n], an integer below [2^n]) are related by
    [bvw] and [zw]; [sobs] views a Sail state as the abstract state
    ([riscv_targetProof.astate]: registers, PC, memory) that the L3 step
    theorem [step_thm] speaks about. *)

From stdpp Require Import base bitvector.definitions.
From SailStdpp Require Import Base ConcurrencyInterfaceV2.
From Riscv Require Import rv64d_types rv64d.
From GaletteSail Require Export Gpr BvSolve.
From Galette.HOL.src.n_bit Require words.
From Galette.HOL.src.combin Require combin.
From Galette.cakeml.compiler.encoders.riscv.proofs Require riscv_targetProof.
From Stdlib Require Import Lia.

Module W := Galette.HOL.src.n_bit.words.
Module P := Galette.cakeml.compiler.encoders.riscv.proofs.riscv_targetProof.

Local Open Scope Z_scope.

(** ** Conversions *)

Definition zw {n : N} (x : W.word n) : Z := Z.of_N (W.w2n x).
Definition bvw {n : N} (x : bv n) : W.word n := W.n2w (Z.to_N (bv_unsigned x)).
Definition wbv {n : N} (x : W.word n) : bv n := Z_to_bv n (zw x).

Lemma dimword_pos (n : N) : (1 <= n)%N -> Z.of_N (W.dimword n) = 2 ^ Z.of_N n.
Proof.
  intros H. unfold W.dimword, W.dimindex. rewrite N.max_r by lia.
  rewrite N2Z.inj_pow. reflexivity.
Qed.

Lemma zw_range {n : N} (x : W.word n) : (1 <= n)%N -> 0 <= zw x < 2 ^ Z.of_N n.
Proof.
  intros H. unfold zw. pose proof (W.w2n_lt x) as Hl. rewrite <- dimword_pos by exact H. lia.
Qed.

Lemma zw_n2w {n : N} (k : N) : (1 <= n)%N -> zw (W.n2w k : W.word n) = Z.of_N k mod 2 ^ Z.of_N n.
Proof.
  intros H. unfold zw. rewrite W.w2n_n2w. rewrite <- dimword_pos by exact H.
  rewrite N2Z.inj_mod. reflexivity.
Qed.

Lemma zw_bvw {n : N} (x : bv n) : (1 <= n)%N -> zw (bvw x) = bv_unsigned x.
Proof.
  intros H. unfold bvw. rewrite zw_n2w by exact H.
  pose proof (bv_unsigned_in_range _ x). unfold bv_modulus in *.
  rewrite Z2N.id by lia. apply Z.mod_small. lia.
Qed.

Lemma word_eq_zw {n : N} (x y : W.word n) : zw x = zw y -> x = y.
Proof. intros H. apply W.word_eq_w2n. unfold zw in H. lia. Qed.

Lemma bvw_wbv {n : N} (x : W.word n) : (1 <= n)%N -> bvw (wbv x) = x.
Proof.
  intros H. apply word_eq_zw. rewrite zw_bvw by exact H. unfold wbv.
  rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. apply Z.mod_small.
  apply zw_range, H.
Qed.

Lemma wbv_unsigned {n : N} (x : W.word n) : (1 <= n)%N -> bv_unsigned (wbv x) = zw x.
Proof.
  intros H. unfold wbv. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  apply Z.mod_small, zw_range, H.
Qed.

Lemma wbv_bvw {n : N} (x : bv n) : (1 <= n)%N -> wbv (bvw x) = x.
Proof. intros H. apply bv_eq. rewrite wbv_unsigned, zw_bvw by exact H. reflexivity. Qed.

(** ** Words as numbers *)

Lemma zw_add {n : N} (x y : W.word n) : (1 <= n)%N ->
  zw (W.word_add x y) = (zw x + zw y) mod 2 ^ Z.of_N n.
Proof. intros H. unfold W.word_add. rewrite zw_n2w by exact H. unfold zw. f_equal. lia. Qed.

(** ** The abstract view of a Sail state *)

(** Register [r] of the Sail state, as an L3 word ([x0] reads as 0). *)
Definition sgpr (rf : regfile) (r : W.word 5) : W.word 64 := bvw (gpr rf (zw r)).

Definition sobs (s : SailState) : P.astate :=
  P.mk_astate (sgpr (regs s)) (bvw (rd (regs s) PC)) (fun a => bvw (mem s (wbv a))).

(** Two abstract states agree, except possibly on the raw value of [x0]. *)
Definition aeq (A B : P.astate) : Prop :=
  (forall r, r <> W.n2w 0 -> P.aregs A r = P.aregs B r) /\
  P.apc A = P.apc B /\ P.amem A = P.amem B.

Lemma zw_w2w {a b : N} (x : W.word a) : (1 <= b)%N -> zw (W.w2w x : W.word b) = zw x mod 2 ^ Z.of_N b.
Proof. intros H. unfold W.w2w. apply zw_n2w, H. Qed.

Lemma zw_concat {a b c : N} (v : W.word a) (w : W.word b) :
  (1 <= a)%N -> (1 <= b)%N -> (1 <= c)%N ->
  zw (W.word_concat v w : W.word c) = (zw v * 2 ^ Z.of_N b + zw w) mod 2 ^ Z.of_N c.
Proof.
  intros Ha Hb Hc. unfold W.word_concat, W.word_join.
  rewrite zw_w2w by exact Hc.
  pose proof (zw_range v Ha) as Hv. pose proof (zw_range w Hb) as Hw.
  assert (Hab : (1 <= a + b)%N) by lia.
  assert (Hdb : W.dimindex b = b) by (unfold W.dimindex; lia).
  assert (Hdab : W.dimindex (a + b) = (a + b)%N) by (unfold W.dimindex; lia).
  f_equal. unfold W.word_or. rewrite zw_n2w by exact Hab.
  unfold W.word_lsl. rewrite Hdb, Hdab.
  destruct (N.ltb_spec (a + b - 1) b) as [Hlt|Hge]; [lia|].
  rewrite N2Z.inj_lor. fold (@zw (a + b) (W.n2w (W.w2n (W.w2w v : W.word (a + b)) * 2 ^ b))).
  fold (@zw (a + b) (W.w2w w)).
  rewrite zw_n2w by exact Hab. rewrite N2Z.inj_mul, N2Z.inj_pow.
  fold (@zw (a + b) (W.w2w v)).
  rewrite !zw_w2w by exact Hab.
  assert (2 ^ Z.of_N a <= 2 ^ Z.of_N (a + b)) by (apply Z.pow_le_mono_r; lia).
  assert (2 ^ Z.of_N b <= 2 ^ Z.of_N (a + b)) by (apply Z.pow_le_mono_r; lia).
  rewrite (Z.mod_small (zw v)) by lia. rewrite (Z.mod_small (zw w)) by lia.
  assert (E : 2 ^ Z.of_N (a + b) = 2 ^ Z.of_N a * 2 ^ Z.of_N b) by (rewrite N2Z.inj_add; apply Z.pow_add_r; lia).
  assert (zw v * 2 ^ Z.of_N b < 2 ^ Z.of_N (a + b)) by (rewrite E; apply Z.mul_lt_mono_pos_r; lia).
  assert (0 <= zw v * 2 ^ Z.of_N b) by (apply Z.mul_nonneg_nonneg; lia).
  rewrite (Z.mod_small (zw v * 2 ^ Z.of_N b)) by lia.
  rewrite Z.mod_small.
  - apply lor_mul_pow2; lia.
  - rewrite lor_mul_pow2 by lia.
    assert (zw v * 2 ^ Z.of_N b <= (2 ^ Z.of_N a - 1) * 2 ^ Z.of_N b) by (apply Z.mul_le_mono_nonneg_r; lia).
    lia.
Qed.

Lemma zw_extract {a b : N} (h l : N) (x : W.word a) :
  (1 <= a)%N -> (1 <= b)%N -> (h < a)%N -> (l <= h + 1)%N ->
  zw (W.word_extract h l x : W.word b) =
  (zw x / 2 ^ Z.of_N l) mod 2 ^ (Z.of_N h + 1 - Z.of_N l) mod 2 ^ Z.of_N b.
Proof.
  intros Ha Hb Hh Hlh. unfold W.word_extract, Basics.compose. rewrite zw_w2w by exact Hb.
  f_equal. unfold W.word_bits. rewrite zw_n2w by exact Ha.
  assert (Hd : W.dimindex a = a) by (unfold W.dimindex; lia).
  rewrite Hd. unfold Galette.HOL.src.num.extra_theories.bit.BITS,
    Galette.HOL.src.num.extra_theories.bit.MOD_2EXP, Galette.HOL.src.num.extra_theories.bit.DIV_2EXP.
  rewrite N2Z.inj_mod, N2Z.inj_div, !N2Z.inj_pow. fold (zw x).
  replace (Galette.HOL.src.num.theories.arithmetic.MIN h (a - 1)) with h
    by (unfold Galette.HOL.src.num.theories.arithmetic.MIN; destruct (N.ltb_spec h (a - 1)); lia).
  assert (Hl : (l <= N.succ h)%N) by lia.
  rewrite N2Z.inj_sub by exact Hl. rewrite N2Z.inj_succ.
  pose proof (zw_range x Ha).
  assert (0 < 2 ^ (Z.succ (Z.of_N h) - Z.of_N l)) by (apply Z.pow_pos_nonneg; lia).
  rewrite (Z.mod_small ((zw x / 2 ^ Z.of_N l) mod 2 ^ (Z.succ (Z.of_N h) - Z.of_N l))).
  + f_equal; try lia.
  + pose proof (Z.mod_pos_bound (zw x / 2 ^ Z.of_N l) (2 ^ (Z.succ (Z.of_N h) - Z.of_N l))).
    assert (2 ^ (Z.succ (Z.of_N h) - Z.of_N l) <= 2 ^ Z.of_N a) by (apply Z.pow_le_mono_r; lia).
    lia.
Qed.

(** ** Registers *)

Lemma zw_eq_0 {n : N} (x : W.word n) : (1 <= n)%N -> x = W.n2w 0 <-> zw x = 0.
Proof.
  intros H. split.
  - intros ->. rewrite zw_n2w by exact H. reflexivity.
  - intros E. apply word_eq_zw. rewrite E, zw_n2w by exact H. reflexivity.
Qed.

Lemma zw_inj {n : N} (x y : W.word n) : x = y <-> zw x = zw y.
Proof. split; [intros ->; reflexivity|apply word_eq_zw]. Qed.

Lemma bvw_zero_reg : bvw zero_reg = (W.n2w 0 : W.word 64).
Proof. reflexivity. Qed.

Lemma rreg_sgpr rf r : P.rreg (sgpr rf) r = sgpr rf r.
Proof.
  unfold P.rreg, sgpr, Galette.Base.bool_decide.
  destruct (Galette.Base.decide (r = W.n2w 0)) as [->|]; [|reflexivity].
  unfold gpr. rewrite zw_n2w by lia. reflexivity.
Qed.

Lemma sgpr_set_gpr rf (d : W.word 5) v r :
  r <> W.n2w 0 -> sgpr (set_gpr rf (zw d) v) r = P.wreg d (bvw v) (sgpr rf) r.
Proof.
  intros Hr. unfold sgpr, P.wreg, combin.UPDATE, Galette.Base.bool_decide.
  pose proof (zw_range d ltac:(lia)) as Hd. pose proof (zw_range r ltac:(lia)) as Hr'.
  cbn [Z.of_N] in Hd, Hr'.
  rewrite gpr_set_gpr by lia.
  assert (Hr0 : zw r <> 0) by (intros E; apply Hr, zw_eq_0; [lia|exact E]).
  destruct (Z.eqb_spec (zw r) 0) as [E|_]; [contradiction|].
  destruct (Galette.Base.decide (d = W.n2w 0)) as [Ed|Ed].
  - apply zw_eq_0 in Ed; [|lia]. destruct (Z.eqb_spec (zw d) (zw r)); [lia|reflexivity].
  - destruct (Galette.Base.decide (d = r)) as [<-|Edr].
    + rewrite Z.eqb_refl. reflexivity.
    + destruct (Z.eqb_spec (zw d) (zw r)) as [E|]; [|reflexivity].
      exfalso. apply Edr, word_eq_zw, E.
Qed.

Lemma sgpr_upd_other rf r v x : is_gpr r = false -> sgpr (upd_reg rf r v) x = sgpr rf x.
Proof.
  intros H. unfold sgpr, gpr. destruct (xreg (zw x)) as [y|] eqn:E; [|reflexivity].
  apply xreg_gpr in E. rewrite (rd_upd_other rf r (R_bitvector_64 y) v ltac:(congruence)). reflexivity.
Qed.

(** ** Operations *)

Ltac nsize := first [ lia | unfold SailStdpp.MachineWord.MachineWord.Z_idx; cbn; lia ].

Lemma bvw_eq_zw {n : N} (x : bv n) (y : W.word n) : (1 <= n)%N -> bv_unsigned x = zw y -> bvw x = y.
Proof. intros H E. apply word_eq_zw. rewrite zw_bvw by exact H. exact E. Qed.

Lemma bvw_add_vec (x y : mword 64) : bvw (add_vec x y) = W.word_add (bvw x) (bvw y).
Proof.
  apply bvw_eq_zw; [nsize|]. rewrite zw_add by nsize. rewrite !zw_bvw by nsize.
  rewrite add_vec_unsigned. reflexivity.
Qed.

Lemma bvw_add_vec_int (x : mword 64) z : 0 <= z -> bvw (add_vec_int x z) = W.word_add (bvw x) (W.n2w (Z.to_N z)).
Proof.
  intros Hz. apply bvw_eq_zw; [nsize|]. rewrite zw_add by nsize. rewrite zw_bvw, zw_n2w by nsize.
  rewrite add_vec_int_unsigned. unfold bv_wrap, bv_modulus. cbn [Z.of_N Z.to_N].
  rewrite Z2N.id by exact Hz. rewrite Zplus_mod_idemp_r. reflexivity.
Qed.
