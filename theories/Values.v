(** * Agreement of the arithmetic of the two models

    For every operation used by the 37 instructions, the Sail result,
    read as an L3 word with [bvw], is L3's result. *)

From stdpp Require Import base bitvector.definitions.
From SailStdpp Require Import Base ConcurrencyInterfaceV2.
From Riscv Require Import rv64d_types rv64d.
From GaletteSail Require Export ExecALU Conv.
From Stdlib Require Import Lia.

Local Open Scope Z_scope.

(** The signed value of an [n]-bit pattern [u]. *)
Definition sgn (n u : Z) : Z := if u <? 2 ^ (n - 1) then u else u - 2 ^ n.

Lemma pow2_split n : 1 <= n -> 2 ^ n = 2 * 2 ^ (n - 1).
Proof. intros H. rewrite <- Z.pow_succ_r by lia. f_equal. lia. Qed.

Lemma bv_signed_sgn {n : N} (b : bv n) : (1 <= n)%N -> bv_signed b = sgn (Z.of_N n) (bv_unsigned b).
Proof.
  intros Hn. unfold bv_signed, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus, sgn.
  pose proof (bv_unsigned_in_range _ b) as Hb. unfold bv_modulus in Hb.
  rewrite (pow2_split (Z.of_N n)) in * by lia.
  assert (0 < 2 ^ (Z.of_N n - 1)) by (apply Z.pow_pos_nonneg; lia).
  rewrite Z.mul_comm, Z.div_mul by lia.
  destruct (Z.ltb_spec (bv_unsigned b) (2 ^ (Z.of_N n - 1))).
  - rewrite Z.mod_small by lia. lia.
  - rewrite (Z.mod_eq _ (2 ^ (Z.of_N n - 1) * 2)) by lia.
    assert (Hq : (bv_unsigned b + 2 ^ (Z.of_N n - 1)) / (2 ^ (Z.of_N n - 1) * 2) = 1).
    { symmetry. apply Z.div_unique with (r := bv_unsigned b - 2 ^ (Z.of_N n - 1)); lia. }
    rewrite Hq. lia.
Qed.

Lemma sint_sgn {n} (x : mword n) : 1 <= n -> sint x = sgn n (bv_unsigned x).
Proof.
  intros H. unfold sint, SailStdpp.MachineWord.MachineWord.word_to_Z.
  rewrite bv_signed_sgn; [|unfold SailStdpp.MachineWord.MachineWord.Z_idx; lia].
  unfold SailStdpp.MachineWord.MachineWord.Z_idx. rewrite Z2N.id by lia. reflexivity.
Qed.

Lemma sign_extend'_unsigned {n} (m : Z) (x : mword n) :
  1 <= n <= m -> bv_unsigned (sign_extend' m x) = sgn n (bv_unsigned x) mod 2 ^ m.
Proof.
  intros H. unfold sign_extend', sign_extend, exts_vec, SailStdpp.MachineWord.MachineWord.sign_extend.
  rewrite bv_sign_extend_unsigned. unfold bv_wrap, bv_modulus.
  rewrite bv_signed_sgn by (unfold SailStdpp.MachineWord.MachineWord.Z_idx; lia).
  unfold SailStdpp.MachineWord.MachineWord.Z_idx. rewrite !Z2N.id by lia. reflexivity.
Qed.

(** [sw2sw] in numbers. *)
Lemma zw_sw2sw {a b : N} (x : W.word a) :
  (1 <= a)%N -> (a <= b)%N -> zw (W.sw2sw x : W.word b) = sgn (Z.of_N a) (zw x) mod 2 ^ Z.of_N b.
Proof.
  intros Ha Hab. unfold W.sw2sw. rewrite zw_n2w by lia.
  unfold Galette.HOL.src.num.extra_theories.bit.SIGN_EXTEND, W.dimindex.
  rewrite !N.max_r by lia. cbv zeta.
  pose proof (zw_range x Ha) as Hx. unfold zw in *.
  rewrite N.mod_small by (apply N2Z.inj_lt; rewrite N2Z.inj_pow; lia).
  rewrite Galette.HOL.src.num.extra_theories.bit.BIT_testbit.
  unfold sgn. set (u := W.w2n x) in *.
  assert (Hp : (2 ^ a = 2 * 2 ^ (a - 1))%N) by (rewrite <- N.pow_succ_r'; f_equal; lia).
  assert (Hu : (u < 2 ^ a)%N) by (apply N2Z.inj_lt; rewrite N2Z.inj_pow; lia).
  assert (Hpz : Z.of_N (2 ^ (a - 1)) = 2 ^ (Z.of_N a - 1)) by (rewrite N2Z.inj_pow, N2Z.inj_sub by lia; reflexivity).
  rewrite N.testbit_eqb.
  destruct (Z.ltb_spec (Z.of_N u) (2 ^ (Z.of_N a - 1))) as [Hlt|Hge].
  - rewrite N.div_small by lia. cbn. reflexivity.
  - assert (Hd : (u / 2 ^ (a - 1) = 1)%N).
    { symmetry. apply N.div_unique with (r := (u - 2 ^ (a - 1))%N); lia. }
    rewrite Hd. change ((1 mod 2 =? 1)%N) with true. cbv iota.
    assert (Hb : (2 ^ a <= 2 ^ b)%N) by (apply N.pow_le_mono_r; lia).
    rewrite N2Z.inj_add, N2Z.inj_sub, !N2Z.inj_pow by lia. change (Z.of_N 2) with 2.
    replace (2 ^ Z.of_N b - 2 ^ Z.of_N a + Z.of_N u) with ((Z.of_N u - 2 ^ Z.of_N a) + 1 * 2 ^ Z.of_N b) by lia.
    apply Z.mod_add. apply Z.pow_nonzero; lia.
Qed.

(** ** Bitwise operations *)

Lemma w2n_bvw {n : N} (x : bv n) : (1 <= n)%N -> W.w2n (bvw x) = Z.to_N (bv_unsigned x).
Proof. intros H. pose proof (zw_bvw x H) as E. unfold zw in E. lia. Qed.

Lemma Z2N_land a b : 0 <= a -> 0 <= b -> Z.to_N (Z.land a b) = N.land (Z.to_N a) (Z.to_N b).
Proof. intros. apply N2Z.inj. rewrite N2Z.inj_land, !Z2N.id; try lia. apply Z.land_nonneg; lia. Qed.
Lemma Z2N_lor a b : 0 <= a -> 0 <= b -> Z.to_N (Z.lor a b) = N.lor (Z.to_N a) (Z.to_N b).
Proof. intros. apply N2Z.inj. rewrite N2Z.inj_lor, !Z2N.id; try lia. apply Z.lor_nonneg; lia. Qed.
Lemma Z2N_lxor a b : 0 <= a -> 0 <= b -> Z.to_N (Z.lxor a b) = N.lxor (Z.to_N a) (Z.to_N b).
Proof. intros. apply N2Z.inj. rewrite N2Z.inj_lxor, !Z2N.id; try lia. apply Z.lxor_nonneg; lia. Qed.

Local Ltac bitwise :=
  intros; unfold W.word_and, W.word_or, W.word_xor, bvw at 1; f_equal;
  unfold and_vec, or_vec, xor_vec, word_binop, SailStdpp.MachineWord.MachineWord.and,
    SailStdpp.MachineWord.MachineWord.or, SailStdpp.MachineWord.MachineWord.xor;
  rewrite ?bv_and_unsigned, ?bv_or_unsigned, ?bv_xor_unsigned; rewrite !w2n_bvw by nsize;
  repeat match goal with
  | x : mword 64 |- _ =>
      lazymatch goal with _ : 0 <= bv_unsigned x < _ |- _ => fail | _ => pose proof (bv_unsigned_in_range _ x) end
  end.

Lemma bvw_and (x y : mword 64) : bvw (and_vec x y) = W.word_and (bvw x) (bvw y).
Proof. bitwise. apply Z2N_land; lia. Qed.

Lemma bvw_or (x y : mword 64) : bvw (or_vec x y) = W.word_or (bvw x) (bvw y).
Proof. bitwise. apply Z2N_lor; lia. Qed.

Lemma bvw_xor (x y : mword 64) : bvw (xor_vec x y) = W.word_xor (bvw x) (bvw y).
Proof. bitwise. apply Z2N_lxor; lia. Qed.

Lemma bvw_sub (x y : mword 64) : bvw (sub_vec x y) = W.word_sub (bvw x) (bvw y).
Proof.
  apply bvw_eq_zw; [nsize|]. rewrite zw_sub by nsize. rewrite !zw_bvw by nsize.
  rewrite sub_vec_unsigned. reflexivity.
Qed.

Lemma bvw_sign_extend12 (i : W.word 12) :
  bvw (sign_extend' 64 (Z_to_bv 12 (zw i) : mword 12)) = (W.sw2sw i : W.word 64).
Proof.
  apply bvw_eq_zw; [nsize|]. rewrite zw_sw2sw by nsize.
  rewrite sign_extend'_unsigned by lia. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  pose proof (zw_range i ltac:(lia)). cbn [Z.of_N] in *. rewrite (Z.mod_small (zw i)) by lia.
  reflexivity.
Qed.
