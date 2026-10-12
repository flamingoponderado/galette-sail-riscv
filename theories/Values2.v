(** * Agreement of comparisons, shifts and multiplication *)

From stdpp Require Import base bitvector.definitions.
From SailStdpp Require Import Base ConcurrencyInterfaceV2.
From Riscv Require Import rv64d_types rv64d riscv_extras.
From GaletteSail Require Export Values.
From Stdlib Require Import Lia.

Local Open Scope Z_scope.

Lemma testbit_top (q k : N) : (q < 2 ^ (k + 1))%N -> N.testbit q k = (2 ^ k <=? q)%N.
Proof.
  intros H. rewrite N.testbit_eqb.
  destruct (N.leb_spec (2 ^ k) q) as [Hle|Hlt].
  - assert (Hd : (q / 2 ^ k = 1)%N).
    { symmetry. apply N.div_unique with (r := (q - 2 ^ k)%N); [|lia].
      rewrite N.pow_add_r in H. cbn in H. lia. }
    rewrite Hd. reflexivity.
  - rewrite N.div_small by exact Hlt. reflexivity.
Qed.

(** [nzcv]'s carry: [b <> 0] and [a >= b]. *)
Lemma word_lo_spec (x y : W.word 64) : W.word_lo x y = (zw x <? zw y).
Proof.
  unfold W.word_lo, W.nzcv. cbv zeta.
  unfold W.word_2comp, Galette.Base.bool_decide.
  pose proof (zw_range x ltac:(lia)) as Hx. pose proof (zw_range y ltac:(lia)) as Hy.
  cbn [Z.of_N] in Hx, Hy. unfold zw in *.
  destruct (Galette.Base.decide (y = W.n2w 0)) as [->|Hne].
  - rewrite orb_true_r. cbn. rewrite N.Div0.mod_0_l. destruct (Z.ltb_spec (Z.of_N (W.w2n x)) (Z.of_N 0)); [lia|reflexivity].
  - rewrite orb_false_r. rewrite Galette.HOL.src.num.extra_theories.bit.BIT_testbit.
    assert (Hy0 : Z.of_N (W.w2n y) <> 0).
    { intros E. apply Hne. apply word_eq_zw. rewrite zw_n2w by lia. unfold zw. rewrite E. reflexivity. }
    rewrite W.w2n_n2w. unfold W.dimword, W.dimindex. change (N.max 1 64) with 64%N.
    change (2 ^ 64)%N with 18446744073709551616%N. change (2 ^ 64) with 18446744073709551616 in Hx, Hy.
    rewrite (N.mod_small (18446744073709551616 - W.w2n y)) by lia.
    rewrite testbit_top by (change (2 ^ (64 + 1))%N with 36893488147419103232%N; lia).
    change (2 ^ 64)%N with 18446744073709551616%N.
    destruct (N.leb_spec 18446744073709551616 (W.w2n x + (18446744073709551616 - W.w2n y))) as [H|H];
      destruct (Z.ltb_spec (Z.of_N (W.w2n x)) (Z.of_N (W.w2n y))); cbn [negb]; first [reflexivity | exfalso; lia].
Qed.

Lemma v2w_1_true : (Galette.HOL.src.n_bit.bitstring.v2w [true] : W.word 64) = W.n2w 1.
Proof. apply word_eq_zw. unfold zw. vm_compute. reflexivity. Qed.

Lemma v2w_1_false : (Galette.HOL.src.n_bit.bitstring.v2w [false] : W.word 64) = W.n2w 0.
Proof. apply word_eq_zw. unfold zw. vm_compute. reflexivity. Qed.

Lemma bvw_bit_true : bvw (zero_extend' 64 (bool_to_bit true)) = W.n2w 1.
Proof. apply word_eq_zw. unfold zw. vm_compute. reflexivity. Qed.

Lemma bvw_bit_false : bvw (zero_extend' 64 (bool_to_bit false)) = W.n2w 0.
Proof. apply word_eq_zw. unfold zw. vm_compute. reflexivity. Qed.

Lemma word_lo_bvw (x y : mword 64) : W.word_lo (bvw x) (bvw y) = zopz0zI_u x y.
Proof. rewrite word_lo_spec, !zw_bvw by nsize. unfold zopz0zI_u. rewrite !uint_spec. reflexivity. Qed.

Lemma bvw_sltu (x y : mword 64) :
  bvw (zero_extend' 64 (bool_to_bit (zopz0zI_u x y))) =
  (Galette.HOL.src.n_bit.bitstring.v2w [W.word_lo (bvw x) (bvw y)] : W.word 64).
Proof.
  rewrite word_lo_bvw. destruct (zopz0zI_u x y).
  - rewrite bvw_bit_true, v2w_1_true. reflexivity.
  - rewrite bvw_bit_false, v2w_1_false. reflexivity.
Qed.

(** ** Shifts *)

Lemma shamt_unsigned (y : mword 64) :
  int_of_mword false (subrange_vec_dec y (log2_xlen - 1) 0) = bv_unsigned y mod 64.
Proof.
  unfold int_of_mword. change (Z.of_N (SailStdpp.MachineWord.MachineWord.word_to_N ?x)) with (uint x).
  rewrite uint_spec. rewrite subrange_vec_dec_unsigned by (unfold log2_xlen; lia).
  unfold log2_xlen. cbn. rewrite Z.div_1_r. reflexivity.
Qed.

Lemma zw_shamt (y : W.word 64) :
  zw (W.w2w (W.word_extract 5 0 y : W.word 6) : W.word 64) = zw y mod 64.
Proof.
  rewrite zw_w2w by lia. rewrite zw_extract by lia. cbn [Z.of_N].
  pose proof (zw_range y ltac:(lia)). cbn in *.
  change (2 ^ 0) with 1. change (2 ^ (5 + 1 - 0)) with 64. change (2 ^ 6) with 64. rewrite Z.div_1_r.
  rewrite Z.mod_mod by lia.
  rewrite Z.mod_small by (pose proof (Z.mod_pos_bound (zw y) 64); lia). reflexivity.
Qed.

Lemma zw_shamt' (y : W.word 64) :
  Z.of_N (W.w2n (W.w2w (W.word_extract 5 0 y : W.word 6) : W.word 64)) = zw y mod 64.
Proof. apply zw_shamt. Qed.

Lemma shamt_lt (y : W.word 64) : (W.w2n (W.w2w (W.word_extract 5 0 y : W.word 6) : W.word 64) < 64)%N.
Proof. apply N2Z.inj_lt. rewrite zw_shamt'. pose proof (Z.mod_pos_bound (zw y) 64). lia. Qed.

Lemma zw_lsl (x : W.word 64) n : (n < 64)%N -> zw (W.word_lsl x n) = (zw x * 2 ^ Z.of_N n) mod 2 ^ 64.
Proof.
  intros H. unfold W.word_lsl, W.dimindex. change (N.max 1 64) with 64%N.
  destruct (N.ltb_spec (64 - 1) n); [lia|]. rewrite zw_n2w by lia. unfold zw.
  rewrite N2Z.inj_mul, N2Z.inj_pow. reflexivity.
Qed.

Lemma zw_lsr (x : W.word 64) n : (n < 64)%N -> zw (W.word_lsr x n) = zw x / 2 ^ Z.of_N n.
Proof.
  intros H. unfold W.word_lsr, W.word_bits, W.dimindex. change (N.max 1 64) with 64%N.
  rewrite zw_n2w by lia. unfold zw.
  unfold Galette.HOL.src.num.extra_theories.bit.BITS, Galette.HOL.src.num.extra_theories.bit.MOD_2EXP,
    Galette.HOL.src.num.extra_theories.bit.DIV_2EXP, Galette.HOL.src.num.theories.arithmetic.MIN.
  pose proof (W.w2n_lt x) as Hx. unfold W.dimword, W.dimindex in Hx. change (N.max 1 64) with 64%N in Hx.
  cbn [N.ltb]. replace (if (64 - 1 <? 64 - 1)%N then (64 - 1)%N else (64 - 1)%N) with 63%N
    by (destruct (N.ltb _ _); reflexivity).
  rewrite N.mod_small.
  - rewrite N2Z.inj_div, N2Z.inj_pow. rewrite Z.mod_small; [reflexivity|].
    split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|].
    apply Z.lt_le_trans with (2 ^ 64); [lia|]. rewrite <- Z.pow_add_r by lia. apply Z.pow_le_mono_r; lia.
  - apply N.Div0.div_lt_upper_bound.
    rewrite <- N.pow_add_r. apply N.lt_le_trans with (2 ^ 64)%N; [exact Hx|apply N.pow_le_mono_r; lia].
Qed.

Lemma bvw_shiftl (x y : mword 64) :
  bvw (shift_bits_left x (subrange_vec_dec y (log2_xlen - 1) 0)) =
  W.word_lsl_bv (bvw x) (W.w2w (W.word_extract 5 0 (bvw y) : W.word 6)).
Proof.
  apply bvw_eq_zw; [nsize|]. unfold W.word_lsl_bv.
  rewrite zw_lsl by apply shamt_lt. rewrite zw_shamt', !zw_bvw by nsize.
  unfold shift_bits_left, shiftl, SailStdpp.MachineWord.MachineWord.logical_shift_left.
  rewrite shamt_unsigned. rewrite bv_shiftl_unsigned.
  unfold SailStdpp.MachineWord.MachineWord.N_to_word. rewrite Z_to_bv_unsigned.
  unfold bv_wrap, bv_modulus, SailStdpp.MachineWord.MachineWord.Z_idx. cbn [Z.of_N Z.to_N].
  pose proof (Z.mod_pos_bound (bv_unsigned y) 64).
  rewrite Z2N.id by lia. rewrite (Z.mod_small (bv_unsigned y mod 64)) by lia.
  rewrite Z.shiftl_mul_pow2 by lia. reflexivity.
Qed.

Lemma bvw_shiftr (x y : mword 64) :
  bvw (shift_bits_right x (subrange_vec_dec y (log2_xlen - 1) 0)) =
  W.word_lsr_bv (bvw x) (W.w2w (W.word_extract 5 0 (bvw y) : W.word 6)).
Proof.
  apply bvw_eq_zw; [nsize|]. unfold W.word_lsr_bv.
  rewrite zw_lsr by apply shamt_lt. rewrite zw_shamt', !zw_bvw by nsize.
  unfold shift_bits_right, shiftr, SailStdpp.MachineWord.MachineWord.logical_shift_right.
  rewrite shamt_unsigned. rewrite bv_shiftr_unsigned.
  unfold SailStdpp.MachineWord.MachineWord.N_to_word. rewrite Z_to_bv_unsigned.
  unfold bv_wrap, bv_modulus, SailStdpp.MachineWord.MachineWord.Z_idx. cbn [Z.of_N Z.to_N].
  pose proof (Z.mod_pos_bound (bv_unsigned y) 64).
  rewrite Z2N.id by lia. rewrite (Z.mod_small (bv_unsigned y mod 64)) by lia.
  rewrite Z.shiftr_div_pow2 by lia. reflexivity.
Qed.
