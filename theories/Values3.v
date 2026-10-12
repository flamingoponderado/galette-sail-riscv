(** * Agreement of multiplication, division, upper immediates and immediate shifts *)

From stdpp Require Import base bitvector.definitions.
From SailStdpp Require Import Base ConcurrencyInterfaceV2.
From Riscv Require Import rv64d_types rv64d riscv_extras.
From GaletteSail Require Export Values2.
From Stdlib Require Import Lia Znumtheory.

Local Open Scope Z_scope.

Lemma to_bits_truncate_unsigned l n : 0 <= l -> bv_unsigned (to_bits_truncate l n) = n mod 2 ^ l.
Proof.
  intros Hl. unfold to_bits_truncate, get_slice_int.
  assert (E : forall z, z = n -> bv_unsigned (get_slice_int' l z 0) = n mod 2 ^ l).
  { intros z ->. unfold get_slice_int'.
    destruct (sumbool_of_bool (l >=? 0)) as [e|e]; [|apply Z.geb_le in Hl; congruence].
    cbv zeta. rewrite autocast_unsigned by lia.
    rewrite subrange_vec_dec_unsigned by lia.
    unfold mword_of_int, SailStdpp.MachineWord.MachineWord.Z_to_word. rewrite Z_to_bv_unsigned.
    unfold bv_wrap, bv_modulus, SailStdpp.MachineWord.MachineWord.Z_idx.
    rewrite Z2N.id by lia. rewrite Z.pow_0_r, Z.div_1_r.
    replace (0 + l - 1 + 1) with l by lia. replace (0 + l - 1 - 0 + 1) with l by lia.
    apply Z.mod_mod. apply Z.pow_nonzero; lia. }
  destruct n; apply E; reflexivity.
Qed.

Lemma sgn_mod n u : 1 <= n -> sgn n u mod 2 ^ n = u mod 2 ^ n.
Proof.
  intros H. unfold sgn. destruct (u <? 2 ^ (n - 1)); [reflexivity|].
  replace (u - 2 ^ n) with (u + (-1) * 2 ^ n) by lia. apply Z.mod_add. apply Z.pow_nonzero; lia.
Qed.

Lemma mod_pow2_mod a k m : 0 <= k <= m -> (a mod 2 ^ m) mod 2 ^ k = a mod 2 ^ k.
Proof.
  intros H. symmetry. apply Znumtheory.Zmod_div_mod; [apply Z.pow_pos_nonneg; lia..|].
  exists (2 ^ (m - k)). rewrite <- Z.pow_add_r by lia. f_equal. lia.
Qed.

Lemma bvw_mul (x y : mword 64) :
  bvw (mult_to_bits_half xlen Signed Signed x y Low) = W.word_mul (bvw x) (bvw y).
Proof.
  apply bvw_eq_zw; [nsize|]. unfold W.word_mul. rewrite zw_n2w by nsize. unfold zw.
  rewrite N2Z.inj_mul. rewrite !w2n_bvw by nsize. rewrite !Z2N.id by (apply bv_unsigned_in_range).
  unfold mult_to_bits_half, xlen. cbn [Z.mul].
  rewrite autocast_unsigned by reflexivity. rewrite subrange_vec_dec_unsigned by lia.
  rewrite to_bits_truncate_unsigned by lia. rewrite !sint_sgn by lia. cbn [Z.of_N].
  rewrite Z.pow_0_r, Z.div_1_r. replace (64 - 1 - 0 + 1) with 64 by lia.
  rewrite mod_pow2_mod by lia.
  rewrite Z.mul_mod, !sgn_mod, <- Z.mul_mod by lia. reflexivity.
Qed.

Lemma bvw_mulhu (x y : mword 64) :
  bvw (mult_to_bits_half xlen Unsigned Unsigned x y High) =
  (W.word_extract 127 64 (W.word_mul (W.w2w (bvw x) : W.word 128) (W.w2w (bvw y))) : W.word 64).
Proof.
  apply bvw_eq_zw; [nsize|]. rewrite zw_extract by nsize. unfold W.word_mul. rewrite zw_n2w by nsize.
  rewrite N2Z.inj_mul.
  change (Z.of_N (W.w2n (W.w2w (bvw x)))) with (zw (W.w2w (bvw x) : W.word 128)).
  change (Z.of_N (W.w2n (W.w2w (bvw y)))) with (zw (W.w2w (bvw y) : W.word 128)).
  rewrite !zw_w2w, !zw_bvw by nsize. unfold SailStdpp.MachineWord.MachineWord.Z_idx.
  unfold mult_to_bits_half, xlen. cbn [Z.mul Z.of_N].
  rewrite autocast_unsigned by reflexivity. rewrite subrange_vec_dec_unsigned by nsize.
  rewrite to_bits_truncate_unsigned by nsize. rewrite !uint_spec.
  pose proof (bv_unsigned_in_range _ x) as Hx. pose proof (bv_unsigned_in_range _ y) as Hy.
  unfold bv_modulus in Hx, Hy. change (Z.of_N (Z.to_N 64)) with 64 in *.
  destruct x as [X Hxw], y as [Y Hyw].
  repeat match goal with
  | |- context [bv_unsigned (BV _ ?z)] => change (bv_unsigned (BV _ z)) with z
  | H : context [bv_unsigned (BV _ ?z)] |- _ => change (bv_unsigned (BV _ z)) with z in H
  end.
  change (2 * 64) with 128. change (2 ^ (128 - 1 - 64 + 1)) with (2 ^ 64). change (2 ^ (127 + 1 - 64)) with (2 ^ 64).
  change (2 ^ Z.of_N (SailStdpp.MachineWord.MachineWord.Z_idx 64)) with (2 ^ 64) in Hx, Hy.
  rewrite (Z.mod_small X (2 ^ 128)) by (split; [lia|]; apply Z.lt_trans with (2 ^ 64); [lia|reflexivity]).
  rewrite (Z.mod_small Y (2 ^ 128)) by (split; [lia|]; apply Z.lt_trans with (2 ^ 64); [lia|reflexivity]).
  rewrite Z.mod_mod by (apply Z.pow_nonzero; lia). reflexivity.
Qed.

Lemma bvw_utype_off (i : W.word 20) :
  bvw (utype_off (Z_to_bv 20 (zw i))) =
  (W.sw2sw (W.word_concat i (W.n2w 0 : W.word 12) : W.word 32) : W.word 64).
Proof.
  apply bvw_eq_zw; [nsize|]. rewrite zw_sw2sw by nsize. rewrite zw_concat by nsize.
  rewrite zw_n2w by nsize. unfold utype_off. rewrite sign_extend'_unsigned by nsize.
  rewrite concat_vec_unsigned by nsize. rewrite Z_to_bv_unsigned. cbn [Z.of_N].
  pose proof (zw_range i ltac:(lia)). cbn [Z.of_N] in *. unfold bv_wrap, bv_modulus. cbn [Z.of_N Z.to_N].
  change (bv_unsigned (Ox"000" : mword 12)) with 0.
  rewrite (Z.mod_small (zw i)) by nsize. rewrite (Z.mod_small 0) by nsize.
  rewrite (Z.mod_small (zw i * 2 ^ 12 + 0)) by nsize. reflexivity.
Qed.

Lemma bvw_shiftl_imm (x : mword 64) (sh : W.word 6) :
  bvw (shift_bits_left x (subrange_vec_dec (Z_to_bv 6 (zw sh) : mword 6) (log2_xlen - 1) 0)) =
  W.word_lsl (bvw x) (W.w2n sh).
Proof.
  apply bvw_eq_zw; [nsize|]. pose proof (W.w2n_lt sh) as Hs. unfold W.dimword, W.dimindex in Hs.
  change (N.max 1 6) with 6%N in Hs. rewrite zw_lsl by (cbn in Hs; lia). rewrite zw_bvw by nsize.
  unfold shift_bits_left, shiftl, SailStdpp.MachineWord.MachineWord.logical_shift_left.
  unfold int_of_mword. change (Z.of_N (SailStdpp.MachineWord.MachineWord.word_to_N ?x)) with (uint x).
  rewrite uint_spec. rewrite subrange_vec_dec_unsigned by (unfold log2_xlen; lia).
  rewrite Z_to_bv_unsigned. rewrite bv_shiftl_unsigned.
  unfold SailStdpp.MachineWord.MachineWord.N_to_word. rewrite Z_to_bv_unsigned.
  unfold bv_wrap, bv_modulus, SailStdpp.MachineWord.MachineWord.Z_idx, log2_xlen, zw. cbn [Z.of_N Z.to_N].
  cbn in Hs. rewrite (Z.mod_small (Z.of_N (W.w2n sh)) (2 ^ 6)) by nsize.
  rewrite Z.div_1_r. rewrite (Z.mod_small (Z.of_N (W.w2n sh)) (2 ^ (6 - 1 - 0 + 1))) by (cbn; lia).
  rewrite Z2N.id by nsize. rewrite (Z.mod_small (Z.of_N (W.w2n sh))) by nsize.
  rewrite Z.shiftl_mul_pow2 by nsize. reflexivity.
Qed.

Lemma bvw_shiftr_imm (x : mword 64) (sh : W.word 6) :
  bvw (shift_bits_right x (subrange_vec_dec (Z_to_bv 6 (zw sh) : mword 6) (log2_xlen - 1) 0)) =
  W.word_lsr (bvw x) (W.w2n sh).
Proof.
  apply bvw_eq_zw; [nsize|]. pose proof (W.w2n_lt sh) as Hs. unfold W.dimword, W.dimindex in Hs.
  change (N.max 1 6) with 6%N in Hs. rewrite zw_lsr by (cbn in Hs; lia). rewrite zw_bvw by nsize.
  unfold shift_bits_right, shiftr, SailStdpp.MachineWord.MachineWord.logical_shift_right.
  unfold int_of_mword. change (Z.of_N (SailStdpp.MachineWord.MachineWord.word_to_N ?x)) with (uint x).
  rewrite uint_spec. rewrite subrange_vec_dec_unsigned by (unfold log2_xlen; lia).
  rewrite Z_to_bv_unsigned. rewrite bv_shiftr_unsigned.
  unfold SailStdpp.MachineWord.MachineWord.N_to_word. rewrite Z_to_bv_unsigned.
  unfold bv_wrap, bv_modulus, SailStdpp.MachineWord.MachineWord.Z_idx, log2_xlen, zw. cbn [Z.of_N Z.to_N].
  cbn in Hs. rewrite (Z.mod_small (Z.of_N (W.w2n sh)) (2 ^ 6)) by nsize.
  rewrite Z.div_1_r. rewrite (Z.mod_small (Z.of_N (W.w2n sh)) (2 ^ (6 - 1 - 0 + 1))) by (cbn; lia).
  rewrite Z2N.id by nsize. rewrite (Z.mod_small (Z.of_N (W.w2n sh))) by nsize.
  rewrite Z.shiftr_div_pow2 by nsize. reflexivity.
Qed.

(** ** Arithmetic shift right *)

Lemma msb64 (x : W.word 64) : W.word_msb x = (2 ^ 63 <=? zw x).
Proof.
  unfold W.word_msb, W.dimindex. change (N.max 1 64 - 1)%N with 63%N.
  rewrite Galette.HOL.src.num.extra_theories.bit.BIT_testbit.
  pose proof (W.w2n_lt x) as H. unfold W.dimword, W.dimindex in H. change (N.max 1 64) with 64%N in H.
  rewrite testbit_top by exact H. unfold zw.
  destruct (N.leb_spec (2 ^ 63) (W.w2n x)); destruct (Z.leb_spec (2 ^ 63) (Z.of_N (W.w2n x))); try reflexivity; lia.
Qed.

Lemma zw_asr (x : W.word 64) n : (n < 64)%N ->
  zw (W.word_asr x n) = (sgn 64 (zw x) / 2 ^ Z.of_N n) mod 2 ^ 64.
Proof.
  intros Hn. pose proof (zw_range x ltac:(lia)) as Hx. cbn [Z.of_N] in Hx.
  assert (Hp : 0 < 2 ^ Z.of_N n) by (apply Z.pow_pos_nonneg; lia).
  assert (Hq : 2 ^ 64 = 2 ^ (64 - Z.of_N n) * 2 ^ Z.of_N n) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
  assert (Hq0 : 0 < 2 ^ (64 - Z.of_N n)) by (apply Z.pow_pos_nonneg; lia).
  unfold W.word_asr. rewrite msb64. unfold sgn. change (64 - 1) with 63.
  destruct (Z.leb_spec (2 ^ 63) (zw x)) as [Hm|Hm].
  - destruct (Z.ltb_spec (zw x) (2 ^ 63)); [lia|].
    unfold W.word_or. rewrite zw_n2w by lia. rewrite N2Z.inj_lor.
    change (Z.of_N (W.w2n (W.word_lsr x n))) with (zw (W.word_lsr x n)).
    change (Z.of_N (W.w2n (W.word_lsl W.word_T (W.dimindex 64 - Galette.HOL.src.num.theories.arithmetic.MIN n (W.dimindex 64)))))
      with (zw (W.word_lsl (W.word_T : W.word 64) (W.dimindex 64 - Galette.HOL.src.num.theories.arithmetic.MIN n (W.dimindex 64)))).
    rewrite zw_lsr by exact Hn.
    unfold W.dimindex, Galette.HOL.src.num.theories.arithmetic.MIN. change (N.max 1 64) with 64%N.
    destruct (N.ltb_spec n 64) as [_|]; [|lia].
    destruct (N.eq_dec n 0) as [->|Hn0].
    + unfold W.word_lsl, W.dimindex. change (N.max 1 64) with 64%N.
      change ((64 - 1 <? 64 - 0)%N) with true. cbv iota.
      rewrite zw_n2w by lia. change (Z.of_N 0) with 0. change (Z.of_N 64) with 64.
      rewrite Z.pow_0_r, !Z.div_1_r. change (0 mod 2 ^ 64) with 0. rewrite Z.lor_0_l.
      replace (zw x - 2 ^ 64) with (zw x + (-1) * 2 ^ 64) by lia. rewrite Z.mod_add by lia.
      reflexivity.
    + replace (64 - n)%N with (64 - n)%N by reflexivity.
      rewrite zw_lsl by lia. unfold W.word_T, W.UINT_MAX. rewrite zw_n2w by lia.
      unfold W.dimword, W.dimindex. change (N.max 1 64) with 64%N.
      rewrite N2Z.inj_sub by (cbn; lia). change (Z.of_N (2 ^ 64)) with (2 ^ 64). change (Z.of_N 1) with 1.
      change (Z.of_N 64) with 64. rewrite N2Z.inj_sub by lia. change (Z.of_N 64) with 64.
      rewrite (Z.mod_small (2 ^ 64 - 1)) by lia.
      set (P := 2 ^ Z.of_N n) in *. set (K := 2 ^ (64 - Z.of_N n)) in *.
      assert (HA : ((2 ^ 64 - 1) * K) mod 2 ^ 64 = (P - 1) * K).
      { symmetry. apply Z.mod_unique with (q := K - 1); [|nia]. rewrite Hq. nia. }
      assert (HB : 0 <= zw x / P < K).
      { split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|]. rewrite Z.mul_comm, <- Hq. lia. }
      rewrite HA. unfold K at 1. rewrite lor_mul_pow2 by lia. fold K.
      rewrite Z.mod_small by nia.
      replace (zw x - 2 ^ 64) with (zw x + (- K) * P) by (rewrite Hq; ring).
      rewrite Z.div_add by lia.
      apply Z.mod_unique with (q := -1); nia.
  - destruct (Z.ltb_spec (zw x) (2 ^ 63)); [|lia].
    rewrite zw_lsr by exact Hn. rewrite Z.mod_small; [reflexivity|].
    split; [apply Z.div_pos; lia|]. apply Z.le_lt_trans with (zw x); [|lia]. apply Z.div_le_upper_bound; [lia|]. nia.
Qed.

Lemma ashiftr_unsigned (x : mword 64) i : 0 <= i < 64 ->
  bv_unsigned (arith_shiftr x i) = (sgn 64 (bv_unsigned x) / 2 ^ i) mod 2 ^ 64.
Proof.
  intros Hi. unfold arith_shiftr, SailStdpp.MachineWord.MachineWord.arith_shift_right.
  rewrite bv_ashiftr_unsigned. unfold SailStdpp.MachineWord.MachineWord.N_to_word. rewrite Z_to_bv_unsigned.
  rewrite bv_signed_sgn by nsize. unfold bv_wrap, bv_modulus, SailStdpp.MachineWord.MachineWord.Z_idx.
  cbn [Z.of_N Z.to_N]. rewrite Z2N.id by lia. rewrite (Z.mod_small i) by lia.
  rewrite Z.shiftr_div_pow2 by lia. reflexivity.
Qed.

Lemma bvw_sra (x y : mword 64) :
  bvw (shift_bits_right_arith x (subrange_vec_dec y (log2_xlen - 1) 0)) =
  W.word_asr_bv (bvw x) (W.w2w (W.word_extract 5 0 (bvw y) : W.word 6)).
Proof.
  apply bvw_eq_zw; [nsize|]. unfold W.word_asr_bv.
  rewrite zw_asr by apply shamt_lt. rewrite zw_shamt', !zw_bvw by nsize.
  unfold shift_bits_right_arith. rewrite shamt_unsigned.
  rewrite ashiftr_unsigned by (pose proof (Z.mod_pos_bound (bv_unsigned y) 64); lia).
  reflexivity.
Qed.

Lemma bvw_sra_imm (x : mword 64) (sh : W.word 6) :
  bvw (shift_bits_right_arith x (subrange_vec_dec (Z_to_bv 6 (zw sh) : mword 6) (log2_xlen - 1) 0)) =
  W.word_asr (bvw x) (W.w2n sh).
Proof.
  apply bvw_eq_zw; [nsize|]. pose proof (W.w2n_lt sh) as Hs. unfold W.dimword, W.dimindex in Hs.
  change (N.max 1 6) with 6%N in Hs. cbn in Hs.
  rewrite zw_asr by lia. rewrite zw_bvw by nsize.
  unfold shift_bits_right_arith, int_of_mword.
  change (Z.of_N (SailStdpp.MachineWord.MachineWord.word_to_N ?x)) with (uint x).
  rewrite uint_spec. rewrite subrange_vec_dec_unsigned by (unfold log2_xlen; lia).
  rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus, log2_xlen, zw. cbn [Z.of_N Z.to_N].
  rewrite Z.div_1_r. rewrite (Z.mod_small (Z.of_N (W.w2n sh)) (2 ^ 6)) by lia.
  rewrite (Z.mod_small (Z.of_N (W.w2n sh)) (2 ^ (6 - 1 - 0 + 1))) by (cbn; lia).
  rewrite ashiftr_unsigned by lia. reflexivity.
Qed.
