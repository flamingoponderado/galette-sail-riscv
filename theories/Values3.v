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
