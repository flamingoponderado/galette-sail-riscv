(** * Agreement of signed division *)

From stdpp Require Import base bitvector.definitions.
From SailStdpp Require Import Base ConcurrencyInterfaceV2.
From Riscv Require Import rv64d_types rv64d riscv_extras.
From GaletteSail Require Export Values3.
From Stdlib Require Import Lia.

Local Open Scope Z_scope.

Lemma zw_2comp (w : W.word 64) : zw (W.word_2comp w) = (- zw w) mod 2 ^ 64.
Proof.
  unfold W.word_2comp. rewrite zw_n2w by lia. pose proof (zw_range w ltac:(lia)) as H. cbn [Z.of_N] in *.
  unfold zw in *. rewrite N2Z.inj_sub by (apply N.lt_le_incl, W.w2n_lt).
  rewrite dimword_pos by lia. cbn [Z.of_N].
  replace (2 ^ 64 - Z.of_N (W.w2n w)) with (- Z.of_N (W.w2n w) + 1 * 2 ^ 64) by lia.
  rewrite Z.mod_add by lia. reflexivity.
Qed.

Lemma zw_div (a b : W.word 64) : zw (W.word_div a b) = zw a / zw b.
Proof.
  unfold W.word_div. rewrite zw_n2w by lia. unfold zw. rewrite N2Z.inj_div.
  pose proof (zw_range a ltac:(lia)) as Ha. pose proof (zw_range b ltac:(lia)) as Hb. unfold zw in *.
  cbn [Z.of_N] in *. apply Z.mod_small.
  destruct (Z.eq_dec (Z.of_N (W.w2n b)) 0) as [->|]; [rewrite Zdiv_0_r; lia|].
  split; [apply Z.div_pos; lia|].
  apply Z.le_lt_trans with (Z.of_N (W.w2n a)); [|lia]. apply Z.div_le_upper_bound; nia.
Qed.

Lemma zw_quot (x y : W.word 64) : zw y <> 0 ->
  zw (W.word_quot x y) = Z.quot (sgn 64 (zw x)) (sgn 64 (zw y)) mod 2 ^ 64.
Proof.
  intros Hy0. pose proof (zw_range x ltac:(lia)) as Hx. pose proof (zw_range y ltac:(lia)) as Hy.
  cbn [Z.of_N] in *. unfold W.word_quot. rewrite !msb64. unfold sgn. change (64 - 1) with 63.
  destruct (Z.leb_spec (2 ^ 63) (zw x)) as [Hxn|Hxp], (Z.leb_spec (2 ^ 63) (zw y)) as [Hyn|Hyp];
  destruct (Z.ltb_spec (zw x) (2 ^ 63)); try lia; destruct (Z.ltb_spec (zw y) (2 ^ 63)); try lia.
  - (* neg / neg *)
    rewrite zw_div, !zw_2comp.
    rewrite !(Z.mod_eq (- _)) by lia.
    assert (Ex : - zw x / 2 ^ 64 = -1) by (symmetry; apply Z.div_unique with (r := 2 ^ 64 - zw x); lia).
    assert (Ey : - zw y / 2 ^ 64 = -1) by (symmetry; apply Z.div_unique with (r := 2 ^ 64 - zw y); lia).
    rewrite Ex, Ey.
    replace (zw x - 2 ^ 64) with (- (2 ^ 64 - zw x)) by lia.
    replace (zw y - 2 ^ 64) with (- (2 ^ 64 - zw y)) by lia.
    rewrite Z.quot_opp_opp by lia. rewrite Z.quot_div_nonneg by lia.
    replace (- zw x - 2 ^ 64 * -1) with (2 ^ 64 - zw x) by lia.
    replace (- zw y - 2 ^ 64 * -1) with (2 ^ 64 - zw y) by lia.
    symmetry. apply Z.mod_small. split; [apply Z.div_pos; lia|].
    apply Z.le_lt_trans with (2 ^ 64 - zw x); [apply Z.div_le_upper_bound; nia|lia].
  - (* neg / pos *)
    rewrite zw_2comp, zw_div, zw_2comp.
    rewrite (Z.mod_eq (- zw x)) by lia.
    assert (Ex : - zw x / 2 ^ 64 = -1) by (symmetry; apply Z.div_unique with (r := 2 ^ 64 - zw x); lia).
    rewrite Ex. replace (- zw x - 2 ^ 64 * -1) with (2 ^ 64 - zw x) by lia.
    replace (zw x - 2 ^ 64) with (- (2 ^ 64 - zw x)) by lia.
    rewrite Z.quot_opp_l by lia. rewrite Z.quot_div_nonneg by lia. reflexivity.
  - (* pos / neg *)
    rewrite zw_2comp, zw_div, zw_2comp.
    rewrite (Z.mod_eq (- zw y)) by lia.
    assert (Ey : - zw y / 2 ^ 64 = -1) by (symmetry; apply Z.div_unique with (r := 2 ^ 64 - zw y); lia).
    rewrite Ey. replace (- zw y - 2 ^ 64 * -1) with (2 ^ 64 - zw y) by lia.
    replace (zw y - 2 ^ 64) with (- (2 ^ 64 - zw y)) by lia.
    rewrite Z.quot_opp_r by lia. rewrite Z.quot_div_nonneg by lia. reflexivity.
  - (* pos / pos *)
    rewrite zw_div. rewrite Z.quot_div_nonneg by lia. symmetry. apply Z.mod_small.
    split; [apply Z.div_pos; lia|]. apply Z.le_lt_trans with (zw x); [apply Z.div_le_upper_bound; nia|lia].
Qed.

Lemma sw2sw_one : (W.sw2sw (W.n2w 1 : W.word 1) : W.word 64) = W.n2w (2 ^ 64 - 1).
Proof. apply word_eq_zw. unfold zw. vm_compute. reflexivity. Qed.

Lemma bvw_div_zero (x y : mword 64) :
  bvw y = W.n2w 0 -> bvw (div_val x y) = W.sw2sw (W.n2w 1 : W.word 1).
Proof.
  intros E. apply bvw_eq_zw; [nsize|]. rewrite zw_sw2sw by nsize. rewrite zw_n2w by nsize.
  apply (f_equal zw) in E. rewrite zw_bvw in E by nsize. rewrite zw_n2w in E by nsize.
  unfold div_val, xlen, pow2. rewrite !sint_sgn by lia.
  rewrite to_bits_truncate_unsigned by lia.
  revert E. bv_destruct. intros E. change (Z.of_N 0 mod 2 ^ Z.of_N 64) with 0 in E. subst.
  reflexivity.
Qed.

Lemma bvw_div_nz (x y : mword 64) :
  bvw y <> W.n2w 0 -> bvw (div_val x y) = W.word_quot (bvw x) (bvw y).
Proof.
  intros E.
  assert (E' : bv_unsigned y <> 0).
  { intros E0. apply E. apply word_eq_zw. rewrite zw_bvw by nsize. rewrite zw_n2w by nsize. rewrite E0. reflexivity. }
  apply bvw_eq_zw; [nsize|]. rewrite zw_quot by (rewrite zw_bvw by nsize; exact E').
  rewrite !zw_bvw by nsize.
  unfold div_val, xlen, pow2. rewrite !sint_sgn by nsize.
  rewrite to_bits_truncate_unsigned by lia.
  clear E. revert E'. bv_destruct. intros E'.
  apply bv_wf_in_range in Hw. apply bv_wf_in_range in Hw0. unfold bv_modulus in Hw, Hw0.
  change (Z.of_N (SailStdpp.MachineWord.MachineWord.Z_idx 64)) with 64 in Hw, Hw0.
  assert (Es : sgn 64 X <> 0) by (unfold sgn; destruct (_ <? _); lia).
  destruct (Z.eqb_spec (sgn 64 X) 0); [contradiction|].
  change (pow 2 (64 - 1)) with (2 ^ (64 - 1)).
  set (q := Z.quot _ _).
  destruct (Z.geb_spec q (2 ^ (64 - 1))) as [Hq|Hq]; [|reflexivity].
  assert (Hb : Z.abs q <= 2 ^ 63).
  { unfold q. rewrite <- Z.quot_abs by lia. rewrite Z.quot_div_nonneg by lia. apply Z.le_trans with (Z.abs (sgn 64 X0)).
    - apply Z.div_le_upper_bound; [lia|]. assert (1 <= Z.abs (sgn 64 X)) by lia. nia.
    - unfold sgn. destruct (_ <? _) eqn:Ex; [apply Z.ltb_lt in Ex|apply Z.ltb_ge in Ex]; lia. }
  assert (Hq2 : q = 2 ^ 63) by (cbn in Hq; lia). rewrite Hq2. reflexivity.
Qed.

