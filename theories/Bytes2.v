(** * Byte-level writes: [write_bytes] pointwise *)

From stdpp Require Import base bitvector.definitions list_numbers.
From SailStdpp Require Import Base ConcurrencyInterfaceV2.
From Riscv Require Import rv64d_types rv64d.
From GaletteSail Require Import Interp BvSolve Bytes.
From Stdlib Require Import Lia ZArith List.
Import ListNotations.

Local Open Scope Z_scope.

Lemma bv_sub_unsigned64 (x a : bv 64) : bv_unsigned (bv_sub x a) = (bv_unsigned x - bv_unsigned a) mod 2 ^ 64.
Proof. rewrite bv_sub_unsigned. reflexivity. Qed.

Lemma bv64_eq_iff (x a : bv 64) : x = a <-> bv_unsigned (bv_sub x a) = 0.
Proof.
  rewrite bv_sub_unsigned64. pose proof (bv_unsigned_in_range _ x). pose proof (bv_unsigned_in_range _ a).
  unfold bv_modulus in *. cbn in *. split.
  - intros ->. rewrite Z.sub_diag. reflexivity.
  - intros Hz. apply bv_eq. apply Z.mod_divide in Hz; [|lia]. destruct Hz as [q Hq]. nia.
Qed.

Lemma write_bytes_spec (m : bv 64 -> bv 8) (a : bv 64) (bs : list (bv 8)) (x : bv 64) :
  (Z.of_nat (length bs) < 2 ^ 64)%Z ->
  write_bytes m a bs x =
  if bv_unsigned (bv_sub x a) <? Z.of_nat (length bs)
  then nth (Z.to_nat (bv_unsigned (bv_sub x a))) bs (m x) else m x.
Proof.
  revert m a. induction bs as [|b bs IH]; intros m a Hl.
  - cbn [write_bytes length]. pose proof (bv_unsigned_in_range _ (bv_sub x a)).
    destruct (Z.ltb_spec (bv_unsigned (bv_sub x a)) (Z.of_nat 0)); [cbn in *; lia|reflexivity].
  - cbn [write_bytes length] in *. rewrite IH by lia.
    pose proof (bv_unsigned_in_range _ x) as Hx. pose proof (bv_unsigned_in_range _ a) as Ha.
    unfold bv_modulus in Hx, Ha. cbn [Z.of_N] in Hx, Ha.
    rewrite !bv_sub_unsigned64. rewrite bv_add_unsigned, Z_to_bv_unsigned.
    unfold bv_wrap, bv_modulus. cbn [Z.of_N].
    set (k := (bv_unsigned x - bv_unsigned a) mod 2 ^ 64).
    assert (Hk : 0 <= k < 2 ^ 64) by (apply Z.mod_pos_bound; lia).
    replace ((bv_unsigned x - (bv_unsigned a + 1 mod 2 ^ 64) mod 2 ^ 64) mod 2 ^ 64) with ((k - 1) mod 2 ^ 64).
    2:{ unfold k. rewrite Zminus_mod_idemp_l, Zminus_mod_idemp_r. f_equal. rewrite Z.mod_small with (a := 1) by lia. lia. }
    unfold upd_byte.
    destruct (Z.eq_dec k 0) as [Hk0|Hk0].
    + assert (Ex : x = a) by (apply bv64_eq_iff; rewrite bv_sub_unsigned64; exact Hk0).
      rewrite decide_True by exact Ex. rewrite Hk0.
      replace ((0 - 1) mod 2 ^ 64) with (2 ^ 64 - 1) by reflexivity.
      destruct (Z.ltb_spec (2 ^ 64 - 1) (Z.of_nat (length bs))); [lia|].
      destruct (Z.ltb_spec 0 (Z.of_nat (S (length bs)))); [reflexivity|lia].
    + assert (Ex : x <> a) by (rewrite bv64_eq_iff, bv_sub_unsigned64; exact Hk0).
      rewrite decide_False by exact Ex.
      rewrite (Z.mod_small (k - 1)) by lia.
      destruct (Z.ltb_spec (k - 1) (Z.of_nat (length bs))) as [Hlt|Hge];
        destruct (Z.ltb_spec k (Z.of_nat (S (length bs)))); try lia.
      * replace (Z.to_nat k) with (S (Z.to_nat (k - 1))) by lia. cbn [nth].
        apply nth_indep. lia.
      * reflexivity.
Qed.
