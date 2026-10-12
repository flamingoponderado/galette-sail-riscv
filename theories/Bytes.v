(** * Byte-level facts: little-endian combination and the Sail byte helpers *)

From stdpp Require Import base bitvector.definitions list_numbers.
From SailStdpp Require Import Base ConcurrencyInterfaceV2.
From Riscv Require Import rv64d_types rv64d.
From GaletteSail Require Import Interp BvSolve.
From Stdlib Require Import Lia ZArith.
Import ListNotations.

Local Open Scope Z_scope.

Lemma le8_nil : little_endian_to_bv 8 [] = 0.
Proof. reflexivity. Qed.

Lemma le8_bound bs : 0 <= little_endian_to_bv 8 bs < 2 ^ (8 * Z.of_nat (length bs)).
Proof.
  induction bs as [|b bs IH]; [cbn; lia|].
  unfold little_endian_to_bv in *. cbn [fmap list_fmap little_endian_to_Z length].
  pose proof (bv_unsigned_in_range _ b) as Hb. unfold bv_modulus in Hb. cbn in Hb.
  rewrite Z.lor_comm, Z.shiftl_mul_pow2 by lia.
  rewrite lor_mul_pow2 by lia.
  replace (8 * Z.of_nat (S (length bs))) with (8 * Z.of_nat (length bs) + 8) by lia.
  rewrite Z.pow_add_r by lia. nia.
Qed.

Lemma le8_cons b bs :
  little_endian_to_bv 8 (b :: bs) = bv_unsigned b + 2 ^ 8 * little_endian_to_bv 8 bs.
Proof.
  unfold little_endian_to_bv. cbn [fmap list_fmap little_endian_to_Z].
  pose proof (bv_unsigned_in_range _ b) as Hb. unfold bv_modulus in Hb. cbn in Hb.
  pose proof (le8_bound bs) as Hbs. unfold little_endian_to_bv in Hbs.
  rewrite Z.lor_comm, Z.shiftl_mul_pow2 by lia.
  rewrite lor_mul_pow2 by lia. lia.
Qed.

(** The [n] bytes at [a] as a number. *)
Definition mem_val (m : bv 64 -> bv 8) (a : bv 64) (n : N) : Z :=
  little_endian_to_bv 8 (read_bytes m a n).

Lemma mem_read_val_unsigned m a n :
  bv_unsigned (mem_read_val m a n) = mem_val m a n.
Proof.
  unfold mem_read_val, mem_val. rewrite Z_to_bv_unsigned. apply bv_wrap_small.
  pose proof (le8_bound (read_bytes m a n)) as H.
  unfold read_bytes in H. rewrite List.length_map, List.length_seq in H.
  unfold bv_modulus. rewrite N2Z.inj_mul. replace (Z.of_nat (N.to_nat n)) with (Z.of_N n) in H by lia. exact H.
Qed.

Definition byte_at (m : bv 64 -> bv 8) (a : bv 64) (i : nat) : Z :=
  bv_unsigned (m (bv_add a (Z_to_bv 64 (Z.of_nat i)))).

Lemma mem_val_1 m a : mem_val m a 1 = byte_at m a 0.
Proof. unfold mem_val, read_bytes. change (N.to_nat 1) with 1%nat. cbn [seq map]. rewrite !le8_cons, le8_nil. unfold byte_at. lia. Qed.

Lemma mem_val_2 m a : mem_val m a 2 = byte_at m a 0 + 2 ^ 8 * byte_at m a 1.
Proof. unfold mem_val, read_bytes. change (N.to_nat 2) with 2%nat. cbn [seq map]. rewrite !le8_cons, le8_nil. unfold byte_at. lia. Qed.

Lemma mem_val_4 m a : mem_val m a 4 =
  byte_at m a 0 + 2 ^ 8 * byte_at m a 1 + 2 ^ 16 * byte_at m a 2 + 2 ^ 24 * byte_at m a 3.
Proof. unfold mem_val, read_bytes. change (N.to_nat 4) with 4%nat. cbn [seq map]. rewrite !le8_cons, le8_nil. unfold byte_at. lia. Qed.

Lemma mem_val_8 m a : mem_val m a 8 =
  byte_at m a 0 + 2 ^ 8 * byte_at m a 1 + 2 ^ 16 * byte_at m a 2 + 2 ^ 24 * byte_at m a 3 +
  2 ^ 32 * byte_at m a 4 + 2 ^ 40 * byte_at m a 5 + 2 ^ 48 * byte_at m a 6 + 2 ^ 56 * byte_at m a 7.
Proof. unfold mem_val, read_bytes. change (N.to_nat 8) with 8%nat. cbn [seq map]. rewrite !le8_cons, le8_nil. unfold byte_at. lia. Qed.

Lemma byte_at_range m a i : 0 <= byte_at m a i < 256.
Proof. unfold byte_at. pose proof (bv_unsigned_in_range _ (m (bv_add a (Z_to_bv 64 (Z.of_nat i))))). unfold bv_modulus in *. cbn in *. lia. Qed.

(** ** The byte-vector helpers of the Sail library *)

Lemma from_bytes_le_1 (bs : vec (mword 8) 1) : from_bytes_le 1 bs =
  update_subrange_vec_dec (zeros (8 * 1)) 7 0 (autocast (vec_access_dec bs 0)).
Proof. reflexivity. Qed.

Lemma from_bytes_le_2 (bs : vec (mword 8) 2) : from_bytes_le 2 bs =
  update_subrange_vec_dec (update_subrange_vec_dec
    (zeros (8 * 2)) 7 0 (autocast (vec_access_dec bs 0))) 15 8 (autocast (vec_access_dec bs 1)).
Proof. reflexivity. Qed.

Lemma from_bytes_le_4 (bs : vec (mword 8) 4) : from_bytes_le 4 bs =
  update_subrange_vec_dec (update_subrange_vec_dec (update_subrange_vec_dec (update_subrange_vec_dec
    (zeros (8 * 4)) 7 0 (autocast (vec_access_dec bs 0))) 15 8 (autocast (vec_access_dec bs 1)))
    23 16 (autocast (vec_access_dec bs 2))) 31 24 (autocast (vec_access_dec bs 3)).
Proof. reflexivity. Qed.

Lemma from_bytes_le_8 (bs : vec (mword 8) 8) : from_bytes_le 8 bs =
  update_subrange_vec_dec (update_subrange_vec_dec (update_subrange_vec_dec (update_subrange_vec_dec
  (update_subrange_vec_dec (update_subrange_vec_dec (update_subrange_vec_dec (update_subrange_vec_dec
    (zeros (8 * 8)) 7 0 (autocast (vec_access_dec bs 0))) 15 8 (autocast (vec_access_dec bs 1)))
    23 16 (autocast (vec_access_dec bs 2))) 31 24 (autocast (vec_access_dec bs 3)))
    39 32 (autocast (vec_access_dec bs 4))) 47 40 (autocast (vec_access_dec bs 5)))
    55 48 (autocast (vec_access_dec bs 6))) 63 56 (autocast (vec_access_dec bs 7)).
Proof. reflexivity. Qed.

Lemma bv_extract_byte {k} (v : bv k) i :
  bv_unsigned (bv_extract (8 * Z.to_N i) 8 v) = (bv_unsigned v / 2 ^ (8 * i)) mod 2 ^ 8 \/ i < 0.
Proof.
  destruct (Z.lt_ge_cases i 0) as [H|H]; [right; exact H|left].
  rewrite bv_extract_unsigned. unfold bv_wrap, bv_modulus. rewrite Z.shiftr_div_pow2 by lia.
  f_equal. f_equal. f_equal. lia.
Qed.

Local Tactic Notation "bytes_access" constr(n) int_or_var(k) :=
  intros Hi;
  match goal with
  | Hi : 0 <= ?i < _ |- context [Defs.bytes_of_bv ?v] =>
      let H := fresh in
      assert (H : exists j : nat, i = Z.of_nat j /\ (j < n)%nat) by (exists (Z.to_nat i); split; lia);
      destruct H as [j [-> Hj]];
      do k (destruct j as [|j];
            [ match goal with |- context [vec_access_dec _ (Z.of_nat ?k)] =>
                destruct (bv_extract_byte v (Z.of_nat k)) as [E|E]; [exact E|lia] end |]);
      lia
  end.

Lemma bytes_of_bv_access_1 (v : bv (8 * Z.to_N 1)) i inst : 0 <= i < 1 ->
  bv_unsigned (@vec_access_dec (mword 8) 1 (Defs.bytes_of_bv v) i inst) = (bv_unsigned v / 2 ^ (8 * i)) mod 2 ^ 8.
Proof. bytes_access 1%nat 1. Qed.
Lemma bytes_of_bv_access_2 (v : bv (8 * Z.to_N 2)) i inst : 0 <= i < 2 ->
  bv_unsigned (@vec_access_dec (mword 8) 2 (Defs.bytes_of_bv v) i inst) = (bv_unsigned v / 2 ^ (8 * i)) mod 2 ^ 8.
Proof. bytes_access 2%nat 2. Qed.
Lemma bytes_of_bv_access_4 (v : bv (8 * Z.to_N 4)) i inst : 0 <= i < 4 ->
  bv_unsigned (@vec_access_dec (mword 8) 4 (Defs.bytes_of_bv v) i inst) = (bv_unsigned v / 2 ^ (8 * i)) mod 2 ^ 8.
Proof. bytes_access 4%nat 4. Qed.
Lemma bytes_of_bv_access_8 (v : bv (8 * Z.to_N 8)) i inst : 0 <= i < 8 ->
  bv_unsigned (@vec_access_dec (mword 8) 8 (Defs.bytes_of_bv v) i inst) = (bv_unsigned v / 2 ^ (8 * i)) mod 2 ^ 8.
Proof. bytes_access 8%nat 8. Qed.

Lemma zeros_unsigned n : bv_unsigned (zeros n) = 0.
Proof. destruct n; reflexivity. Qed.

Lemma zeros'_unsigned n : bv_unsigned (zeros' n) = 0.
Proof. apply zeros_unsigned. Qed.

Lemma vec_access_bytes_unsigned {n} (v : bv (8 * Z.to_N n)) i inst :
  n = 1 \/ n = 2 \/ n = 4 \/ n = 8 -> 0 <= i < n ->
  bv_unsigned (@vec_access_dec (mword 8) n (Defs.bytes_of_bv v) i inst) = (bv_unsigned v / 2 ^ (8 * i)) mod 2 ^ 8.
Proof.
  intros H Hi; destruct H as [H|[H|[H|H]]]; subst n.
  - apply bytes_of_bv_access_1, Hi.
  - apply bytes_of_bv_access_2, Hi.
  - apply bytes_of_bv_access_4, Hi.
  - apply bytes_of_bv_access_8, Hi.
Qed.

Ltac bv_lemma_extra t ::=
  lazymatch t with
  | mem_read_val ?m ?a ?n => constr:(mem_read_val_unsigned m a n)
  | zeros' ?n => constr:(zeros'_unsigned n)
  | zeros ?n => constr:(zeros_unsigned n)
  | @vec_access_dec _ ?n (@Defs.bytes_of_bv _ ?v) ?i ?inst => constr:(@vec_access_bytes_unsigned n v i inst)
  | from_bytes_le 1 ?bs => constr:(f_equal bv_unsigned (from_bytes_le_1 bs))
  | from_bytes_le 2 ?bs => constr:(f_equal bv_unsigned (from_bytes_le_2 bs))
  | from_bytes_le 4 ?bs => constr:(f_equal bv_unsigned (from_bytes_le_4 bs))
  | from_bytes_le 8 ?bs => constr:(f_equal bv_unsigned (from_bytes_le_8 bs))
  end.

Lemma upd_acc {n} (v : mword n) hi lo (x : mword (hi - (lo - 1))) :
  0 <= lo -> lo <= hi + 1 -> hi < n -> bv_unsigned v < 2 ^ lo ->
  bv_unsigned (update_subrange_vec_dec v hi lo x) = bv_unsigned v + bv_unsigned x * 2 ^ lo.
Proof.
  intros H1 H2 H3 H4. rewrite update_subrange_vec_dec_unsigned by lia.
  pose proof (bv_unsigned_in_range _ v).
  assert (0 < 2 ^ lo) by (apply Z.pow_pos_nonneg; lia).
  assert (2 ^ lo <= 2 ^ (hi + 1)) by (apply Z.pow_le_mono_r; lia).
  rewrite Z.mod_small by lia. rewrite Z.div_small by lia. lia.
Qed.

Lemma upd_acc_lt {n} (v : mword n) hi lo (x : mword (hi - (lo - 1))) :
  0 <= lo -> lo <= hi + 1 -> hi < n -> bv_unsigned v < 2 ^ lo ->
  bv_unsigned (update_subrange_vec_dec v hi lo x) < 2 ^ (hi + 1).
Proof.
  intros H1 H2 H3 H4. rewrite upd_acc by lia.
  pose proof (bv_unsigned_in_range _ x) as Hx. unfold bv_modulus, SailStdpp.MachineWord.MachineWord.Z_idx in Hx.
  rewrite Z2N.id in Hx by lia.
  assert (0 < 2 ^ lo) by (apply Z.pow_pos_nonneg; lia).
  assert (E : 2 ^ (hi + 1) = 2 ^ (hi - (lo - 1)) * 2 ^ lo) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
  rewrite E. pose proof (bv_unsigned_in_range _ v).
  unfold SailStdpp.MachineWord.MachineWord.Z_idx in *.
  assert (bv_unsigned x * 2 ^ lo <= (2 ^ (hi - (lo - 1)) - 1) * 2 ^ lo)
    by (apply Z.mul_le_mono_nonneg_r; unfold SailStdpp.MachineWord.MachineWord.Z_idx in *; lia).
  unfold SailStdpp.MachineWord.MachineWord.Z_idx in *. lia.
Qed.

Ltac upd_bound :=
  lazymatch goal with
  | |- bv_unsigned (zeros _) < _ => rewrite zeros_unsigned; apply Z.pow_pos_nonneg; lia
  | |- bv_unsigned (update_subrange_vec_dec ?v ?hi ?lo ?x) < 2 ^ ?l =>
      eapply Z.lt_le_trans; [apply upd_acc_lt; [lia|lia|lia|upd_bound] | apply Z.pow_le_mono_r; lia]
  end.

Ltac upd_chain :=
  repeat match goal with
  | |- context [bv_unsigned (update_subrange_vec_dec ?v ?hi ?lo ?x)] =>
      rewrite (upd_acc v hi lo x) by (lia || upd_bound)
  end.

Lemma from_bytes_le_bytes_1 (v : bv (8 * Z.to_N 1)) :
  bv_unsigned (from_bytes_le 1 (Defs.bytes_of_bv v)) = bv_unsigned v.
Proof.
  rewrite from_bytes_le_1. upd_chain. rewrite zeros_unsigned.
  rewrite !autocast_unsigned by lia. rewrite !bytes_of_bv_access_1 by lia.
  pose proof (bv_unsigned_in_range _ v). unfold bv_modulus in *. cbn in *. lia.
Qed.

Lemma from_bytes_le_bytes_2 (v : bv (8 * Z.to_N 2)) :
  bv_unsigned (from_bytes_le 2 (Defs.bytes_of_bv v)) = bv_unsigned v.
Proof.
  rewrite from_bytes_le_2. upd_chain. rewrite zeros_unsigned.
  rewrite !autocast_unsigned by lia. rewrite !bytes_of_bv_access_2 by lia.
  pose proof (bv_unsigned_in_range _ v). unfold bv_modulus in *. cbn in *. lia.
Qed.

Lemma from_bytes_le_bytes_4 (v : bv (8 * Z.to_N 4)) :
  bv_unsigned (from_bytes_le 4 (Defs.bytes_of_bv v)) = bv_unsigned v.
Proof.
  rewrite from_bytes_le_4. upd_chain. rewrite zeros_unsigned.
  rewrite !autocast_unsigned by lia. rewrite !bytes_of_bv_access_4 by lia.
  pose proof (bv_unsigned_in_range _ v). unfold bv_modulus in *. cbn in *. lia.
Qed.

Lemma from_bytes_le_bytes_8 (v : bv (8 * Z.to_N 8)) :
  bv_unsigned (from_bytes_le 8 (Defs.bytes_of_bv v)) = bv_unsigned v.
Proof.
  rewrite from_bytes_le_8. upd_chain. rewrite zeros_unsigned.
  rewrite !autocast_unsigned by lia. rewrite !bytes_of_bv_access_8 by lia.
  pose proof (bv_unsigned_in_range _ v). unfold bv_modulus in *. cbn in *. lia.
Qed.

Ltac bv_lemma_extra t ::=
  lazymatch t with
  | mem_read_val ?m ?a ?n => constr:(mem_read_val_unsigned m a n)
  | zeros' ?n => constr:(zeros'_unsigned n)
  | zeros ?n => constr:(zeros_unsigned n)
  | @vec_access_dec _ ?n (@Defs.bytes_of_bv _ ?v) ?i ?inst => constr:(@vec_access_bytes_unsigned n v i inst)
  | from_bytes_le 1 (Defs.bytes_of_bv ?v) => constr:(from_bytes_le_bytes_1 v)
  | from_bytes_le 2 (Defs.bytes_of_bv ?v) => constr:(from_bytes_le_bytes_2 v)
  | from_bytes_le 4 (Defs.bytes_of_bv ?v) => constr:(from_bytes_le_bytes_4 v)
  | from_bytes_le 8 (Defs.bytes_of_bv ?v) => constr:(from_bytes_le_bytes_8 v)
  | from_bytes_le 1 ?bs => constr:(f_equal bv_unsigned (from_bytes_le_1 bs))
  | from_bytes_le 2 ?bs => constr:(f_equal bv_unsigned (from_bytes_le_2 bs))
  | from_bytes_le 4 ?bs => constr:(f_equal bv_unsigned (from_bytes_le_4 bs))
  | from_bytes_le 8 ?bs => constr:(f_equal bv_unsigned (from_bytes_le_8 bs))
  end.
