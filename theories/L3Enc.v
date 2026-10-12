(** * L3's instruction encoding, as numbers *)

From stdpp Require Import base bitvector.definitions.
From GaletteSail Require Export Conv.
From Galette.HOL.examples.l3_machine_code.riscv.model Require riscv.
From Stdlib Require Import Lia.

Module R := Galette.HOL.examples.l3_machine_code.riscv.model.riscv.

Local Open Scope Z_scope.

Ltac zw_bounds :=
  repeat match goal with
  | |- context [@zw ?n ?x] =>
      lazymatch goal with
      | _ : 0 <= @zw n x < _ |- _ => fail
      | _ => let H := fresh in pose proof (zw_range x ltac:(lia)) as H; cbn [Z.of_N] in H
      end
  end.

Lemma zw_Rtype o f3 rd rs1 rs2 f7 :
  zw (R.Rtype (o, f3, rd, rs1, rs2, f7)) =
  zw o + 2 ^ 7 * zw rd + 2 ^ 12 * zw f3 + 2 ^ 15 * zw rs1 + 2 ^ 20 * zw rs2 + 2 ^ 25 * zw f7.
Proof.
  unfold R.Rtype. rewrite !zw_concat by lia. cbn [Z.of_N]. zw_bounds.
  rewrite !(Z.mod_small _ (2 ^ _)); lia.
Qed.

Lemma zw_Itype o f3 rd rs1 imm :
  zw (R.Itype (o, f3, rd, rs1, imm)) =
  zw o + 2 ^ 7 * zw rd + 2 ^ 12 * zw f3 + 2 ^ 15 * zw rs1 + 2 ^ 20 * zw imm.
Proof.
  unfold R.Itype. rewrite !zw_concat by lia. cbn [Z.of_N]. zw_bounds.
  rewrite !(Z.mod_small _ (2 ^ _)); lia.
Qed.

Lemma zw_Utype o rd imm :
  zw (R.Utype (o, rd, imm)) = zw o + 2 ^ 7 * zw rd + 2 ^ 12 * zw imm.
Proof.
  unfold R.Utype. rewrite !zw_concat by lia. cbn [Z.of_N]. zw_bounds.
  rewrite !(Z.mod_small _ (2 ^ _)); lia.
Qed.
