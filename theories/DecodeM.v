(** * Decoding lemmas (DecodeM) *)

From stdpp Require Import base bitvector.definitions.
From SailStdpp Require Import Base ConcurrencyInterfaceV2.
From Riscv Require Import rv64d_types rv64d.
From GaletteSail Require Export Decode.
From Stdlib Require Import Lia.
Import ListNotations.

Local Open Scope Z_scope.

Section D.
Variable s : SailState.
Hypothesis Hinv : agree ctrl cfg (regs s).

Lemma decode_LD w rd rs1 imm :
  reg5 rd -> reg5 rs1 -> 0 <= imm < 4096 -> bv_unsigned w = encI imm rs1 3 rd 0x03 ->
  runX (ext_decode w) s = Some (inl (LOAD (Z_to_bv 12 imm, Regidx (Z_to_bv 5 rs1), Regidx (Z_to_bv 5 rd), false, 8)), s).
Proof. dec_prove. Qed.

Lemma decode_LWU w rd rs1 imm :
  reg5 rd -> reg5 rs1 -> 0 <= imm < 4096 -> bv_unsigned w = encI imm rs1 6 rd 0x03 ->
  runX (ext_decode w) s = Some (inl (LOAD (Z_to_bv 12 imm, Regidx (Z_to_bv 5 rs1), Regidx (Z_to_bv 5 rd), true, 4)), s).
Proof. dec_prove. Qed.

Lemma decode_LHU w rd rs1 imm :
  reg5 rd -> reg5 rs1 -> 0 <= imm < 4096 -> bv_unsigned w = encI imm rs1 5 rd 0x03 ->
  runX (ext_decode w) s = Some (inl (LOAD (Z_to_bv 12 imm, Regidx (Z_to_bv 5 rs1), Regidx (Z_to_bv 5 rd), true, 2)), s).
Proof. dec_prove. Qed.

Lemma decode_LBU w rd rs1 imm :
  reg5 rd -> reg5 rs1 -> 0 <= imm < 4096 -> bv_unsigned w = encI imm rs1 4 rd 0x03 ->
  runX (ext_decode w) s = Some (inl (LOAD (Z_to_bv 12 imm, Regidx (Z_to_bv 5 rs1), Regidx (Z_to_bv 5 rd), true, 1)), s).
Proof. dec_prove. Qed.

Lemma decode_SD w rs1 rs2 imm :
  reg5 rs1 -> reg5 rs2 -> 0 <= imm < 4096 -> bv_unsigned w = encS imm rs2 rs1 3 0x23 ->
  runX (ext_decode w) s = Some (inl (STORE (Z_to_bv 12 imm, Regidx (Z_to_bv 5 rs2), Regidx (Z_to_bv 5 rs1), 8)), s).
Proof. dec_prove. Qed.

Lemma decode_SW w rs1 rs2 imm :
  reg5 rs1 -> reg5 rs2 -> 0 <= imm < 4096 -> bv_unsigned w = encS imm rs2 rs1 2 0x23 ->
  runX (ext_decode w) s = Some (inl (STORE (Z_to_bv 12 imm, Regidx (Z_to_bv 5 rs2), Regidx (Z_to_bv 5 rs1), 4)), s).
Proof. dec_prove. Qed.

Lemma decode_SH w rs1 rs2 imm :
  reg5 rs1 -> reg5 rs2 -> 0 <= imm < 4096 -> bv_unsigned w = encS imm rs2 rs1 1 0x23 ->
  runX (ext_decode w) s = Some (inl (STORE (Z_to_bv 12 imm, Regidx (Z_to_bv 5 rs2), Regidx (Z_to_bv 5 rs1), 2)), s).
Proof. dec_prove. Qed.

Lemma decode_SB w rs1 rs2 imm :
  reg5 rs1 -> reg5 rs2 -> 0 <= imm < 4096 -> bv_unsigned w = encS imm rs2 rs1 0 0x23 ->
  runX (ext_decode w) s = Some (inl (STORE (Z_to_bv 12 imm, Regidx (Z_to_bv 5 rs2), Regidx (Z_to_bv 5 rs1), 1)), s).
Proof. dec_prove. Qed.

End D.
