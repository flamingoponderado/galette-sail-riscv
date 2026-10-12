(** * Decoding lemmas (DecodeB) *)

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

Lemma decode_BEQ w rs1 rs2 imm :
  reg5 rs1 -> reg5 rs2 -> 0 <= imm < 4096 -> bv_unsigned w = encB imm rs2 rs1 0 0x63 ->
  runX (ext_decode w) s = Some (inl (BTYPE (Z_to_bv 13 (2 * imm), Regidx (Z_to_bv 5 rs2), Regidx (Z_to_bv 5 rs1), BEQ)), s).
Proof. dec_prove. Qed.

Lemma decode_BNE w rs1 rs2 imm :
  reg5 rs1 -> reg5 rs2 -> 0 <= imm < 4096 -> bv_unsigned w = encB imm rs2 rs1 1 0x63 ->
  runX (ext_decode w) s = Some (inl (BTYPE (Z_to_bv 13 (2 * imm), Regidx (Z_to_bv 5 rs2), Regidx (Z_to_bv 5 rs1), BNE)), s).
Proof. dec_prove. Qed.

Lemma decode_BLT w rs1 rs2 imm :
  reg5 rs1 -> reg5 rs2 -> 0 <= imm < 4096 -> bv_unsigned w = encB imm rs2 rs1 4 0x63 ->
  runX (ext_decode w) s = Some (inl (BTYPE (Z_to_bv 13 (2 * imm), Regidx (Z_to_bv 5 rs2), Regidx (Z_to_bv 5 rs1), BLT)), s).
Proof. dec_prove. Qed.

Lemma decode_BGE w rs1 rs2 imm :
  reg5 rs1 -> reg5 rs2 -> 0 <= imm < 4096 -> bv_unsigned w = encB imm rs2 rs1 5 0x63 ->
  runX (ext_decode w) s = Some (inl (BTYPE (Z_to_bv 13 (2 * imm), Regidx (Z_to_bv 5 rs2), Regidx (Z_to_bv 5 rs1), BGE)), s).
Proof. dec_prove. Qed.

Lemma decode_BLTU w rs1 rs2 imm :
  reg5 rs1 -> reg5 rs2 -> 0 <= imm < 4096 -> bv_unsigned w = encB imm rs2 rs1 6 0x63 ->
  runX (ext_decode w) s = Some (inl (BTYPE (Z_to_bv 13 (2 * imm), Regidx (Z_to_bv 5 rs2), Regidx (Z_to_bv 5 rs1), BLTU)), s).
Proof. dec_prove. Qed.

Lemma decode_BGEU w rs1 rs2 imm :
  reg5 rs1 -> reg5 rs2 -> 0 <= imm < 4096 -> bv_unsigned w = encB imm rs2 rs1 7 0x63 ->
  runX (ext_decode w) s = Some (inl (BTYPE (Z_to_bv 13 (2 * imm), Regidx (Z_to_bv 5 rs2), Regidx (Z_to_bv 5 rs1), BGEU)), s).
Proof. dec_prove. Qed.

Lemma decode_JAL w rd imm :
  reg5 rd -> 0 <= imm < 2 ^ 20 -> bv_unsigned w = encJ imm rd 0x6f ->
  runX (ext_decode w) s = Some (inl (JAL (Z_to_bv 21 (2 * imm), Regidx (Z_to_bv 5 rd))), s).
Proof. dec_prove. Qed.

Lemma decode_JALR w rd rs1 imm :
  reg5 rd -> reg5 rs1 -> 0 <= imm < 4096 -> bv_unsigned w = encI imm rs1 0 rd 0x67 ->
  runX (ext_decode w) s = Some (inl (JALR (Z_to_bv 12 imm, Regidx (Z_to_bv 5 rs1), Regidx (Z_to_bv 5 rd))), s).
Proof. dec_prove. Qed.

End D.
