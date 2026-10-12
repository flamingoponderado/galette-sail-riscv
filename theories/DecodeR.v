(** * Decoding lemmas (DecodeR) *)

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

Lemma decode_SUB w rd rs1 rs2 :
  reg5 rd -> reg5 rs1 -> reg5 rs2 -> bv_unsigned w = encR 32 rs2 rs1 0 rd 0x33 ->
  runX (ext_decode w) s = Some (inl (RTYPE (Regidx (Z_to_bv 5 rs2), Regidx (Z_to_bv 5 rs1), Regidx (Z_to_bv 5 rd), SUB)), s).
Proof. dec_prove. Qed.

Lemma decode_SLL w rd rs1 rs2 :
  reg5 rd -> reg5 rs1 -> reg5 rs2 -> bv_unsigned w = encR 0 rs2 rs1 1 rd 0x33 ->
  runX (ext_decode w) s = Some (inl (RTYPE (Regidx (Z_to_bv 5 rs2), Regidx (Z_to_bv 5 rs1), Regidx (Z_to_bv 5 rd), SLL)), s).
Proof. dec_prove. Qed.

Lemma decode_SLTU w rd rs1 rs2 :
  reg5 rd -> reg5 rs1 -> reg5 rs2 -> bv_unsigned w = encR 0 rs2 rs1 3 rd 0x33 ->
  runX (ext_decode w) s = Some (inl (RTYPE (Regidx (Z_to_bv 5 rs2), Regidx (Z_to_bv 5 rs1), Regidx (Z_to_bv 5 rd), SLTU)), s).
Proof. dec_prove. Qed.

Lemma decode_XOR w rd rs1 rs2 :
  reg5 rd -> reg5 rs1 -> reg5 rs2 -> bv_unsigned w = encR 0 rs2 rs1 4 rd 0x33 ->
  runX (ext_decode w) s = Some (inl (RTYPE (Regidx (Z_to_bv 5 rs2), Regidx (Z_to_bv 5 rs1), Regidx (Z_to_bv 5 rd), XOR)), s).
Proof. dec_prove. Qed.

Lemma decode_SRL w rd rs1 rs2 :
  reg5 rd -> reg5 rs1 -> reg5 rs2 -> bv_unsigned w = encR 0 rs2 rs1 5 rd 0x33 ->
  runX (ext_decode w) s = Some (inl (RTYPE (Regidx (Z_to_bv 5 rs2), Regidx (Z_to_bv 5 rs1), Regidx (Z_to_bv 5 rd), SRL)), s).
Proof. dec_prove. Qed.

Lemma decode_SRA w rd rs1 rs2 :
  reg5 rd -> reg5 rs1 -> reg5 rs2 -> bv_unsigned w = encR 32 rs2 rs1 5 rd 0x33 ->
  runX (ext_decode w) s = Some (inl (RTYPE (Regidx (Z_to_bv 5 rs2), Regidx (Z_to_bv 5 rs1), Regidx (Z_to_bv 5 rd), SRA)), s).
Proof. dec_prove. Qed.

Lemma decode_OR w rd rs1 rs2 :
  reg5 rd -> reg5 rs1 -> reg5 rs2 -> bv_unsigned w = encR 0 rs2 rs1 6 rd 0x33 ->
  runX (ext_decode w) s = Some (inl (RTYPE (Regidx (Z_to_bv 5 rs2), Regidx (Z_to_bv 5 rs1), Regidx (Z_to_bv 5 rd), OR)), s).
Proof. dec_prove. Qed.

Lemma decode_AND w rd rs1 rs2 :
  reg5 rd -> reg5 rs1 -> reg5 rs2 -> bv_unsigned w = encR 0 rs2 rs1 7 rd 0x33 ->
  runX (ext_decode w) s = Some (inl (RTYPE (Regidx (Z_to_bv 5 rs2), Regidx (Z_to_bv 5 rs1), Regidx (Z_to_bv 5 rd), AND)), s).
Proof. dec_prove. Qed.

Lemma decode_MUL w rd rs1 rs2 :
  reg5 rd -> reg5 rs1 -> reg5 rs2 -> bv_unsigned w = encR 1 rs2 rs1 0 rd 0x33 ->
  runX (ext_decode w) s = Some (inl (MUL (Regidx (Z_to_bv 5 rs2), Regidx (Z_to_bv 5 rs1), Regidx (Z_to_bv 5 rd), {| mul_op_result_part := Low; mul_op_signed_rs1 := Signed; mul_op_signed_rs2 := Signed |})), s).
Proof. dec_prove. Qed.

Lemma decode_MULHU w rd rs1 rs2 :
  reg5 rd -> reg5 rs1 -> reg5 rs2 -> bv_unsigned w = encR 1 rs2 rs1 3 rd 0x33 ->
  runX (ext_decode w) s = Some (inl (MUL (Regidx (Z_to_bv 5 rs2), Regidx (Z_to_bv 5 rs1), Regidx (Z_to_bv 5 rd), {| mul_op_result_part := High; mul_op_signed_rs1 := Unsigned; mul_op_signed_rs2 := Unsigned |})), s).
Proof. dec_prove. Qed.

Lemma decode_DIV w rd rs1 rs2 :
  reg5 rd -> reg5 rs1 -> reg5 rs2 -> bv_unsigned w = encR 1 rs2 rs1 4 rd 0x33 ->
  runX (ext_decode w) s = Some (inl (DIV (Regidx (Z_to_bv 5 rs2), Regidx (Z_to_bv 5 rs1), Regidx (Z_to_bv 5 rd), false)), s).
Proof. dec_prove. Qed.

End D.
