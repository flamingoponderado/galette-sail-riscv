(** * Decoding lemmas (DecodeI) *)

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

Lemma decode_ADDI w rd rs1 imm :
  reg5 rd -> reg5 rs1 -> 0 <= imm < 4096 -> bv_unsigned w = encI imm rs1 0 rd 0x13 ->
  runX (ext_decode w) s = Some (inl (ITYPE (Z_to_bv 12 imm, Regidx (Z_to_bv 5 rs1), Regidx (Z_to_bv 5 rd), ADDI)), s).
Proof. dec_prove. Qed.

Lemma decode_XORI w rd rs1 imm :
  reg5 rd -> reg5 rs1 -> 0 <= imm < 4096 -> bv_unsigned w = encI imm rs1 4 rd 0x13 ->
  runX (ext_decode w) s = Some (inl (ITYPE (Z_to_bv 12 imm, Regidx (Z_to_bv 5 rs1), Regidx (Z_to_bv 5 rd), XORI)), s).
Proof. dec_prove. Qed.

Lemma decode_ANDI w rd rs1 imm :
  reg5 rd -> reg5 rs1 -> 0 <= imm < 4096 -> bv_unsigned w = encI imm rs1 7 rd 0x13 ->
  runX (ext_decode w) s = Some (inl (ITYPE (Z_to_bv 12 imm, Regidx (Z_to_bv 5 rs1), Regidx (Z_to_bv 5 rd), ANDI)), s).
Proof. dec_prove. Qed.

Lemma decode_ORI w rd rs1 imm :
  reg5 rd -> reg5 rs1 -> 0 <= imm < 4096 -> ~ (rd = 0 /\ (imm mod 32 = 0 \/ imm mod 32 = 1 \/ imm mod 32 = 3)) -> bv_unsigned w = encI imm rs1 6 rd 0x13 ->
  runX (ext_decode w) s = Some (inl (ITYPE (Z_to_bv 12 imm, Regidx (Z_to_bv 5 rs1), Regidx (Z_to_bv 5 rd), ORI)), s).
Proof. dec_prove. Qed.

Lemma decode_SLLI w rd rs1 sh :
  reg5 rd -> reg5 rs1 -> 0 <= sh < 64 -> bv_unsigned w = encI sh rs1 1 rd 0x13 ->
  runX (ext_decode w) s = Some (inl (SHIFTIOP (Z_to_bv 6 sh, Regidx (Z_to_bv 5 rs1), Regidx (Z_to_bv 5 rd), SLLI)), s).
Proof. dec_prove. Qed.

Lemma decode_SRLI w rd rs1 sh :
  reg5 rd -> reg5 rs1 -> 0 <= sh < 64 -> bv_unsigned w = encI sh rs1 5 rd 0x13 ->
  runX (ext_decode w) s = Some (inl (SHIFTIOP (Z_to_bv 6 sh, Regidx (Z_to_bv 5 rs1), Regidx (Z_to_bv 5 rd), SRLI)), s).
Proof. dec_prove. Qed.

Lemma decode_SRAI w rd rs1 sh :
  reg5 rd -> reg5 rs1 -> 0 <= sh < 64 -> bv_unsigned w = encI (1024 + sh) rs1 5 rd 0x13 ->
  runX (ext_decode w) s = Some (inl (SHIFTIOP (Z_to_bv 6 sh, Regidx (Z_to_bv 5 rs1), Regidx (Z_to_bv 5 rd), SRAI)), s).
Proof. dec_prove. Qed.

Lemma decode_LUI w rd imm :
  reg5 rd -> 0 <= imm < 2 ^ 20 -> bv_unsigned w = encU imm rd 0x37 ->
  runX (ext_decode w) s = Some (inl (UTYPE (Z_to_bv 20 imm, Regidx (Z_to_bv 5 rd), LUI)), s).
Proof. dec_prove. Qed.

Lemma decode_AUIPC w rd imm :
  reg5 rd -> 0 <= imm < 2 ^ 20 -> bv_unsigned w = encU imm rd 0x17 ->
  runX (ext_decode w) s = Some (inl (UTYPE (Z_to_bv 20 imm, Regidx (Z_to_bv 5 rd), AUIPC)), s).
Proof. dec_prove. Qed.

End D.
