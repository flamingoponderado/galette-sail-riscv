(** * Execution of the arithmetic instructions *)

From stdpp Require Import base bitvector.definitions.
From SailStdpp Require Import Base ConcurrencyInterfaceV2.
From Riscv Require Import rv64d_types rv64d riscv_extras.
From GaletteSail Require Export Exec.
From Stdlib Require Import Lia.
Import ListNotations.

Local Open Scope Z_scope.

Definition rop_val (op : rop) (x y : mword 64) : mword 64 :=
  match op with
  | ADD => add_vec x y
  | SLT => zero_extend' 64 (bool_to_bit (zopz0zI_s x y))
  | SLTU => zero_extend' 64 (bool_to_bit (zopz0zI_u x y))
  | AND => and_vec x y
  | OR => or_vec x y
  | XOR => xor_vec x y
  | SLL => shift_bits_left x (subrange_vec_dec y (log2_xlen - 1) 0)
  | SRL => shift_bits_right x (subrange_vec_dec y (log2_xlen - 1) 0)
  | SUB => sub_vec x y
  | SRA => shift_bits_right_arith x (subrange_vec_dec y (log2_xlen - 1) 0)
  end.

Lemma exec_RTYPE (s : SailState) a b c op :
  runX (execute (RTYPE (Regidx a, Regidx b, Regidx c, op))) s =
  Some (inl RETIRE_SUCCESS,
        mkSailState (set_gpr (regs s) (uint c) (rop_val op (gpr (regs s) (uint b)) (gpr (regs s) (uint a)))) (mem s)).
Proof. destruct op; ev. Qed.

Definition iop_val (op : iop) (x : mword 64) (imm : mword 12) : mword 64 :=
  let immext : mword 64 := sign_extend' 64 imm in
  match op with
  | ADDI => add_vec x immext
  | SLTI => zero_extend' 64 (bool_to_bit (zopz0zI_s x immext))
  | SLTIU => zero_extend' 64 (bool_to_bit (zopz0zI_u x immext))
  | ANDI => and_vec x immext
  | ORI => or_vec x immext
  | XORI => xor_vec x immext
  end.

Lemma exec_ITYPE (s : SailState) imm b c op :
  runX (execute (ITYPE (imm, Regidx b, Regidx c, op))) s =
  Some (inl RETIRE_SUCCESS,
        mkSailState (set_gpr (regs s) (uint c) (iop_val op (gpr (regs s) (uint b)) imm)) (mem s)).
Proof. destruct op; ev. Qed.

Definition sop_val (op : sop) (x : mword 64) (sh : mword 6) : mword 64 :=
  let sh := subrange_vec_dec sh (log2_xlen - 1) 0 in
  match op with
  | SLLI => shift_bits_left x sh
  | SRLI => shift_bits_right x sh
  | SRAI => shift_bits_right_arith x sh
  end.

Lemma exec_SHIFTIOP (s : SailState) sh b c op :
  runX (execute (SHIFTIOP (sh, Regidx b, Regidx c, op))) s =
  Some (inl RETIRE_SUCCESS,
        mkSailState (set_gpr (regs s) (uint c) (sop_val op (gpr (regs s) (uint b)) sh)) (mem s)).
Proof. destruct op; ev. Qed.

Lemma exec_MUL (s : SailState) a b c mop :
  runX (execute (MUL (Regidx a, Regidx b, Regidx c, mop))) s =
  Some (inl RETIRE_SUCCESS,
        mkSailState (set_gpr (regs s) (uint c)
          (mult_to_bits_half xlen (mul_op_signed_rs1 mop) (mul_op_signed_rs2 mop)
             (gpr (regs s) (uint b)) (gpr (regs s) (uint a)) (mul_op_result_part mop))) (mem s)).
Proof. ev. Qed.

Definition div_val (x y : mword 64) : mword 64 :=
  let q := if Z.eqb (sint y) 0 then Z.opp 1 else Z.quot (sint x) (sint y) in
  let q := if Z.geb q (pow2 (xlen - 1)) then Z.opp (pow2 (xlen - 1)) else q in
  to_bits_truncate 64 q.

Lemma exec_DIV (s : SailState) a b c :
  runX (execute (DIV (Regidx a, Regidx b, Regidx c, false))) s =
  Some (inl RETIRE_SUCCESS,
        mkSailState (set_gpr (regs s) (uint c) (div_val (gpr (regs s) (uint b)) (gpr (regs s) (uint a)))) (mem s)).
Proof. ev. Qed.

Definition utype_off (imm : mword 20) : mword 64 := sign_extend' 64 (concat_vec imm (Ox"000" : mword 12)).

Lemma exec_LUI (s : SailState) imm c :
  runX (execute (UTYPE (imm, Regidx c, LUI))) s =
  Some (inl RETIRE_SUCCESS, mkSailState (set_gpr (regs s) (uint c) (utype_off imm)) (mem s)).
Proof. ev. Qed.

Lemma exec_AUIPC (s : SailState) imm c :
  runX (execute (UTYPE (imm, Regidx c, AUIPC))) s =
  Some (inl RETIRE_SUCCESS,
        mkSailState (set_gpr (regs s) (uint c) (add_vec (rd (regs s) PC) (utype_off imm))) (mem s)).
Proof. ev. Qed.
