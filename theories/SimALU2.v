(** * Simulation of shifts, multiplication, comparisons and upper immediates *)

From stdpp Require Import base bitvector.definitions.
From SailStdpp Require Import Base ConcurrencyInterfaceV2.
From Riscv Require Import rv64d_types rv64d riscv_extras.
From GaletteSail Require Export SimALU Values4.
From Stdlib Require Import Lia.

Local Open Scope Z_scope.

Section Sims.

Variables (base size : mword 64) (s : SailState).
Hypothesis Hinv : SailInv base size s.
Hypothesis Hal : bv_unsigned (rd (regs s) PC) mod 4 = 0.
Hypothesis Hin : in_region base size (rd (regs s) PC) 4.

(** The common shape: decode to [ast], execute to [v] in register [d]. *)
Local Ltac alu_sim ast d v dec exec_eq :=
  intros Hw; enc_simpl2 Hw; reg_ranges;
  repeat match goal with
  | x : W.word ?k |- _ =>
      lazymatch k with 5%N => fail | _ => idtac end;
      lazymatch goal with
      | _ : 0 <= zw x < _ |- _ => fail
      | _ => let H := fresh in pose proof (zw_range x ltac:(lia)) as H; cbn [Z.of_N] in H
      end
  end;
  pose proof Hinv as (_ & Hag & _);
  apply (sailsim_alu base size s Hinv Hal Hin _ ast d v);
  [ rewrite Hw; lia
  | intros w Hw'; apply dec; first [ exact Hag | assumption | (unfold reg5; lia) |
                                     (unfold encR, encI, encU; lia) | lia ]
  | rewrite exec_eq, ?uint_reg, ?gpr_step_pre; try reflexivity
  | cbv [P.aexec]; cbn [sobs P.aregs P.apc P.amem]; rewrite ?rreg_sgpr, ?sgpr_gpr ].

Lemma sim_SLTU d r1 r2 :
  mem_val (mem s) (rd (regs s) PC) 4 = zw (R.Encode (R.ArithR (R.SLTU (d, r1, r2)))) ->
  SailSim base size (R.ArithR (R.SLTU (d, r1, r2))) s.
Proof.
  alu_sim (RTYPE (Regidx (Z_to_bv 5 (zw r2)), Regidx (Z_to_bv 5 (zw r1)), Regidx (Z_to_bv 5 (zw d)), SLTU))
    d (rop_val SLTU (gpr (regs s) (zw r1)) (gpr (regs s) (zw r2))) decode_SLTU exec_RTYPE.
  cbn [rop_val]. rewrite bvw_sltu. reflexivity.
Qed.

Lemma sim_SLL d r1 r2 :
  mem_val (mem s) (rd (regs s) PC) 4 = zw (R.Encode (R.Shift (R.SLL (d, r1, r2)))) ->
  SailSim base size (R.Shift (R.SLL (d, r1, r2))) s.
Proof.
  alu_sim (RTYPE (Regidx (Z_to_bv 5 (zw r2)), Regidx (Z_to_bv 5 (zw r1)), Regidx (Z_to_bv 5 (zw d)), SLL))
    d (rop_val SLL (gpr (regs s) (zw r1)) (gpr (regs s) (zw r2))) decode_SLL exec_RTYPE.
  cbn [rop_val]. rewrite bvw_shiftl. reflexivity.
Qed.

Lemma sim_SRL d r1 r2 :
  mem_val (mem s) (rd (regs s) PC) 4 = zw (R.Encode (R.Shift (R.SRL (d, r1, r2)))) ->
  SailSim base size (R.Shift (R.SRL (d, r1, r2))) s.
Proof.
  alu_sim (RTYPE (Regidx (Z_to_bv 5 (zw r2)), Regidx (Z_to_bv 5 (zw r1)), Regidx (Z_to_bv 5 (zw d)), SRL))
    d (rop_val SRL (gpr (regs s) (zw r1)) (gpr (regs s) (zw r2))) decode_SRL exec_RTYPE.
  cbn [rop_val]. rewrite bvw_shiftr. reflexivity.
Qed.

Lemma sim_SRA d r1 r2 :
  mem_val (mem s) (rd (regs s) PC) 4 = zw (R.Encode (R.Shift (R.SRA (d, r1, r2)))) ->
  SailSim base size (R.Shift (R.SRA (d, r1, r2))) s.
Proof.
  alu_sim (RTYPE (Regidx (Z_to_bv 5 (zw r2)), Regidx (Z_to_bv 5 (zw r1)), Regidx (Z_to_bv 5 (zw d)), SRA))
    d (rop_val SRA (gpr (regs s) (zw r1)) (gpr (regs s) (zw r2))) decode_SRA exec_RTYPE.
  cbn [rop_val]. rewrite bvw_sra. reflexivity.
Qed.

Lemma sim_SLLI d r1 sh :
  mem_val (mem s) (rd (regs s) PC) 4 = zw (R.Encode (R.Shift (R.SLLI (d, r1, sh)))) ->
  SailSim base size (R.Shift (R.SLLI (d, r1, sh))) s.
Proof.
  alu_sim (SHIFTIOP (Z_to_bv 6 (zw sh), Regidx (Z_to_bv 5 (zw r1)), Regidx (Z_to_bv 5 (zw d)), SLLI))
    d (sop_val SLLI (gpr (regs s) (zw r1)) (Z_to_bv 6 (zw sh))) decode_SLLI exec_SHIFTIOP.
  cbn [sop_val]. rewrite bvw_shiftl_imm. reflexivity.
Qed.

Lemma sim_SRLI d r1 sh :
  mem_val (mem s) (rd (regs s) PC) 4 = zw (R.Encode (R.Shift (R.SRLI (d, r1, sh)))) ->
  SailSim base size (R.Shift (R.SRLI (d, r1, sh))) s.
Proof.
  alu_sim (SHIFTIOP (Z_to_bv 6 (zw sh), Regidx (Z_to_bv 5 (zw r1)), Regidx (Z_to_bv 5 (zw d)), SRLI))
    d (sop_val SRLI (gpr (regs s) (zw r1)) (Z_to_bv 6 (zw sh))) decode_SRLI exec_SHIFTIOP.
  cbn [sop_val]. rewrite bvw_shiftr_imm. reflexivity.
Qed.

Lemma sim_SRAI d r1 sh :
  mem_val (mem s) (rd (regs s) PC) 4 = zw (R.Encode (R.Shift (R.SRAI (d, r1, sh)))) ->
  SailSim base size (R.Shift (R.SRAI (d, r1, sh))) s.
Proof.
  alu_sim (SHIFTIOP (Z_to_bv 6 (zw sh), Regidx (Z_to_bv 5 (zw r1)), Regidx (Z_to_bv 5 (zw d)), SRAI))
    d (sop_val SRAI (gpr (regs s) (zw r1)) (Z_to_bv 6 (zw sh))) decode_SRAI exec_SHIFTIOP.
  cbn [sop_val]. rewrite bvw_sra_imm. reflexivity.
Qed.

Lemma sim_MUL d r1 r2 :
  mem_val (mem s) (rd (regs s) PC) 4 = zw (R.Encode (R.MulDiv (R.MUL (d, r1, r2)))) ->
  SailSim base size (R.MulDiv (R.MUL (d, r1, r2))) s.
Proof.
  alu_sim (MUL (Regidx (Z_to_bv 5 (zw r2)), Regidx (Z_to_bv 5 (zw r1)), Regidx (Z_to_bv 5 (zw d)),
                {| mul_op_result_part := Low; mul_op_signed_rs1 := Signed; mul_op_signed_rs2 := Signed |}))
    d (mult_to_bits_half xlen Signed Signed (gpr (regs s) (zw r1)) (gpr (regs s) (zw r2)) Low) decode_MUL exec_MUL.
  rewrite bvw_mul. reflexivity.
Qed.

Lemma sim_MULHU d r1 r2 :
  mem_val (mem s) (rd (regs s) PC) 4 = zw (R.Encode (R.MulDiv (R.MULHU (d, r1, r2)))) ->
  SailSim base size (R.MulDiv (R.MULHU (d, r1, r2))) s.
Proof.
  alu_sim (MUL (Regidx (Z_to_bv 5 (zw r2)), Regidx (Z_to_bv 5 (zw r1)), Regidx (Z_to_bv 5 (zw d)),
                {| mul_op_result_part := High; mul_op_signed_rs1 := Unsigned; mul_op_signed_rs2 := Unsigned |}))
    d (mult_to_bits_half xlen Unsigned Unsigned (gpr (regs s) (zw r1)) (gpr (regs s) (zw r2)) High) decode_MULHU exec_MUL.
  rewrite bvw_mulhu. reflexivity.
Qed.

Lemma sim_LUI d i :
  mem_val (mem s) (rd (regs s) PC) 4 = zw (R.Encode (R.ArithI (R.LUI (d, i)))) ->
  SailSim base size (R.ArithI (R.LUI (d, i))) s.
Proof.
  alu_sim (UTYPE (Z_to_bv 20 (zw i), Regidx (Z_to_bv 5 (zw d)), LUI)) d (utype_off (Z_to_bv 20 (zw i)))
    decode_LUI exec_LUI.
  rewrite bvw_utype_off. reflexivity.
Qed.

Lemma sim_AUIPC d i :
  mem_val (mem s) (rd (regs s) PC) 4 = zw (R.Encode (R.ArithI (R.AUIPC (d, i)))) ->
  SailSim base size (R.ArithI (R.AUIPC (d, i))) s.
Proof.
  alu_sim (UTYPE (Z_to_bv 20 (zw i), Regidx (Z_to_bv 5 (zw d)), AUIPC)) d
    (add_vec (rd (regs s) PC) (utype_off (Z_to_bv 20 (zw i)))) decode_AUIPC exec_AUIPC.
  rewrite bvw_add_vec, bvw_utype_off. reflexivity.
Qed.

Lemma sim_DIV d r1 r2 :
  mem_val (mem s) (rd (regs s) PC) 4 = zw (R.Encode (R.MulDiv (R.DIV (d, r1, r2)))) ->
  SailSim base size (R.MulDiv (R.DIV (d, r1, r2))) s.
Proof.
  alu_sim (DIV (Regidx (Z_to_bv 5 (zw r2)), Regidx (Z_to_bv 5 (zw r1)), Regidx (Z_to_bv 5 (zw d)), false))
    d (div_val (gpr (regs s) (zw r1)) (gpr (regs s) (zw r2))) decode_DIV exec_DIV.
  unfold Galette.Base.bool_decide. destruct (Galette.Base.decide _) as [E|E].
  - rewrite bvw_div_zero by exact E. reflexivity.
  - rewrite bvw_div_nz by exact E. reflexivity.
Qed.

End Sims.
