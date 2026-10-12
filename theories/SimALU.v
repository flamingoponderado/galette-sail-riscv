(** * Simulation of the register-register and register-immediate instructions *)

From stdpp Require Import base bitvector.definitions.
From SailStdpp Require Import Base ConcurrencyInterfaceV2.
From Riscv Require Import rv64d_types rv64d.
From GaletteSail Require Export StepSim Values DecodeR DecodeI DecodeM DecodeB.
From Stdlib Require Import Lia.

Local Open Scope Z_scope.

Section Sims.

Variables (base size : mword 64) (s : SailState).
Hypothesis Hinv : SailInv base size s.
Hypothesis Hal : bv_unsigned (rd (regs s) PC) mod 4 = 0.
Hypothesis Hin : in_region base size (rd (regs s) PC) 4.

Lemma sim_ADD d r1 r2 :
  mem_val (mem s) (rd (regs s) PC) 4 = zw (R.Encode (R.ArithR (R.ADD (d, r1, r2)))) ->
  ~ (zw d = 0 /\ zw r1 = 0 /\ 2 <= zw r2 <= 5) ->
  SailSim base size (R.ArithR (R.ADD (d, r1, r2))) s.
Proof.
  intros Hw Hntl. enc_simpl Hw. reg_ranges.
  pose proof Hinv as (_ & Hag & _).
  apply (sailsim_alu base size s Hinv Hal Hin _
           (RTYPE (Regidx (Z_to_bv 5 (zw r2)), Regidx (Z_to_bv 5 (zw r1)), Regidx (Z_to_bv 5 (zw d)), ADD))
           d (add_vec (gpr (regs s) (zw r1)) (gpr (regs s) (zw r2)))).
  - rewrite Hw. lia.
  - intros w Hw'. apply decode_ADD; [exact Hag|unfold reg5; lia..|unfold encR; lia|exact Hntl].
  - rewrite exec_ADD, !uint_reg, !gpr_step_pre. reflexivity.
  - cbv [P.aexec]. cbn [sobs P.aregs P.apc P.amem]. rewrite !rreg_sgpr, !sgpr_gpr, bvw_add_vec. reflexivity.
Qed.

End Sims.

Ltac enc_simpl2 H :=
  cbn [R.Encode] in H; rewrite ?zw_Rtype, ?zw_Itype, ?zw_Utype in H;
  rewrite ?zw_concat in H by lia; zw_closed; cbn [Z.of_N] in H.

Section Sims2.

Variables (base size : mword 64) (s : SailState).
Hypothesis Hinv : SailInv base size s.
Hypothesis Hal : bv_unsigned (rd (regs s) PC) mod 4 = 0.
Hypothesis Hin : in_region base size (rd (regs s) PC) 4.

Local Ltac rr d r1 r2 op dec rvsail :=
  intros Hw; enc_simpl Hw; reg_ranges;
  pose proof Hinv as (_ & Hag & _);
  apply (sailsim_alu base size s Hinv Hal Hin _
           (RTYPE (Regidx (Z_to_bv 5 (zw r2)), Regidx (Z_to_bv 5 (zw r1)), Regidx (Z_to_bv 5 (zw d)), op))
           d (rop_val op (gpr (regs s) (zw r1)) (gpr (regs s) (zw r2))));
  [ rewrite Hw; lia
  | intros w Hw'; apply dec; [exact Hag|unfold reg5; lia..|unfold encR; lia]
  | rewrite exec_RTYPE, !uint_reg, !gpr_step_pre; reflexivity
  | cbv [P.aexec]; cbn [sobs P.aregs P.apc P.amem]; rewrite !rreg_sgpr, !sgpr_gpr; cbn [rop_val];
    rewrite rvsail; reflexivity ].

Lemma sim_SUB d r1 r2 :
  mem_val (mem s) (rd (regs s) PC) 4 = zw (R.Encode (R.ArithR (R.SUB (d, r1, r2)))) ->
  SailSim base size (R.ArithR (R.SUB (d, r1, r2))) s.
Proof. rr d r1 r2 SUB decode_SUB bvw_sub. Qed.

Lemma sim_AND d r1 r2 :
  mem_val (mem s) (rd (regs s) PC) 4 = zw (R.Encode (R.ArithR (R.AND (d, r1, r2)))) ->
  SailSim base size (R.ArithR (R.AND (d, r1, r2))) s.
Proof. rr d r1 r2 AND decode_AND bvw_and. Qed.

Lemma sim_OR d r1 r2 :
  mem_val (mem s) (rd (regs s) PC) 4 = zw (R.Encode (R.ArithR (R.OR (d, r1, r2)))) ->
  SailSim base size (R.ArithR (R.OR (d, r1, r2))) s.
Proof. rr d r1 r2 OR decode_OR bvw_or. Qed.

Lemma sim_XOR d r1 r2 :
  mem_val (mem s) (rd (regs s) PC) 4 = zw (R.Encode (R.ArithR (R.XOR (d, r1, r2)))) ->
  SailSim base size (R.ArithR (R.XOR (d, r1, r2))) s.
Proof. rr d r1 r2 XOR decode_XOR bvw_xor. Qed.

End Sims2.
