(** * Simulation of the register-register and register-immediate instructions *)

From stdpp Require Import base bitvector.definitions.
From SailStdpp Require Import Base ConcurrencyInterfaceV2.
From Riscv Require Import rv64d_types rv64d.
From GaletteSail Require Export StepSim.
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
