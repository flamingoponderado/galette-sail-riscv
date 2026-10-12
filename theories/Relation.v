(** * The state relation and the Sail invariant

    [Rel ms m] relates an L3 state and a Sail machine:
    - [riscv_ok ms = sail_ok m] (both include a 4-byte aligned PC);
    - the PCs, the registers [x1]..[x31] and the whole memories agree
      ([aeq] on the abstract views [obs ms] and [sobs (sm_state m)]).
      The raw value of L3's [x0] is not related: Sail has no [x0]
      register, and both models read [x0] as 0.

    [SailInv base size s] collects the Sail-only conditions under which
    [try_step] behaves as a plain RV64IM step (see [Config.v] for the
    meaning of each control register):
    - every control register (all registers except [PC], [nextPC],
      [x1]..[x31], [minstret] and [pma_regions]) has its value in the
      reference configuration [cfg]: machine mode, hart active,
      [mstatus = 0] (MIE = 0, MPRV = 0), no pending or enabled interrupt,
      PMP off, [misa] = RV64IMC, triggers off, counters on;
    - [pma_regions] is the single RAM region [[base, base + size)] with
      main-memory attributes ([ram_attrs]: readable, writable,
      executable, misaligned accesses allowed);
    - that region lies below [2^64] and avoids the CLINT and the
      signature device ([region_ok]). *)

From stdpp Require Import base bitvector.definitions.
From SailStdpp Require Import Base ConcurrencyInterfaceV2.
From Riscv Require Import rv64d_types rv64d.
From GaletteSail Require Export SailTarget Mem.
From Galette.cakeml.compiler.encoders.riscv Require riscv_target.
From Galette.HOL.examples.l3_machine_code.riscv.model Require riscv.
Module R := Galette.HOL.examples.l3_machine_code.riscv.model.riscv.

Definition SailInv (base size : mword 64) (s : SailState) : Prop :=
  region_ok base size /\ agree ctrl cfg (regs s) /\
  rd (regs s) pma_regions = [ram_region base size].

Definition Rel (ms : R.riscv_state) (m : SailMachine) : Prop :=
  riscv_target.riscv_ok ms = sail_ok m /\ aeq (P.obs ms) (sobs (sm_state m)).

(** ** [aexec] respects [aeq] *)

Lemma rreg_aeq g1 g2 :
  (forall r, r <> W.n2w 0 -> g1 r = g2 r) -> forall x, P.rreg g1 x = P.rreg g2 x.
Proof.
  intros H x. unfold P.rreg, Galette.Base.bool_decide.
  destruct (Galette.Base.decide (x = W.n2w 0)); [reflexivity|apply H; assumption].
Qed.

Lemma wreg_aeq g1 g2 d v :
  (forall r, r <> W.n2w 0 -> g1 r = g2 r) ->
  forall r, r <> W.n2w 0 -> P.wreg d v g1 r = P.wreg d v g2 r.
Proof.
  intros H r Hr. unfold P.wreg, combin.UPDATE, Galette.Base.bool_decide.
  destruct (Galette.Base.decide (d = W.n2w 0)); [apply H, Hr|].
  destruct (Galette.Base.decide (d = r)); [reflexivity|apply H, Hr].
Qed.

Lemma aexec_aeq i A B : aeq A B -> aeq (P.aexec i A) (P.aexec i B).
Proof.
  intros (Hr & Hpc & Hm). pose proof (rreg_aeq _ _ Hr) as Hrr.
  destruct A as [gA pA mA], B as [gB pB mB]; cbn in Hpc, Hm, Hr, Hrr; subst pB mB.
  unfold P.aexec; cbn [P.aregs P.apc P.amem].
  destruct i;
    try match goal with
    | x : R.ArithI_ty |- _ => destruct x | x : R.ArithR_ty |- _ => destruct x
    | x : R.Shift_ty |- _ => destruct x | x : R.MulDiv_ty |- _ => destruct x
    | x : R.Load_ty |- _ => destruct x | x : R.Store_ty |- _ => destruct x
    | x : R.Branch_ty |- _ => destruct x
    end;
    repeat match goal with p : _ * _ |- _ => destruct p end;
    cbv zeta; rewrite ?Hrr;
    (split; [intros r Hr0; cbn [P.aregs]; first [apply wreg_aeq; assumption | apply Hr; assumption | reflexivity]
            | split; reflexivity]).
Qed.
