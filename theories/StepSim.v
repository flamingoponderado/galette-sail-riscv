(** * Step simulation between L3 and Sail

    [step_sim_of_sail] reduces the simulation of one instruction to a
    statement about Sail alone ([SailSim]): one [try_step] retires, keeps
    [SailInv], and changes the abstract view of the state as L3's [aexec]
    does.  The per-instruction [SailSim] lemmas are below. *)

From stdpp Require Import base bitvector.definitions.
From SailStdpp Require Import Base ConcurrencyInterfaceV2.
From Riscv Require Import rv64d_types rv64d.
From GaletteSail Require Export Relation SailStep L3Enc.
From Galette.HOL.examples.l3_machine_code.riscv.step Require riscv_step.
From Galette.HOL.src.coretypes Require option.
From Stdlib Require Import Lia.

Local Open Scope Z_scope.

Lemma aeq_refl A : aeq A A.
Proof. split; [reflexivity|split; reflexivity]. Qed.

Lemma aeq_sym A B : aeq A B -> aeq B A.
Proof. intros (H1 & H2 & H3). split; [intros r Hr; symmetry; apply H1, Hr|split; symmetry; assumption]. Qed.

Lemma aeq_trans A B C : aeq A B -> aeq B C -> aeq A C.
Proof.
  intros (H1 & H2 & H3) (G1 & G2 & G3).
  split; [intros r Hr; rewrite H1, G1 by exact Hr; reflexivity|split; congruence].
Qed.

(** The Sail half of the simulation of instruction [i]. *)
Definition SailSim (base size : mword 64) (i : R.instruction) (s : SailState) : Prop :=
  exists s', run (try_step 0 false) s = Some (false, s') /\ retired s s' = true /\
    SailInv base size s' /\ aeq (sobs s') (P.aexec i (sobs s)).

Section Generic.

Variables (base size : mword 64).

Theorem step_sim_of_sail ms m i :
  P.supported i = true -> Rel ms m -> riscv_target.riscv_ok ms = true ->
  P.bytes_at ms (R.Encode i) -> P.mem_ok i (P.obs ms) ->
  SailSim base size i (sm_state m) ->
  Rel (riscv_target.riscv_next ms) (sail_next m) /\ SailInv base size (sm_state (sail_next m)).
Proof.
  intros Hsup (Hok & Haeq) Hrok Hb Hm (s' & Hrun & Hret & Hinv' & Hs').
  apply P.riscv_ok_iff in Hrok as Hrok'. destruct Hrok' as (Hsok & Hal).
  destruct (P.step_thm ms i Hsup Hsok Hal Hb Hm) as (ms' & Hnext & Hsok' & Hobs).
  assert (Hm_ok : sm_ok m = true).
  { unfold sail_ok in Hok. rewrite Hrok in Hok. symmetry in Hok. apply andb_prop in Hok. apply Hok. }
  assert (Hsn : sail_next m = mkSM s' true).
  { unfold sail_next. rewrite Hrun, Hret, Hm_ok. reflexivity. }
  assert (Hrn : riscv_target.riscv_next ms = ms').
  { unfold riscv_target.riscv_next. rewrite Hnext. reflexivity. }
  rewrite Hsn, Hrn. cbn [sm_state]. split; [|exact Hinv'].
  assert (HA : aeq (P.obs ms') (sobs s')).
  { rewrite Hobs. eapply aeq_trans; [apply aexec_aeq, Haeq|apply aeq_sym, Hs']. }
  split; [|exact HA].
  destruct HA as (_ & Hpc & _).
  unfold sail_ok, sail_pc. cbn [sm_ok sm_state].
  destruct (riscv_target.riscv_ok ms') eqn:E.
  - apply P.riscv_ok_iff in E as (_ & E). cbn [P.obs P.apc sobs] in Hpc. rewrite <- Hpc, E. reflexivity.
  - assert (E' : alignment.aligned 2 (R.riscv_state_c_PC ms' (R.riscv_state_procID ms')) = false).
    { destruct (alignment.aligned 2 (R.riscv_state_c_PC ms' (R.riscv_state_procID ms'))) eqn:E2; [|reflexivity].
      exfalso. assert (riscv_target.riscv_ok ms' = true) by (apply P.riscv_ok_iff; tauto). congruence. }
    cbn [P.obs P.apc sobs] in Hpc. rewrite <- Hpc, E'. reflexivity.
Qed.

End Generic.
