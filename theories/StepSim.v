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

(** ** Linking the fetched word to L3's memory *)

Lemma wbv_add_n (p : mword 64) (k : nat) :
  wbv (W.word_add (bvw p) (W.n2w (N.of_nat k)) : W.word 64) = bv_add p (Z_to_bv 64 (Z.of_nat k)).
Proof.
  apply bv_eq. rewrite wbv_unsigned by lia. rewrite zw_add by lia. rewrite zw_bvw, zw_n2w by nsize.
  rewrite bv_add_unsigned, Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn [Z.of_N].
  rewrite nat_N_Z. rewrite !Zplus_mod_idemp_r. reflexivity.
Qed.

Lemma byte_at_link ms s k :
  aeq (P.obs ms) (sobs s) ->
  byte_at (mem s) (rd (regs s) PC) k =
  zw (R.riscv_state_MEM8 ms (W.word_add (R.riscv_state_c_PC ms (R.riscv_state_procID ms)) (W.n2w (N.of_nat k)))).
Proof.
  intros (_ & Hpc & Hm). cbn [P.obs P.apc P.amem sobs] in Hpc, Hm. rewrite Hm, Hpc.
  rewrite zw_bvw by lia. rewrite wbv_add_n. reflexivity.
Qed.

Lemma fetch_word_link ms s (w : W.word 32) :
  aeq (P.obs ms) (sobs s) -> P.bytes_at ms w -> mem_val (mem s) (rd (regs s) PC) 4 = zw w.
Proof.
  intros Ha (H0 & H1 & H2 & H3). rewrite mem_val_4. rewrite !(byte_at_link ms s) by exact Ha.
  change (N.of_nat 0) with 0%N. change (N.of_nat 1) with 1%N. change (N.of_nat 2) with 2%N. change (N.of_nat 3) with 3%N.
  replace (W.word_add (R.riscv_state_c_PC ms (R.riscv_state_procID ms)) (W.n2w 0))
    with (R.riscv_state_c_PC ms (R.riscv_state_procID ms))
    by (apply word_eq_zw; rewrite zw_add, zw_n2w by lia;
        pose proof (zw_range (R.riscv_state_c_PC ms (R.riscv_state_procID ms)) ltac:(lia));
        cbn in *; rewrite Z.add_0_r; symmetry; apply Z.mod_small; lia).
  rewrite H0, H1, H2, H3. rewrite !zw_extract by lia. cbn [Z.of_N]. pose proof (zw_range w ltac:(lia)) as Hw.
  cbn [Z.of_N] in Hw. rewrite !(Z.mod_small (_ mod _) (2 ^ 8)) by (apply Z.mod_pos_bound; lia).
  lia.
Qed.

(** ** Instructions that write one register and fall through *)

Lemma retired_post s s1 :
  rd (regs s1) minstret = rd (regs s) minstret -> retired s (step_post s1) = true.
Proof.
  intros H. unfold retired, step_post. cbn [regs].
  rewrite rd_upd_same. rewrite H.
  apply bool_decide_eq_true. reflexivity.
Qed.

Lemma SailInv_post base size s s1 :
  SailInv base size s -> agree ctrl cfg (regs s1) -> rd (regs s1) pma_regions = rd (regs s) pma_regions ->
  SailInv base size (step_post s1).
Proof.
  intros (H1 & H2 & H3) H4 H5. split; [exact H1|split].
  - unfold step_post; cbn [regs]. apply agree_upd_data; [apply agree_upd_data; [exact H4|reflexivity]|reflexivity].
  - unfold step_post; cbn [regs]. rewrite !rd_upd_other by discriminate. rewrite H5. exact H3.
Qed.

Section Alu.

Variables (base size : mword 64) (s : SailState).
Hypothesis Hinv : SailInv base size s.
Hypothesis Hal : bv_unsigned (rd (regs s) PC) mod 4 = 0.
Hypothesis Hin : in_region base size (rd (regs s) PC) 4.

Lemma sailsim_alu i ast (d : W.word 5) v :
  mem_val (mem s) (rd (regs s) PC) 4 mod 4 = 3 ->
  (forall w, bv_unsigned w = mem_val (mem s) (rd (regs s) PC) 4 -> runX (ext_decode w) s = Some (inl ast, s)) ->
  runX (execute ast) (step_pre s) =
    Some (inl RETIRE_SUCCESS, mkSailState (set_gpr (regs (step_pre s)) (zw d) v) (mem s)) ->
  P.aexec i (sobs s) =
    P.mk_astate (P.wreg d (bvw v) (sgpr (regs s))) (W.word_add (bvw (rd (regs s) PC)) (W.n2w 4)) (P.amem (sobs s)) ->
  SailSim base size i s.
Proof.
  intros Hrvc Hdec Hexec Hax. destruct Hinv as (Hreg & Hag & Hpma).
  set (s1 := mkSailState (set_gpr (regs (step_pre s)) (zw d) v) (mem s)).
  assert (Hag1 : agree ctrl cfg (regs s1)).
  { apply agree_set_gpr. apply agree_upd_data; [exact Hag|reflexivity]. }
  exists (step_post s1). split; [|split; [|split]].
  - apply (step_with_decode base size s Hreg Hag Hpma Hal Hin ast s1); auto.
  - apply retired_post. cbn [s1 regs step_pre]. rewrite rd_set_gpr_other by reflexivity.
    apply rd_upd_other. discriminate.
  - apply (SailInv_post base size s s1); [split; [exact Hreg|split; assumption]|exact Hag1|].
    cbn [s1 regs step_pre]. rewrite rd_set_gpr_other by reflexivity. apply rd_upd_other. discriminate.
  - rewrite Hax. split; [|split].
    + intros r Hr. cbn [sobs P.aregs step_post s1 regs step_pre].
      rewrite !sgpr_upd_other by reflexivity. rewrite sgpr_set_gpr by exact Hr.
      apply wreg_aeq; [|exact Hr]. intros r' _. apply sgpr_upd_other. reflexivity.
    + cbn [sobs P.apc step_post s1 regs step_pre].
      rewrite (rd_upd_other _ minstret PC) by discriminate. rewrite rd_upd_same.
      rewrite rd_set_gpr_other by reflexivity. rewrite rd_upd_same.
      apply bvw_add_vec_int. lia.
    + reflexivity.
Qed.

End Alu.

(** ** Per-instruction simulations *)

Ltac zw_closed :=
  repeat match goal with
  | |- context [@zw ?n ?x] =>
      is_closed_term x; let v := eval vm_compute in (@zw n x) in change (@zw n x) with v
  | H : context [@zw ?n ?x] |- _ =>
      is_closed_term x; let v := eval vm_compute in (@zw n x) in change (@zw n x) with v in H
  end.

Ltac enc_simpl H :=
  cbn [R.Encode] in H; rewrite ?zw_Rtype in H; zw_closed.

Ltac reg_ranges :=
  repeat match goal with
  | x : W.word 5 |- _ =>
      lazymatch goal with
      | _ : 0 <= zw x < 32 |- _ => fail
      | _ => let H := fresh in pose proof (zw_range x ltac:(lia)) as H; change (2 ^ Z.of_N 5) with 32 in H
      end
  end.

Lemma gpr_step_pre s i : gpr (regs (step_pre s)) i = gpr (regs s) i.
Proof. apply gpr_upd_other. reflexivity. Qed.

Lemma uint_reg (r : W.word 5) : uint (Z_to_bv 5 (zw r) : mword 5) = zw r.
Proof. apply uint_Z_to_bv5. pose proof (zw_range r ltac:(lia)). cbn in *. lia. Qed.

Lemma sgpr_gpr rf r : sgpr rf r = bvw (gpr rf (zw r)).
Proof. reflexivity. Qed.

