(** * One Sail step for each instruction kind *)

From stdpp Require Import base bitvector.definitions.
From SailStdpp Require Import Base ConcurrencyInterfaceV2.
From Riscv Require Import rv64d_types rv64d.
From GaletteSail Require Export Decode Exec.
From Stdlib Require Import Lia.
Import ListNotations.

Local Open Scope Z_scope.

Lemma gpr_upd_other rf r v i : is_gpr r = false -> gpr (upd_reg rf r v) i = gpr rf i.
Proof.
  intros H. unfold gpr. destruct (xreg i) as [x|] eqn:E; [|reflexivity].
  apply xreg_gpr in E. exact (rd_upd_other rf r (R_bitvector_64 x) v ltac:(congruence)).
Qed.

Lemma uint_Z_to_bv5 r : 0 <= r < 32 -> uint (Z_to_bv 5 r : mword 5) = r.
Proof. intros H. rewrite uint_spec, Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn. apply Z.mod_small. lia. Qed.

Section SailStep.

Variables (base size : mword 64) (s : SailState).
Hypothesis Hreg : region_ok base size.
Hypothesis Hinv : agree ctrl cfg (regs s).
Hypothesis Hpma : rd (regs s) pma_regions = [ram_region base size].
Hypothesis Hal : bv_unsigned (rd (regs s) PC) mod 4 = 0.
Hypothesis Hin : in_region base size (rd (regs s) PC) 4.

Let pc := rd (regs s) PC.

(** Fetch and decode, for a word whose decoding is known. *)
Lemma step_with_decode ast s1 :
  (forall w, bv_unsigned w = mem_val (mem s) pc 4 -> runX (ext_decode w) s = Some (inl ast, s)) ->
  mem_val (mem s) pc 4 mod 4 = 3 ->
  runX (execute ast) (step_pre s) = Some (inl RETIRE_SUCCESS, s1) ->
  agree ctrl cfg (regs s1) ->
  run (try_step 0 false) s = Some (false, step_post s1).
Proof.
  intros Hdec Hrvc Hexec Hinv1.
  destruct (fetch_spec base size s Hreg Hinv Hpma Hal Hin Hrvc) as (w & Hf & Hw).
  eapply run_try_step_retire; eauto.
Qed.

End SailStep.
