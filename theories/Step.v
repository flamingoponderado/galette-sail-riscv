(** * Decomposition of [try_step]

    Under the control-register invariant, one [try_step] of an active hart
    is: fetch, decode, write [nextPC := PC + 4], execute, then (when the
    instruction retires) [PC := nextPC] and [minstret := minstret + 1].
    Interrupt dispatch, triggers, landing pads, counters and the other
    bookkeeping of [try_step] are evaluated by computation on the
    reference configuration [cfg] (see [ev_ctrl]) and change nothing. *)

From stdpp Require Import base bitvector.definitions.
From SailStdpp Require Import Base ConcurrencyInterfaceV2.
From Riscv Require Import rv64d_types rv64d.
From GaletteSail Require Export Gpr.
Import ListNotations.

(** The state after the epilogue of a retired step. *)
Definition step_post (s1 : SailState) : SailState :=
  mkSailState
    (upd_reg (upd_reg (regs s1) PC (rd (regs s1) nextPC)) minstret
       (add_vec_int (rd (regs s1) minstret) 1))
    (mem s1).

(** The state in which [execute] runs. *)
Definition step_pre (s : SailState) : SailState :=
  mkSailState (upd_reg (regs s) nextPC (add_vec_int (rd (regs s) PC) 4)) (mem s).

Ltac ev_val_agree :=
  match goal with
  | H : agree ctrl cfg (regs ?s) |- context [rd (regs ?s) ?r] => rewrite <- (H r eq_refl)
  end.

Section TryStep.

Variables (s : SailState) (w : mword 32) (ast : instruction) (s1 : SailState).
Hypothesis Hinv : agree ctrl cfg (regs s).
Hypothesis Hfetch : runX (fetch tt) s = Some (inl (F_Base w), s).
Hypothesis Hdecode : runX (ext_decode w) s = Some (inl ast, s).
Hypothesis Hexec : runX (execute ast) (step_pre s) = Some (inl RETIRE_SUCCESS, s1).
Hypothesis Hinv1 : agree ctrl cfg (regs s1).

Theorem try_step_retire : runX (try_step 0 false) s = Some (inl false, step_post s1).
Proof.
  Ltac ev_val_hook ::= ev_val_agree.
  Ltac ev_hook ::= first [ ev_ctrl | apply Hfetch | apply Hdecode | apply Hexec ].
  ev.
Qed.

Corollary run_try_step_retire : run (try_step 0 false) s = Some (false, step_post s1).
Proof. rewrite run_runX, try_step_retire. reflexivity. Qed.

End TryStep.
