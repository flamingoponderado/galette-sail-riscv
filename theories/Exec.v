(** * Execution of the decoded instructions *)

From stdpp Require Import base bitvector.definitions.
From SailStdpp Require Import Base ConcurrencyInterfaceV2.
From Riscv Require Import rv64d_types rv64d.
From GaletteSail Require Export Mem.
From Stdlib Require Import Lia.
Import ListNotations.

Local Open Scope Z_scope.

Lemma exec_ADD (s : SailState) a b c :
  runX (execute (RTYPE (Regidx a, Regidx b, Regidx c, ADD))) s =
  Some (inl RETIRE_SUCCESS,
        mkSailState (set_gpr (regs s) (uint c) (add_vec (gpr (regs s) (uint b)) (gpr (regs s) (uint a)))) (mem s)).
Proof.
  ev.
Qed.
