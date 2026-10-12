(** * The Sail model as a Galette [asmProps.target]

    A [SailMachine] is a Sail state together with an [ok] flag, as in
    riscv-im-compare's [ZState].  [sail_next] runs one [try_step 0 false]
    with the sequential interpreter [run] and keeps [ok] only if the step
    retired an instruction normally:

    - [run] fails ([None]): a [Choose], [GenericFail] (Sail [assert]/[exit],
      internal errors), or an uncaught Sail exception;
    - [try_step] returns [true]: the hart entered a wait state (WFI, ...);
    - [minstret] did not advance by one: the step took a trap (an
      exception or an interrupt), or otherwise did not retire.

    In each of these cases the state is left unchanged and [ok] is
    cleared, so that Galette's evaluator stops with an error.  This mirrors
    L3, where [NextRISCV] returns [None] on any exception and the target's
    [riscv_ok] then fails.  Counting [minstret] relies on the configuration
    of [Config.v] ([mcountinhibit.IR = 0], [minstretcfg = 0]), which
    [SailInv] fixes; under it [minstret] counts exactly the retired
    instructions.  (An instruction that writes [minstret] itself, a CSR
    write, would be reported as not retired; Galette never emits CSR
    instructions.)

    [sail_ok] is [ok] and a 4-byte aligned PC, the counterpart of the
    [aligned 2 pc] conjunct of [riscv_ok].  Registers, PC and bytes are
    read through [bvw]; [x0] reads as [0]. *)

From stdpp Require Import base bitvector.definitions.
From SailStdpp Require Import Base ConcurrencyInterfaceV2.
From Riscv Require Import rv64d_types rv64d.
From GaletteSail Require Export Conv.
From Galette.HOL.src.n_bit Require alignment.
From Galette.HOL.examples.machine_code.hoare_triple Require set_sep.
From Galette.cakeml.compiler.encoders.asm Require asmProps.
From Galette.cakeml.compiler.encoders.riscv Require riscv_target.

Record SailMachine : Type := mkSM { sm_state : SailState; sm_ok : bool }.

(** The step retired one instruction. *)
Definition retired (s s' : SailState) : bool :=
  bool_decide (rd (regs s') minstret = add_vec_int (rd (regs s) minstret) 1).

Definition sail_next (m : SailMachine) : SailMachine :=
  match run (try_step 0 false) (sm_state m) with
  | Some (false, s') =>
      if retired (sm_state m) s' then mkSM s' (sm_ok m) else mkSM (sm_state m) false
  | _ => mkSM (sm_state m) false
  end.

Definition sail_pc (m : SailMachine) : W.word 64 := bvw (rd (regs (sm_state m)) PC).

Definition sail_reg (m : SailMachine) (n : N) : W.word 64 := sgpr (regs (sm_state m)) (W.n2w n).

Definition sail_byte (m : SailMachine) (a : W.word 64) : W.word 8 := bvw (mem (sm_state m) (wbv a)).

Definition sail_ok (m : SailMachine) : bool := sm_ok m && alignment.aligned 2 (sail_pc m).

Definition sail_proj (d : W.word 64 -> Prop) (m : SailMachine) :
    bool * W.word 64 * (N -> W.word 64) * (W.word 64 * W.word 8 -> Prop) :=
  (sm_ok m, sail_pc m, sail_reg m, set_sep.fun2set (sail_byte m, d)).

Definition sail_target :=
  asmProps.mk_target riscv_target.riscv_config sail_next sail_pc sail_reg
    (fun _ _ => W.n2w 0) sail_byte sail_ok sail_proj.
