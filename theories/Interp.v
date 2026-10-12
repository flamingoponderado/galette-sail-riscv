(** * Sequential interpreter for the Sail RISC-V model

    The Rocq output of Sail describes each instruction as an interaction tree
    ([Interface.iMon]) of concurrency-interface-V2 outcomes. This file fixes
    a sequential reading of those outcomes against a concrete machine state:
    - register reads and writes act on a total register file;
    - memory reads and writes act on a total byte memory, little-endian;
      Sail's [bytes_of_bv] puts byte [i] at bits [8i .. 8i+7];
    - announcements, barriers, cache/TLB operations and messages are no-ops;
    - [Choose], [Discard], [GenericFail] and uncaught Sail exceptions
      ([ExtraOutcome]) make the run fail ([None]).

    This interpreter is part of the trusted base of the comparison. *)

From stdpp Require Import base bitvector.definitions.
From SailStdpp Require Import Base ConcurrencyInterfaceV2.
From Riscv Require Import rv64d_types.
From GaletteSail Require Export Regfile.
Import ListNotations.

Record SailState : Type := mkSailState {
  regs : regfile;
  mem : bv 64 -> bv 8;
}.

(** The bytes [mem (a + i)] for [i < n], least significant first. *)
Definition read_bytes (m : bv 64 -> bv 8) (a : bv 64) (n : N) : list (bv 8) :=
  map (fun i => m (bv_add a (Z_to_bv 64 (Z.of_nat i)))) (seq 0 (N.to_nat n)).

Definition mem_read_val (m : bv 64 -> bv 8) (a : bv 64) (n : N) : bv (8 * n) :=
  Z_to_bv (8 * n) (little_endian_to_bv 8 (read_bytes m a n)).

Definition upd_byte (m : bv 64 -> bv 8) (a : bv 64) (b : bv 8) : bv 64 -> bv 8 :=
  fun x => if decide (x = a) then b else m x.

(** Write [bs] at [a], [a + 1], ..., least significant first. *)
Fixpoint write_bytes (m : bv 64 -> bv 8) (a : bv 64) (bs : list (bv 8)) : bv 64 -> bv 8 :=
  match bs with
  | [] => m
  | b :: bs' => write_bytes (upd_byte m a b) (bv_add a (Z_to_bv 64 1)) bs'
  end.

Definition mem_write_val (m : bv 64 -> bv 8) (a : bv 64) (n : N) (v : bv (8 * n)) : bv 64 -> bv 8 :=
  write_bytes m a (bv_to_little_endian (Z.of_N n) 8 (bv_unsigned v)).

Section Run.

(** The address of a request, as a 64-bit vector. *)
Definition req_addr (mr : Interface.MemReq.t) : bv 64 := Interface.MemReq.address mr.

Fixpoint run {A : Type} (m : M A) (s : SailState) : option (A * SailState) :=
  match m with
  | Interface.Ret a => Some (a, s)
  | @Interface.Next _ _ T oc k =>
      match oc in Interface.outcome _ T' return (T' -> M A) -> option (A * SailState) with
      | Interface.RegRead r _ => fun k => run (k (rd (regs s) r)) s
      | Interface.RegWrite r _ v => fun k =>
          run (k tt) (mkSailState (upd_reg (regs s) r v) (mem s))
      | Interface.MemRead mr => fun k =>
          run (k (inl (mem_read_val (mem s) (req_addr mr) (Interface.MemReq.size mr),
                       bv_0 (Interface.MemReq.num_tag mr)))) s
      | Interface.MemWrite mr v _ => fun k =>
          run (k (inl None))
              (mkSailState (regs s) (mem_write_val (mem s) (req_addr mr) (Interface.MemReq.size mr) v))
      | Interface.MemAddressAnnounce _ => fun k => run (k tt) s
      | Interface.InstrAnnounce _ => fun k => run (k tt) s
      | Interface.BranchAnnounce _ _ => fun k => run (k tt) s
      | Interface.Barrier _ => fun k => run (k tt) s
      | Interface.CacheOp _ => fun k => run (k tt) s
      | Interface.TlbOp _ => fun k => run (k tt) s
      | Interface.TakeException _ => fun k => run (k tt) s
      | Interface.ReturnException => fun k => run (k tt) s
      | Interface.TranslationStart _ => fun k => run (k tt) s
      | Interface.TranslationEnd _ => fun k => run (k tt) s
      | Interface.CycleCount => fun k => run (k tt) s
      | Interface.Message _ => fun k => run (k tt) s
      | _ => fun _ => None
      end k
  end.

End Run.
