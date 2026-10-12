From stdpp Require Import base bitvector.definitions.
From SailStdpp Require Import Base ConcurrencyInterfaceV2.
From Riscv Require Import rv64d_types rv64d.
From GaletteSail Require Import Interp.

Definition rf0 : regfile := default_regfile.
Definition w64 (z : Z) : mword 64 := Z_to_bv 64 z.
Definition rf1 : regfile :=
  upd_reg (upd_reg (upd_reg (upd_reg (upd_reg rf0
    (R_bitvector_64 PC) (w64 0x80000000))
    (R_bitvector_64 x1) (w64 5))
    (R_bitvector_64 x2) (w64 7))
    (R_Privilege cur_privilege) Machine)
    (R_HartState hart_state) (HART_ACTIVE tt).
Definition instr : list (bv 8) := [Z_to_bv 8 0xb3; Z_to_bv 8 0x81; Z_to_bv 8 0x20; Z_to_bv 8 0x00].
Definition m0 : bv 64 -> bv 8 := write_bytes (fun _ => bv_0 8) (Z_to_bv 64 0x80000000) instr.
Definition s0 := mkSailState rf1 m0.

Definition pc0 : mword 64 := w64 0x80000000.
(** Smoke tests of the interpreter (vm_compute): register read, decode of
    [add x3, x1, x2], execution of the decoded AST, and one full [try_step]
    (which traps here: the default register file configures no PMA region,
    so the fetch faults). *)
Example read_pc : (match run (Defs.read_reg PC : M (mword 64)) s0 with Some (v, _) => Some (bv_unsigned v) | None => None end) = Some 0x80000000.
Proof. vm_compute. reflexivity. Qed.
Example exec_add : (match run (execute (RTYPE (Regidx (Z_to_bv 5 2), Regidx (Z_to_bv 5 1), Regidx (Z_to_bv 5 3), ADD))) s0 with Some (_, s) => Some (bv_unsigned (rd (regs s) (R_bitvector_64 x3))) | None => None end) = Some 12.
Proof. vm_compute. reflexivity. Qed.
