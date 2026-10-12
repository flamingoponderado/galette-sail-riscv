(** * The reference configuration of the Sail machine

    The Sail model has hundreds of registers beyond the program-visible
    state.  The simulation fixes the values of the ones that [try_step]
    reads ("control registers") to those of a reference register file
    [cfg], and leaves the data registers ([PC], [nextPC], [x1]..[x31],
    [minstret]) and the memory free.

    The settings that matter (see README "Differences"):
    - [cur_privilege = Machine], [hart_state = HART_ACTIVE]:
      machine mode, no address translation, PMP checks only apply to
      locked entries;
    - [misa]: RV64 ([MXL = 2]) with I, M and C.  C is enabled so that, as
      in L3, jumps and branches to 2-byte aligned targets do not trap
      (L3 only checks bit 0 of a jump target); every instruction the
      encoder emits is a 32-bit one, so C does not change fetch;
      F, D, A, V, S, U, H are off;
    - [mstatus = 0]: MIE = 0 (no interrupt is taken in M-mode), MPRV = 0
      (loads/stores use M-mode), FS = VS = 0;
    - [mie = 0], [mip = 0], [mtimecmp = 2^64 - 1] (no timer interrupt
      pending), no PMP entry enabled ([pmpcfg_n = 0]);
    - [mcountinhibit = 0], [minstretcfg = 0]: [minstret] counts every
      retired instruction, which is how [sail_next] recognises a retired
      step;
    - [minstret_increment = true], the value [try_step] writes in
      machine mode;
    - [htif_tohost_base = None]: no HTIF device;
    - triggers: all disabled (default).

    The PMA regions ([pma_regions]) are not part of [cfg]: they are a
    parameter of the simulation ([SailInv] in [Relation.v]). *)

From stdpp Require Import base bitvector.definitions.
From SailStdpp Require Import Base ConcurrencyInterfaceV2.
From Riscv Require Import rv64d_types rv64d.
From GaletteSail Require Export Eval.
Import ListNotations.

Definition w64 (z : Z) : mword 64 := Z_to_bv 64 z.

(** RV64, I, M, C. *)
Definition misa0 : mword 64 := w64 (2 * 2^62 + 2^12 + 2^8 + 2^2).

Definition cfg : regfile :=
  upd_reg (upd_reg (upd_reg (upd_reg (upd_reg (upd_reg default_regfile
    (R_Privilege cur_privilege) Machine)
    (R_HartState hart_state) (HART_ACTIVE tt))
    (R_bitvector_64 misa) misa0)
    (R_bitvector_64 mtimecmp) (w64 (2^64 - 1)))
    (R_bool minstret_increment) true)
    (R_option_bitvector_64 htif_tohost_base) None.

(** The data registers: program counter, next PC, integer registers, and
    the retired-instruction counter. *)
Definition is_data (r : register) : bool :=
  match r with
  | R_bitvector_64 r' =>
      match r' with
      | PC | nextPC | minstret | x1 | x2 | x3 | x4 | x5 | x6 | x7 | x8 | x9 | x10 | x11 | x12
      | x13 | x14 | x15 | x16 | x17 | x18 | x19 | x20 | x21 | x22 | x23 | x24 | x25 | x26
      | x27 | x28 | x29 | x30 | x31 => true
      | _ => false
      end
  | _ => false
  end.

(** Control registers: everything else, except the PMA regions. *)
Definition ctrl (r : register) : bool :=
  match r with
  | R_list_PMA_Region pma_regions => false
  | _ => negb (is_data r)
  end.

(** ** Control-register invariance *)

Lemma agree_upd_data rf r v :
  agree ctrl cfg rf -> ctrl r = false -> agree ctrl cfg (upd_reg rf r v).
Proof.
  intros H Hr r' Hr'. rewrite rd_upd_other; [apply H, Hr'|congruence].
Qed.

Lemma agree_upd_same rf r v :
  agree ctrl cfg rf -> v = rd rf r -> agree ctrl cfg (upd_reg rf r v).
Proof. intros H ->. rewrite upd_reg_rd. exact H. Qed.

Lemma agree_upd_ctrl rf r v :
  agree ctrl cfg rf -> v = rd cfg r -> agree ctrl cfg (upd_reg rf r v).
Proof.
  intros H Hv r' Hr'. destruct (decide (r = r')) as [<-|Hne].
  - rewrite rd_upd_same. exact (eq_sym Hv).
  - rewrite rd_upd_other by exact Hne. apply H, Hr'.
Qed.

(** Prove [agree ctrl cfg (regs s)] for a state obtained by register
    writes from a state for which it is a hypothesis. *)
Ltac solve_agree_extra := fail.
Ltac solve_agree :=
  cbn [regs mem];
  solve [ repeat first
    [ assumption
    | apply agree_upd_data; [|reflexivity]
    | apply agree_upd_ctrl; [|vm_compute; reflexivity]
    | solve_agree_extra ] ].

(** Control-only computations: evaluate on [cfg] by computation, and
    transfer to the symbolic state with [runS_frame]. *)
Ltac ev_ctrl :=
  lazymatch goal with
  | |- runX ?P ?s = _ =>
      closed P;
      eapply (runS_frame ctrl P cfg); [vm_compute; reflexivity | solve_agree]
  end.

(** ** The memory region *)

(** Attributes of main memory (those of sail-riscv's default RAM region). *)
Definition ram_attrs : PMA :=
  {| PMA_mem_type := MainMemory; PMA_cacheable := true; PMA_coherent := true;
     PMA_executable := true; PMA_readable := true; PMA_writable := true;
     PMA_read_idempotent := true; PMA_write_idempotent := true;
     PMA_misaligned_exceptions :=
       {| PMAMisalignedExceptions_load_store := None; PMAMisalignedExceptions_vector := None;
          PMAMisalignedExceptions_amo := AccessFault; PMAMisalignedExceptions_lrsc := AccessFault |};
     PMA_atomic_support := AMOCASQ; PMA_reservability := RsrvEventual;
     PMA_supports_cbo_zero := true; PMA_supports_pte_read := true; PMA_supports_pte_write := true;
     PMA_misaligned_atomicity_granule_size_exp := 4;
     PMA_vector_misaligned_atomicity_granule_size_exp := 4 |}.

Definition ram_region (base size : mword 64) : PMA_Region :=
  {| PMA_Region_base := base; PMA_Region_size := size;
     PMA_Region_attributes := ram_attrs; PMA_Region_include_in_device_tree := true |}.
