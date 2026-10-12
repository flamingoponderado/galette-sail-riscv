(** * Memory accesses of the Sail model

    Instruction fetch, loads and stores, evaluated symbolically for an
    address inside the RAM region of [pma_regions], with the access
    aligned to its width. *)

From stdpp Require Import base bitvector.definitions.
From SailStdpp Require Import Base ConcurrencyInterfaceV2.
From Riscv Require Import rv64d_types rv64d.
From GaletteSail Require Export Step Bytes.
From Stdlib Require Import Lia.
Import ListNotations.

Local Open Scope Z_scope.

(** The RAM region [[base, base + size)] fits in the address space and
    avoids the memory-mapped devices of the Sail platform: the CLINT
    [[0x2000000, 0x200C000)] and the signature device
    [[0xC000000, 0xC000020)]. *)
Definition region_ok (base size : mword 64) : Prop :=
  bv_unsigned base + bv_unsigned size <= 2 ^ 64 /\
  (bv_unsigned base + bv_unsigned size <= 0x2000000 \/ 0x200C000 <= bv_unsigned base) /\
  (bv_unsigned base + bv_unsigned size <= 0xC000000 \/ 0xC000020 <= bv_unsigned base).

(** The [width] bytes at [a] lie in the region. *)
Definition in_region (base size a : mword 64) (width : Z) : Prop :=
  bv_unsigned base <= bv_unsigned a /\ bv_unsigned a + width <= bv_unsigned base + bv_unsigned size.

Lemma matching_pma_region_in base size a width :
  region_ok base size -> in_region base size a width -> 0 < width < 2 ^ 64 ->
  matching_pma_region [ram_region base size] (Physaddr a) width = Some (ram_region base size).
Proof.
  intros (H1 & _) (H2 & H3) H4. unfold matching_pma_region, matching_pma_region_bits_range.
  cbn [ram_region PMA_Region_base PMA_Region_size].
  replace (range_subset _ _ base size) with true; [reflexivity|]. symmetry. bsolve.
Qed.

Ltac ev_case_pma :=
  match goal with
  | |- context [matching_pma_region [ram_region ?b ?sz] (Physaddr ?x) ?w] =>
      rewrite (matching_pma_region_in b sz x w);
      [ cbv iota | assumption | unfold in_region in *; zsolve | lia ]
  end.

(** Simplify the address of a memory request to the term it was built from. *)
Ltac simpl_req :=
  repeat match goal with
  | |- context [req_addr ?R] =>
      let R' := eval cbn in (req_addr R) in change (req_addr R) with R'
  | |- context [Interface.MemReq.size ?R] =>
      let R' := eval cbn in (Interface.MemReq.size R) in change (Interface.MemReq.size R) with R'
  end;
  repeat match goal with
  | |- context [f_bitvector_64 ?rf ?r] => change (f_bitvector_64 rf r) with (rd rf (R_bitvector_64 r))
  end.

Section Fetch.

Variables (base size : mword 64) (s : SailState).
Hypothesis Hreg : region_ok base size.
Hypothesis Hinv : agree ctrl cfg (regs s).
Hypothesis Hpma : rd (regs s) pma_regions = [ram_region base size].
Hypothesis Hal : bv_unsigned (rd (regs s) PC) mod 4 = 0.
Hypothesis Hin : in_region base size (rd (regs s) PC) 4.

Hypothesis Hrvc : mem_val (mem s) (rd (regs s) PC) 4 mod 4 = 3.

Lemma fetch_spec : exists w,
  runX (fetch tt) s = Some (inl (F_Base w), s) /\ bv_unsigned w = mem_val (mem s) (rd (regs s) PC) 4.
Proof.
  Ltac ev_val_hook ::= ev_val_agree.
  Ltac ev_hook ::= ev_ctrl.
  Ltac ev_case ::= ev_case_pma.
  pose proof Hreg as (Hr1 & Hr2 & Hr3). pose proof Hin as (Hi1 & Hi2).
  eexists; split.
  - ev. simpl_req.
    match goal with
    | |- context [add_vec_int (zero_extend' 64 ?x) (0 * 4)] =>
        replace (add_vec_int (zero_extend' 64 x) (0 * 4)) with x by (apply bv_eq; zsolve)
    end.
    match goal with
    | |- context [isRVC ?h] => replace (isRVC h) with false by (symmetry; bsolve)
    end.
    cbv iota. apply cr_inl.
  - zsolve.
Qed.

End Fetch.
