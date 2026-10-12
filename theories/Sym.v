(** * Symbolic evaluation of the Sail monad

    [runX] is [Interp.run] extended to report uncaught Sail exceptions
    ([ExtraOutcome], used both for Sail exceptions and for early returns
    inside [catch_early_return]) instead of failing.  It is defined for an
    arbitrary exception type, so it also covers the [MR] (early-return)
    computations that occur inside [catch_early_return].

    This file provides:
    - [run_runX]: [run] is [runX] with exceptions turned into failure;
    - equations for [runX] on [bind], [try_catch], register accesses, ...;
    - facts about the register file ([rd]/[upd_reg]);
    - a frame theorem ([runW_frame]): a computation that only touches a set
      [C] of registers, and no memory, behaves the same on every state that
      agrees on [C].  Its hypothesis is checked by computation on a concrete
      reference register file, which lets us evaluate the large
      control-only parts of [try_step] (interrupts, triggers, counters)
      without any symbolic reduction. *)

From stdpp Require Import base bitvector.definitions.
From SailStdpp Require Import Base ConcurrencyInterfaceV2.
From Riscv Require Import rv64d_types.
From GaletteSail Require Export Interp.
From Stdlib Require Import FunctionalExtensionality.
Import ListNotations.

(** ** The extended interpreter *)

Definition iM (E A : Type) := Interface.iMon (fun _ => E) A.

Fixpoint runX {E A : Type} (m : iM E A) (s : SailState) : option ((A + E) * SailState) :=
  match m with
  | Interface.Ret a => Some (inl a, s)
  | @Interface.Next _ _ T oc k =>
      match oc in Interface.outcome _ T' return (T' -> iM E A) -> option ((A + E) * SailState) with
      | Interface.RegRead r _ => fun k => runX (k (rd (regs s) r)) s
      | Interface.RegWrite r _ v => fun k =>
          runX (k tt) (mkSailState (upd_reg (regs s) r v) (mem s))
      | Interface.MemRead mr => fun k =>
          runX (k (inl (mem_read_val (mem s) (req_addr mr) (Interface.MemReq.size mr),
                       bv_0 (Interface.MemReq.num_tag mr)))) s
      | Interface.MemWrite mr v _ => fun k =>
          runX (k (inl None))
              (mkSailState (regs s) (mem_write_val (mem s) (req_addr mr) (Interface.MemReq.size mr) v))
      | Interface.ExtraOutcome e => fun _ => Some (inr e, s)
      | Interface.MemAddressAnnounce _ => fun k => runX (k tt) s
      | Interface.InstrAnnounce _ => fun k => runX (k tt) s
      | Interface.BranchAnnounce _ _ => fun k => runX (k tt) s
      | Interface.Barrier _ => fun k => runX (k tt) s
      | Interface.CacheOp _ => fun k => runX (k tt) s
      | Interface.TlbOp _ => fun k => runX (k tt) s
      | Interface.TakeException _ => fun k => runX (k tt) s
      | Interface.ReturnException => fun k => runX (k tt) s
      | Interface.TranslationStart _ => fun k => runX (k tt) s
      | Interface.TranslationEnd _ => fun k => runX (k tt) s
      | Interface.CycleCount => fun k => runX (k tt) s
      | Interface.Message _ => fun k => runX (k tt) s
      | _ => fun _ => None
      end k
  end.

(** The result of running the continuation of a [bind]. *)
Definition bindres {E A B} (r : option ((A + E) * SailState)) (k : A -> iM E B)
  : option ((B + E) * SailState) :=
  match r with
  | Some (inl a, s') => runX (k a) s'
  | Some (inr e, s') => Some (inr e, s')
  | None => None
  end.

Definition catchres {E1 E2 A} (r : option ((A + E1) * SailState)) (h : E1 -> iM E2 A)
  : option ((A + E2) * SailState) :=
  match r with
  | Some (inl a, s') => Some (inl a, s')
  | Some (inr e, s') => runX (h e) s'
  | None => None
  end.

Definition okres {A E} (r : option ((A + E) * SailState)) : option (A * SailState) :=
  match r with
  | Some (inl a, s') => Some (a, s')
  | _ => None
  end.

Lemma run_runX {A} (m : M A) s : run m s = okres (runX m s).
Proof.
  revert s; induction m as [a|T oc k IH]; intros s; [reflexivity|].
  destruct oc; cbn; try reflexivity; apply IH.
Qed.

Lemma runX_bind {E A B} (m : iM E A) (k : A -> iM E B) s :
  runX (Defs.bind m k) s = bindres (runX m s) k.
Proof.
  revert s; induction m as [a|T oc k' IH]; intros s; [reflexivity|].
  destruct oc; cbn; try reflexivity; apply IH.
Qed.

Lemma runX_bind0 {E A} (m : iM E unit) (n : iM E A) s :
  runX (Defs.bind0 m n) s = bindres (runX m s) (fun _ => n).
Proof. apply runX_bind. Qed.

Lemma runX_try_catch {E1 E2 A} (m : iM E1 A) (h : E1 -> iM E2 A) s :
  runX (Defs.try_catch m h) s = catchres (runX m s) h.
Proof.
  revert s; induction m as [a|T oc k' IH]; intros s; [reflexivity|].
  destruct oc; cbn; try reflexivity; apply IH.
Qed.

Lemma runX_ret {E A} (a : A) s : runX (Interface.Ret a : iM E A) s = Some (inl a, s).
Proof. reflexivity. Qed.

Lemma runX_read_reg {E} (r : register) s :
  runX (Defs.read_reg r : iM E _) s = Some (inl (rd (regs s) r), s).
Proof. reflexivity. Qed.

Lemma runX_write_reg {E} (r : register) v s :
  runX (Defs.write_reg r v : iM E unit) s =
  Some (inl tt, mkSailState (upd_reg (regs s) r v) (mem s)).
Proof. reflexivity. Qed.

Lemma runX_throw {E A} (e : E) s : runX (Defs.throw e : iM E A) s = Some (inr e, s).
Proof. reflexivity. Qed.

(** ** Register file facts *)

Lemma rd_upd_same rf r v : rd (upd_reg rf r v) r = v.
Proof. destruct r; cbn; rewrite decide_True by reflexivity; reflexivity. Qed.

Lemma rd_upd_other rf r r' v : r <> r' -> rd (upd_reg rf r v) r' = rd rf r'.
Proof.
  intros H; destruct r, r'; cbn; try reflexivity;
    rewrite decide_False by congruence; reflexivity.
Qed.

Lemma regfile_ext rf1 rf2 : (forall r, rd rf1 r = rd rf2 r) -> rf1 = rf2.
Proof.
  intros H; destruct rf1, rf2; cbn in *.
  f_equal; apply functional_extensionality; intros n;
    match goal with
    | n : register_HartState |- _ => apply (H (R_HartState n))
    | n : register_Privilege |- _ => apply (H (R_Privilege n))
    | n : register_bitvector_1 |- _ => apply (H (R_bitvector_1 n))
    | n : register_bitvector_128 |- _ => apply (H (R_bitvector_128 n))
    | n : register_bitvector_192 |- _ => apply (H (R_bitvector_192 n))
    | n : register_bitvector_3 |- _ => apply (H (R_bitvector_3 n))
    | n : register_bitvector_32 |- _ => apply (H (R_bitvector_32 n))
    | n : register_bitvector_320 |- _ => apply (H (R_bitvector_320 n))
    | n : register_bitvector_4 |- _ => apply (H (R_bitvector_4 n))
    | n : register_bitvector_5 |- _ => apply (H (R_bitvector_5 n))
    | n : register_bitvector_64 |- _ => apply (H (R_bitvector_64 n))
    | n : register_bitvector_704 |- _ => apply (H (R_bitvector_704 n))
    | n : register_bitvector_exp_8 |- _ => apply (H (R_bitvector_exp_8 n))
    | n : register_bool |- _ => apply (H (R_bool n))
    | n : register_list_PMA_Region |- _ => apply (H (R_list_PMA_Region n))
    | n : register_option_bitvector_64 |- _ => apply (H (R_option_bitvector_64 n))
    | n : register_option_tuple__range_0_15_tdata |- _ => apply (H (R_option_tuple__range_0_15_tdata n))
    | n : register_option_tuple__range_3_31_event_csr |- _ => apply (H (R_option_tuple__range_3_31_event_csr n))
    | n : register_vector_16_Trigger |- _ => apply (H (R_vector_16_Trigger n))
    | n : register_vector_32_bitvector_64 |- _ => apply (H (R_vector_32_bitvector_64 n))
    | n : register_vector_64_bitvector_64 |- _ => apply (H (R_vector_64_bitvector_64 n))
    | n : register_vector_64_bitvector_8 |- _ => apply (H (R_vector_64_bitvector_8 n))
    | n : register_vector_64_option_TLB_Entry |- _ => apply (H (R_vector_64_option_TLB_Entry n))
    end.
Qed.

Lemma upd_reg_rd rf r : upd_reg rf r (rd rf r) = rf.
Proof.
  apply regfile_ext; intros r'.
  destruct (decide (r = r')) as [<-|Hne].
  - apply rd_upd_same.
  - apply rd_upd_other, Hne.
Qed.

(** ** Frame theorem for control-only computations *)

(** [runW C m rf]: run [m] on the register file [rf], failing on memory
    accesses and on accesses to registers outside [C]. *)
Fixpoint runW {E A : Type} (C : register -> bool) (m : iM E A) (rf : regfile) : option ((A + E) * regfile) :=
  match m with
  | Interface.Ret a => Some (inl a, rf)
  | @Interface.Next _ _ T oc k =>
      match oc in Interface.outcome _ T' return (T' -> iM E A) -> option ((A + E) * regfile) with
      | Interface.RegRead r _ => fun k => if C r then runW C (k (rd rf r)) rf else None
      | Interface.RegWrite r _ v => fun k => if C r then runW C (k tt) (upd_reg rf r v) else None
      | Interface.ExtraOutcome e => fun _ => Some (inr e, rf)
      | Interface.MemAddressAnnounce _ => fun k => runW C (k tt) rf
      | Interface.InstrAnnounce _ => fun k => runW C (k tt) rf
      | Interface.BranchAnnounce _ _ => fun k => runW C (k tt) rf
      | Interface.Barrier _ => fun k => runW C (k tt) rf
      | Interface.CacheOp _ => fun k => runW C (k tt) rf
      | Interface.TlbOp _ => fun k => runW C (k tt) rf
      | Interface.TakeException _ => fun k => runW C (k tt) rf
      | Interface.ReturnException => fun k => runW C (k tt) rf
      | Interface.TranslationStart _ => fun k => runW C (k tt) rf
      | Interface.TranslationEnd _ => fun k => runW C (k tt) rf
      | Interface.CycleCount => fun k => runW C (k tt) rf
      | Interface.Message _ => fun k => runW C (k tt) rf
      | _ => fun _ => None
      end k
  end.

Definition agree (C : register -> bool) (rf1 rf2 : regfile) : Prop :=
  forall r, C r = true -> rd rf1 r = rd rf2 r.

(** The register file obtained from [rf2] by copying the [C] registers of [rf1]. *)
Definition frame_of (C : register -> bool) (rf1 rf2 : regfile) : Prop :=
  (forall r, C r = true -> rd rf2 r = rd rf1 r).

Theorem runW_frame {E A} (C : register -> bool) (m : iM E A) rf1 rf1' res rf2 mm :
  runW C m rf1 = Some (res, rf1') ->
  agree C rf1 rf2 ->
  exists rf2', runX m (mkSailState rf2 mm) = Some (res, mkSailState rf2' mm) /\
    agree C rf1' rf2' /\ (forall r, C r = false -> rd rf2' r = rd rf2 r).
Proof.
  revert rf1 rf2; induction m as [a|T oc k IH]; intros rf1 rf2 Hw Hag.
  - cbn in Hw. inversion Hw; subst. exists rf2. split; [reflexivity|]. split; [exact Hag|]. reflexivity.
  - destruct oc; cbn in Hw |- *; try discriminate;
      try (eapply IH; [exact Hw|exact Hag]).
    + (* RegRead *)
      destruct (C reg) eqn:Hc; [|discriminate].
      rewrite <- (Hag reg Hc). eapply IH; [exact Hw|exact Hag].
    + (* RegWrite *)
      destruct (C reg) eqn:Hc; [|discriminate].
      destruct (IH tt _ (upd_reg rf2 reg regval) Hw) as (rf2' & H1 & H2 & H3).
      { intros r Hr. destruct (decide (reg = r)) as [<-|Hne].
        - rewrite !rd_upd_same; reflexivity.
        - rewrite !rd_upd_other by exact Hne. apply Hag, Hr. }
      exists rf2'. split; [exact H1|]. split; [exact H2|].
      intros r Hr. rewrite H3 by exact Hr. apply rd_upd_other. congruence.
    + (* ExtraOutcome *)
      inversion Hw; subst. exists rf2. split; [reflexivity|]. split; [exact Hag|]. reflexivity.
Qed.

(** The common use: [m] restores every [C] register of the reference file
    [rf1] it writes (or writes the value already there), so the state is
    unchanged. *)
Corollary runW_frame_same {E A} (C : register -> bool) (m : iM E A) rf1 res rf2 mm :
  runW C m rf1 = Some (res, rf1) ->
  agree C rf1 rf2 ->
  runX m (mkSailState rf2 mm) = Some (res, mkSailState rf2 mm).
Proof.
  intros Hw Hag. destruct (runW_frame C m rf1 rf1 res rf2 mm Hw Hag) as (rf2' & H1 & H2 & H3).
  rewrite H1. f_equal. f_equal. f_equal. apply regfile_ext. intros r.
  destruct (C r) eqn:Hc.
  - rewrite <- (H2 r Hc). apply Hag, Hc.
  - apply H3, Hc.
Qed.

(** A variant that only accepts writes of the value already present
    ("silent" writes); the register file then never changes, and the
    frame theorem concludes that the state is unchanged. *)
Fixpoint runS {E A : Type} (C : register -> bool) (m : iM E A) (rf : regfile) : option (A + E) :=
  match m with
  | Interface.Ret a => Some (inl a)
  | @Interface.Next _ _ T oc k =>
      match oc in Interface.outcome _ T' return (T' -> iM E A) -> option (A + E) with
      | Interface.RegRead r _ => fun k => if C r then runS C (k (rd rf r)) rf else None
      | Interface.RegWrite r _ v => fun k =>
          if C r && bool_decide (rd rf r = v) then runS C (k tt) rf else None
      | Interface.ExtraOutcome e => fun _ => Some (inr e)
      | Interface.MemAddressAnnounce _ => fun k => runS C (k tt) rf
      | Interface.InstrAnnounce _ => fun k => runS C (k tt) rf
      | Interface.BranchAnnounce _ _ => fun k => runS C (k tt) rf
      | Interface.Barrier _ => fun k => runS C (k tt) rf
      | Interface.CacheOp _ => fun k => runS C (k tt) rf
      | Interface.TlbOp _ => fun k => runS C (k tt) rf
      | Interface.TakeException _ => fun k => runS C (k tt) rf
      | Interface.ReturnException => fun k => runS C (k tt) rf
      | Interface.TranslationStart _ => fun k => runS C (k tt) rf
      | Interface.TranslationEnd _ => fun k => runS C (k tt) rf
      | Interface.CycleCount => fun k => runS C (k tt) rf
      | Interface.Message _ => fun k => runS C (k tt) rf
      | _ => fun _ => None
      end k
  end.

Theorem runS_frame {E A} (C : register -> bool) (m : iM E A) rf1 res s :
  runS C m rf1 = Some res ->
  agree C rf1 (regs s) ->
  runX m s = Some (res, s).
Proof.
  destruct s as [rf2 mm]; cbn [regs].
  revert rf2; induction m as [a|T oc k IH]; intros rf2 Hw Hag.
  - cbn in Hw. inversion Hw; subst. reflexivity.
  - destruct oc; cbn in Hw |- *; try discriminate; try (eapply IH; [exact Hw|exact Hag]).
    + destruct (C reg) eqn:Hc; [|discriminate].
      rewrite <- (Hag reg Hc). eapply IH; [exact Hw|exact Hag].
    + destruct (C reg) eqn:Hc; [|discriminate].
      destruct (bool_decide (rd rf1 reg = regval)) eqn:Hv; [|discriminate].
      apply bool_decide_eq_true in Hv. cbn in Hw.
      assert (E1 : upd_reg rf2 reg regval = rf2).
      { rewrite <- Hv, (Hag reg Hc). apply upd_reg_rd. }
      rewrite E1. eapply IH; [exact Hw|exact Hag].
    + inversion Hw; subst. reflexivity.
Qed.
