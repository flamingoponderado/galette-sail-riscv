(** * A symbolic evaluator for [runX]

    The tactic [ev] proves goals [runX P s = ?r] by stepping through the
    monadic program [P] one operation at a time: [bind] and [try_catch]
    are split with the continuation-passing lemmas below, register reads
    and writes act on the state, conditionals on closed values are decided
    by computation, and other constants are unfolded at the head only.
    Nothing is normalised under binders, so the parts of [P] that are not
    executed are never reduced.  Calls for which a specification lemma is
    available are discharged by the hook [ev_hook]; branches on symbolic
    values by the hook [ev_case]. *)

From stdpp Require Import base bitvector.definitions.
From SailStdpp Require Import Base ConcurrencyInterfaceV2.
From Riscv Require Import rv64d_types.
From GaletteSail Require Export Sym BvSolve.

Section Lemmas.
Context {E : Type}.

Lemma ev_bind {A B} (m : iM E A) (k : A -> iM E B) s r0 r :
  runX m s = r0 -> bindres r0 k = r -> runX (Defs.bind m k) s = r.
Proof. intros <- <-; apply runX_bind. Qed.

Lemma ev_ibind {A B} (m : iM E A) (k : A -> iM E B) s r0 r :
  runX m s = r0 -> bindres r0 k = r -> runX (Interface.iMon_bind m k) s = r.
Proof. intros <- <-; apply runX_bind. Qed.

Lemma ev_bind0 {A} (m : iM E unit) (n : iM E A) s r0 r :
  runX m s = r0 -> bindres r0 (fun _ => n) = r -> runX (Defs.bind0 m n) s = r.
Proof. intros <- <-; apply runX_bind. Qed.

Lemma ev_try {E2 A} (m : iM E A) (h : E -> iM E2 A) s r0 r :
  runX m s = r0 -> catchres r0 h = r -> runX (Defs.try_catch m h) s = r.
Proof. intros <- <-; apply runX_try_catch. Qed.

Lemma ev_ret {A} (a : A) s : runX (Interface.Ret a : iM E A) s = Some (inl a, s).
Proof. reflexivity. Qed.

Lemma ev_read {A} (r : register) a (k : _ -> iM E A) s v r0 :
  rd (regs s) r = v -> runX (k v) s = r0 ->
  runX (Interface.Next (Interface.RegRead r a) k) s = r0.
Proof. intros <- <-; reflexivity. Qed.

Lemma ev_write {A} (r : register) a v (k : unit -> iM E A) s r0 :
  runX (k tt) (mkSailState (upd_reg (regs s) r v) (mem s)) = r0 ->
  runX (Interface.Next (Interface.RegWrite r a v) k) s = r0.
Proof. intros <-; reflexivity. Qed.

Lemma ev_throw {A T} (e : E) (k : T -> iM E A) s :
  runX (Interface.Next (Interface.ExtraOutcome e) k) s = Some (inr e, s).
Proof. reflexivity. Qed.

Lemma ev_memread {A} mr (k : _ -> iM E A) s r0 :
  runX (k (inl (mem_read_val (mem s) (req_addr mr) (Interface.MemReq.size mr),
               bv_0 (Interface.MemReq.num_tag mr)))) s = r0 ->
  runX (Interface.Next (Interface.MemRead mr) k) s = r0.
Proof. intros <-; reflexivity. Qed.

Lemma ev_memwrite {A} mr v t (k : _ -> iM E A) s r0 :
  runX (k (inl None))
    (mkSailState (regs s) (mem_write_val (mem s) (req_addr mr) (Interface.MemReq.size mr) v)) = r0 ->
  runX (Interface.Next (Interface.MemWrite mr v t) k) s = r0.
Proof. intros <-; reflexivity. Qed.

Lemma br_inl {A B} (a a' : A) s (k : A -> iM E B) r :
  a = a' -> runX (k a') s = r -> bindres (Some (inl a, s)) k = r.
Proof. intros -> <-; reflexivity. Qed.

Lemma br_inr {A B} (e : E) s (k : A -> iM E B) :
  bindres (Some (inr e, s)) k = Some (inr e, s).
Proof. reflexivity. Qed.

Lemma cr_inl {E2 A} (a : A) s (h : E -> iM E2 A) :
  catchres (Some (inl a, s)) h = Some (inl a, s).
Proof. reflexivity. Qed.

Lemma cr_inr {E2 A} (e : E) s (h : E -> iM E2 A) r :
  runX (h e) s = r -> catchres (Some (inr e, s)) h = r.
Proof. intros <-; reflexivity. Qed.

End Lemmas.

(** Head symbol of an application. *)
Ltac head_of t :=
  lazymatch t with
  | ?f _ => head_of f
  | _ => t
  end.

(** A term without free variables and without evars. *)
Ltac closed t :=
  match t with
  | context [?x] => is_var x; fail 1
  | context [?x] => is_evar x; fail 1
  | _ => idtac
  end.

(** Hooks, to be redefined (with [Ltac ev_hook ::= ...]) by clients. *)
Ltac ev_hook := fail.
Ltac ev_case b := fail.
Ltac ev_val_hook := fail.
(** Simplify a register read [rd (regs s) r] (goal [rd (regs s) r = ?v]). *)
Ltac ev_val :=
  repeat first [ progress cbn [regs mem]
               | rewrite rd_upd_same
               | rewrite rd_upd_other by discriminate
               | ev_val_hook
               | match goal with H : rd (regs ?s) ?r = _ |- rd (regs ?s) ?r = _ => rewrite H end ];
  lazymatch goal with
  | |- ?l = _ => first [ closed l; let l' := eval vm_compute in l in change l with l' | idtac ]
  end;
  reflexivity.

(** Decide the scrutinee [b] of a match by computation, if it is closed. *)
Ltac ev_compute_scrutinee b :=
  let b' := eval vm_compute in b in
  change b with b'.

Ltac ev_unfold P :=
  let f := head_of P in
  is_const f;
  let P' := eval cbv delta [f] beta iota zeta in P in
  change P with P'.

(** A match whose scrutinee reduces to a constructor by weak-head
    reduction, although it is not closed. *)
Ltac ev_hnf_match P :=
  let P' := eval hnf in P in
  lazymatch P' with
  | match _ with _ => _ end => fail
  | _ => change P with P'
  end.

(** Rewrite the scrutinee with a hypothesis [l = r] whose left-hand side
    occurs in it. *)
Ltac ev_case_hyp b :=
  match goal with
  | H : ?l = ?r |- _ =>
      lazymatch b with context [l] => idtac end;
      rewrite H
  end.

(** A boolean scrutinee decided by [bsolve]. *)
Ltac ev_case_bool b :=
  lazymatch type of b with
  | bool =>
      let Eb := fresh "Eb" in
      first [ assert (Eb : b = false) by bsolve
            | assert (Eb : b = true) by bsolve ];
      rewrite Eb; clear Eb; cbv iota
  end.

(** A scrutinee containing a conditional [if c then _ else _] whose
    condition [c] is decided by [bsolve]. *)
Ltac ev_case_inner_if b :=
  match b with
  | context [if ?c then _ else _] =>
      let Eb := fresh "Eb" in
      first [ assert (Eb : c = false) by bsolve
            | assert (Eb : c = true) by bsolve ];
      rewrite Eb; clear Eb; cbv iota
  end.

Ltac ev_hnf P :=
  let P' := eval hnf in P in
  change P with P'.

Ltac ev_step :=
  lazymatch goal with
  | |- runX ?P ?s = _ =>
      lazymatch P with
      | Defs.bind ?m ?k => eapply ev_bind
      | Interface.iMon_bind ?m ?k => eapply ev_ibind
      | Defs.bind0 ?m ?n => eapply ev_bind0
      | Defs.try_catch ?m ?h => eapply ev_try
      | Interface.Ret ?a => apply ev_ret
      | Interface.Next (Interface.RegRead _ _) _ => eapply ev_read; [ev_val | cbv beta]
      | Interface.Next (Interface.RegWrite _ _ _) _ => eapply ev_write; cbv beta
      | Interface.Next (Interface.ExtraOutcome _) _ => apply ev_throw
      | Interface.Next (Interface.MemRead _) _ => eapply ev_memread; cbv beta
      | Interface.Next (Interface.MemWrite _ _ _) _ => eapply ev_memwrite; cbv beta
      | Interface.Next _ _ => let P' := eval hnf in (runX P s) in change (runX P s) with P'; cbv beta
      | (fun _ => _) _ => cbv beta
      | (let _ := _ in _) => cbv zeta
      | match ?b with _ => _ end =>
          first [ (closed b; ev_compute_scrutinee b; cbv iota)
                | ev_case_bool b
                | ev_case b
                | ev_case_inner_if b
                | ev_case_hyp b
                | ev_hnf_match P ]
      | _ => first [ ev_hook | ev_unfold P | ev_hnf P ]
      end
  | |- bindres (Some (inl _, _)) _ = _ => eapply br_inl; [ev_val | cbv beta]
  | |- bindres (Some (inr _, _)) _ = _ => apply br_inr
  | |- catchres (Some (inl _, _)) _ = _ => apply cr_inl
  | |- catchres (Some (inr _, _)) _ = _ => eapply cr_inr; cbv beta
  | |- Some _ = _ => reflexivity
  end.

(** Run [ev_step] on the first goal until it is solved or stuck. *)
Ltac ev := repeat ev_step.

Lemma ev_ret_eq {E A} (a a' : A) s : a = a' -> runX (Interface.Ret a : iM E A) s = Some (inl a', s).
Proof. intros ->; reflexivity. Qed.
