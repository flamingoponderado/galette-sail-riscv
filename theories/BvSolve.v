(** * Deciding Sail boolean conditions on symbolic bit vectors

    [bsolve] proves goals [b = true] or [b = false], where [b] is a
    boolean computed by the Sail model from symbolic bit vectors (an
    address, an instruction word, register values), from hypotheses
    about the unsigned values of these bit vectors.  It unfolds the Sail
    operators to stdpp's [bv] operations, turns them into arithmetic on
    [Z] and calls [lia]. *)

From stdpp Require Import base bitvector.definitions bitvector.tactics.
From SailStdpp Require Import Base.
From Riscv Require Import rv64d_types rv64d.
From Stdlib Require Import Lia ZArith Bool.

Ltac Zify.zify_post_hook ::= Z.to_euclidean_division_equations.

Local Open Scope Z_scope.

Lemma uint_spec {n} (x : mword n) : uint x = bv_unsigned x.
Proof.
  unfold uint, SailStdpp.MachineWord.MachineWord.word_to_N. pose proof (bv_unsigned_in_range _ x). lia.
Qed.

Lemma eq_vec_spec {n} (x y : mword n) : eq_vec x y = bool_decide (bv_unsigned x = bv_unsigned y).
Proof.
  unfold eq_vec, SailStdpp.MachineWord.MachineWord.eqb. apply bool_decide_ext. split.
  - intros ->; reflexivity.
  - apply bv_eq.
Qed.

Lemma neq_vec_spec {n} (x y : mword n) : neq_vec x y = negb (bool_decide (bv_unsigned x = bv_unsigned y)).
Proof. unfold neq_vec. rewrite eq_vec_spec. reflexivity. Qed.

Lemma bool_decide_eqb (a b : Z) : bool_decide (a = b) = (a =? b).
Proof. destruct (Z.eqb_spec a b); [rewrite bool_decide_true|rewrite bool_decide_false]; auto. Qed.

Lemma access_vec_dec_unsigned {n} (x : mword n) i :
  0 <= i ->
  bv_unsigned (access_vec_dec x i) = (bv_unsigned x / 2 ^ i) mod 2.
Proof.
  intros Hi. unfold access_vec_dec, access_mword_dec, slice, SailStdpp.MachineWord.MachineWord.slice.
  rewrite bv_extract_unsigned. unfold bv_wrap, bv_modulus.
  rewrite Z.shiftr_div_pow2 by lia. rewrite Z2N.id by lia. reflexivity.
Qed.

Lemma add_vec_int_unsigned {n} (x : mword n) z :
  bv_unsigned (add_vec_int x z) = bv_wrap (Z.to_N n) (bv_unsigned x + z).
Proof.
  unfold add_vec_int, add_vec, word_binop, SailStdpp.MachineWord.MachineWord.add, mword_of_int, SailStdpp.MachineWord.MachineWord.Z_to_word.
  rewrite bv_add_unsigned, Z_to_bv_unsigned. unfold bv_wrap.
  rewrite Zplus_mod_idemp_r. reflexivity.
Qed.

Lemma add_vec_unsigned {n} (x y : mword n) :
  bv_unsigned (add_vec x y) = bv_wrap (Z.to_N n) (bv_unsigned x + bv_unsigned y).
Proof. unfold add_vec, word_binop, SailStdpp.MachineWord.MachineWord.add. apply bv_add_unsigned. Qed.

Lemma sub_vec_unsigned {n} (x y : mword n) :
  bv_unsigned (sub_vec x y) = bv_wrap (Z.to_N n) (bv_unsigned x - bv_unsigned y).
Proof. unfold sub_vec, word_binop, SailStdpp.MachineWord.MachineWord.sub. apply bv_sub_unsigned. Qed.

Lemma zero_extend'_unsigned {n} m (x : mword n) :
  0 <= n <= m -> bv_unsigned (zero_extend' m x) = bv_unsigned x.
Proof.
  intros Hn. unfold zero_extend', zero_extend, extz_vec, SailStdpp.MachineWord.MachineWord.zero_extend.
  rewrite bv_zero_extend_unsigned; [reflexivity|unfold SailStdpp.MachineWord.MachineWord.Z_idx; lia].
Qed.

Lemma cast_Z_unsigned {m n} (x : mword m) (e : m = n) :
  bv_unsigned (cast_Z (T := mword) x e) = bv_unsigned x.
Proof. subst. rewrite cast_Z_refl. reflexivity. Qed.

Lemma autocast_unsigned {m n} (x : mword m) :
  m = n -> bv_unsigned (autocast (T := mword) (n := n) x) = bv_unsigned x.
Proof. intros e. rewrite (autocast_eq x e). apply cast_Z_unsigned. Qed.

Lemma cast_N_unsigned {m n : N} (x : bv m) (e : m = n) :
  bv_unsigned (cast_N (T := bv) x e) = bv_unsigned x.
Proof. subst. rewrite cast_N_refl. reflexivity. Qed.

Lemma to_word_idx_unsigned {n} (x : bv n) : bv_unsigned (to_word_idx x) = bv_unsigned x.
Proof. unfold to_word_idx, SailStdpp.MachineWord.MachineWord.cast_idx. apply cast_N_unsigned. Qed.

Lemma subrange_vec_dec_unsigned {n} (v : mword n) hi lo :
  0 <= lo -> lo <= hi + 1 ->
  bv_unsigned (subrange_vec_dec v hi lo) = (bv_unsigned v / 2 ^ lo) mod 2 ^ (hi - lo + 1).
Proof.
  intros H1 H2. unfold subrange_vec_dec.
  rewrite autocast_unsigned.
  2:{ unfold SailStdpp.MachineWord.MachineWord.idx_Z, SailStdpp.MachineWord.MachineWord.Z_idx. lia. }
  rewrite to_word_idx_unsigned. unfold SailStdpp.MachineWord.MachineWord.slice.
  rewrite bv_extract_unsigned. unfold bv_wrap, bv_modulus.
  unfold SailStdpp.MachineWord.MachineWord.Z_idx.
  rewrite Z.shiftr_div_pow2 by lia. rewrite !Z2N.id by lia. reflexivity.
Qed.

Lemma lor_mul_pow2 a b n : 0 <= n -> 0 <= b < 2 ^ n -> Z.lor (a * 2 ^ n) b = a * 2 ^ n + b.
Proof.
  intros Hn Hb.
  assert (Hl : Z.land (a * 2 ^ n) b = 0).
  { apply Z.bits_inj_0. intros i. rewrite Z.land_spec.
    destruct (Z.lt_ge_cases i 0) as [Hi|Hi]; [rewrite Z.testbit_neg_r by exact Hi; reflexivity|].
    destruct (Z.lt_ge_cases i n) as [Hi'|Hi'].
    - rewrite Z.mul_pow2_bits_low by lia. reflexivity.
    - destruct (Z.eq_dec b 0) as [->|Hb0]; [rewrite Z.bits_0; apply andb_false_r|].
      rewrite (Z.bits_above_log2 b i); [apply andb_false_r|lia|].
      assert (Z.log2 b < n) by (apply Z.log2_lt_pow2; lia). lia. }
  rewrite <- Z.lxor_lor by exact Hl. symmetry. apply Z.add_nocarry_lxor, Hl.
Qed.

Lemma concat_vec_unsigned {a b} (x : mword a) (y : mword b) :
  0 <= a -> 0 <= b ->
  bv_unsigned (concat_vec x y) = bv_unsigned x * 2 ^ b + bv_unsigned y.
Proof.
  intros Ha Hb. unfold concat_vec.
  rewrite autocast_unsigned.
  2:{ unfold SailStdpp.MachineWord.MachineWord.idx_Z, SailStdpp.MachineWord.MachineWord.Z_idx. lia. }
  rewrite to_word_idx_unsigned. unfold SailStdpp.MachineWord.MachineWord.concat.
  rewrite bv_concat_unsigned.
  2:{ unfold SailStdpp.MachineWord.MachineWord.Z_idx. lia. }
  pose proof (bv_unsigned_in_range _ y) as Hy. unfold bv_modulus in Hy.
  unfold SailStdpp.MachineWord.MachineWord.Z_idx in *. rewrite Z2N.id in * by lia.
  rewrite Z.shiftl_mul_pow2 by lia.
  apply lor_mul_pow2; [lia|]. pose proof (bv_unsigned_in_range _ y). unfold bv_modulus in *.
  rewrite Z2N.id in * by lia. lia.
Qed.

Lemma if_true_else (b x : bool) : (if b then true else x) = (b || x)%bool.
Proof. destruct b; reflexivity. Qed.

Lemma if_false_else (b x : bool) : (if b then false else x) = (negb b && x)%bool.
Proof. destruct b; reflexivity. Qed.

(** The field matchers of the decoder ([encdec_*_backwards_matches]). *)
Ltac unfold_matchers_in H :=
  unfold bool_bit_backwards_matches, encdec_amoop_backwards_matches, encdec_biop_backwards_matches, encdec_bop_backwards_matches, encdec_cbop_backwards_matches, encdec_cbop_zicbop_backwards_matches, encdec_csrop_backwards_matches, encdec_freg_backwards_matches, encdec_fvffunct6_backwards_matches, encdec_fvfmafunct6_backwards_matches, encdec_fvfmfunct6_backwards_matches, encdec_fvvfunct6_backwards_matches, encdec_fvvmafunct6_backwards_matches, encdec_fvvmfunct6_backwards_matches, encdec_fwffunct6_backwards_matches, encdec_fwvffunct6_backwards_matches, encdec_fwvfmafunct6_backwards_matches, encdec_fwvfunct6_backwards_matches, encdec_fwvvfunct6_backwards_matches, encdec_fwvvmafunct6_backwards_matches, encdec_indexed_mop_backwards_matches, encdec_iop_backwards_matches, encdec_lsop_backwards_matches, encdec_mmfunct6_backwards_matches, encdec_mul_op_backwards_matches, encdec_mvvfunct6_backwards_matches, encdec_mvvmafunct6_backwards_matches, encdec_mvxfunct6_backwards_matches, encdec_mvxmafunct6_backwards_matches, encdec_nifunct6_backwards_matches, encdec_nisfunct6_backwards_matches, encdec_ntl_backwards_matches, encdec_nvfunct6_backwards_matches, encdec_nvsfunct6_backwards_matches, encdec_nxfunct6_backwards_matches, encdec_nxsfunct6_backwards_matches, encdec_reg_backwards_matches, encdec_rfvvfunct6_backwards_matches, encdec_rfwvvfunct6_backwards_matches, encdec_rivvfunct6_backwards_matches, encdec_rmvvfunct6_backwards_matches, encdec_rounding_mode_backwards_matches, encdec_uop_backwards_matches, encdec_vaesdf_backwards_matches, encdec_vaesdm_backwards_matches, encdec_vaesef_backwards_matches, encdec_vaesem_backwards_matches, encdec_vfnunary0_vs1_backwards_matches, encdec_vfunary0_vs1_backwards_matches, encdec_vfunary1_vs1_backwards_matches, encdec_vfwunary0_vs1_backwards_matches, encdec_vicmpfunct6_backwards_matches, encdec_vifunct6_backwards_matches, encdec_vimcfunct6_backwards_matches, encdec_vimfunct6_backwards_matches, encdec_vimsfunct6_backwards_matches, encdec_visgfunct6_backwards_matches, encdec_vlewidth_backwards_matches, encdec_vreg_backwards_matches, encdec_vsha2_backwards_matches, encdec_vvcmpfunct6_backwards_matches, encdec_vvfunct6_backwards_matches, encdec_vvmcfunct6_backwards_matches, encdec_vvmfunct6_backwards_matches, encdec_vvmsfunct6_backwards_matches, encdec_vxcmpfunct6_backwards_matches, encdec_vxfunct6_backwards_matches, encdec_vxmcfunct6_backwards_matches, encdec_vxmfunct6_backwards_matches, encdec_vxmsfunct6_backwards_matches, encdec_vxsgfunct6_backwards_matches, encdec_wmvvfunct6_backwards_matches, encdec_wmvxfunct6_backwards_matches, encdec_wrsop_backwards_matches, encdec_wvfunct6_backwards_matches, encdec_wvvfunct6_backwards_matches, encdec_wvxfunct6_backwards_matches, encdec_wxfunct6_backwards_matches, encdec_zicondop_backwards_matches, encdec_zilx_mode_backwards_matches, encdec_zvabd_vabd_func6_backwards_matches, encdec_zvabd_vwabda_func6_backwards_matches, vext_vs1_backwards_matches, width_enc_backwards_matches, width_enc_wide_backwards_matches , base_E_enabled, not in H;
  cbv zeta in H; rewrite ?if_true_else, ?if_false_else in H;
  cbn [orb andb negb] in H.

(** Rewrite [@bv_unsigned k t] with the lemma instance [L], whose
    left-hand side is [@bv_unsigned k' t] for an index [k'] convertible
    to [k]. *)
Ltac lhs_index L :=
  let T := type of L in
  lazymatch T with
  | context [@bv_unsigned ?k' _ = _] => k'
  end.

Ltac rw_bv_in H k t L :=
  let k' := lhs_index L in
  change (@bv_unsigned k t) with (@bv_unsigned k' t) in H;
  rewrite L in H by lia.

Ltac rw_bv k t L :=
  let k' := lhs_index L in
  change (@bv_unsigned k t) with (@bv_unsigned k' t);
  rewrite L by lia.

(** Unfold the Sail operators that occur in conditions into [Z]. *)
Ltac bv_to_Z_in H :=
  repeat first
    [ progress cbn [bits_of_physaddr bits_of_virtaddr negb andb orb] in H
    | match type of H with
      | context [if ?c then _ else _] =>
          is_closed_term c;
          let v := eval vm_compute in c in change c with v in H; cbv iota in H
      end
    | progress unfold is_aligned_vaddr, is_aligned_paddr, zopz0zI_u, zopz0zK_u, zopz0zIzJ_u,
        zopz0zKzJ_u, zopz0zJzJzK, range_subset, __id, not in H
    | rewrite !uint_spec in H
    | rewrite !eq_vec_spec in H
    | rewrite !neq_vec_spec in H
    | rewrite !bool_decide_eqb in H
    | rewrite !access_vec_dec_unsigned in H by lia
    | rewrite !add_vec_int_unsigned in H
    | rewrite !add_vec_unsigned in H
    | rewrite !sub_vec_unsigned in H
    | match type of H with
      | context [@bv_unsigned ?k (subrange_vec_dec ?v ?hi ?lo)] =>
          rw_bv_in H k (subrange_vec_dec v hi lo) (subrange_vec_dec_unsigned v hi lo)
      | context [@bv_unsigned ?k (concat_vec ?x ?y)] =>
          rw_bv_in H k (concat_vec x y) (concat_vec_unsigned x y)
      | context [@bv_unsigned ?k (zero_extend' ?m ?x)] =>
          rw_bv_in H k (zero_extend' m x) (zero_extend'_unsigned m x)
      end ].

(** Compute closed [bv_unsigned] subterms. *)
Ltac bv_closed_in H :=
  repeat match type of H with
  | context [bv_unsigned ?c] =>
      is_closed_term c;
      let v := eval vm_compute in (bv_unsigned c) in
      change (bv_unsigned c) with v in H
  end.

(** Turn boolean hypotheses into propositions. *)
Ltac bool_to_prop :=
  repeat match goal with
  | H : (_ && _)%bool = true |- _ => apply andb_prop in H; destruct H
  | H : (_ || _)%bool = true |- _ => apply orb_prop in H; destruct H
  | H : (_ && _)%bool = false |- _ => apply andb_false_elim in H; destruct H
  | H : (_ || _)%bool = false |- _ => apply orb_false_elim in H; destruct H
  | H : negb _ = true |- _ => apply negb_true_iff in H
  | H : negb _ = false |- _ => apply negb_false_iff in H
  | H : (_ <=? _) = true |- _ => apply Z.leb_le in H
  | H : (_ <=? _) = false |- _ => apply Z.leb_gt in H
  | H : (_ <? _) = true |- _ => apply Z.ltb_lt in H
  | H : (_ <? _) = false |- _ => apply Z.ltb_ge in H
  | H : (_ >=? _) = _ |- _ => rewrite Z.geb_leb in H
  | H : (_ >? _) = _ |- _ => rewrite Z.gtb_ltb in H
  | H : (_ =? _) = true |- _ => apply Z.eqb_eq in H
  | H : (_ =? _) = false |- _ => apply Z.eqb_neq in H
  | H : true = false |- _ => discriminate H
  | H : false = true |- _ => discriminate H
  end.

Ltac bv_bounds :=
  repeat match goal with
  | |- context [bv_unsigned ?x] =>
      lazymatch goal with
      | _ : 0 <= bv_unsigned x < _ |- _ => fail
      | _ => pose proof (bv_unsigned_in_range _ x)
      end
  | _ : context [bv_unsigned ?x] |- _ =>
      lazymatch goal with
      | _ : 0 <= bv_unsigned x < _ |- _ => fail
      | _ => pose proof (bv_unsigned_in_range _ x)
      end
  end.

(** Evaluate closed powers of 2 and other closed arithmetic. *)
Ltac Z_closed :=
  repeat match goal with
  | H : context [?a ^ ?b] |- _ =>
      is_closed_term (a ^ b); let v := eval vm_compute in (a ^ b) in change (a ^ b) with v in H
  | |- context [?a ^ ?b] =>
      is_closed_term (a ^ b); let v := eval vm_compute in (a ^ b) in change (a ^ b) with v
  end.

Ltac bsolve_absurd H :=
  try unfold_matchers_in H;
  bv_to_Z_in H; bv_closed_in H; bv_bounds; bool_to_prop;
  unfold bv_wrap, bv_modulus in *; cbn [Z.of_N Z.to_N] in *; Z_closed;
  lia.

(** Prove [b = c] for a constructor [c] of [bool]. *)
Ltac bsolve :=
  lazymatch goal with
  | |- ?b = true =>
      let E := fresh "E" in
      destruct b eqn:E; [reflexivity|exfalso; bsolve_absurd E]
  | |- ?b = false =>
      let E := fresh "E" in
      destruct b eqn:E; [exfalso; bsolve_absurd E|reflexivity]
  end.

(** Prove an equation or inequation of unsigned values of bit vectors. *)
Ltac zsolve :=
  repeat first
    [ progress cbn [bits_of_physaddr bits_of_virtaddr] 
    | rewrite !uint_spec
    | rewrite !access_vec_dec_unsigned by lia
    | rewrite !add_vec_int_unsigned
    | rewrite !add_vec_unsigned
    | rewrite !sub_vec_unsigned
    | match goal with
      | |- context [@bv_unsigned ?k (subrange_vec_dec ?v ?hi ?lo)] =>
          rw_bv k (subrange_vec_dec v hi lo) (subrange_vec_dec_unsigned v hi lo)
      | |- context [@bv_unsigned ?k (concat_vec ?x ?y)] =>
          rw_bv k (concat_vec x y) (concat_vec_unsigned x y)
      | |- context [@bv_unsigned ?k (zero_extend' ?m ?x)] =>
          rw_bv k (zero_extend' m x) (zero_extend'_unsigned m x)
      end ];
  bv_bounds; unfold bv_wrap, bv_modulus in *; cbn [Z.of_N Z.to_N] in *; Z_closed;
  lia.
