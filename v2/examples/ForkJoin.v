(** * Fork-join with replies

      main = let (w, w′) = new in spawn (λu. (force wk) w′); close w
      wk   = !(λw. let (c1, c1′) = new in let (c2, c2′) = new in
                   spawn (λu. close c1′); spawn (λu. close c2′);
                   close c1; close c2; close w)

    One round of binary fork-join. The worker waits for the replies of
    its two children and then answers its parent. main creates w at a
    fresh root ρ and keeps the end at ρ. The worker holds w′ at ι = ρ‾
    and creates both child channels at the fields ι·0 and ι·1 by
    E-New-Field. It keeps the ends at the fields and closes them first,
    so readiness asks ι·0 ≺ (ι·1)‾ and ι·0 ≺ ῑ for the first close and
    ι·1 ≺ ῑ for the second. These three facts are the box hypothesis H.
    The laws of ρ state H at ρ‾, so main forces the box there.

    - [fj_dftyped], [fj_term]: main types, and P-Term types the closed
      program over the empty world.
    - [fj_deadlock_free]: deadlock freedom by [soundness].
    - [fjr_dftyped], [fjr_term], [fjr_deadlock_free]: the recursive
      worker types in the deadlock-free judgment, whose E-New asks
      (acyc-new) (docs/redesign/check-df-acyclic.md, section 4.1). The
      box hypothesis H is infinite and closed under the descent to a
      child, and the laws of ρ hold an infinite descending chain.
    - [fj_wait_needs]: every typing of close a; close b at any bound
      asks the point of a below the head of b. In the recursive worker
      the child's end sits at the dual of the parent's, so the recursive
      force needs H at an instance whose dual lies below ῑ. Under
      (gen-new), the premise of E-New at a finite N, no box admits that
      descent (docs/redesign/check-general-new.md, Proposition 7), so
      the lock-free judgment rejects the recursive version.

    The channels carry no data, so "recv-or-close" is close throughout. *)

From GV Require Export examples.Tools.
From GV Require Import static.FundamentalProc examples.SemBranch.

Abbreviation ρ := (pvar 0).

(** ** The box hypothesis, over ι = 0 *)

Definition fj_P (g : fact) : Prop :=
  g = FLt (ρ·0) (ρ·1)‾ ∨ g = FLt (ρ·0) ρ‾ ∨ g = FLt (ρ·1) ρ‾.
Definition fj_H : bcs := BCs [] fj_P.

(** The laws of the root of w, H at ρ‾. A field is the same from both
    ends, ρ‾·κ = ρ·κ. *)
Definition fj_L (g : fact) : Prop :=
  g = FLt (ρ·0) (ρ·1)‾ ∨ g = FLt (ρ·0) ρ ∨ g = FLt (ρ·1) ρ.

Lemma fj_wf_new : wf_new (bcs_of fj_L).
Proof.
  apply (wf_new_lex3 _ (λ x, (if decide (pt_depth x = 0) then 1 else 0, pt_fsum x, pt_off x))).
  - intros x y Hk. destruct Hk as [E|[E|E]]; injection E as -> ->; split; reflexivity.
  - intros x. unfold lex3, pt_depth, pt_fsum. simpl. destruct (decide _); lia.
  - intros x y Hk. destruct Hk as [E|[E|E]]; injection E as -> ->; unfold pt_fsum, pt_depth; simpl; lia.
Qed.
#[global] Hint Resolve fj_wf_new : wfnew.

(** ** The programs *)

Definition wk_arr : ty := TLolli UTop LNone None (TSess SEnd ρ None None) TUnit None.
Definition wk_box : ty := TBox 1 0 fj_H None None wk_arr.

Definition wk_body : expr :=
  LetP ENew (LetP ENew
    (LetU (ESpawn (Lam (LetU (Var 0) (EClose (Var 3)))))
    (LetU (ESpawn (Lam (LetU (Var 0) (EClose (Var 1)))))
    (LetU (EClose (Var 3))
    (LetU (EClose (Var 1))
          (EClose (Var 4))))))).

Definition wk : expr := EBox (Lam wk_body).

Definition fj_main : expr :=
  let_new (LetU (ESpawn (Lam (LetU (Var 0) (App (EForce wk) (Var 1))))) (EClose (Var 1))).

(** ** The worker *)

Lemma fj_fact W Γ x y :
  (fj_H, ids 1) ∈ hc_hyps Γ → fj_P (FLt x y) → slt W Γ x y.
Proof.
  intros Hin Hf. eapply (slt_hyp _ _ fj_P (ids 1) (FLt x y)); [done|done| |].
  - destruct Hf as [E|[E|E]]; injection E as -> ->; simpl; lia.
  - destruct Hf as [E|[E|E]]; injection E as -> ->; fact_eq.
Qed.

Lemma wk_box_shift n :
  lenv_pinst (pshift 1) (Some wk_box :: nones n) = Some wk_box :: nones n.
Proof. unfold lenv_pinst. rewrite fmap_cons, fmap_replicate. reflexivity. Qed.

Section worker.
  Context (W : sworld) (Γ : hctx).
  Local Definition Γw : hctx := hc_open 1 fj_H Γ.

  Lemma fj_in : (fj_H, ids 1) ∈ hc_hyps Γw.
  Proof. unfold Γw, hc_open. simpl. apply elem_of_app. right. by left. Qed.

  Lemma wk_body_typed n :
    dftyped W ∅ Γw (Some (TSess SEnd ρ None None) :: Some wk_box :: nones n)
      (∅, None) wk_body TUnit.
  Proof.
    unfold wk_body.
    eapply d_letp; [apply tsplit_empty|lsplit_tac ENew EUnit| |].
    { apply (d_new_fld _ _ _ _ ρ 0 SEnd); [apply spare_unl; spare_tac|contr_tac]. }
    eapply d_letp; [apply tsplit_empty|lsplit_tac ENew EUnit| |].
    { apply (d_new_fld _ _ _ _ ρ 1 SEnd); [apply spare_unl; spare_tac|contr_tac]. }
    eapply d_letu; [apply tsplit_empty|lsplit_tac (ESpawn (Lam (LetU (Var 0) (EClose (Var 3))))) EUnit| |].
    { apply d_spawn_lam.
      eapply d_letu; [apply tsplit_empty|lsplit_tac (Var 0) EUnit| |].
      { eapply d_var'; [reflexivity|]. spare_tac. }
      eapply d_close with (S0 := SEnd); [reflexivity|apply ub_below_empty|].
      eapply d_var'; [reflexivity|]. spare_tac. }
    eapply d_letu; [apply tsplit_empty|lsplit_tac (ESpawn (Lam (LetU (Var 0) (EClose (Var 1))))) EUnit| |].
    { apply d_spawn_lam.
      eapply d_letu; [apply tsplit_empty|lsplit_tac (Var 0) EUnit| |].
      { eapply d_var'; [reflexivity|]. spare_tac. }
      eapply d_close with (S0 := SEnd); [reflexivity|apply ub_below_empty|].
      eapply d_var'; [reflexivity|]. spare_tac. }
    eapply d_letu; [apply tsplit_empty|lsplit_tac (EClose (Var 3)) EUnit| |].
    { eapply d_close with (S0 := SEnd) (x := ρ·0); [reflexivity| |].
      - cbn [lenv_bot hbot orb]. rewrite lenv_bot_nones. cbn [sf_unionb].
        split_and!; [|done|done]. intros y Hy. cbn [fst] in Hy. heads_simpl Hy.
        destruct Hy as [[]|[[]|[->|[->|[[]|[]]]]]];
          apply fj_fact; [apply fj_in|left; done|apply fj_in|right; left; done].
      - eapply d_var'; [reflexivity|]. spare_tac. }
    eapply d_letu; [apply tsplit_empty|lsplit_tac (EClose (Var 1)) EUnit| |].
    { eapply d_close with (S0 := SEnd) (x := ρ·1); [reflexivity| |].
      - cbn [lenv_bot hbot orb]. rewrite lenv_bot_nones. cbn [sf_unionb].
        split_and!; [|done|done]. intros y Hy. cbn [fst] in Hy. heads_simpl Hy.
        destruct Hy as [[]|[[]|[->|[[]|[]]]]].
        apply fj_fact; [apply fj_in|right; right; done].
      - eapply d_var'; [reflexivity|]. spare_tac. }
    eapply d_close with (S0 := SEnd) (x := ρ); [reflexivity|apply ub_below_empty|].
    eapply d_var'; [reflexivity|]. spare_tac.
    Unshelve. all: exact None.
  Qed.
End worker.

Lemma wk_typed W Γ n F : dftyped W ∅ Γ (nones n) F wk wk_box.
Proof.
  eapply d_box.
  { intros o Ho. apply elem_of_replicate in Ho as [-> _]. by left. }
  { cbn [tcontr]. repeat (apply Is_true_andb; split); done. }
  intros ss Hk _. destruct ss; [|done]. rewrite sinst_nil, wk_box_shift.
  eapply d_abs.
  { apply lb_below_none. spare_tac. }
  { done. }
  apply wk_body_typed.
Qed.

(** ** main *)

Definition Γm : hctx := hc_open 1 (bcs_of fj_L) hc_empty.

Lemma law_fact W x y : fj_L (FLt x y) → slt W Γm x y.
Proof.
  intros Hf. eapply (slt_hyp _ _ fj_L (ids 1) (FLt x y)); [unfold Γm, hc_open; simpl; by left|done| |].
  - destruct Hf as [E|[E|E]]; injection E as -> ->; simpl; lia.
  - destruct Hf as [E|[E|E]]; injection E as -> ->; fact_eq.
Qed.

(** The force of the worker at ρ‾, where the laws give H. *)
Lemma wk_force W n F :
  dftyped W ∅ Γm (nones n) F (EForce wk) (TLolli UTop LNone None (TSess SEnd ρ‾ None None) TUnit None).
Proof.
  assert (sinst_ty (slist []) (ty_inst [ρ‾] wk_arr) =
    TLolli UTop LNone None (TSess SEnd ρ‾ None None) TUnit None) as <-.
  { rewrite sinst_nil. reflexivity. }
  eapply d_force with (C := fj_H) (ub := None) (c := None);
    [done| |done|split; [split; apply Forall_nil|intros _; apply Forall_nil]|exact I|apply wk_typed].
  apply hold_at_nil. intros f Hf _.
  destruct Hf as [->|[->| ->]]; simpl; apply law_fact; unfold fj_L.
  all: first [left; fact_eq | right; left; fact_eq | right; right; fact_eq].
Qed.

Theorem fj_dftyped : dftyped sw_empty ∅ hc_empty [] (∅, None) fj_main TUnit.
Proof.
  unfold fj_main, let_new.
  eapply d_let; [apply tsplit_empty|apply lsplit_nil| |].
  { eapply (d_new' _ _ _ _ _ SEnd None None); [spare_tac|apply fj_wf_new|contr_tac]. }
  eapply d_open with (i := 0); [reflexivity|cbn; tauto|cons_tac|].
  rewrite tenv_pinst_empty, sf_pinst_empty. cbn [lenv_pinst fmap list_fmap insert list_insert].
  fold Γm.
  eapply d_letp; [apply tsplit_empty|lsplit_tac (Var 0) EUnit| |].
  { eapply d_var'; [reflexivity|]. spare_tac. }
  eapply d_letu; [apply tsplit_empty
                 |lsplit_tac (ESpawn (Lam (LetU (Var 0) (App (EForce wk) (Var 1))))) EUnit| |].
  - apply d_spawn_lam.
    eapply d_letu; [apply tsplit_empty|lsplit_tac (Var 0) EUnit| |].
    { eapply d_var'; [reflexivity|]. spare_tac. }
    eapply d_app with (ub := UTop); [apply tsplit_empty|lsplit_tac (EForce wk) EUnit|done| |].
    + apply (wk_force _ 4).
    + eapply d_var'; [reflexivity|]. spare_tac.
  - eapply d_close with (S0 := SEnd); [reflexivity|apply ub_below_empty|].
    eapply d_var'; [reflexivity|]. spare_tac.
  Unshelve. all: exact None.
Qed.

(** P-Term types the closed program over the empty world. *)
Theorem fj_term : fptyped None sw_empty ∅ (∅, {[+ fj_main +]}) TUnit.
Proof.
  apply (fp_term None sw_empty ∅ ∅ ∅ _ TUnit None).
  - constructor.
  - intros o. rewrite dom_empty_L. set_solver.
  - unfold chans_of. rewrite dom_empty_L. set_solver.
  - apply pfree_empty.
  - intros o e He. by rewrite lookup_empty in He.
  - set_solver.
  - assert (tenv_of (fhalf None) ∅ ∪ ∅ = tenv_df ∅) as ->.
    { unfold tenv_of, tenv_df. by rewrite !fmap_empty, map_union_empty. }
    apply fj_dftyped.
  - apply sw_empty_wok.
Qed.

Theorem fj_deadlock_free : deadlock_free (∅, {[+ fj_main +]}).
Proof. exact (soundness sw_empty _ TUnit fj_term). Qed.

(** ** Recursive fork-join with replies

    docs/redesign/check-df-acyclic.md, section 4.1. The worker is a box
    that calls itself through its box variable f. Each child forces the
    same box at the dual of the field of its channel.

      wkr  = !(f = λw. let (c1, c1′) = new_{ι·0} in let (c2, c2′) = new_{ι·1} in
                       spawn (λu. (force f) c1′); spawn (λu. (force f) c2′);
                       close c1; close c2; close w)
      main = let (w, w′) = new in spawn (λu. (force wkr) w′); close w

    The language has no numbers, so this worker has no base case and
    never replies. A base case is a case split, which adds no fact, and
    the derivation reads no data, so it is the derivation of every depth.

    The readiness of the worker asks F(ι), with
    F(x) = {x·0 ≺ (x·1)‾, x·0 ≺ x‾, x·1 ≺ x‾}. The child of c1 forces the
    box at ι′ = (ι·0)‾. The box hypothesis H(ι) is F(ι) together with
    F((ι·w)‾) for every nonempty word w of fields, so H(ι′) ⊆ H(ι)
    ([fjH_desc]). main creates w at a fresh root ρ with the laws H(ρ‾),
    which descend forever, ρ ≻ ρ·0 ≻ ρ·0·0 ≻ …. (gen-new) rejects them.
    (acyc-new) accepts them ([fjr_acyc]): C with program order is acyclic,
    by the order of offset, then polarity, then depth reversed, and no
    fact leaves the tree of ρ. *)

Fixpoint fpath (x : point) (w : list field) : point :=
  match w with [] => x | κ :: w' => fpath (x·κ) w' end.

Lemma fpath_inst σ x w : pt_inst σ (fpath x w) = fpath (pt_inst σ x) w.
Proof. revert x. induction w as [|κ w IH]; intros x; [done|]. simpl. by rewrite IH, pt_inst_field. Qed.

Lemma fpath_dual x w : w ≠ [] → fpath x‾ w = fpath x w.
Proof. destruct w; [done|]. reflexivity. Qed.

Lemma fpath_root x w : pt_root (fpath x w) = pt_root x.
Proof. revert x. induction w as [|κ w IH]; intros x; [done|]. simpl. by rewrite IH. Qed.

Lemma fpath_depth x w : pt_depth (fpath x w) = pt_depth x + length w.
Proof. revert x. induction w as [|κ w IH]; intros x; simpl; [lia|]. rewrite IH. unfold pt_depth. simpl. lia. Qed.

Lemma fpath_field x w : w ≠ [] → pt_pol (fpath x w) = true ∧ pt_off (fpath x w) = 0.
Proof.
  revert x. induction w as [|κ [|κ' w] IH]; intros x Hw; [done|done|]. simpl. apply IH. done.
Qed.

Definition fjF (x : point) (g : fact) : Prop :=
  g = FLt (x·0) (x·1)‾ ∨ g = FLt (x·0) x‾ ∨ g = FLt (x·1) x‾.
Definition fjH (x : point) (g : fact) : Prop :=
  fjF x g ∨ ∃ w, w ≠ [] ∧ fjF (fpath x w)‾ g.

Lemma fjF_inst σ y g : fjF y g → fjF (pt_inst σ y) (fact_map (pt_inst σ) g).
Proof.
  intros [->|[->| ->]]; cbn [fact_map]; rewrite ?pt_inst_dual, ?pt_inst_field;
    [left|right; left|right; right]; reflexivity.
Qed.

Lemma fjH_inst σ x g : fjH x g → fjH (pt_inst σ x) (fact_map (pt_inst σ) g).
Proof.
  intros [H|(w & Hw & H)]; [left; by apply fjF_inst|right].
  exists w. split; [done|]. rewrite <-fpath_inst, <-pt_inst_dual. by apply fjF_inst.
Qed.

(** H descends to a child: H((x·κ)‾) ⊆ H(x). *)
Lemma fjH_desc x κ g : fjH (x·κ)‾ g → fjH x g.
Proof.
  intros [H|(w & Hw & H)]; right.
  - exists [κ]. split; [done|]. exact H.
  - exists (κ :: w). split; [done|]. by rewrite fpath_dual in H.
Qed.

Lemma fjF_root y u v : fjF y (FLt u v) → pt_root u = pt_root y ∧ pt_root v = pt_root y.
Proof. intros [E|[E|E]]; injection E as -> ->; done. Qed.

Lemma fjH_root x u v : fjH x (FLt u v) → pt_root u = pt_root x ∧ pt_root v = pt_root x.
Proof.
  intros [H|(w & _ & H)]; [by apply (fjF_root x)|].
  apply fjF_root in H. change (pt_root (fpath x w)‾) with (pt_root (fpath x w)) in H. by rewrite fpath_root in H.
Qed.

Lemma pn_vb_root0 p : pn_root p = NVar 0 → pn_vb 1 p.
Proof. induction p as [a|a|q IH b κ]; simpl; try discriminate. - intros [= ->]. lia. - done. Qed.

Lemma pt_inst_id0 x : pt_root x = NVar 0 → pt_inst (plist [ρ]) x = x.
Proof.
  intros Hx. rewrite (pt_inst_ext_root _ pvar); [apply pt_inst_pvar|].
  intros a Ha. rewrite Hx in Ha. injection Ha as <-. done.
Qed.

(** A fact of H at an instance of the hypothesis of the root x. *)
Lemma fjH_slt W Γ (x : point) u v : pt_root x = NVar 0 →
  (BCs [] (fjH x), ids 1) ∈ hc_hyps Γ → fjH x (FLt u v) → slt W Γ u v.
Proof.
  intros Hx Hin Hf. destruct (fjH_root x u v Hf) as [Hu Hv].
  eapply (slt_hyp _ _ (fjH x) (ids 1) (FLt u v)); [done|done| |].
  - split; apply pn_vb_root0; [change (pt_root u = NVar 0)|change (pt_root v = NVar 0)]; congruence.
  - cbn [fact_map]. change (ids 1) with [ρ]. by rewrite !pt_inst_id0 by congruence.
Qed.

Definition fjr_H : bcs := BCs [] (fjH ρ).

(** The laws of the root of w, H at ρ‾. *)
Definition fjr_L : fact → Prop := fjH ρ‾.

(** ** (acyc-new) for the laws *)

Definition fjr_lt (u v : point) : Prop :=
  pt_off u < pt_off v ∨
  (pt_off u = pt_off v ∧ ((pt_pol u = true ∧ pt_pol v = false) ∨
                           (pt_pol u = pt_pol v ∧ pt_depth v < pt_depth u))).

Lemma fjr_lt_trans u v w : fjr_lt u v → fjr_lt v w → fjr_lt u w.
Proof.
  unfold fjr_lt. destruct (pt_pol u), (pt_pol v), (pt_pol w); intros [?|[? [[? ?]|[? ?]]]] [?|[? [[? ?]|[? ?]]]];
    first [left; lia|right; split; [lia|]; first [left; split; congruence|right; split; [congruence|lia]]|discriminate].
Qed.

Lemma fjr_lt_irrefl u : ¬ fjr_lt u u.
Proof. unfold fjr_lt. intros [?|[_ [[E1 E2]|[_ ?]]]]; [lia|congruence|lia]. Qed.

Lemma fjF_lt z u v : pt_pol z‾ = true → pt_off z = 0 → fjF z (FLt u v) → fjr_lt u v.
Proof.
  intros Hp Ho [E|[E|E]]; injection E as -> ->; right; cbn [pt_field pt_dual pt_pol pt_off].
  - split; [done|]. by left.
  - split; [done|]. right. split; [done|]. unfold pt_depth. simpl. lia.
  - split; [done|]. right. split; [done|]. unfold pt_depth. simpl. lia.
Qed.

Lemma fjr_L_lt u v : fjr_L (FLt u v) → fjr_lt u v.
Proof.
  intros [H|(w & Hw & H)].
  - by apply (fjF_lt ρ‾).
  - apply (fjF_lt (fpath ρ‾ w)‾); [|change (pt_off (fpath ρ‾ w)‾) with (pt_off (fpath ρ‾ w))|exact H].
    + rewrite pt_dual_dual. by apply fpath_field.
    + by apply fpath_field.
Qed.

Lemma fjr_step_lt u v : new_step (bcs_of fjr_L) u v → fjr_lt u v.
Proof.
  intros (_ & _ & [[Hf _]|[-> | ->]]); [by apply fjr_L_lt| |]; left; cbn [pt_shift pt_dual pt_off]; lia.
Qed.

Lemma fjr_tc_lt u v : tc (new_step (bcs_of fjr_L)) u v → fjr_lt u v.
Proof.
  induction 1 as [u v H|u v w H _ IH]; [by apply fjr_step_lt|].
  eapply fjr_lt_trans; [by apply fjr_step_lt|exact IH].
Qed.

(** The laws meet (acyc-new): no cycle, and no fact leaves the tree of
    ρ, so there is no bridge. *)
Lemma fjr_acyc W Γ : acyc_new W Γ (bcs_of fjr_L).
Proof.
  split.
  - intros x _ Hc. exact (fjr_lt_irrefl x (fjr_tc_lt x x Hc)).
  - intros z y (Hz & _ & [[Hf _]|(v & u & [Hf _] & _)]); exfalso; apply Hz; unfold in_tree0;
      by destruct (fjH_root _ _ _ Hf) as [-> _].
Qed.

Lemma fjr_tree_ends : tree_ends (bcs_of fjr_L).
Proof. intros x y Hf _. unfold in_tree0. by destruct (fjH_root _ _ _ Hf) as [_ ->]. Qed.

(** ** The programs *)

Definition wkr_arr : ty := TLolli UTop LNone None (TSess SEnd ρ None None) TUnit None.
Definition wkr_box : ty := TBox 1 0 fjr_H None None wkr_arr.

Definition wkr_body : expr :=
  LetP ENew (LetP ENew
    (LetU (ESpawn (Lam (LetU (Var 0) (App (EForce (Var 6)) (Var 3)))))
    (LetU (ESpawn (Lam (LetU (Var 0) (App (EForce (Var 6)) (Var 1)))))
    (LetU (EClose (Var 3))
    (LetU (EClose (Var 1))
          (EClose (Var 4))))))).

Definition wkr : expr := EBox (Lam wkr_body).

Definition fjr_main : expr :=
  let_new (LetU (ESpawn (Lam (LetU (Var 0) (App (EForce wkr) (Var 1))))) (EClose (Var 1))).

(** ** The worker *)

Lemma wkr_box_shift n :
  lenv_pinst (pshift 1) (Some wkr_box :: nones n) = Some wkr_box :: nones n.
Proof. unfold lenv_pinst. rewrite fmap_cons, fmap_replicate. reflexivity. Qed.

Lemma wkr_arr_inst x : ty_inst [x] wkr_arr = TLolli UTop LNone None (TSess SEnd x None None) TUnit None.
Proof. unfold ty_inst, wkr_arr. simpl. by rewrite pt_inst_pvar_at. Qed.

(** The recursive call: the box variable forced at x, where H holds. *)
Lemma wkr_force_var W Γ Δ F i x :
  Δ !! i = Some (Some wkr_box) → (∀ y o, y ≠ i → Δ !! y = Some o → spare o) →
  hold_at W Γ fjr_H [x] →
  dftyped W ∅ Γ Δ F (EForce (Var i)) (TLolli UTop LNone None (TSess SEnd x None None) TUnit None).
Proof.
  intros Hi Hs HC. rewrite <-wkr_arr_inst, <-(sinst_nil (ty_inst [x] wkr_arr)).
  eapply d_force with (C := fjr_H) (ub := None) (c := None);
    [done|exact HC|done|split; [split; apply Forall_nil|intros _; apply Forall_nil]|exact I|].
  by eapply d_var'.
Qed.

Section rworker.
  Context (W : sworld) (Γ : hctx).
  Local Definition Γr_w : hctx := hc_open 1 fjr_H Γ.

  Lemma fjr_in : (fjr_H, ids 1) ∈ hc_hyps Γr_w.
  Proof. unfold Γr_w, hc_open. simpl. apply elem_of_app. right. by left. Qed.

  Lemma fjr_fact u v : fjH ρ (FLt u v) → slt W Γr_w u v.
  Proof. intros Hf. apply (fjH_slt W Γr_w ρ); [done|apply fjr_in|exact Hf]. Qed.

  (** A child forces the box at (ι·κ)‾, where H holds by descent. *)
  Lemma fjr_desc_hold κ : hold_at W Γr_w fjr_H [(ρ·κ)‾].
  Proof.
    apply hold_at_nil. intros f Hf _.
    pose proof (fjH_inst (plist [(ρ·κ)‾]) ρ f Hf) as H.
    assert (pt_inst (plist [(ρ·κ)‾]) ρ = (ρ·κ)‾) as E by (rewrite pt_inst_pvar_at; reflexivity).
    rewrite E in H. apply fjH_desc in H.
    destruct (fact_map (pt_inst (plist [(ρ·κ)‾])) f) as [u v]. by apply fjr_fact.
  Qed.

  Lemma wkr_body_typed n :
    dftyped W ∅ Γr_w (Some (TSess SEnd ρ None None) :: Some wkr_box :: nones n)
      (∅, None) wkr_body TUnit.
  Proof.
    unfold wkr_body.
    eapply d_letp; [apply tsplit_empty|lsplit_tac ENew EUnit| |].
    { apply (d_new_fld _ _ _ _ ρ 0 SEnd); [apply spare_unl; spare_tac|contr_tac]. }
    eapply d_letp; [apply tsplit_empty|lsplit_tac ENew EUnit| |].
    { apply (d_new_fld _ _ _ _ ρ 1 SEnd); [apply spare_unl; spare_tac|contr_tac]. }
    eapply d_letu; [apply tsplit_empty
                   |lsplit_tac (ESpawn (Lam (LetU (Var 0) (App (EForce (Var 6)) (Var 3))))) EUnit| |].
    { apply d_spawn_lam.
      eapply d_letu; [apply tsplit_empty|lsplit_tac (Var 0) EUnit| |].
      { eapply d_var'; [reflexivity|]. spare_tac. }
      eapply d_app with (ub := UTop); [apply tsplit_empty|lsplit_tac (EForce (Var 6)) EUnit|done| |].
      + apply wkr_force_var; [reflexivity|spare_tac|apply fjr_desc_hold].
      + eapply d_var'; [reflexivity|]. spare_tac. }
    eapply d_letu; [apply tsplit_empty
                   |lsplit_tac (ESpawn (Lam (LetU (Var 0) (App (EForce (Var 6)) (Var 1))))) EUnit| |].
    { apply d_spawn_lam.
      eapply d_letu; [apply tsplit_empty|lsplit_tac (Var 0) EUnit| |].
      { eapply d_var'; [reflexivity|]. spare_tac. }
      eapply d_app with (ub := UTop); [apply tsplit_empty|lsplit_tac (EForce (Var 6)) EUnit|done| |].
      + apply wkr_force_var; [reflexivity|spare_tac|apply fjr_desc_hold].
      + eapply d_var'; [reflexivity|]. spare_tac. }
    eapply d_letu; [apply tsplit_empty|lsplit_tac (EClose (Var 3)) EUnit| |].
    { eapply d_close with (S0 := SEnd) (x := ρ·0); [reflexivity| |].
      - cbn [lenv_bot hbot orb]. rewrite lenv_bot_nones. cbn [sf_unionb].
        split_and!; [|done|done]. intros y Hy. cbn [fst] in Hy. heads_simpl Hy.
        destruct Hy as [[]|[[]|[->|[->|[[]|[]]]]]]; apply fjr_fact;
          [left; left; reflexivity|left; right; left; reflexivity].
      - eapply d_var'; [reflexivity|]. spare_tac. }
    eapply d_letu; [apply tsplit_empty|lsplit_tac (EClose (Var 1)) EUnit| |].
    { eapply d_close with (S0 := SEnd) (x := ρ·1); [reflexivity| |].
      - cbn [lenv_bot hbot orb]. rewrite lenv_bot_nones. cbn [sf_unionb].
        split_and!; [|done|done]. intros y Hy. cbn [fst] in Hy. heads_simpl Hy.
        destruct Hy as [[]|[[]|[->|[[]|[]]]]].
        apply fjr_fact. left; right; right; reflexivity.
      - eapply d_var'; [reflexivity|]. spare_tac. }
    eapply d_close with (S0 := SEnd) (x := ρ); [reflexivity|apply ub_below_empty|].
    eapply d_var'; [reflexivity|]. spare_tac.
    Unshelve. all: exact None.
  Qed.
End rworker.

Lemma wkr_typed W Γ n F : dftyped W ∅ Γ (nones n) F wkr wkr_box.
Proof.
  eapply d_box.
  { intros o Ho. apply elem_of_replicate in Ho as [-> _]. by left. }
  { cbn [tcontr]. repeat (apply Is_true_andb; split); done. }
  intros ss Hk _. destruct ss; [|done]. rewrite sinst_nil, wkr_box_shift.
  eapply d_abs.
  { apply lb_below_none. spare_tac. }
  { done. }
  apply wkr_body_typed.
Qed.

(** ** main *)

Definition Γr : hctx := hc_open 1 (bcs_of fjr_L) hc_empty.

Lemma fjr_law W u v : fjr_L (FLt u v) → slt W Γr u v.
Proof. intros Hf. apply (fjH_slt W Γr ρ‾); [done|unfold Γr, hc_open; simpl; by left|exact Hf]. Qed.

(** The force of the worker at ρ‾, where the laws give H. *)
Lemma wkr_force W n F :
  dftyped W ∅ Γr (nones n) F (EForce wkr) (TLolli UTop LNone None (TSess SEnd ρ‾ None None) TUnit None).
Proof.
  rewrite <-wkr_arr_inst, <-(sinst_nil (ty_inst [ρ‾] wkr_arr)).
  eapply d_force with (C := fjr_H) (ub := None) (c := None);
    [done| |done|split; [split; apply Forall_nil|intros _; apply Forall_nil]|exact I|apply wkr_typed].
  apply hold_at_nil. intros f Hf _.
  pose proof (fjH_inst (plist [ρ‾]) ρ f Hf) as H.
  assert (pt_inst (plist [ρ‾]) ρ = ρ‾) as E by (rewrite pt_inst_pvar_at; reflexivity). rewrite E in H.
  destruct (fact_map (pt_inst (plist [ρ‾])) f) as [u v]. by apply fjr_law.
Qed.

Theorem fjr_dftyped : dftyped sw_empty ∅ hc_empty [] (∅, None) fjr_main TUnit.
Proof.
  unfold fjr_main, let_new.
  eapply d_let; [apply tsplit_empty|apply lsplit_nil| |].
  { apply (d_new_acyc _ _ _ _ (bcs_of fjr_L) SEnd None None None None);
      [apply spare_unl; spare_tac|apply fjr_acyc|contr_tac]. }
  eapply d_open with (i := 0); [reflexivity|cbn; tauto|apply cons_tree; [by intros ?? []|apply fjr_tree_ends]|].
  rewrite tenv_pinst_empty, sf_pinst_empty. cbn [lenv_pinst fmap list_fmap insert list_insert].
  fold Γr.
  eapply d_letp; [apply tsplit_empty|lsplit_tac (Var 0) EUnit| |].
  { eapply d_var'; [reflexivity|]. spare_tac. }
  eapply d_letu; [apply tsplit_empty
                 |lsplit_tac (ESpawn (Lam (LetU (Var 0) (App (EForce wkr) (Var 1))))) EUnit| |].
  - apply d_spawn_lam.
    eapply d_letu; [apply tsplit_empty|lsplit_tac (Var 0) EUnit| |].
    { eapply d_var'; [reflexivity|]. spare_tac. }
    eapply d_app with (ub := UTop); [apply tsplit_empty|lsplit_tac (EForce wkr) EUnit|done| |].
    + apply (wkr_force _ 4).
    + eapply d_var'; [reflexivity|]. spare_tac.
  - eapply d_close with (S0 := SEnd); [reflexivity|apply ub_below_empty|].
    eapply d_var'; [reflexivity|]. spare_tac.
  Unshelve. all: exact None.
Qed.

(** P-Term types the closed program over the empty world. *)
Theorem fjr_term : fptyped None sw_empty ∅ (∅, {[+ fjr_main +]}) TUnit.
Proof.
  apply (fp_term None sw_empty ∅ ∅ ∅ _ TUnit None).
  - constructor.
  - intros o. rewrite dom_empty_L. set_solver.
  - unfold chans_of. rewrite dom_empty_L. set_solver.
  - apply pfree_empty.
  - intros o e He. by rewrite lookup_empty in He.
  - set_solver.
  - assert (tenv_of (fhalf None) ∅ ∪ ∅ = tenv_df ∅) as ->.
    { unfold tenv_of, tenv_df. by rewrite !fmap_empty, map_union_empty. }
    apply fjr_dftyped.
  - apply sw_empty_wok.
Qed.

(** Recursive fork-join with replies is deadlock free, without excluded
    middle. *)
Theorem fjr_deadlock_free : deadlock_free (∅, {[+ fjr_main +]}).
Proof. exact (soundness sw_empty _ TUnit fjr_term). Qed.

(** ** Why the recursion does not type at a finite N

    In the recursive worker the parent closes its child's channel c and
    then w, so after the spawn it runs close c; close w. Every typing of
    that term, at any bound, world and context, asks the point p of c
    below the head ῑ of w. The child holds the other end at p‾ and forces
    the same box there, so it needs H at an instance ι′ = p‾ with
    ῑ′ = p ≺ ῑ. Proposition 7 of docs/redesign/check-general-new.md shows
    that W, Γ and H then have no common model of rank, for a field
    creation and for a fresh root alike, so under (gen-new) main cannot
    force the box. Strict worlds have no least rank, so the argument
    does not apply to the deadlock-free judgment ([fjr_dftyped]). *)
Lemma fj_wait_needs W N Θ Γ Δ F c w T k ec ew :
  c ≠ w → typed W N Θ Γ Δ F (LetU (EClose (Chan c)) (EClose (Chan w))) T k →
  Θ !! c = Some ec → Θ !! w = Some ew → slt W Γ (te_pt ec) (te_pt ew)‾.
Proof. apply cl2_needs. Qed.

Print Assumptions fj_deadlock_free.
Print Assumptions fj_wait_needs.
Print Assumptions fjr_acyc.
Print Assumptions fjr_dftyped.
Print Assumptions fjr_deadlock_free.
