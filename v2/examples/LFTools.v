(** * Tools for lock-free example derivations (stage S9)

    A closed program t is lock free by [lf_soundness] when it types at a
    finite refill N with the empty future, is guarded, meets its ticket
    transformer at 0 and lives in a lock-free world ([lf_main]).

    A world is a lock-free world when some measure into a well-founded
    transitive order rises along every generating step of ≺
    ([lfworld_measure]). The measures of the examples are lexicographic
    triples ([lex3]) of the field sum, the depth and the offset of a
    point. *)

From GV Require Export examples.Tools2.
From GV Require Export soup.LFTyped.

(** ** Lock-free worlds by a measure *)

Lemma lfworld_measure {A} (R : relation A) (m : point → A) W :
  world_wf W → well_founded R → Transitive R →
  (∀ x y, wstep W x y → R (m x) (m y)) → lfworld W.
Proof.
  intros Hwf HR HT Hs.
  assert (∀ x y, W ⊢ x ≺ y → R (m x) (m y)) as Hlt.
  { induction 1 as [x y H|x z y H _ IH]; [by apply Hs|]. apply Hs in H. by transitivity (m z). }
  split; [split; [done|]|].
  - intros x H. apply Hlt in H. revert H. generalize (m x) as a. intros a.
    induction (HR a) as [a _ IH]. intros Ha. exact (IH a Ha Ha).
  - assert (∀ a x, m x = a → Acc (w_lt W) x) as Hacc.
    { intros a. induction (HR a) as [a _ IH]. intros x <-. constructor.
      intros y Hy. eapply IH; [apply Hlt, Hy|done]. }
    intros x. by apply (Hacc (m x)).
Qed.

(** The lexicographic order on triples of natural numbers. *)
Definition lex3 (a b : nat * nat * nat) : Prop :=
  let '(a1, a2, a3) := a in let '(b1, b2, b3) := b in
  a1 < b1 ∨ (a1 = b1 ∧ (a2 < b2 ∨ (a2 = b2 ∧ a3 < b3))).

Lemma lex3_wf : well_founded lex3.
Proof.
  intros [[a1 a2] a3]. revert a2 a3. induction a1 as [a1 IH1] using lt_wf_ind.
  intros a2. induction a2 as [a2 IH2] using lt_wf_ind.
  intros a3. induction a3 as [a3 IH3] using lt_wf_ind.
  constructor. intros [[b1 b2] b3] H. simpl in H.
  destruct H as [H|[<- [H|[<- H]]]]; eauto.
Qed.

Global Instance lex3_trans : Transitive lex3.
Proof. intros [[a1 a2] a3] [[b1 b2] b3] [[c1 c2] c3]; simpl; lia. Qed.

(** The number of fields of a name and the sum of their labels. *)
Fixpoint pn_depth (p : pname) : nat :=
  match p with NField q _ _ => S (pn_depth q) | _ => 0 end.
Fixpoint pn_fsum (p : pname) : nat :=
  match p with NField q _ κ => κ + pn_fsum q | _ => 0 end.

Definition pt_depth (x : point) : nat := pn_depth (pt_name x).
Definition pt_fsum (x : point) : nat := pn_fsum (pt_name x).

(** The program-order steps raise the offset and keep the name. *)
Lemma wstep_po_off x y : (y = x⁺ ∨ y = x‾⁺) →
  pt_name y = pt_name x ∧ pt_off y = S (pt_off x).
Proof. intros [->| ->]; simpl; split; [done|lia|done|lia]. Qed.

(** A measure that rises on the laws and on x ≺ x⁺, x ≺ x‾⁺ through the
    offset, for a world without facts. *)
Lemma lfworld_lex3 W (m : point → nat * nat * nat) :
  world_wf W → (∀ f, ¬ w_facts W f) →
  (∀ x, lex3 (m x) (m x⁺) ∧ lex3 (m x) (m x‾⁺)) →
  (∀ ℓ g x y, ℓ ∈ w_fams W → w_laws W ℓ (FLt x y) → lex3 (m (law_inst ℓ g x)) (m (law_inst ℓ g y))) →
  lfworld W.
Proof.
  intros Hwf Hf Hpo Hlaw. apply (lfworld_measure lex3 m W Hwf lex3_wf _).
  intros x y H. destruct H as [x y H|ℓ g x y Hℓ Hl|x|x].
  - by destruct (Hf _ H).
  - by apply Hlaw.
  - apply Hpo.
  - apply Hpo.
Qed.

(** ** Closed programs *)

Lemma lf_main_typed N W t T a c ϑ tk :
  types.Types.prim T → typed W (Some N) ∅ hc_empty [] (∅, None) t T a c ϑ →
  guarded t → meets ϑ 0 tk → ∅ ⊩^N _ W (∅, {[+ t +]}) : T.
Proof.
  intros Hp Ht Hg Hm. apply (p_term N W ∅ ∅ ∅ t T a c ϑ tk); [done| | | |done|done|done].
  - intros o. rewrite dom_empty_L. set_solver.
  - set_solver.
  - set_solver.
Qed.

Lemma lf_main N W t T a c ϑ tk :
  lfworld W → types.Types.prim T → typed W (Some N) ∅ hc_empty [] (∅, None) t T a c ϑ →
  guarded t → meets ϑ 0 tk → lock_free (∅, {[+ t +]}).
Proof. intros HW Hp Ht Hg Hm. eapply (lf_soundness N W _ T HW), lf_main_typed; eauto. Qed.

(** ** Rules of the merged judgment with weakening built in *)

Lemma e_var' W N Γ Δ F x T a :
  Δ !! x = Some (Some (T, a)) → (∀ y o, y ≠ x → Δ !! y = Some o → spare o) →
  typed W N ∅ Γ Δ F (Var x) T a (Some 0) tid.
Proof.
  intros Hx Hs. eapply e_weak; [by apply drop_but_wk|]. eapply e_var. by apply drop_but_only.
Qed.

Lemma e_unit' W N Γ Δ F : (∀ y o, Δ !! y = Some o → spare o) →
  typed W N ∅ Γ Δ F EUnit TUnit None (Some 0) tid.
Proof. intros H. eapply e_weak; [by apply lenv_all_spare_empty|]. apply e_unit, lenv_empty_nones. Qed.

Lemma e_new' W N Γ Δ F ℓ S :
  (∀ y o, Δ !! y = Some o → spare o) → ℓ ∈ w_fams W →
  typed W N ∅ Γ Δ F (ENew ℓ)
    (TEx LBot 1 (bcs_of (w_laws W ℓ)) (TProd (TSess S (pvar 0)) N (TSess (dual S) (pvar 0)‾) N) (Some 0))
    (Some 0) (Some 0) tid.
Proof. intros H Hℓ. eapply e_weak; [by apply lenv_all_spare_empty|]. apply e_new; [apply lenv_empty_nones|done]. Qed.

Lemma thage_empty c : thage c ∅ ∅.
Proof. intros o. by rewrite lookup_empty. Qed.

(** The rules with two operands over Θ = ∅, the premises in the order
    a derivation meets them: the first operand fixes the cost that ages
    the context of the second. *)

Lemma e_let_ W N Γ Δ Δ1 Δ2 Δ2' F e1 e2 T1 a1 T aT c1 t1 c2 t2 :
  lenv_split Δ Δ1 Δ2 →
  typed W N ∅ Γ Δ1 (sf_unionb F (tenv_heads ∅ ∪ lenv_heads Δ2) (lenv_bot Δ2)) e1 T1 a1 c1 t1 →
  lage c1 Δ2 Δ2' →
  typed W N ∅ Γ (Some (T1, a1) :: Δ2') F e2 T aT c2 t2 →
  tok t1 t2 →
  typed W N ∅ Γ Δ F (ELet e1 e2) T aT (fadd c1 c2) (tseq t1 t2).
Proof. intros. eapply e_let; eauto using tsplit_empty, thage_empty. Qed.

Lemma e_letu_ W N Γ Δ Δ1 Δ2 Δ2' F e1 e2 a T aT c1 t1 c2 t2 :
  lenv_split Δ Δ1 Δ2 →
  typed W N ∅ Γ Δ1 (sf_unionb F (tenv_heads ∅ ∪ lenv_heads Δ2) (lenv_bot Δ2)) e1 TUnit a c1 t1 →
  lage c1 Δ2 Δ2' →
  typed W N ∅ Γ Δ2' F e2 T aT c2 t2 →
  tok t1 t2 →
  typed W N ∅ Γ Δ F (LetU e1 e2) T aT (fadd c1 c2) (tseq t1 t2).
Proof. intros. eapply e_letu; eauto using tsplit_empty, thage_empty. Qed.

Lemma e_letp_ W N Γ Δ Δ1 Δ2 Δ2' F e1 e2 T1 a1 T2 a2 a T aT c1 t1 c2 t2 :
  lenv_split Δ Δ1 Δ2 →
  typed W N ∅ Γ Δ1 (sf_unionb F (tenv_heads ∅ ∪ lenv_heads Δ2) (lenv_bot Δ2)) e1
    (TProd T1 a1 T2 a2) a c1 t1 →
  lage c1 Δ2 Δ2' →
  typed W N ∅ Γ (Some (T2, fadd a a2) :: Some (T1, fadd a a1) :: Δ2') F e2 T aT c2 t2 →
  tok t1 t2 →
  typed W N ∅ Γ Δ F (LetP e1 e2) T aT (fadd c1 c2) (tseq t1 t2).
Proof. intros. eapply e_letp; eauto using tsplit_empty, thage_empty. Qed.

Lemma e_pair_ W N Γ Δ Δ1 Δ2 Δ2' F e1 e2 T1 a1 T1' a1' T2 a2 c1 t1 c2 t2 :
  lenv_split Δ Δ1 Δ2 →
  typed W N ∅ Γ Δ1 (sf_unionb F (tenv_heads ∅ ∪ lenv_heads Δ2) (lenv_bot Δ2)) e1 T1 a1 c1 t1 →
  lage c1 Δ2 Δ2' →
  typed W N ∅ Γ Δ2' (sf_unionb F (heads T1) (hbot T1)) e2 T2 a2 c2 t2 →
  tage c2 (T1, a1) (T1', a1') → tok t1 t2 →
  typed W N ∅ Γ Δ F (Pair e1 e2) (TProd T1' a1' T2 a2) (Some 0) (fadd c1 c2) (tseq t1 t2).
Proof. intros. eapply e_pair; eauto using tsplit_empty, thage_empty. Qed.

Lemma e_app_ W N Γ Δ Δ1 Δ2 Δ2' F e1 e2 ub lb c t h T aT U aU a1 c1 t1 c2 t2 :
  lenv_split Δ Δ1 Δ2 → ub_below_s W Γ ub F →
  typed W N ∅ Γ Δ1 (sf_unionb F (tenv_heads ∅ ∪ lenv_heads Δ2) (lenv_bot Δ2)) e1
    (TLolli ub lb c t h T aT U aU) a1 c1 t1 →
  lage c1 Δ2 Δ2' →
  typed W N ∅ Γ Δ2' (sf_union F (opt_heads lb)) e2 T aT c2 t2 →
  fle c2 a1 → tok t2 t → tok t1 (tseq t2 t) →
  typed W N ∅ Γ Δ F (App e1 e2) U aU (fadd c1 (fadd c2 c)) (tseq t1 (tseq t2 t)).
Proof. intros. eapply e_app; eauto using tsplit_empty, thage_empty. Qed.

(** ** Tactics *)

(** Aging a concrete entry: free, by its credit, or by its parts. *)
Ltac age_tac :=
  first [ solve [apply age_free; repeat constructor]
        | apply age_credit; simpl; lia
        | apply age_prod; age_tac
        | apply age_ex; age_tac ].

Ltac lage_tac :=
  solve [repeat first [ apply lage_nones | apply lage_nil | apply lage_none
                      | apply lage_some; [age_tac|] ]].

Ltac tok_tac := first [ left; reflexivity | right; left; discriminate | right; right; reflexivity ].

Ltac acts_tac :=
  first [ apply acts_op; exact I
        | apply acts_op_arg; acts_tac
        | apply acts_app1; acts_tac | apply acts_app2; acts_tac
        | apply acts_pair1; acts_tac | apply acts_pair2; acts_tac
        | apply acts_letu1; acts_tac | apply acts_letu2; acts_tac
        | apply acts_letp1; acts_tac | apply acts_letp2; acts_tac
        | apply acts_let1; acts_tac | apply acts_let2; acts_tac ].

(** The guard: an operand that acts clears the marks for the rest. *)
Ltac guard_tac :=
  first [ apply glive_var; reflexivity | apply glive_unit | apply glive_chan | apply glive_new
        | apply glive_lam; guard_tac | apply glive_box; guard_tac
        | apply glive_op; guard_tac
        | apply glive_app_acts; [guard_tac|acts_tac|guard_tac] | apply glive_app; guard_tac
        | apply glive_pair_acts; [guard_tac|acts_tac|guard_tac] | apply glive_pair; guard_tac
        | apply glive_letu_acts; [guard_tac|acts_tac|guard_tac] | apply glive_letu; guard_tac
        | apply glive_letp_acts; [guard_tac|acts_tac|guard_tac] | apply glive_letp; guard_tac
        | apply glive_let_acts; [guard_tac|acts_tac|guard_tac] | apply glive_let; guard_tac
        | apply glive_inj1; guard_tac | apply glive_inj2; guard_tac
        | apply glive_case; guard_tac ].

Ltac meets_tac := unfold meets; simpl; lia.

(** ** Boxes of one arrow

    □∀ιs. C. T^aT ⊸^ub U^aU with box cost 0 and transformer 1̂. The arrow
    has cost ∞ and transformer (∞, 0), which every body with offset 0
    meets ([tle_tz]). A call is then a last step of its thread or of a
    box body: whatever is held across it would age by ∞. *)

Definition tz : tix := (None, Some 0).

Lemma tle_tz t : t.2 = Some 0 → tle t tz.
Proof.
  destruct t as [s b]. simpl. intros -> r tk. unfold meets, tz, tapp.
  destruct (Nat.eqb_spec r 0) as [->|]; [|done]. simpl. intros H.
  destruct s; simpl; lia.
Qed.

Lemma lcap_nones h a n : lcap h a (nones n) (nones n).
Proof. induction n; simpl; constructor; done. Qed.

Definition lbox (m : nat) (C : bcs) (ub : option point) (T : ty) (aT : fuel) (U : ty) (aU : fuel) : ty :=
  TBox m 0 C None (Some 0) tid (TLolli ub None None tz (Some 0) T aT U aU) None.

Lemma lbox_typed W N Γ n F m C ub T aT U aU e c t :
  hc_fv Γ = ∅ → pinst_ty (pshift m) (lbox m C ub T aT U aU) = lbox m C ub T aT U aU →
  typed W N ∅ (hc_fvar 1 ub (hc_fvar 0 None (hc_open m C Γ)))
    (Some (T, aT) :: Some (lbox m C ub T aT U aU, None) :: nones n) (∅, Some (FVar 1)) e U aU c t →
  t.2 = Some 0 →
  typed W N ∅ Γ (nones n) F (EBox (Lam e)) (lbox m C ub T aT U aU) None (Some 0) tid.
Proof.
  intros HΓ HB He Ht. unfold lbox at 1. eapply e_box with (φ := 0).
  { intros o Ho. apply elem_of_replicate in Ho as [-> _]. by left. }
  { unfold hc_open. simpl. rewrite HΓ. unfold fhyps_pinst. rewrite fmap_empty. set_solver. }
  intros ss Hk _. destruct ss; [|done]. rewrite sinst_nil.
  rewrite lenv_pinst_cons'. cbn [fmap option_fmap option_map]. fold (lbox m C ub T aT U aU).
  rewrite HB, lenv_pinst_nones.
  eapply e_abs with (φ := 1) (h := Some 0) (a := None) (Θh := ∅).
  { unfold hc_fvar. simpl. rewrite HΓ. unfold fhyps_pinst.
    rewrite fmap_empty, insert_empty, dom_singleton_L. set_solver. }
  { apply lb_below_none. spare_tac. }
  { intros o. by rewrite !lookup_empty. }
  { apply lcap_some; [apply cap_free; constructor|apply lcap_nones]. }
  eapply e_sub; [exact He|apply tsub_refl|apply fle_inf|by apply tle_tz].
Qed.

Lemma lbox_force W N Γ Δ F e m C ub T aT U aU xs a c0 t0 :
  length xs = m → hold_at W Γ C xs →
  typed W N ∅ Γ Δ F e (lbox m C ub T aT U aU) a c0 t0 →
  typed W N ∅ Γ Δ F (EForce e)
    (TLolli (pt_inst (plist xs) <$> ub) None None tz (Some 0) (ty_inst xs T) aT (ty_inst xs U) aU)
    None (fadd c0 (Some 0)) (tseq t0 tid).
Proof.
  intros Hm HC He.
  rewrite <-(sinst_nil (TLolli _ _ _ _ _ _ _ _ _)).
  eapply (e_force W N ∅ Γ Δ F e m 0 C None (Some 0) tid
            (TLolli ub None None tz (Some 0) T aT U aU) None a xs []);
    first [done | split; [apply Forall_nil|intros _; apply Forall_nil] | left; done].
Qed.

(** The force at a list of points, with the instantiated types given. *)
Lemma lbox_force_eq W N Γ Δ F e m C ub T aT U aU xs a c0 t0 ub' T' U' :
  length xs = m → hold_at W Γ C xs →
  (pt_inst (plist xs) <$> ub) = ub' → ty_inst xs T = T' → ty_inst xs U = U' →
  typed W N ∅ Γ Δ F e (lbox m C ub T aT U aU) a c0 t0 →
  typed W N ∅ Γ Δ F (EForce e) (TLolli ub' None None tz (Some 0) T' aT U' aU)
    None (fadd c0 (Some 0)) (tseq t0 tid).
Proof. intros ?? <- <- <-. by apply lbox_force. Qed.
