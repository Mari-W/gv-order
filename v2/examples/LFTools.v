(** * Tools for lock-free example derivations (stage S9)

    A closed program t is lock free by [lf_soundness] when it types at a
    finite bound N with the empty future, is guarded and lives in a
    well-formed, well-founded static world ([lf_main]). The constraints
    of the creations meet (wf-new) by lexicographic measures
    ([wf_new_lex3], examples/Tools.v). *)

From GV Require Export examples.Tools2.
From GV Require Export soup.LFTyped.
From GV Require lockfree.FairRun.

(** The classical hypotheses of lock-free adequacy, by name. *)
Notation excluded_middle := lockfree.FairRun.excluded_middle.
Notation functional_choice := lockfree.FairRun.functional_choice.

(** ** Closed programs *)

Lemma lf_main_typed N W t T c :
  sworld_wf W ∧ swf W → tfree T → typed W (Some N) ∅ hc_empty [] (∅, None) t T c →
  ∅ ⊢▷ t → ∅ ⊩^N _ W (∅, {[+ t +]}) : T.
Proof.
  intros HS Hp Ht Hg. split.
  - apply (fp_term (Some N) W ∅ ∅ ∅ t T c); [done| | | | | | |done].
    6: { unfold tenv_of. rewrite fmap_empty, map_union_empty. exact Ht. }
    + intros o. rewrite dom_empty_L. set_solver.
    + set_solver.
    + apply pfree_empty.
    + intros o e He. by rewrite lookup_empty in He.
    + set_solver.
  - intros t' Ht'. simpl in Ht'. apply gmultiset_elem_of_singleton in Ht' as ->. done.
Qed.

Lemma lf_main (EM : excluded_middle) (FC : functional_choice) N W t T c :
  sworld_wf W ∧ swf W → tfree T → typed W (Some N) ∅ hc_empty [] (∅, None) t T c →
  ∅ ⊢▷ t → lock_free (∅, {[+ t +]}).
Proof. intros HS Hp Ht Hg. eapply (lf_soundness N W _ T EM FC), lf_main_typed; eauto. Qed.

(** ** Rules of the merged judgment with weakening built in *)

Lemma e_var' W N Γ Δ F x T :
  Δ !! x = Some (Some T) → (∀ y o, y ≠ x → Δ !! y = Some o → spare o) →
  typed W N ∅ Γ Δ F (Var x) T (Some 0).
Proof.
  intros Hx Hs. eapply e_var. by apply spare_only.
Qed.

Lemma e_unit' W N Γ Δ F : (∀ y o, Δ !! y = Some o → spare o) →
  typed W N ∅ Γ Δ F EUnit TUnit (Some 0).
Proof. intros H. by apply e_unit, spare_unl. Qed.

Lemma e_new' W N Γ Δ F (L : fact → Prop) S :
  (∀ y o, Δ !! y = Some o → spare o) → wf_new (bcs_of L) → scontr S →
  typed W N ∅ Γ Δ F ENew (TEx LBot 1 (bcs_of L)
    (TProd (TSess S (pvar 0) (fhalf N) (fhalf N)) (TSess (dual S) (pvar 0)‾ (ncap N (fhalf N)) (ncap N (fhalf N))))) (Some 0).
Proof. intros H HL HS. apply e_new; [by apply spare_unl|by apply gen_new_ok, wf_new_gen|apply tsum_half|done]. Qed.

(** A creation at the field κ of the point x of the end y, ⟨y, new⟩, at
    the tickets m of the anchor and N − m. *)
Lemma e_new_at' W N (Θ : tenv) Γ Δ F (y : nat) κ S0 x a m S :
  Θ = ∅ → fle m N → Δ !! y = Some (Some (TSess S0 x a m)) → (∀ z o, z ≠ y → Δ !! z = Some o → spare o) →
  scontr S →
  typed W N Θ Γ Δ F (Pair (Var y) ENew)
    (TProd (TSess S0 x a m) (TProd (TSess S (x·κ) m m) (TSess (dual S) (x·κ)‾ (ncap N m) (ncap N m)))) (Some 0).
Proof.
  intros -> Hm Hy Hs HS. rewrite <-(fadd_0_r (Some 0)).
  eapply (e_pair _ _ ∅ ∅ ∅ ∅); [apply tsplit_empty|apply (lsplit_only y), Hs| |intros o; by rewrite lookup_empty|apply lage_0| |apply tage_0].
  - eapply e_var'; [exact Hy|exact Hs].
  - apply e_new_fld; [by apply lenv_unl_only|by apply tsum_ncap|done].
Qed.

(** E-New at any tickets m1 + m2 ≤ N. *)
Lemma e_new_tk W N Γ Δ F (L : fact → Prop) S m1 m2 :
  (∀ y o, Δ !! y = Some o → spare o) → wf_new (bcs_of L) → tsum_ok N m1 m2 → scontr S →
  typed W N ∅ Γ Δ F ENew (TEx LBot 1 (bcs_of L)
    (TProd (TSess S (pvar 0) m1 m1) (TSess (dual S) (pvar 0)‾ m2 m2))) (Some 0).
Proof. intros H HL Hm HS. apply e_new; [by apply spare_unl|by apply gen_new_ok, wf_new_gen|done|done]. Qed.

Lemma thage_empty c : thage c ∅ ∅.
Proof. intros o. by rewrite lookup_empty. Qed.

(** The rules with two operands over Θ = ∅, the premises in the order
    a derivation meets them: the first operand fixes the cost that ages
    the context of the second. *)

Lemma e_let_ W N Γ Δ Δ1 Δ2 Δ2' F e1 e2 T1 T c1 c2 :
  lenv_split Δ Δ1 Δ2 →
  typed W N ∅ Γ Δ1 (sf_unionb F (tenv_heads ∅ ∪ lenv_heads Δ2) (lenv_bot Δ2)) e1 T1 c1 →
  lage c1 Δ2 Δ2' →
  typed W N ∅ Γ (Some T1 :: Δ2') F e2 T c2 →
  typed W N ∅ Γ Δ F (ELet e1 e2) T (fadd c1 c2).
Proof. intros. eapply e_let; eauto using tsplit_empty, thage_empty. Qed.

Lemma e_letu_ W N Γ Δ Δ1 Δ2 Δ2' F e1 e2 T c1 c2 :
  lenv_split Δ Δ1 Δ2 →
  typed W N ∅ Γ Δ1 (sf_unionb F (tenv_heads ∅ ∪ lenv_heads Δ2) (lenv_bot Δ2)) e1 TUnit c1 →
  lage c1 Δ2 Δ2' →
  typed W N ∅ Γ Δ2' F e2 T c2 →
  typed W N ∅ Γ Δ F (LetU e1 e2) T (fadd c1 c2).
Proof. intros. eapply e_letu; eauto using tsplit_empty, thage_empty. Qed.

Lemma e_letp_ W N Γ Δ Δ1 Δ2 Δ2' F e1 e2 T1 T2 T c1 c2 :
  lenv_split Δ Δ1 Δ2 →
  typed W N ∅ Γ Δ1 (sf_unionb F (tenv_heads ∅ ∪ lenv_heads Δ2) (lenv_bot Δ2)) e1 (TProd T1 T2) c1 →
  lage c1 Δ2 Δ2' →
  typed W N ∅ Γ (Some T2 :: Some T1 :: Δ2') F e2 T c2 →
  typed W N ∅ Γ Δ F (LetP e1 e2) T (fadd c1 c2).
Proof. intros. eapply e_letp; eauto using tsplit_empty, thage_empty. Qed.

Lemma e_pair_ W N Γ Δ Δ1 Δ2 Δ2' F e1 e2 T1 T1' T2 c1 c2 :
  lenv_split Δ Δ1 Δ2 →
  typed W N ∅ Γ Δ1 (sf_unionb F (tenv_heads ∅ ∪ lenv_heads Δ2) (lenv_bot Δ2)) e1 T1 c1 →
  lage c1 Δ2 Δ2' →
  typed W N ∅ Γ Δ2' (sf_unionb F (heads T1) (hbot T1)) e2 T2 c2 →
  tage c2 T1 T1' →
  typed W N ∅ Γ Δ F (Pair e1 e2) (TProd T1' T2) (fadd c1 c2).
Proof. intros. eapply e_pair; eauto using tsplit_empty, thage_empty. Qed.

Lemma e_app_ W N Γ Δ Δ1 Δ2 Δ2' F e1 e2 ub lb c T U a1 c1 c2 :
  lenv_split Δ Δ1 Δ2 → ub_below_u W Γ ub F →
  typed W N ∅ Γ Δ1 (sf_unionb F (tenv_heads ∅ ∪ lenv_heads Δ2) (lenv_bot Δ2)) e1 (TLolli ub lb c T U a1) c1 →
  lage c1 Δ2 Δ2' →
  typed W N ∅ Γ Δ2' (sf_unionb F (lb_heads lb) (lb_bot lb)) e2 T c2 →
  fle c2 a1 →
  typed W N ∅ Γ Δ F (App e1 e2) U (fadd c1 (fadd c2 c)).
Proof. intros. eapply e_app; eauto using tsplit_empty, thage_empty. Qed.

(** A pair of ends whose credits fall. *)
Lemma e_sub_sess2 W N Γ Δ F e S1 x S2 y a1 a2 b1 b2 c m1 m2 :
  typed W N ∅ Γ Δ F e (TProd (TSess S1 x a1 m1) (TSess S2 y a2 m2)) c →
  fle b1 a1 → fle b2 a2 →
  typed W N ∅ Γ Δ F e (TProd (TSess S1 x b1 m1) (TSess S2 y b2 m2)) c.
Proof.
  intros He H1 H2. eapply e_sub; [exact He| |apply fle_refl|intros HC; exact HC].
  apply sub_prod; apply sub_sess; rewrite ?fadd_0_l; auto using sequiv_refl.
Qed.

(** ** Tactics *)

(** Aging a concrete entry: free, by its credit, an idle end by
    truncation, or by its parts. *)
Ltac age_tac :=
  first [ solve [apply age_free; repeat constructor]
        | apply age_sess; simpl; lia
        | apply age_arr; simpl; lia
        | apply age_idle; reflexivity
        | apply age_prod; age_tac
        | apply age_ex; age_tac ].

Ltac lage_tac :=
  solve [repeat first [ apply lage_nones | apply lage_nil | apply lage_none
                      | apply lage_some; [age_tac|] ]].

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
  first [ apply gl_var; reflexivity | apply gl_unit | apply gl_chan | apply gl_new
        | apply gl_lam; guard_tac | apply gl_box; guard_tac
        | apply gl_op; guard_tac
        | apply gl_tick_app; [guard_tac|acts_tac|guard_tac] | eapply gl_app; [guard_tac|left; reflexivity|guard_tac]
        | apply gl_tick_pair; [guard_tac|acts_tac|guard_tac] | eapply gl_pair; [guard_tac|left; reflexivity|guard_tac]
        | apply gl_tick_letu; [guard_tac|acts_tac|guard_tac] | eapply gl_letu; [guard_tac|left; reflexivity|guard_tac]
        | apply gl_tick_letp; [guard_tac|acts_tac|guard_tac] | eapply gl_letp; [guard_tac|left; reflexivity|guard_tac]
        | apply gl_tick_let; [guard_tac|acts_tac|guard_tac] | apply gl_let; guard_tac
        | apply gl_inj; guard_tac
        | eapply gl_case; [guard_tac|left; reflexivity|guard_tac|guard_tac] ].

(** ** Boxes of one arrow

    □∀ιs. C. (T ⊸^ub U)^∞ with box cost 0. The arrow has cost ∞. A call
    is then a last step of its thread or of a box body: whatever is held
    across it would age by ∞. *)

Definition lbox (m : nat) (C : bcs) (ub : option point) (T U : ty) : ty :=
  TBox m 0 C None (Some 0) (TLolli (ubound_of ub) LNone None T U None).

Lemma lbox_typed W N Γ n F m C ub T U e c :
  tcontr T → tcontr U →
  pinst_ty (pshift m) (lbox m C ub T U) = lbox m C ub T U →
  typed W N ∅ (hc_open m C Γ) (Some T :: Some (lbox m C ub T U) :: nones n) (∅, Some (FRest (rest_of ub))) e U c →
  typed W N ∅ Γ (nones n) F (EBox (Lam e)) (lbox m C ub T U) (Some 0).
Proof.
  intros HT HU HB He. unfold lbox at 1. eapply e_box.
  { intros o Ho. apply elem_of_replicate in Ho as [-> _]. by left. }
  { cbn [tcontr]. by apply Is_true_andb. }
  intros ss Hk _. destruct ss; [|done]. rewrite sinst_nil.
  rewrite lenv_pinst_cons'. cbn [fmap option_fmap option_map]. fold (lbox m C ub T U).
  rewrite HB, lenv_pinst_nones.
  eapply e_abs with (a := None) (Θh := ∅); rewrite ?abs_fut_of.
  { apply lb_below_none. spare_tac. }
  { intros o. by rewrite !lookup_empty. }
  { apply lage_some; [apply age_free; constructor|apply lage_nones]. }
  { done. }
  eapply e_sub; [exact He|apply tsub_refl|apply fle_inf|by intros].
Qed.

Lemma lbox_force W N Γ Δ F e m C ub T U xs c0 :
  length xs = m → hold_at W Γ C xs →
  typed W N ∅ Γ Δ F e (lbox m C ub T U) c0 →
  typed W N ∅ Γ Δ F (EForce e) (TLolli (ubound_of (pt_inst (plist xs) <$> ub)) LNone None (ty_inst xs T) (ty_inst xs U) None) (fadd c0 (Some 0)).
Proof.
  intros Hm HC He. rewrite <-ub_map_of.
  rewrite <-(sinst_nil (TLolli _ _ _ _ _ _)).
  eapply (e_force W N ∅ Γ Δ F e m 0 C None (Some 0)
            (TLolli (ubound_of ub) LNone None T U None) xs []);
    first [done | split; [split; apply Forall_nil|intros _; apply Forall_nil] | left; done].
Qed.

(** The force at a list of points, with the instantiated types given. *)
Lemma lbox_force_eq W N Γ Δ F e m C ub T U xs c0 ub' T' U' :
  length xs = m → hold_at W Γ C xs →
  ubound_of (pt_inst (plist xs) <$> ub) = ub' → ty_inst xs T = T' → ty_inst xs U = U' →
  typed W N ∅ Γ Δ F e (lbox m C ub T U) c0 →
  typed W N ∅ Γ Δ F (EForce e) (TLolli ub' LNone None T' U' None) (fadd c0 (Some 0)).
Proof. intros ?? <- <- <-. by apply lbox_force. Qed.
