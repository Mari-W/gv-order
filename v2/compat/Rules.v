(** * The operator rules, for every cost table (stage S4)

    Each typing rule of a saturated operator (E-Send, E-Recv, E-Close,
    E-Select, E-Branch, E-Link, E-Spawn, E-Force, E-NewAt) and E-New is
    valid for the semantic judgment at a set of points, for every cost
    table ([gen_e_*]). The proof is the bind lemma at the frame of the
    operator, which holds no end, and the redex of compat/Redex.v.
    [sem_e_*] and [live_e_*] are the instances κ_DF and κ_L (A.4).

    The rules are stated at the set form [sem_typed_at], with the facts
    of the typing rule read in W. The static facts Γ ⊢ x ≺ y of S2 and
    the static future reach this form in stage S5, by instantiating the
    future variables and the point variables of Γ. *)

From GV Require Export compat.SemTyped compat.Redex.

Section rules.
  Context (κ : ctable).

  Lemma sem_op k W Θ Δ F e Targ Tres :
    (∀ W' j Θv v, W ⊑ W' → Vrel κ j W' Θv Targ v → Erel κ j W' Θv Tres F (Op k v)) →
    sem_typed_at κ W Θ Δ F e Targ → sem_typed_at κ W Θ Δ F (Op k e) Tres.
  Proof.
    intros Hred He n W' Θ' γ HW Hd HG. simpl.
    rewrite <-(map_union_empty (tenv_erase Θ ∪ Θ')).
    apply (Erel_bind κ n (FOp k) W' _ ∅ Targ Tres F (subst γ e)); [done|apply map_disjoint_empty_r| |].
    - rewrite senv_heads_empty, union_empty_r_L. by apply He.
    - intros W'' j Θv v HW' _ _ Hv. rewrite map_union_empty. apply Hred; [by eapply wext_trans|done].
  Qed.

  Local Ltac lt_mono := intros; eapply w_lt_mono; [eassumption|]; auto.

  Lemma gen_e_send W Θ Δ F e S0 x m U b S ap aS :
    unfoldS S0 = SSeq (SSnd m U b) S → hbot (payload_at m U x) = false →
    (∀ y, y ∈ heads (payload_at m U x) → W ⊢ x ≺ y) → (∀ y, y ∈ F → W ⊢ x ≺ y) →
    sem_typed_at κ W Θ Δ F e (TProd (payload_at m U x) ap (TSess S0 x) aS) →
    sem_typed_at κ W Θ Δ F (ESend e) (TSess S x⁺).
  Proof.
    intros Hu Hb Hh HF. apply sem_op. intros W' j Θv v HW Hv.
    eapply Erel_send; [done|done| | |exact Hv]; lt_mono.
  Qed.

  Lemma gen_e_recv W Θ Δ F e S0 x m U b S b' a' :
    unfoldS S0 = SSeq (SRcv m U b) S → (∀ y, y ∈ F → W ⊢ x ≺ y) →
    sem_typed_at κ W Θ Δ F e (TSess S0 x) →
    sem_typed_at κ W Θ Δ F (ERecv e) (TProd (payload_at m U x) b' (TSess S x⁺) a').
  Proof.
    intros Hu HF. apply sem_op. intros W' j Θv v HW Hv.
    eapply Erel_recv; [done| |exact Hv]; lt_mono.
  Qed.

  Lemma gen_e_close W Θ Δ F e S0 x :
    unfoldS S0 = SEnd → (∀ y, y ∈ F → W ⊢ x ≺ y) →
    sem_typed_at κ W Θ Δ F e (TSess S0 x) → sem_typed_at κ W Θ Δ F (EClose e) TUnit.
  Proof.
    intros Hu HF. apply sem_op. intros W' j Θv v HW Hv.
    eapply Erel_close; [done| |exact Hv]; lt_mono.
  Qed.

  Lemma gen_e_select (i : bool) W Θ Δ F e S0 x S1 S2 :
    unfoldS S0 = SPlus S1 S2 → (∀ y, y ∈ F → W ⊢ x ≺ y) →
    sem_typed_at κ W Θ Δ F e (TSess S0 x) →
    sem_typed_at κ W Θ Δ F (ESel i e) (TSess (if i then S2 else S1) (sel_pt x i)).
  Proof.
    intros Hu HF. apply sem_op. intros W' j Θv v HW Hv.
    eapply Erel_select; [done| |exact Hv]; lt_mono.
  Qed.

  Lemma gen_e_branch W Θ Δ F e S0 x S1 S2 a1 a2 :
    unfoldS S0 = SWith S1 S2 → (∀ y, y ∈ F → W ⊢ x ≺ y) →
    sem_typed_at κ W Θ Δ F e (TSess S0 x) →
    sem_typed_at κ W Θ Δ F (EBra e) (TSum (TSess S1 (bra_pt x false)) a1 (TSess S2 (bra_pt x true)) a2).
  Proof.
    intros Hu HF. apply sem_op. intros W' j Θv v HW Hv.
    eapply Erel_branch; [done| |exact Hv]; lt_mono.
  Qed.

  Lemma gen_e_link W Θ Δ F e S x a1 a2 :
    sem_typed_at κ W Θ Δ F e (TProd (TSess S x) a1 (TSess (dual S) x‾) a2) →
    sem_typed_at κ W Θ Δ F (ELink e) TUnit.
  Proof. apply sem_op. intros W' j Θv v HW Hv. by eapply Erel_link. Qed.

  Lemma gen_e_spawn W Θ Δ F e ub lb c t h a1 aU :
    sem_typed_at κ W Θ Δ F e (TLolli ub lb c t h TUnit a1 TUnit aU) →
    sem_typed_at κ W Θ Δ F (ESpawn e) TUnit.
  Proof. apply sem_op. intros W' j Θv v HW Hv. by eapply Erel_spawn. Qed.

  Lemma gen_e_new_at (κf : field) W Θ Δ F e S0 x S a a1 a2 a3 :
    sem_typed_at κ W Θ Δ F e (TSess S0 x) →
    sem_typed_at κ W Θ Δ F (ENewAt κf e)
      (TProd (TSess S0 x) a (TProd (TSess S (x·κf)) a1 (TSess (dual S) (x·κf)‾) a2) a3).
  Proof. apply sem_op. intros W' j Θv v HW Hv. by eapply Erel_new_at. Qed.

  Lemma gen_e_force W Θ Δ F e m kk C ub c t U a xs ss :
    length xs = m → length ss = kk → Forall hcontractive ss → wholds W C xs →
    ub_lt W (pt_inst (plist xs) <$> ub) F →
    sem_typed_at κ W Θ Δ F e (TBox m kk C ub c t U a) →
    sem_typed_at κ W Θ Δ F (EForce e) (sinst_ty (slist ss) (ty_inst xs U)).
  Proof.
    intros Hxs Hss Hsc HC Hub. apply sem_op. intros W' j Θv v HW Hv.
    pose proof Hv as Hv'. apply Vrel_box_iff in Hv' as [-> _].
    eapply Erel_force; [done|done|done| | |exact Hv].
    - by eapply wholds_mono.
    - by eapply ub_lt_mono.
  Qed.

  Lemma gen_e_new (ℓ : family) W Δ F S a1 a2 a3 :
    lenv_empty Δ → ℓ ∈ w_fams W →
    sem_typed_at κ W ∅ Δ F (ENew ℓ)
      (TEx LBot 1 (bcs_of (w_laws W ℓ)) (TProd (TSess S (pvar 0)) a1 (TSess (dual S) (pvar 0)‾) a2) a3).
  Proof.
    intros HΔ Hℓ n W' Θ' γ HW Hd HG. simpl.
    rewrite (Grel_empty κ _ _ _ _ _ HΔ HG). unfold tenv_erase. rewrite fmap_empty, map_union_empty.
    apply Erel_new_sub.
    - by apply (wext_fams _ _ HW).
    - intros f Hf. by apply (wext_laws _ _ HW).
  Qed.
End rules.

(** ** The instances (A.4) *)

Definition sem_e_send := gen_e_send κ_DF.
Definition sem_e_recv := gen_e_recv κ_DF.
Definition sem_e_close := gen_e_close κ_DF.
Definition sem_e_select := gen_e_select κ_DF.
Definition sem_e_branch := gen_e_branch κ_DF.
Definition sem_e_link := gen_e_link κ_DF.
Definition sem_e_spawn := gen_e_spawn κ_DF.
Definition sem_e_new_at := gen_e_new_at κ_DF.
Definition sem_e_force := gen_e_force κ_DF.
Definition sem_e_new := gen_e_new κ_DF.

Definition live_e_send := gen_e_send κ_L.
Definition live_e_recv := gen_e_recv κ_L.
Definition live_e_close := gen_e_close κ_L.
Definition live_e_select := gen_e_select κ_L.
Definition live_e_branch := gen_e_branch κ_L.
Definition live_e_link := gen_e_link κ_L.
Definition live_e_spawn := gen_e_spawn κ_L.
Definition live_e_new_at := gen_e_new_at κ_L.
Definition live_e_force := gen_e_force κ_L.
Definition live_e_new := gen_e_new κ_L.
