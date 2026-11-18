(** * P-Connect, links (stage S4)

    The step clause of the composite for a link of a thread whose
    removed channel lies outside its own component, in the context of
    compat/ConnectSteps.v. *)

From GV Require Export compat.ConnectSteps compat.ConnectRen.
From GV Require Import fuel.FuelMono.

Lemma gch_csub o1 o2 c : gch (csub o1 o2) c = if decide (c = ech o1) then ech o2 else c.
Proof.
  unfold gch. case_decide as Hc.
  - subst. destruct (csub_cases o1 o2 (EPos (ech o1))) as [(E & ->)|[(E & ->)|(N1 & N2 & _)]]; [done|by rewrite ech_edual|].
    exfalso. destruct o1; simpl in *; congruence.
  - rewrite csub_ne; [done|done].
Qed.

Lemma set_map_gch_csub o1 o2 (X : gset chan) :
  set_map (gch (csub o1 o2)) X = X ∖ {[ech o1]} ∪ (if decide (ech o1 ∈ X) then {[ech o2]} else ∅).
Proof.
  apply set_eq. intros c. rewrite elem_of_map. split.
  - intros (c0 & -> & H). rewrite gch_csub. case_decide; subst; case_decide; set_solver.
  - intros H. case_decide as Hin.
    + apply elem_of_union in H as [H|H].
      * exists c. rewrite gch_csub, decide_False; set_solver.
      * exists (ech o1). rewrite gch_csub, decide_True; set_solver.
    + exists c. rewrite gch_csub, decide_False; set_solver.
Qed.

Lemma chans_of_kren h (X : senv) : dcomm h → kinj h X → chans_of (kren h X) = set_map (gch h) (chans_of X).
Proof.
  intros Hd Hk. apply set_eq. intros c. rewrite elem_of_chans_of_iff, elem_of_map. setoid_rewrite elem_of_chans_of_iff.
  rewrite kren_dom by done. split.
  - intros (o & (a & -> & Ha)%elem_of_map & <-). exists (ech a). rewrite ech_gch by done. eauto.
  - intros (c0 & -> & (a & Ha & <-)). exists (h a). rewrite ech_gch by done. split; [by apply elem_of_map_2|done].
Qed.

Lemma chan_eq_own o1 o2 (A B K : gset chan) : ech o1 ∉ A → ech o2 ∈ A → ech o1 ∈ B ∪ K → ech o1 ≠ ech o2 →
  (A ∪ B ∪ K) ∖ {[ech o1]} =
  set_map (gch (csub o1 o2)) (A ∖ {[ech o2]}) ∪ set_map (gch (csub o1 o2)) B ∪ set_map (gch (csub o1 o2)) K.
Proof.
  intros H1 H2 H3 H4. rewrite !set_map_gch_csub. repeat case_decide.
  all: apply set_eq; intros c; destruct (decide (c = ech o2)) as [E2|N2]; [subst c|]; set_solver.
Qed.

Lemma chan_eq_own2 o1 o2 (A B K : gset chan) : ech o1 ∉ B → ech o2 ∈ B → ech o1 ∈ A ∪ K → ech o1 ≠ ech o2 →
  (A ∪ B ∪ K) ∖ {[ech o1]} =
  set_map (gch (csub o1 o2)) A ∪ set_map (gch (csub o1 o2)) (B ∖ {[ech o2]}) ∪ set_map (gch (csub o1 o2)) K.
Proof.
  intros H1 H2 H3 H4. rewrite !set_map_gch_csub. repeat case_decide.
  all: apply set_eq; intros c; destruct (decide (c = ech o2)) as [E2|N2]; [subst c|]; set_solver.
Qed.

Lemma soup_emap (g : cend → cend) M : soup (emap g <$> M) = emapE g (soup M).
Proof. apply soup_fmap. Qed.

Section links.
  Context (κ : ctable) (n : nat) (W1 : world) (HS : strict W1) (T : ty) (HT : prim T) (X1 X2 : prel).
  Context (Σ1 ΣC Σ2 ΣD : senv) (q1 q2 : proc) (Hc : conn Σ1 ΣC q1.1 Σ2 ΣD q2.1).
  Context (H1 : Pclauses κ (S n) (Vrel κ) (Prel κ) (Vrel κ (S n)) X1 W1 (Σ1 ∪ ΣC) T q1).
  Context (H2 : Pclauses κ (S n) (Vrel κ) (Prel κ) (Vrel κ (S n)) X2 W1 (Σ2 ∪ ΣD) TUnit q2).
  Context (L : ∀ j, j < S n → ConnL κ j W1 T).
  Context (X1P : ∀ W Σ T p, X1 W Σ T p → Prel κ (S n) W Σ T p).
  Context (X2P : ∀ W Σ T p, X2 W Σ T p → Prel κ (S n) W Σ T p).
  Context (HP1 : ∀ h D, fuse_ok h D (Σ1 ∪ ΣC) q1 →
    Prel κ (S n) W1 (sdrop D (kren h (Σ1 ∪ ΣC))) T (pfuse h D q1)).
  Context (HP2 : ∀ h D, fuse_ok h D (Σ2 ∪ ΣD) q2 →
    Prel κ (S n) W1 (sdrop D (kren h (Σ2 ∪ ΣD))) TUnit (pfuse h D q2)).
  Context (G1 : ∀ p1' Σa h D Σ1' ΣC' Σ2' ΣD' p2', X1 W1 Σa T p1' → fuse_ok h D Σa p1' →
    sdrop D (kren h Σa) = Σ1' ∪ ΣC' → Prel κ (S n) W1 (Σ2' ∪ ΣD') TUnit p2' →
    conn Σ1' ΣC' (pfuse h D p1').1 Σ2' ΣD' p2'.1 →
    Prel κ (S n) W1 (Σ1' ∪ Σ2') T (pconn (pfuse h D p1') p2' (chans_of ΣC'))).
  Context (G2 : ∀ p2' Σb h D Σ1' ΣC' Σ2' ΣD' h1 D1, X2 W1 Σb TUnit p2' → fuse_ok h D Σb p2' →
    sdrop D (kren h Σb) = Σ2' ∪ ΣD' → fuse_ok h1 D1 (Σ1 ∪ ΣC) q1 →
    sdrop D1 (kren h1 (Σ1 ∪ ΣC)) = Σ1' ∪ ΣC' →
    conn Σ1' ΣC' (pfuse h1 D1 q1).1 Σ2' ΣD' (pfuse h D p2').1 →
    Prel κ (S n) W1 (Σ1' ∪ Σ2') T (pconn (pfuse h1 D1 q1) (pfuse h D p2') (chans_of ΣC'))).
  Local Abbreviation K := (chans_of ΣC).
  Local Abbreviation pc := (pconn q1 q2 K).

  Local Lemma KD : chans_of ΣD = K.
  Proof. destruct Hc as [_ _ Hcut _ _ _ _ _ _ _ _ _]. by apply cut_dual_chans. Qed.

  Local Lemma kren_split h (Σa Σb : senv) : pren_ok h (Σa ∪ Σb) (∅, ∅) ∨ True → kinj h (Σa ∪ Σb) →
    (∀ o, o ∈ dom Σa → h o = o) → kren h (Σa ∪ Σb) = Σa ∪ kren h Σb.
  Proof. intros _ Hk Hf. rewrite kren_union by done. f_equal. by apply kren_id. Qed.

  (** A renaming of the composite after a step of p1 alone. *)
  Lemma ren_comp1 c p1' h :
    at_cost_P (S n) c (Prel κ) X1 W1 (Σ1 ∪ ΣC) T p1' →
    conn Σ1 ΣC p1'.1 Σ2 ΣD q2.1 →
    pren_ok h (Σ1 ∪ Σ2) (pconn p1' q2 K) →
    (∀ o, o ∈ dom (Σ1 ∪ Σ2) → h o = o) →
    at_cost_P (S n) c (Prel κ) (Prel κ (S n)) W1 (Σ1 ∪ Σ2) T (pconn (pmap h p1') (pmap h q2) (set_map (gch h) K)).
  Proof.
    intros [A0 A1] Hc1 Hok Hfix.
    assert (pren_ok h (Σ1 ∪ ΣC) p1') as Hok1 by (eapply pren_ok_sub; [exact Hok|]; intros o; apply pheld_pconn_1).
    assert (pren_ok h (Σ2 ∪ ΣD) q2) as Hok2.
    { eapply pren_ok_sub; [exact Hok|]. intros o Ho. rewrite pconn_sym, (map_union_comm Σ1 Σ2).
      - rewrite <-KD. apply pheld_pconn_1. done.
      - apply chans_disj_map. by destruct Hc. }
    assert (∀ o, o ∈ dom Σ1 → h o = o) as F1 by (intros o Ho; apply Hfix; rewrite dom_union_L; set_solver).
    assert (∀ o, o ∈ dom Σ2 → h o = o) as F2 by (intros o Ho; apply Hfix; rewrite dom_union_L; set_solver).
    assert (kren h (Σ1 ∪ ΣC) = Σ1 ∪ kren h ΣC) as E1 by (apply kren_split; [by right|by eapply pren_ok_kinj|done]).
    assert (kren h (Σ2 ∪ ΣD) = Σ2 ∪ kren h ΣD) as E2 by (apply kren_split; [by right|by eapply pren_ok_kinj|done]).
    pose proof (conn_rename Σ1 ΣC Σ2 ΣD p1'.1 q2.1 Hc1 h (p1'.2 ⊎ q2.2) Hok Hfix) as Hc'.
    assert (chans_of (kren h ΣC) = set_map (gch h) K) as HK.
    { apply chans_of_kren; [by destruct Hok|]. intros a b va vb Ha Hb. apply Hok; apply pheld_pconn_1; left;
        rewrite dom_union_L; apply elem_of_union_r; by eapply elem_of_dom_2. }
    assert (Prel κ (S n) W1 (Σ2 ∪ kren h ΣD) TUnit (pmap h q2)) as P2.
    { pose proof (HP2 h ∅ (pren_fuse_ok _ _ _ Hok2)) as H. by rewrite sdrop_empty, E2, pfuse_empty in H. }
    rewrite <-HK. split.
    - intros Hc0. pose proof (G1 p1' (Σ1 ∪ ΣC) h ∅ Σ1 (kren h ΣC) Σ2 (kren h ΣD) (pmap h q2) (A0 Hc0) (pren_fuse_ok _ _ _ Hok1)) as HG.
      rewrite sdrop_empty, pfuse_empty in HG. apply HG; [done|done|done].
    - intros Hc0. apply (L (S n - c) ltac:(lia) Σ1 (kren h ΣC) Σ2 (kren h ΣD)); [|eapply Prel_down; [|exact P2]; lia|done].
      rewrite <-E1. apply Prel_rename; [done|by apply A1].
  Qed.

  (** A renaming of the composite after a step of p2 alone. *)
  Lemma ren_comp2 c p2' h :
    at_cost_P (S n) c (Prel κ) X2 W1 (Σ2 ∪ ΣD) TUnit p2' →
    conn Σ1 ΣC q1.1 Σ2 ΣD p2'.1 →
    pren_ok h (Σ1 ∪ Σ2) (pconn q1 p2' K) →
    (∀ o, o ∈ dom (Σ1 ∪ Σ2) → h o = o) →
    at_cost_P (S n) c (Prel κ) (Prel κ (S n)) W1 (Σ1 ∪ Σ2) T (pconn (pmap h q1) (pmap h p2') (set_map (gch h) K)).
  Proof.
    intros [A0 A1] Hc2 Hok Hfix.
    assert (pren_ok h (Σ1 ∪ ΣC) q1) as Hok1 by (eapply pren_ok_sub; [exact Hok|]; intros o; apply pheld_pconn_1).
    assert (pren_ok h (Σ2 ∪ ΣD) p2') as Hok2.
    { eapply pren_ok_sub; [exact Hok|]. intros o Ho. rewrite pconn_sym, (map_union_comm Σ1 Σ2).
      - rewrite <-KD. apply pheld_pconn_1. done.
      - apply chans_disj_map. by destruct Hc. }
    assert (∀ o, o ∈ dom Σ1 → h o = o) as F1 by (intros o Ho; apply Hfix; rewrite dom_union_L; set_solver).
    assert (∀ o, o ∈ dom Σ2 → h o = o) as F2 by (intros o Ho; apply Hfix; rewrite dom_union_L; set_solver).
    assert (kren h (Σ1 ∪ ΣC) = Σ1 ∪ kren h ΣC) as E1 by (apply kren_split; [by right|by eapply pren_ok_kinj|done]).
    assert (kren h (Σ2 ∪ ΣD) = Σ2 ∪ kren h ΣD) as E2 by (apply kren_split; [by right|by eapply pren_ok_kinj|done]).
    pose proof (conn_rename Σ1 ΣC Σ2 ΣD q1.1 p2'.1 Hc2 h (q1.2 ⊎ p2'.2) Hok Hfix) as Hc'.
    assert (chans_of (kren h ΣC) = set_map (gch h) K) as HK.
    { apply chans_of_kren; [by destruct Hok|]. intros a b va vb Ha Hb. apply Hok; apply pheld_pconn_1; left;
        rewrite dom_union_L; apply elem_of_union_r; by eapply elem_of_dom_2. }
    rewrite <-HK. split.
    - intros Hc0. pose proof (G2 p2' (Σ2 ∪ ΣD) h ∅ Σ1 (kren h ΣC) Σ2 (kren h ΣD) h ∅ (A0 Hc0) (pren_fuse_ok _ _ _ Hok2)) as HG.
      rewrite !sdrop_empty, !pfuse_empty in HG. apply HG; [done|by apply pren_fuse_ok|done|done].
    - intros Hc0. apply (L (S n - c) ltac:(lia) Σ1 (kren h ΣC) Σ2 (kren h ΣD)); [|rewrite <-E2; apply Prel_rename; [done|by apply A1]|done].
      pose proof (HP1 h ∅ (pren_fuse_ok _ _ _ Hok1)) as H. rewrite sdrop_empty, E1, pfuse_empty in H.
      eapply Prel_down; [|exact H]. lia.
  Qed.
  Local Lemma Hq1e M1 : soup M1 = q1.2 → erase (q1.1, M1) = q1.
  Proof. intros H. unfold erase. simpl. rewrite H. by destruct q1. Qed.
  Local Lemma Hq2e M2 : soup M2 = q2.2 → erase (q2.1, M2) = q2.
  Proof. intros H. unfold erase. simpl. rewrite H. by destruct q2. Qed.

  Local Lemma link_sym (o1 o2 : cend) : ({[o2]} ∪ {[o1]} : gset cend) = {[o1]} ∪ {[o2]}.
  Proof. set_solver. Qed.

  Local Lemma soup_ins_fmap g (M1 M2 : gmap nat expr) i e' :
    M1 ##ₘ M2 → is_Some (M1 !! i) →
    soup (emap g <$> (<[i := e']> (M1 ∪ M2))) = emapE g (soup (<[i := e']> M1)) ⊎ emapE g (soup M2).
  Proof.
    intros Hd [e Hi]. assert (M2 !! i = None) as Hi2 by (apply eq_None_not_Some; intros [? ?]; eapply (disj_lookup_n M1 M2); eassumption).
    rewrite insert_union_l, map_fmap_union, soup_union, !soup_emap; [done|].
    apply map_disjoint_fmap. apply map_disjoint_insert_l. by split.
  Qed.

  Local Lemma soup_ins_fmap2 g (M1 M2 : gmap nat expr) i e' :
    M1 ##ₘ M2 → is_Some (M2 !! i) →
    soup (emap g <$> (<[i := e']> (M1 ∪ M2))) = emapE g (soup M1) ⊎ emapE g (soup (<[i := e']> M2)).
  Proof.
    intros Hd [e Hi]. assert (M1 !! i = None) as Hi1 by (apply eq_None_not_Some; intros [? ?]; eapply (disj_lookup_n M1 M2); eassumption).
    rewrite insert_union_r by done. rewrite map_fmap_union, soup_union, !soup_emap; [done|].
    apply map_disjoint_fmap. apply map_disjoint_insert_r. by split.
  Qed.

  (** A link of p1 whose kept end o2 is restricted in p1 and whose
      removed channel is a cut channel or restricted in p2. p1 takes the
      link of o2, and the composite is the result renamed by csub o1 o2. *)
  Lemma tau_link_own1 M1 M2 i e e' o1 o2 :
    M1 ##ₘ M2 → soup M1 = q1.2 → soup M2 = q2.2 → M1 !! i = Some e →
    tstep e (LSess (SLink ({[o1]} ∪ {[o2]}))) e' → ech o1 ∈ q2.1 ∪ K → ech o2 ∈ q1.1 →
    at_cost_P (S n) (c_link κ) (Prel κ) (Prel κ (S n)) W1 (Σ1 ∪ Σ2) T
      (erase ((q1.1 ∪ q2.1 ∪ K) ∖ {[ech o1]}, emap (csub o1 o2) <$> (<[i := e']> (M1 ∪ M2)))).
  Proof.
    intros Hd HM1 HM2 Hi He Ho1 Ho2.
    pose proof Hc as Hc0. destruct Hc0 as [Hd1 Hd2 Hcut Hf1 Hf2 HfC H12 H1C H2C HCC HC1 HC2].
    assert (ech o1 ∉ q1.1) as Hn1 by (clear -Ho1 HCC HC1; set_solver).
    assert (ech o1 ≠ ech o2) as Hne by (intros E; rewrite E in Hn1; done).
    assert (istep (q1.1, M1) (EvLink i o2 o1) (q1.1 ∖ {[ech o2]}, emap (csub o2 o1) <$> (<[i := e']> M1))) as Hst1.
    { eapply p_act_link; [exact Hi|by rewrite link_sym|done]. }
    destruct H1 as (_ & _ & (Ht1 & _)).
    pose proof (Ht1 (q1.1, M1) _ _ (Hq1e M1 HM1) Hst1 eq_refl) as A. simpl in A.
    set (p1'' := erase (q1.1 ∖ {[ech o2]}, emap (csub o2 o1) <$> (<[i := e']> M1))) in A.
    assert (erase ((q1.1 ∪ q2.1 ∪ K) ∖ {[ech o1]}, emap (csub o1 o2) <$> (<[i := e']> (M1 ∪ M2))) =
      pconn (pmap (csub o1 o2) p1'') (pmap (csub o1 o2) q2) (set_map (gch (csub o1 o2)) K)) as ->.
    { unfold erase, pconn, pmap, p1''. simpl. f_equal.
      - by apply chan_eq_own.
      - rewrite soup_ins_fmap by eauto. rewrite soup_emap, emapE_emapE, HM2. f_equal.
        apply emapE_ext. intros o. simpl. symmetry. by apply csub_csub. }
    apply ren_comp1.
    - apply A. unfold p1'', erase. simpl. rewrite chans_of_union. clear -HC1. set_solver.
    - apply (conn_C1 _ _ q1.1); [done| |]; unfold p1'', erase; simpl; clear -HCC HC1; set_solver.
    - apply pren_ok_csub_r; [done| |]; intros [H|H].
      + rewrite dom_union_L in H.
        apply elem_of_union in H as [H|H]; apply elem_of_chans_of in H; clear -H Ho2 HC1; set_solver.
      + unfold p1'', erase in H. simpl in H. clear -H Ho2 HCC HC1. set_solver.
      + rewrite dom_union_L in H. apply elem_of_union in H as [H|H]; apply elem_of_chans_of in H;
          rewrite ech_edual in H; clear -H Ho2 HC1; set_solver.
      + unfold p1'', erase in H. simpl in H. rewrite ech_edual in H. clear -H Ho2 HCC HC1. set_solver.
    - intros o Ho. apply csub_ne. intros E. rewrite dom_union_L in Ho.
      apply elem_of_union in Ho as [Ho|Ho]; apply elem_of_chans_of in Ho; rewrite E in Ho;
        clear -Ho Ho1 H1C H2C HC2 HC1; set_solver.
  Qed.

  (** The mirror, a link of p2. *)
  Lemma tau_link_own2 M1 M2 i e e' o1 o2 :
    M1 ##ₘ M2 → soup M1 = q1.2 → soup M2 = q2.2 → M2 !! i = Some e →
    tstep e (LSess (SLink ({[o1]} ∪ {[o2]}))) e' → ech o1 ∈ q1.1 ∪ K → ech o2 ∈ q2.1 →
    at_cost_P (S n) (c_link κ) (Prel κ) (Prel κ (S n)) W1 (Σ1 ∪ Σ2) T
      (erase ((q1.1 ∪ q2.1 ∪ K) ∖ {[ech o1]}, emap (csub o1 o2) <$> (<[i := e']> (M1 ∪ M2)))).
  Proof.
    intros Hd HM1 HM2 Hi He Ho1 Ho2.
    pose proof Hc as Hc0. destruct Hc0 as [Hd1 Hd2 Hcut Hf1 Hf2 HfC H12 H1C H2C HCC HC1 HC2].
    assert (ech o1 ∉ q2.1) as Hn1 by (clear -Ho1 HCC HC2; set_solver).
    assert (ech o1 ≠ ech o2) as Hne by (intros E; rewrite E in Hn1; done).
    assert (istep (q2.1, M2) (EvLink i o2 o1) (q2.1 ∖ {[ech o2]}, emap (csub o2 o1) <$> (<[i := e']> M2))) as Hst2.
    { eapply p_act_link; [exact Hi|by rewrite link_sym|done]. }
    destruct H2 as (_ & _ & (Ht2 & _)).
    pose proof (Ht2 (q2.1, M2) _ _ (Hq2e M2 HM2) Hst2 eq_refl) as A. simpl in A.
    set (p2'' := erase (q2.1 ∖ {[ech o2]}, emap (csub o2 o1) <$> (<[i := e']> M2))) in A.
    assert (erase ((q1.1 ∪ q2.1 ∪ K) ∖ {[ech o1]}, emap (csub o1 o2) <$> (<[i := e']> (M1 ∪ M2))) =
      pconn (pmap (csub o1 o2) q1) (pmap (csub o1 o2) p2'') (set_map (gch (csub o1 o2)) K)) as ->.
    { unfold erase, pconn, pmap, p2''. simpl. f_equal.
      - by apply chan_eq_own2.
      - rewrite soup_ins_fmap2 by eauto. rewrite soup_emap, emapE_emapE, HM1. f_equal.
        apply emapE_ext. intros o. simpl. symmetry. by apply csub_csub. }
    pose proof KD as HKD.
    apply ren_comp2.
    - apply A. unfold p2'', erase. simpl. rewrite chans_of_union, HKD. clear -HC2. set_solver.
    - apply (conn_C2 _ _ _ _ _ q2.1); [done| |]; unfold p2'', erase; simpl; clear -HCC HC2; set_solver.
    - apply pren_ok_csub_r; [done| |]; intros [H|H].
      + rewrite dom_union_L in H.
        apply elem_of_union in H as [H|H]; apply elem_of_chans_of in H; clear -H Ho2 HC2; set_solver.
      + unfold p2'', erase in H. simpl in H. clear -H Ho2 HCC HC2. set_solver.
      + rewrite dom_union_L in H. apply elem_of_union in H as [H|H]; apply elem_of_chans_of in H;
          rewrite ech_edual in H; clear -H Ho2 HC2; set_solver.
      + unfold p2'', erase in H. simpl in H. rewrite ech_edual in H. clear -H Ho2 HCC HC2. set_solver.
    - intros o Ho. apply csub_ne. intros E. rewrite dom_union_L in Ho.
      apply elem_of_union in Ho as [Ho|Ho]; apply elem_of_chans_of in Ho; rewrite E in Ho;
        clear -Ho Ho1 H1C H2C HC1 HC2; set_solver.
  Qed.
End links.
