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

Lemma ne_edual o : o ≠ edual o.
Proof. intros E. by apply (edual_ne o). Qed.

Lemma pair_eq (a b c d : cend) : ({[a]} ∪ {[b]} : gset cend) = {[c]} ∪ {[d]} → c ≠ d →
  (a = c ∧ b = d) ∨ (a = d ∧ b = c).
Proof.
  intros E Hcd. assert (c ∈ ({[a]} ∪ {[b]} : gset cend)) as Hc by (rewrite E; set_solver).
  assert (d ∈ ({[a]} ∪ {[b]} : gset cend)) as Hd by (rewrite E; set_solver).
  apply elem_of_union in Hc as [Hc|Hc], Hd as [Hd|Hd]; apply elem_of_singleton in Hc, Hd; subst; auto; done.
Qed.

Lemma soup_emap (g : cend → cend) M : soup (emap g <$> M) = emapE g (soup M).
Proof. apply soup_fmap. Qed.

Section links.
  Context (κ : ctable) (n : nat) (W1 : world) (T : ty) (X1 X2 : prel).
  Context (Σ1 ΣC Σ2 ΣD : senv) (q1 q2 : proc) (CC : cctx κ n W1 T X1 X2 Σ1 ΣC Σ2 ΣD q1 q2).
  Let HS := cc_HS CC. Let HT := cc_HT CC. Let Hc := cc_Hc CC.
  Let H1 := cc_H1 CC. Let H2 := cc_H2 CC. Let L := cc_L CC.
  Let X1P := cc_X1P CC. Let X2P := cc_X2P CC. Let HP1 := cc_HP1 CC. Let HP2 := cc_HP2 CC.
  Let G1 := cc_G1 CC. Let G2 := cc_G2 CC.
  Local Abbreviation K := (chans_of ΣC).
  Local Abbreviation pc := (pconn q1 q2 K).

  Local Lemma KD : chans_of ΣD = K.
  Proof. destruct Hc as [_ _ Hcut _ _ _ _ _ _ _ _ _]. by apply cut_dual_chans. Qed.

  Local Lemma kren_split h (Σa Σb : senv) : pren_ok h (Σa ∪ Σb) (∅, ∅) ∨ True → kinj h (Σa ∪ Σb) →
    (∀ o, o ∈ dom Σa → h o = o) → kren h (Σa ∪ Σb) = Σa ∪ kren h Σb.
  Proof. intros _ Hk Hf. rewrite kren_union by done. f_equal. by apply kren_id. Qed.

  (** A renaming of the composite after a step of p1 alone. *)
  Lemma ren_comp1 c p1' h :
    at_cost_P n c (Prel κ) X1 W1 (Σ1 ∪ ΣC) T p1' →
    conn Σ1 ΣC p1'.1 Σ2 ΣD q2.1 →
    pren_ok h (Σ1 ∪ Σ2) (pconn p1' q2 K) →
    (∀ o, o ∈ dom (Σ1 ∪ Σ2) → h o = o) →
    at_cost_P n c (Prel κ) (Prel κ n) W1 (Σ1 ∪ Σ2) T (pconn (pmap h p1') (pmap h q2) (set_map (gch h) K)).
  Proof.
    intros [A0 A1] Hc1 Hok Hfix.
    assert (pren_ok h (Σ1 ∪ ΣC) p1') as Hok1 by (eapply pren_ok_sub; [exact Hok|]; intros o; apply pheld_pconn_1).
    assert (pren_ok h (Σ2 ∪ ΣD) q2) as Hok2.
    { eapply pren_ok_sub; [exact Hok|]. intros o Ho. rewrite pconn_sym, (map_union_comm Σ1 Σ2).
      - rewrite <-KD. apply pheld_pconn_1. done.
      - apply chans_disj_map. by destruct Hc. }
    assert (∀ o, o ∈ dom Σ1 → h o = o) as F1 by (intros o Ho; apply Hfix; rewrite dom_union_L; cc_set_solver).
    assert (∀ o, o ∈ dom Σ2 → h o = o) as F2 by (intros o Ho; apply Hfix; rewrite dom_union_L; cc_set_solver).
    assert (kren h (Σ1 ∪ ΣC) = Σ1 ∪ kren h ΣC) as E1 by (apply kren_split; [by right|by eapply pren_ok_kinj|done]).
    assert (kren h (Σ2 ∪ ΣD) = Σ2 ∪ kren h ΣD) as E2 by (apply kren_split; [by right|by eapply pren_ok_kinj|done]).
    pose proof (conn_rename Σ1 ΣC Σ2 ΣD p1'.1 q2.1 Hc1 h (p1'.2 ⊎ q2.2) Hok Hfix) as Hc'.
    assert (chans_of (kren h ΣC) = set_map (gch h) K) as HK.
    { apply chans_of_kren; [by destruct Hok|]. intros a b va vb Ha Hb. apply Hok; apply pheld_pconn_1; left;
        rewrite dom_union_L; apply elem_of_union_r; by eapply elem_of_dom_2. }
    assert (Prel κ n W1 (Σ2 ∪ kren h ΣD) TUnit (pmap h q2)) as P2.
    { pose proof (HP2 h ∅ (pren_fuse_ok _ _ _ Hok2)) as H. by rewrite sdrop_empty, E2, pfuse_empty in H. }
    rewrite <-HK. split.
    - intros Hc0. pose proof (G1 p1' (Σ1 ∪ ΣC) h ∅ Σ1 (kren h ΣC) Σ2 (kren h ΣD) (pmap h q2) (A0 Hc0) (pren_fuse_ok _ _ _ Hok1)) as HG.
      rewrite sdrop_empty, pfuse_empty in HG. apply HG; [done|done|done].
    - intros Hc0. apply (L (S n - c) ltac:(lia) Σ1 (kren h ΣC) Σ2 (kren h ΣD)); [|eapply Prel_down; [|exact P2]; lia|done].
      rewrite <-E1. apply Prel_rename; [done|by apply A1].
  Qed.

  (** A renaming of the composite after a step of p2 alone. *)
  Lemma ren_comp2 c p2' h :
    at_cost_P n c (Prel κ) X2 W1 (Σ2 ∪ ΣD) TUnit p2' →
    conn Σ1 ΣC q1.1 Σ2 ΣD p2'.1 →
    pren_ok h (Σ1 ∪ Σ2) (pconn q1 p2' K) →
    (∀ o, o ∈ dom (Σ1 ∪ Σ2) → h o = o) →
    at_cost_P n c (Prel κ) (Prel κ n) W1 (Σ1 ∪ Σ2) T (pconn (pmap h q1) (pmap h p2') (set_map (gch h) K)).
  Proof.
    intros [A0 A1] Hc2 Hok Hfix.
    assert (pren_ok h (Σ1 ∪ ΣC) q1) as Hok1 by (eapply pren_ok_sub; [exact Hok|]; intros o; apply pheld_pconn_1).
    assert (pren_ok h (Σ2 ∪ ΣD) p2') as Hok2.
    { eapply pren_ok_sub; [exact Hok|]. intros o Ho. rewrite pconn_sym, (map_union_comm Σ1 Σ2).
      - rewrite <-KD. apply pheld_pconn_1. done.
      - apply chans_disj_map. by destruct Hc. }
    assert (∀ o, o ∈ dom Σ1 → h o = o) as F1 by (intros o Ho; apply Hfix; rewrite dom_union_L; cc_set_solver).
    assert (∀ o, o ∈ dom Σ2 → h o = o) as F2 by (intros o Ho; apply Hfix; rewrite dom_union_L; cc_set_solver).
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
  Proof. cc_set_solver. Qed.

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
    at_cost_P n (c_link κ) (Prel κ) (Prel κ n) W1 (Σ1 ∪ Σ2) T
      (erase ((q1.1 ∪ q2.1 ∪ K) ∖ {[ech o1]}, emap (csub o1 o2) <$> (<[i := e']> (M1 ∪ M2)))).
  Proof.
    intros Hd HM1 HM2 Hi He Ho1 Ho2.
    pose proof Hc as Hc0. destruct Hc0 as [Hd1 Hd2 Hcut Hf1 Hf2 HfC H12 H1C H2C HCC HC1 HC2].
    assert (ech o1 ∉ q1.1) as Hn1 by (clear -Ho1 HCC HC1; cc_set_solver).
    assert (ech o1 ≠ ech o2) as Hne by (intros E; rewrite E in Hn1; done).
    assert (istep (q1.1, M1) (EvSolo i (LSess (SLink ({[o2]} ∪ {[o1]}))) (PickLink o2 o1)) (q1.1 ∖ {[ech o2]}, emap (csub o2 o1) <$> (<[i := e']> M1))) as Hst1.
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
    - apply A. unfold p1'', erase. simpl. rewrite chans_of_union. clear -HC1. cc_set_solver.
    - apply (conn_C1 _ _ q1.1); [done| |]; unfold p1'', erase; simpl; clear -HCC HC1; cc_set_solver.
    - apply pren_ok_csub_r; [done| |]; intros [H|H].
      + rewrite dom_union_L in H.
        apply elem_of_union in H as [H|H]; apply elem_of_chans_of in H; clear -H Ho2 HC1; cc_set_solver.
      + unfold p1'', erase in H. simpl in H. clear -H Ho2 HCC HC1. cc_set_solver.
      + rewrite dom_union_L in H. apply elem_of_union in H as [H|H]; apply elem_of_chans_of in H;
          rewrite ech_edual in H; clear -H Ho2 HC1; cc_set_solver.
      + unfold p1'', erase in H. simpl in H. rewrite ech_edual in H. clear -H Ho2 HCC HC1. cc_set_solver.
    - intros o Ho. apply csub_ne. intros E. rewrite dom_union_L in Ho.
      apply elem_of_union in Ho as [Ho|Ho]; apply elem_of_chans_of in Ho; rewrite E in Ho;
        clear -Ho Ho1 H1C H2C HC2 HC1; cc_set_solver.
  Qed.

  (** The mirror, a link of p2. *)
  Lemma tau_link_own2 M1 M2 i e e' o1 o2 :
    M1 ##ₘ M2 → soup M1 = q1.2 → soup M2 = q2.2 → M2 !! i = Some e →
    tstep e (LSess (SLink ({[o1]} ∪ {[o2]}))) e' → ech o1 ∈ q1.1 ∪ K → ech o2 ∈ q2.1 →
    at_cost_P n (c_link κ) (Prel κ) (Prel κ n) W1 (Σ1 ∪ Σ2) T
      (erase ((q1.1 ∪ q2.1 ∪ K) ∖ {[ech o1]}, emap (csub o1 o2) <$> (<[i := e']> (M1 ∪ M2)))).
  Proof.
    intros Hd HM1 HM2 Hi He Ho1 Ho2.
    pose proof Hc as Hc0. destruct Hc0 as [Hd1 Hd2 Hcut Hf1 Hf2 HfC H12 H1C H2C HCC HC1 HC2].
    assert (ech o1 ∉ q2.1) as Hn1 by (clear -Ho1 HCC HC2; cc_set_solver).
    assert (ech o1 ≠ ech o2) as Hne by (intros E; rewrite E in Hn1; done).
    assert (istep (q2.1, M2) (EvSolo i (LSess (SLink ({[o2]} ∪ {[o1]}))) (PickLink o2 o1)) (q2.1 ∖ {[ech o2]}, emap (csub o2 o1) <$> (<[i := e']> M2))) as Hst2.
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
    - apply A. unfold p2'', erase. simpl. rewrite chans_of_union, HKD. clear -HC2. cc_set_solver.
    - apply (conn_C2 _ _ _ _ _ q2.1); [done| |]; unfold p2'', erase; simpl; clear -HCC HC2; cc_set_solver.
    - apply pren_ok_csub_r; [done| |]; intros [H|H].
      + rewrite dom_union_L in H.
        apply elem_of_union in H as [H|H]; apply elem_of_chans_of in H; clear -H Ho2 HC2; cc_set_solver.
      + unfold p2'', erase in H. simpl in H. clear -H Ho2 HCC HC2. cc_set_solver.
      + rewrite dom_union_L in H. apply elem_of_union in H as [H|H]; apply elem_of_chans_of in H;
          rewrite ech_edual in H; clear -H Ho2 HC2; cc_set_solver.
      + unfold p2'', erase in H. simpl in H. rewrite ech_edual in H. clear -H Ho2 HCC HC2. cc_set_solver.
    - intros o Ho. apply csub_ne. intros E. rewrite dom_union_L in Ho.
      apply elem_of_union in Ho as [Ho|Ho]; apply elem_of_chans_of in Ho; rewrite E in Ho;
        clear -Ho Ho1 H1C H2C HC1 HC2; cc_set_solver.
  Qed.
  (** A link of p1 on two ends it does not restrict: Q-Link of p1. The
      removed end o1 is a cut end, the kept end o2 an interface end
      (the holder of o1‾ in p2 now holds o2) or a cut end (p2 holds both
      ends of the channel of o2, a fusion). *)
  Lemma tau_link_ext1 M1 M2 i e e' o1 o2 :
    M1 ##ₘ M2 → soup M1 = q1.2 → soup M2 = q2.2 → M1 !! i = Some e →
    tstep e (LSess (SLink ({[o1]} ∪ {[o2]}))) e' → ech o1 ∈ q1.1 ∪ q2.1 ∪ K → ech o1 ∉ q1.1 → ech o2 ∉ q1.1 →
    at_cost_P n (c_link κ) (Prel κ) (Prel κ n) W1 (Σ1 ∪ Σ2) T
      (erase ((q1.1 ∪ q2.1 ∪ K) ∖ {[ech o1]}, emap (csub o1 o2) <$> (<[i := e']> (M1 ∪ M2)))).
  Proof.
    intros Hd HM1 HM2 Hi He HoC Hn1 Hn2.
    pose proof Hc as Hc0. destruct Hc0 as [Hd1 Hd2 Hcut Hf1 Hf2 HfC H12 H1C H2C HCC HC1 HC2].
    pose proof KD as HKD.
    assert (istep (q1.1, M1) (EvOffer i (SLink ({[o1]} ∪ {[o2]}))) (q1.1 ∖ sentc (SLink ({[o1]} ∪ {[o2]})), <[i := e']> M1)) as Hst1.
    { eapply p_act_session; [exact Hi|exact He|]. simpl. rewrite set_map_union_L, !set_map_singleton_L. clear -Hn1 Hn2. cc_set_solver. }
    pose proof H1 as H1'. destruct H1' as (_ & _ & (_ & _ & _ & _ & _ & _ & Hl1)).
    destruct (Hl1 _ _ _ _ (Hq1e M1 HM1) Hst1) as (oa & ob & Sa & Sb & x & Eab & Nab & La & Lb & Hab & A).
    simpl in A. rewrite difference_empty_L in A.
    assert (∃ S1 S2 y, (Σ1 ∪ ΣC) !! o1 = Some (S1, y) ∧ (Σ1 ∪ ΣC) !! o2 = Some (S2, y‾) ∧ sdual S1 S2 ∧ o1 ≠ o2 ∧
      at_cost_P n (c_link κ) (Prel κ) X1 W1 (delete o1 (delete o2 (Σ1 ∪ ΣC))) T (erase (q1.1, <[i := e']> M1)))
      as (S1 & S2 & y & L1 & L2 & H12' & No & A').
    { destruct (pair_eq _ _ _ _ Eab Nab) as [[-> ->]|[-> ->]].
      - exists Sa, Sb, x. done.
      - exists Sb, Sa, (x‾). rewrite pt_dual_dual. split_and!; [done|done|by apply sdual_sym|done|].
        by rewrite delete_delete. }
    clear Eab Nab La Lb Hab A oa ob Sa Sb x.
    pose proof (pfree_1C _ _ _ _ _ _ Hc) as Hpf.
    assert (o1 ∈ dom ΣC) as D1.
    { destruct (lookup_1C _ _ _ _ L1) as [[_ D]|[_ D]]; [|done]. exfalso.
      apply elem_of_chans_of in D. clear -D HoC H12 H1C HC1 HC2. cc_set_solver. }
    pose proof (cls_C _ _ _ _ _ _ Hc o1 D1) as Co1.
    assert (ΣC !! o1 = Some (S1, y)) as L1c by (destruct (lookup_1C _ _ _ _ L1) as [[_ D]|[? _]]; [tauto|done]).
    assert (ech o1 ≠ ech o2) as Hne.
    { intros E. apply ech_eq in E as [E|E]; [done|]. apply (Hpf o1); [by eapply elem_of_dom_2|rewrite <-E; by eapply elem_of_dom_2]. }
    destruct (proj2 Hcut _ _ _ L1c) as (S1' & L1d & Hd1').
    assert (ech o1 ∉ q2.1) as Hn1' by tauto.
    set (h := csub o1 o2).
    set (p1' := erase (q1.1, <[i := e']> M1)) in A'.
    assert (∀ o, pheld (delete o1 (delete o2 (Σ1 ∪ ΣC))) p1' o → h o = o) as Hfix1.
    { intros o [Ho|Ho]; apply csub_ne.
      - rewrite !dom_delete_L in Ho. intros E. apply ech_eq in E as [E|E]; [cc_set_solver|].
        apply elem_of_difference in Ho as [Ho _]. apply elem_of_difference in Ho as [Ho _].
        rewrite dom_union_L, elem_of_union in Ho. subst. rewrite edual_edual in Co1. tauto.
      - simpl in Ho. intros E. rewrite E in Ho. done. }
    destruct (ren_held_id h _ _ (csub_dcomm _ _ (not_eq_sym Hne)) Hfix1) as (Hok1 & Hk1 & Hc1').
    assert (set_map (gch h) q1.1 = q1.1) as G1e by (unfold h; rewrite set_map_gch_csub, decide_False by done; cc_set_solver).
    assert (set_map (gch h) q2.1 = q2.1) as G2e by (unfold h; rewrite set_map_gch_csub, decide_False by done; cc_set_solver).
    assert (soup (emap h <$> (<[i := e']> (M1 ∪ M2))) = (pmap h p1').2 ⊎ emapE h q2.2) as Es.
    { rewrite soup_ins_fmap by eauto. unfold pmap, p1', erase. simpl. by rewrite HM2. }
    destruct (conn_del _ _ _ _ _ _ o1 Hc D1) as [_ HK1].
    destruct (lookup_1C _ _ _ _ L2) as [[L2' D2]|[L2' D2]].
    - (* o2 is an interface end of p1 *)
      pose proof (cls_1 _ _ _ _ _ _ Hc o2 D2) as Co2.
      assert (kren h (Σ2 ∪ ΣD) = <[o2 := (S1', y‾)]> (Σ2 ∪ delete (edual o1) ΣD)) as Kh.
      { unfold h. rewrite (kren_csub_eq _ _ _ (S1', y‾)).
        - rewrite delete_union, (delete_id Σ2); [done|apply not_elem_of_dom; tauto].
        - by apply (lookup_2D_D Σ1 ΣC Σ2 ΣD q1.1 q2.1).
        - rewrite dom_union_L. clear -Co1. cc_set_solver.
        - rewrite dom_union_L. clear -Co2. cc_set_solver.
        - by apply not_eq_sym. }
      assert (pren_ok h (Σ2 ∪ ΣD) q2) as Hok2.
      { apply pren_ok_csub; [by apply not_eq_sym| | |]; intros [H|H]; rewrite ?dom_union_L in H; simpl in H;
          rewrite ?ech_edual in H; clear -H Co1 Co2 Hn1'; cc_set_solver. }
      assert (Prel κ n W1 (<[o2 := (S2, y‾)]> Σ2 ∪ delete (edual o1) ΣD) TUnit (pmap h q2)) as P2.
      { pose proof (HP2 h ∅ (pren_fuse_ok _ _ _ Hok2)) as P. rewrite sdrop_empty, pfuse_empty, Kh in P.
        rewrite <-insert_union_l. revert P. apply Prel_conv. apply senv_eqv_insert; [apply senv_eqv_refl|].
        eapply sdual_trans_l; [exact Hd1'|exact H12']. }
      assert (delete o1 (delete o2 (Σ1 ∪ ΣC)) = delete o2 Σ1 ∪ delete o1 ΣC) as E1.
      { rewrite !delete_union. rewrite (delete_id (delete o2 Σ1) o1), (delete_id ΣC o2); [done| |].
        - apply not_elem_of_dom. tauto.
        - apply not_elem_of_dom. rewrite dom_delete_L. clear -Co1. cc_set_solver. }
      assert (delete o2 Σ1 ∪ <[o2 := (S2, y‾)]> Σ2 = Σ1 ∪ Σ2) as EI.
      { rewrite <-insert_union_r by (apply lookup_delete_eq). rewrite <-(delete_id Σ2 o2) at 1 by (apply not_elem_of_dom; tauto). rewrite <-delete_union.
        apply insert_delete_id. by apply lookup_union_Some_l. }
      pose proof (conn_link_iface _ _ _ _ _ _ o1 o2 S2 (y‾) Hc D1 L2') as Hcn.
      assert (erase ((q1.1 ∪ q2.1 ∪ K) ∖ {[ech o1]}, emap h <$> (<[i := e']> (M1 ∪ M2))) =
        pconn (pmap h p1') (pmap h q2) (chans_of (delete o1 ΣC))) as ->.
      { unfold erase, pconn. cbn [fst snd]. rewrite Es. f_equal. unfold pmap. simpl. rewrite G1e, G2e, HK1.
        clear -Hn1 Hn1'. cc_set_solver. }
      rewrite <-EI. destruct A' as [A0 A1]. split.
      + intros Hz. pose proof (G1 p1' _ h ∅ (delete o2 Σ1) (delete o1 ΣC) (<[o2 := (S2, y‾)]> Σ2) (delete (edual o1) ΣD) (pmap h q2) (A0 Hz) (pren_fuse_ok _ _ _ Hok1)) as HG.
        rewrite sdrop_empty, pfuse_empty, Hk1 in HG. apply HG; [exact E1|exact P2|]. rewrite Hc1'. unfold pmap, p1', erase. simpl. by rewrite G2e.
      + intros Hz. apply (L (S n - c_link κ) ltac:(lia) (delete o2 Σ1) (delete o1 ΣC) (<[o2 := (S2, y‾)]> Σ2) (delete (edual o1) ΣD)).
        * rewrite <-E1, <-Hk1. apply Prel_rename; [done|by apply A1].
        * eapply Prel_down; [|exact P2]. lia.
        * rewrite Hc1'. unfold pmap, p1', erase. simpl. by rewrite G2e.
    - (* o2 is a cut end of p1 *)
      pose proof (cls_C _ _ _ _ _ _ Hc o2 D2) as Co2.
      destruct (proj2 Hcut _ _ _ L2') as (S2' & L2d & Hd2'). rewrite pt_dual_dual in L2d.
      assert (o2 ≠ edual o1) as No' by (intros ->; tauto).
      assert (kren h (Σ2 ∪ ΣD) = <[o2 := (S1', y‾)]> (delete (edual o1) (Σ2 ∪ ΣD))) as Kh.
      { unfold h. apply kren_csub_eq.
        - by apply (lookup_2D_D Σ1 ΣC Σ2 ΣD q1.1 q2.1).
        - rewrite dom_union_L. clear -Co1. cc_set_solver.
        - rewrite dom_union_L. clear -Co2. cc_set_solver.
        - by apply not_eq_sym. }
      assert (fuse_ok h {[ech o2]} (Σ2 ∪ ΣD) q2) as Hok2.
      { apply fuse_ok_csub_cut; [by apply not_eq_sym| | |].
        - intros [H|H]; rewrite ?dom_union_L in H; simpl in H; clear -H Co1 Hn1'; cc_set_solver.
        - intros [H|H]; rewrite ?dom_union_L in H; simpl in H; clear -H Co2; cc_set_solver.
        - fold h. rewrite Kh. intros o Ho. apply elem_of_singleton in Ho. apply ech_eq in Ho as [Eo|Eo].
          + subst o. exists S1', (y‾), S2'. rewrite lookup_insert_eq, lookup_insert_ne by first [apply ne_edual|apply edual_ne].
            rewrite lookup_delete_ne by (intros E; apply No; by apply edual_inj).
            split_and!; [done| |].
            * rewrite pt_dual_dual. by apply (lookup_2D_D Σ1 ΣC Σ2 ΣD q1.1 q2.1).
            * by apply (sdual_dual_dual S1 S1' S2 S2').
          + assert (o = edual o2) as -> by (rewrite Eo, edual_edual; done). exists S2', y, S1'. rewrite edual_edual, lookup_insert_eq, lookup_insert_ne by first [apply ne_edual|apply edual_ne].
            rewrite lookup_delete_ne by (intros E; apply No; by apply edual_inj).
            split_and!; [by apply (lookup_2D_D Σ1 ΣC Σ2 ΣD q1.1 q2.1)|done|].
            apply sdual_sym. by apply (sdual_dual_dual S1 S1' S2 S2'). }
      assert (sdrop {[ech o2]} (kren h (Σ2 ∪ ΣD)) = Σ2 ∪ delete (edual o1) (delete (edual o2) ΣD)) as ES.
      { rewrite Kh. apply map_eq. intros o. destruct (decide (ech o = ech o2)) as [Eo|Eo].
        - assert (sdrop {[ech o2]} (<[o2 := (S1', y‾)]> (delete (edual o1) (Σ2 ∪ ΣD))) !! o = None) as ->.
          { apply eq_None_not_Some. intros [v Hv]. apply sdrop_lookup in Hv as [_ Hv]. apply Hv. rewrite Eo. by apply elem_of_singleton. }
          symmetry. apply lookup_union_None.
          apply ech_eq in Eo as [Eo|Eo]; [subst o|assert (o = edual o2) as -> by (rewrite Eo, edual_edual; done)]; split.
          + apply not_elem_of_dom. tauto.
          + rewrite lookup_delete_ne by (intros E; apply No'; by rewrite E). rewrite lookup_delete_ne by apply edual_ne.
            apply not_elem_of_dom. tauto.
          + apply not_elem_of_dom. tauto.
          + rewrite lookup_delete_ne by (intros E; apply edual_inj in E; by apply No). by rewrite lookup_delete_eq.
        - destruct (sdrop {[ech o2]} (<[o2 := (S1', y‾)]> (delete (edual o1) (Σ2 ∪ ΣD))) !! o) as [v|] eqn:Ev.
          + apply sdrop_lookup in Ev as [Ev _]. rewrite lookup_insert_ne in Ev by (intros ->; done).
            apply lookup_delete_Some in Ev as [Ne Ev]. symmetry.
            rewrite <-(delete_id Σ2 (edual o1)) by (apply not_elem_of_dom; tauto).
            rewrite <-delete_union, lookup_delete_ne by done.
            rewrite <-(delete_id Σ2 (edual o2)) at 1 by (apply not_elem_of_dom; tauto).
            rewrite <-delete_union, lookup_delete_ne by (intros <-; apply Eo; by rewrite ech_edual). done.
          + symmetry. apply eq_None_not_Some. intros [v Hv].
            assert (sdrop {[ech o2]} (<[o2 := (S1', y‾)]> (delete (edual o1) (Σ2 ∪ ΣD))) !! o = Some v) as Hc'; [|congruence].
            apply sdrop_lookup. split; [|by intros ?%elem_of_singleton]. rewrite lookup_insert_ne by (intros ->; done).
            apply lookup_union_Some_raw in Hv as [Hv|[Nv Hv]].
            * rewrite lookup_delete_ne by (intros <-; apply elem_of_dom_2 in Hv; tauto).
              by apply lookup_union_Some_l.
            * apply lookup_delete_Some in Hv as [N1 Hv]. apply lookup_delete_Some in Hv as [N2 Hv].
              rewrite lookup_delete_ne by done. apply lookup_union_Some_raw. by right. }
      assert (delete o1 (delete o2 (Σ1 ∪ ΣC)) = Σ1 ∪ delete o1 (delete o2 ΣC)) as E1.
      { rewrite !delete_union. rewrite (delete_id Σ1 o2), (delete_id Σ1 o1); [done|apply not_elem_of_dom; tauto|apply not_elem_of_dom; tauto]. }
      destruct (conn_del _ _ _ _ _ _ o2 Hc D2) as [Hca HKa].
      destruct (conn_del _ _ _ _ _ _ o1 Hca) as [Hcb HKb]; [rewrite dom_delete_L; clear -D1 No; cc_set_solver|].
      assert (conn Σ1 (delete o1 (delete o2 ΣC)) q1.1 Σ2 (delete (edual o1) (delete (edual o2) ΣD)) (q2.1 ∪ {[ech o2]})) as Hcn.
      { assert (ech o2 ∉ q1.1) as N2 by (destruct Co2 as (_ & _ & _ & ? & _); done).
        assert (ech o2 ∈ K) as Ek by (by apply elem_of_chans_of).
        apply (conn_C2 _ _ _ _ _ q2.1); [done| |]; rewrite ?HKb, ?HKa.
        - apply disjoint_union_l. split.
          + clear -HCC HC2. cc_set_solver.
          + apply disjoint_singleton_l. clear -N2. cc_set_solver.
        - apply disjoint_union_l. split.
          + clear -HC2. cc_set_solver.
          + apply disjoint_singleton_l. clear -Ek H1C H2C. cc_set_solver. }
      assert (erase ((q1.1 ∪ q2.1 ∪ K) ∖ {[ech o1]}, emap h <$> (<[i := e']> (M1 ∪ M2))) =
        pconn (pmap h p1') (pfuse h {[ech o2]} q2) (chans_of (delete o1 (delete o2 ΣC)))) as ->.
      { unfold erase, pconn. cbn [fst snd]. rewrite Es. f_equal. unfold pmap, pfuse. simpl. rewrite G1e, G2e, HKb, HKa.
        apply elem_of_chans_of in D1, D2. clear -Hn1 Hn1' D1 D2 Hne. apply set_eq. intros c.
        destruct (decide (c = ech o2)) as [->|?]; cc_set_solver. }
      pose proof (HP2 h {[ech o2]} Hok2) as P2. rewrite ES in P2.
      destruct A' as [A0 A1]. split.
      + intros Hz. pose proof (G1 p1' _ h ∅ Σ1 (delete o1 (delete o2 ΣC)) Σ2 (delete (edual o1) (delete (edual o2) ΣD)) (pfuse h {[ech o2]} q2) (A0 Hz) (pren_fuse_ok _ _ _ Hok1)) as HG.
        rewrite sdrop_empty, pfuse_empty, Hk1 in HG. apply HG; [exact E1|exact P2|]. rewrite Hc1'. unfold pfuse, p1', erase. simpl. by rewrite G2e.
      + intros Hz. apply (L (S n - c_link κ) ltac:(lia) Σ1 (delete o1 (delete o2 ΣC)) Σ2 (delete (edual o1) (delete (edual o2) ΣD))).
        * rewrite <-E1, <-Hk1. apply Prel_rename; [done|by apply A1].
        * eapply Prel_down; [|exact P2]. lia.
        * rewrite Hc1'. unfold pfuse, p1', erase. simpl. by rewrite G2e.
  Qed.
  (** The mirror, a link of p2 on two ends it does not restrict. *)
  Lemma tau_link_ext2 M1 M2 i e e' o1 o2 :
    M1 ##ₘ M2 → soup M1 = q1.2 → soup M2 = q2.2 → M2 !! i = Some e →
    tstep e (LSess (SLink ({[o1]} ∪ {[o2]}))) e' → ech o1 ∈ q1.1 ∪ q2.1 ∪ K → ech o1 ∉ q2.1 → ech o2 ∉ q2.1 →
    at_cost_P n (c_link κ) (Prel κ) (Prel κ n) W1 (Σ1 ∪ Σ2) T
      (erase ((q1.1 ∪ q2.1 ∪ K) ∖ {[ech o1]}, emap (csub o1 o2) <$> (<[i := e']> (M1 ∪ M2)))).
  Proof.
    intros Hd HM1 HM2 Hi He HoC Hn1 Hn2.
    pose proof Hc as Hc0. destruct Hc0 as [Hd1 Hd2 Hcut Hf1 Hf2 HfC H12 H1C H2C HCC HC1 HC2].
    pose proof KD as HKD. pose proof (conn_sym _ _ _ _ _ _ Hc) as Hcs.
    assert (istep (q2.1, M2) (EvOffer i (SLink ({[o1]} ∪ {[o2]}))) (q2.1 ∖ sentc (SLink ({[o1]} ∪ {[o2]})), <[i := e']> M2)) as Hst2.
    { eapply p_act_session; [exact Hi|exact He|]. simpl. rewrite set_map_union_L, !set_map_singleton_L. clear -Hn1 Hn2. cc_set_solver. }
    pose proof H2 as H2'. destruct H2' as (_ & _ & (_ & _ & _ & _ & _ & _ & Hl2)).
    destruct (Hl2 _ _ _ _ (Hq2e M2 HM2) Hst2) as (oa & ob & Sa & Sb & x & Eab & Nab & La & Lb & Hab & A).
    simpl in A. rewrite difference_empty_L in A.
    assert (∃ S1 S2 y, (Σ2 ∪ ΣD) !! o1 = Some (S1, y) ∧ (Σ2 ∪ ΣD) !! o2 = Some (S2, y‾) ∧ sdual S1 S2 ∧ o1 ≠ o2 ∧
      at_cost_P n (c_link κ) (Prel κ) X2 W1 (delete o1 (delete o2 (Σ2 ∪ ΣD))) TUnit (erase (q2.1, <[i := e']> M2)))
      as (S1 & S2 & y & L1 & L2 & H12' & No & A').
    { destruct (pair_eq _ _ _ _ Eab Nab) as [[-> ->]|[-> ->]].
      - exists Sa, Sb, x. done.
      - exists Sb, Sa, (x‾). rewrite pt_dual_dual. split_and!; [done|done|by apply sdual_sym|done|].
        by rewrite delete_delete. }
    clear Eab Nab La Lb Hab A oa ob Sa Sb x.
    pose proof (pfree_1C _ _ _ _ _ _ Hcs) as Hpf.
    assert (o1 ∈ dom ΣD) as D1.
    { destruct (lookup_1C _ _ _ _ L1) as [[_ D]|[_ D]]; [|done]. exfalso.
      apply elem_of_chans_of in D. clear -D HoC H12 H2C HC1 HC2 HKD. rewrite <-HKD in HoC. cc_set_solver. }
    pose proof (cls_C _ _ _ _ _ _ Hcs o1 D1) as Co1.
    assert (ΣD !! o1 = Some (S1, y)) as L1c by (destruct (lookup_1C _ _ _ _ L1) as [[_ D]|[? _]]; [tauto|done]).
    assert (ech o1 ≠ ech o2) as Hne.
    { intros E. apply ech_eq in E as [E|E]; [done|]. apply (Hpf o1); [by eapply elem_of_dom_2|rewrite <-E; by eapply elem_of_dom_2]. }
    destruct (proj2 (cut_dual_sym _ _ HfC Hcut) _ _ _ L1c) as (S1' & L1d & Hd1').
    assert (ech o1 ∉ q1.1) as Hn1' by tauto.
    set (h := csub o1 o2).
    set (p2' := erase (q2.1, <[i := e']> M2)) in A'.
    assert (∀ o, pheld (delete o1 (delete o2 (Σ2 ∪ ΣD))) p2' o → h o = o) as Hfix2.
    { intros o [Ho|Ho]; apply csub_ne.
      - rewrite !dom_delete_L in Ho. intros E. apply ech_eq in E as [E|E]; [cc_set_solver|].
        apply elem_of_difference in Ho as [Ho _]. apply elem_of_difference in Ho as [Ho _].
        rewrite dom_union_L, elem_of_union in Ho. subst. rewrite edual_edual in Co1. tauto.
      - simpl in Ho. intros E. rewrite E in Ho. done. }
    destruct (ren_held_id h _ _ (csub_dcomm _ _ (not_eq_sym Hne)) Hfix2) as (Hok2 & Hk2 & Hc2').
    assert (set_map (gch h) q1.1 = q1.1) as G1e by (unfold h; rewrite set_map_gch_csub, decide_False by done; cc_set_solver).
    assert (set_map (gch h) q2.1 = q2.1) as G2e by (unfold h; rewrite set_map_gch_csub, decide_False by done; cc_set_solver).
    assert (soup (emap h <$> (<[i := e']> (M1 ∪ M2))) = emapE h q1.2 ⊎ (pmap h p2').2) as Es.
    { rewrite soup_ins_fmap2 by eauto. unfold pmap, p2', erase. simpl. by rewrite HM1. }
    destruct (conn_del _ _ _ _ _ _ o1 Hcs D1) as [_ HK1].
    destruct (lookup_1C _ _ _ _ L2) as [[L2' D2]|[L2' D2]].
    - (* o2 is an interface end of p2 *)
      pose proof (cls_1 _ _ _ _ _ _ Hcs o2 D2) as Co2.
      assert (kren h (Σ1 ∪ ΣC) = <[o2 := (S1', y‾)]> (Σ1 ∪ delete (edual o1) ΣC)) as Kh.
      { unfold h. rewrite (kren_csub_eq _ _ _ (S1', y‾)).
        - rewrite delete_union, (delete_id Σ1); [done|apply not_elem_of_dom; tauto].
        - by apply (lookup_1C_C Σ1 ΣC Σ2 ΣD q1.1 q2.1).
        - rewrite dom_union_L. clear -Co1. cc_set_solver.
        - rewrite dom_union_L. clear -Co2. cc_set_solver.
        - by apply not_eq_sym. }
      assert (pren_ok h (Σ1 ∪ ΣC) q1) as Hok1.
      { apply pren_ok_csub; [by apply not_eq_sym| | |]; intros [H|H]; rewrite ?dom_union_L in H; simpl in H;
          rewrite ?ech_edual in H; clear -H Co1 Co2 Hn1'; cc_set_solver. }
      set (Σ1' := <[o2 := (S1', y‾)]> Σ1).
      assert (Prel κ n W1 (Σ1' ∪ delete (edual o1) ΣC) T (pmap h q1)) as P1.
      { pose proof (HP1 h ∅ (pren_fuse_ok _ _ _ Hok1)) as P. rewrite sdrop_empty, pfuse_empty, Kh in P.
        unfold Σ1'. by rewrite <-insert_union_l. }
      assert (delete o1 (delete o2 (Σ2 ∪ ΣD)) = delete o2 Σ2 ∪ delete o1 ΣD) as E2.
      { rewrite !delete_union. rewrite (delete_id (delete o2 Σ2) o1), (delete_id ΣD o2); [done| |].
        - apply not_elem_of_dom. tauto.
        - apply not_elem_of_dom. rewrite dom_delete_L. clear -Co1. cc_set_solver. }
      assert (senv_eqv (Σ1' ∪ delete o2 Σ2) (Σ1 ∪ Σ2)) as EI.
      { assert (Σ1 ∪ Σ2 = <[o2 := (S2, y‾)]> Σ1 ∪ delete o2 Σ2) as ->.
        { rewrite <-insert_union_l. rewrite <-(delete_id Σ1 o2) at 2 by (apply not_elem_of_dom; tauto).
          rewrite <-delete_union. symmetry. apply insert_delete_id. apply lookup_union_Some_raw. right. split; [apply not_elem_of_dom; tauto|done]. }
        apply senv_eqv_union; [|apply senv_eqv_refl]. apply senv_eqv_insert; [apply senv_eqv_refl|].
        eapply sdual_trans_l; [exact Hd1'|exact H12']. }
      pose proof (conn_link_iface _ _ _ _ _ _ o1 o2 S2 (y‾) Hcs D1 L2') as Hcn0.
      assert (conn Σ1' (delete (edual o1) ΣC) q1.1 (delete o2 Σ2) (delete o1 ΣD) q2.1) as Hcn.
      { apply conn_sym in Hcn0. unfold Σ1'. rewrite <-(insert_insert_eq Σ1 o2 (S1', y‾) (S2, y‾)).
        apply conn_retype1; [done|]. rewrite dom_insert_L. cc_set_solver. }
      pose proof (cut_dual_chans _ _ (match Hcn with Conn _ _ _ _ _ _ _ _ c _ _ _ _ _ _ _ _ _ => c end)) as HKc.
      assert (erase ((q1.1 ∪ q2.1 ∪ K) ∖ {[ech o1]}, emap h <$> (<[i := e']> (M1 ∪ M2))) =
        pconn (pmap h q1) (pmap h p2') (chans_of (delete (edual o1) ΣC))) as ->.
      { unfold erase, pconn. cbn [fst snd]. rewrite Es. f_equal. unfold pmap. simpl. rewrite G1e, G2e, <-HKc, HK1, HKD.
        clear -Hn1 Hn1'. cc_set_solver. }
      revert EI. generalize (Σ1 ∪ Σ2). intros Σx EI. destruct A' as [A0 A1]. split.
      + intros Hz. apply (Prel_conv _ _ _ _ _ _ _ EI).
        pose proof (G2 p2' _ h ∅ Σ1' (delete (edual o1) ΣC) (delete o2 Σ2) (delete o1 ΣD) h ∅ (A0 Hz) (pren_fuse_ok _ _ _ Hok2)) as HG.
        rewrite !sdrop_empty, !pfuse_empty, Hk2, Kh in HG. apply HG; [exact E2|by apply pren_fuse_ok|unfold Σ1'; by rewrite insert_union_l|].
        rewrite Hc2'. unfold pmap, p2', erase. simpl. by rewrite G1e.
      + intros Hz. apply (Prel_conv _ _ _ _ _ _ _ EI).
        apply (L (S n - c_link κ) ltac:(lia) Σ1' (delete (edual o1) ΣC) (delete o2 Σ2) (delete o1 ΣD)).
        * eapply Prel_down; [|exact P1]. lia.
        * rewrite <-E2, <-Hk2. apply Prel_rename; [done|by apply A1].
        * rewrite Hc2'. unfold pmap, p2', erase. simpl. by rewrite G1e.
    - (* o2 is a cut end of p2 *)
      pose proof (cls_C _ _ _ _ _ _ Hcs o2 D2) as Co2.
      destruct (proj2 (cut_dual_sym _ _ HfC Hcut) _ _ _ L2') as (S2' & L2d & Hd2'). rewrite pt_dual_dual in L2d.
      assert (o2 ≠ edual o1) as No' by (intros ->; tauto).
      assert (kren h (Σ1 ∪ ΣC) = <[o2 := (S1', y‾)]> (delete (edual o1) (Σ1 ∪ ΣC))) as Kh.
      { unfold h. apply kren_csub_eq.
        - by apply (lookup_1C_C Σ1 ΣC Σ2 ΣD q1.1 q2.1).
        - rewrite dom_union_L. clear -Co1. cc_set_solver.
        - rewrite dom_union_L. clear -Co2. cc_set_solver.
        - by apply not_eq_sym. }
      assert (fuse_ok h {[ech o2]} (Σ1 ∪ ΣC) q1) as Hok1.
      { apply fuse_ok_csub_cut; [by apply not_eq_sym| | |].
        - intros [H|H]; rewrite ?dom_union_L in H; simpl in H; clear -H Co1 Hn1'; cc_set_solver.
        - intros [H|H]; rewrite ?dom_union_L in H; simpl in H; clear -H Co2; cc_set_solver.
        - fold h. rewrite Kh. intros o Ho. apply elem_of_singleton in Ho. apply ech_eq in Ho as [Eo|Eo].
          + subst o. exists S1', (y‾), S2'. rewrite lookup_insert_eq, lookup_insert_ne by first [apply ne_edual|apply edual_ne].
            rewrite lookup_delete_ne by (intros E; apply No; by apply edual_inj).
            split_and!; [done| |].
            * rewrite pt_dual_dual. by apply (lookup_1C_C Σ1 ΣC Σ2 ΣD q1.1 q2.1).
            * by apply (sdual_dual_dual S1 S1' S2 S2').
          + assert (o = edual o2) as -> by (rewrite Eo, edual_edual; done). exists S2', y, S1'. rewrite edual_edual, lookup_insert_eq, lookup_insert_ne by first [apply ne_edual|apply edual_ne].
            rewrite lookup_delete_ne by (intros E; apply No; by apply edual_inj).
            split_and!; [by apply (lookup_1C_C Σ1 ΣC Σ2 ΣD q1.1 q2.1)|done|].
            apply sdual_sym. by apply (sdual_dual_dual S1 S1' S2 S2'). }
      assert (sdrop {[ech o2]} (kren h (Σ1 ∪ ΣC)) = Σ1 ∪ delete (edual o1) (delete (edual o2) ΣC)) as ES.
      { rewrite Kh. apply map_eq. intros o. destruct (decide (ech o = ech o2)) as [Eo|Eo].
        - assert (sdrop {[ech o2]} (<[o2 := (S1', y‾)]> (delete (edual o1) (Σ1 ∪ ΣC))) !! o = None) as ->.
          { apply eq_None_not_Some. intros [v Hv]. apply sdrop_lookup in Hv as [_ Hv]. apply Hv. rewrite Eo. by apply elem_of_singleton. }
          symmetry. apply lookup_union_None.
          apply ech_eq in Eo as [Eo|Eo]; [subst o|assert (o = edual o2) as -> by (rewrite Eo, edual_edual; done)]; split.
          + apply not_elem_of_dom. tauto.
          + rewrite lookup_delete_ne by (intros E; apply No'; by rewrite E). rewrite lookup_delete_ne by apply edual_ne.
            apply not_elem_of_dom. tauto.
          + apply not_elem_of_dom. tauto.
          + rewrite lookup_delete_ne by (intros E; apply edual_inj in E; by apply No). by rewrite lookup_delete_eq.
        - destruct (sdrop {[ech o2]} (<[o2 := (S1', y‾)]> (delete (edual o1) (Σ1 ∪ ΣC))) !! o) as [v|] eqn:Ev.
          + apply sdrop_lookup in Ev as [Ev _]. rewrite lookup_insert_ne in Ev by (intros ->; done).
            apply lookup_delete_Some in Ev as [Ne Ev]. symmetry.
            rewrite <-(delete_id Σ1 (edual o1)) by (apply not_elem_of_dom; tauto).
            rewrite <-delete_union, lookup_delete_ne by done.
            rewrite <-(delete_id Σ1 (edual o2)) at 1 by (apply not_elem_of_dom; tauto).
            rewrite <-delete_union, lookup_delete_ne by (intros <-; apply Eo; by rewrite ech_edual). done.
          + symmetry. apply eq_None_not_Some. intros [v Hv].
            assert (sdrop {[ech o2]} (<[o2 := (S1', y‾)]> (delete (edual o1) (Σ1 ∪ ΣC))) !! o = Some v) as Hc'; [|congruence].
            apply sdrop_lookup. split; [|by intros ?%elem_of_singleton]. rewrite lookup_insert_ne by (intros ->; done).
            apply lookup_union_Some_raw in Hv as [Hv|[Nv Hv]].
            * rewrite lookup_delete_ne by (intros <-; apply elem_of_dom_2 in Hv; tauto).
              by apply lookup_union_Some_l.
            * apply lookup_delete_Some in Hv as [N1 Hv]. apply lookup_delete_Some in Hv as [N2 Hv].
              rewrite lookup_delete_ne by done. apply lookup_union_Some_raw. by right. }
      assert (delete o1 (delete o2 (Σ2 ∪ ΣD)) = Σ2 ∪ delete o1 (delete o2 ΣD)) as E2.
      { rewrite !delete_union. rewrite (delete_id Σ2 o2), (delete_id Σ2 o1); [done|apply not_elem_of_dom; tauto|apply not_elem_of_dom; tauto]. }
      destruct (conn_del _ _ _ _ _ _ o2 Hcs D2) as [Hca HKa].
      destruct (conn_del _ _ _ _ _ _ o1 Hca) as [Hcb HKb]; [rewrite dom_delete_L; clear -D1 No; cc_set_solver|].
      assert (conn Σ2 (delete o1 (delete o2 ΣD)) q2.1 Σ1 (delete (edual o1) (delete (edual o2) ΣC)) (q1.1 ∪ {[ech o2]})) as Hcn0.
      { assert (ech o2 ∉ q2.1) as N2 by (destruct Co2 as (_ & _ & _ & ? & _); done).
        assert (ech o2 ∈ K) as Ek by (rewrite <-HKD; by apply elem_of_chans_of).
        apply (conn_C2 _ _ _ _ _ q1.1); [done| |]; rewrite ?HKb, ?HKa.
        - apply disjoint_union_l. split.
          + rewrite HKD. clear -HCC HC1. cc_set_solver.
          + apply disjoint_singleton_l. clear -N2. cc_set_solver.
        - apply disjoint_union_l. split.
          + clear -HC1. cc_set_solver.
          + apply disjoint_singleton_l. clear -Ek H1C H2C. cc_set_solver. }
      pose proof (conn_sym _ _ _ _ _ _ Hcn0) as Hcn.
      pose proof (cut_dual_chans _ _ (match Hcn with Conn _ _ _ _ _ _ _ _ c _ _ _ _ _ _ _ _ _ => c end)) as HKc.
      assert (erase ((q1.1 ∪ q2.1 ∪ K) ∖ {[ech o1]}, emap h <$> (<[i := e']> (M1 ∪ M2))) =
        pconn (pfuse h {[ech o2]} q1) (pmap h p2') (chans_of (delete (edual o1) (delete (edual o2) ΣC)))) as ->.
      { unfold erase, pconn. cbn [fst snd]. rewrite Es. f_equal. unfold pmap, pfuse. simpl. rewrite G1e, G2e, <-HKc, HKb, HKa, HKD.
        apply elem_of_chans_of in D1, D2. rewrite HKD in D1, D2. clear -Hn1 Hn1' D1 D2 Hne. apply set_eq. intros c.
        destruct (decide (c = ech o2)) as [->|?]; cc_set_solver. }
      pose proof (HP1 h {[ech o2]} Hok1) as P1. rewrite ES in P1.
      destruct A' as [A0 A1]. split.
      + intros Hz. pose proof (G2 p2' _ h ∅ Σ1 (delete (edual o1) (delete (edual o2) ΣC)) Σ2 (delete o1 (delete o2 ΣD)) h {[ech o2]} (A0 Hz) (pren_fuse_ok _ _ _ Hok2)) as HG.
        rewrite sdrop_empty, pfuse_empty, Hk2 in HG. apply HG; [exact E2|exact Hok1|exact ES|].
        rewrite Hc2'. unfold pfuse, p2', erase. simpl. by rewrite G1e.
      + intros Hz. apply (L (S n - c_link κ) ltac:(lia) Σ1 (delete (edual o1) (delete (edual o2) ΣC)) Σ2 (delete o1 (delete o2 ΣD))).
        * eapply Prel_down; [|exact P1]. lia.
        * rewrite <-E2, <-Hk2. apply Prel_rename; [done|by apply A1].
        * rewrite Hc2'. unfold pfuse, p2', erase. simpl. by rewrite G1e.
  Qed.
End links.
