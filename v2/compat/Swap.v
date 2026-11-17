(** * R^κ is invariant under renaming channels (stage S4)

    A transposition of two channel names a ↔ b renames every end of a
    term ([eswap a b], lang/ChannelSwap.v) and every end of an
    environment ([sswap a b] = kmap (oswap a b)). V and E are invariant
    under it, for every cost table ([Vrel_swap], [Erel_swap]). A step of
    the renamed term is the renamed step of the term
    ([tstep_eswap]), so every obligation moves along the transposition,
    and the transposition is its own inverse. *)

From GV Require Export compat.Blind lang.ChannelSwap.

Section swap.
  Context (a b : chan).

  Global Instance oswap_inj_inst : Inj eq eq (oswap a b).
  Proof. intros o o'. apply oswap_inj. Qed.

  Definition sswap (Θ : senv) : senv := kmap (oswap a b) Θ.

  Lemma sswap_lookup Θ o : sswap Θ !! oswap a b o = Θ !! o.
  Proof. apply lookup_kmap. all: try apply _. Qed.

  Lemma sswap_lookup' Θ o : sswap Θ !! o = Θ !! oswap a b o.
  Proof. by rewrite <-(oswap_involutive a b o) at 1; rewrite sswap_lookup. Qed.

  Lemma sswap_inv Θ : sswap (sswap Θ) = Θ.
  Proof. apply map_eq. intros o. by rewrite !sswap_lookup', oswap_involutive. Qed.

  Lemma sswap_empty : sswap ∅ = ∅.
  Proof. apply kmap_empty. all: try apply _. Qed.
  Lemma sswap_singleton o x : sswap {[o := x]} = {[oswap a b o := x]}.
  Proof. apply kmap_singleton. all: try apply _. Qed.
  Lemma sswap_insert Θ o x : sswap (<[o := x]> Θ) = <[oswap a b o := x]> (sswap Θ).
  Proof. apply kmap_insert. all: try apply _. Qed.
  Lemma sswap_delete Θ o : sswap (delete o Θ) = delete (oswap a b o) (sswap Θ).
  Proof. apply kmap_delete. all: try apply _. Qed.
  Lemma sswap_union Θ1 Θ2 : sswap (Θ1 ∪ Θ2) = sswap Θ1 ∪ sswap Θ2.
  Proof. apply kmap_union. all: try apply _. Qed.
  Lemma sswap_disjoint Θ1 Θ2 : sswap Θ1 ##ₘ sswap Θ2 ↔ Θ1 ##ₘ Θ2.
  Proof. apply map_disjoint_kmap. all: try apply _. Qed.
  Lemma set_map_oswap_inv (X : gset cend) : set_map (D:=gset cend) (oswap a b) (set_map (D:=gset cend) (oswap a b) X) = X.
  Proof.
    apply set_eq. intros o. split.
    - intros (o1 & -> & Ho1)%elem_of_map. apply elem_of_map in Ho1 as (o2 & -> & Ho2).
      by rewrite oswap_involutive.
    - intros H. apply elem_of_map. exists (oswap a b o). split; [by rewrite oswap_involutive|].
      apply elem_of_map. by exists o.
  Qed.

  Lemma sswap_dom Θ : dom (sswap Θ) = set_map (oswap a b) (dom Θ).
  Proof. apply dom_kmap_L. all: try apply _. Qed.
  Lemma sswap_heads Θ : senv_heads (sswap Θ) = senv_heads Θ.
  Proof.
    apply set_eq. intros y. rewrite !elem_of_senv_heads. setoid_rewrite sswap_lookup'.
    split; intros (o & S & x & H & ->); [|exists (oswap a b o); rewrite oswap_involutive];
      eauto.
  Qed.

  Lemma sswap_disjoint_l Θ1 Θ2 : sswap Θ1 ##ₘ Θ2 ↔ Θ1 ##ₘ sswap Θ2.
  Proof. by rewrite <-sswap_disjoint, sswap_inv. Qed.

  Lemma sswap_new_env c S x Θ :
    sswap (new_env c S x Θ) = new_env (cswap a b c) S x (sswap Θ).
  Proof. unfold new_env. by rewrite !sswap_insert. Qed.

  Lemma cfresh_swap c Θ : cfresh (cswap a b c) (sswap Θ) ↔ cfresh c Θ.
  Proof.
    unfold cfresh. rewrite !not_elem_of_dom.
    rewrite <-!(sswap_lookup Θ). simpl. done.
  Qed.

  Lemma gfresh_swap ℓ g Θ : gfresh ℓ g (sswap Θ) ↔ gfresh ℓ g Θ.
  Proof.
    unfold gfresh. setoid_rewrite sswap_lookup'. split; intros H o S x Hx.
    - apply (H (oswap a b o) S x). by rewrite oswap_involutive.
    - by apply (H (oswap a b o) S x).
  Qed.

  Lemma eswap_subst1 w e : eswap a b (subst1 w e) = subst1 (eswap a b w) (eswap a b e).
  Proof. apply emap_subst1. Qed.

  Lemma eswap_thunk e : eswap a b (thunk e) = thunk (eswap a b e).
  Proof. unfold thunk. simpl. by rewrite emap_rename, eswap_subst1. Qed.

  Lemma fends_eswap e : fends (eswap a b e) = set_map (oswap a b) (fends e).
  Proof. apply fends_emap. Qed.

  Lemma tstep_unswap e α e' :
    tstep (eswap a b e) α e' → tstep e (lren (cswap a b) α) (eswap a b e').
  Proof. intros H. apply (tstep_eswap a b) in H. by rewrite eswap_involutive in H. Qed.

  Lemma irred_swap e : irred e → irred (eswap a b e).
  Proof. intros Hi α e' Hs. by apply (Hi _ _ (tstep_unswap _ _ _ Hs)). Qed.

  Lemma sends_sren σ : sends (sren (cswap a b) σ) = set_map (oswap a b) (sends σ).
  Proof. destruct σ; simpl; set_solver. Qed.

  Lemma offered_swap Θ e o : offered_t (sswap Θ) (eswap a b e) o ↔ offered_t Θ e (oswap a b o).
  Proof.
    unfold offered_t. rewrite sswap_dom. split.
    - intros [Hd (σ & e' & Hs & Ho)]. split; [apply elem_of_map in Hd as (o' & -> & ?); by rewrite oswap_involutive|].
      apply tstep_unswap in Hs. exists (sren (cswap a b) σ), (eswap a b e'). split; [done|].
      rewrite sends_sren. by apply elem_of_map_2.
    - intros [Hd (σ & e' & Hs & Ho)]. split; [apply elem_of_map; exists (oswap a b o); by rewrite oswap_involutive|].
      apply (tstep_eswap a b) in Hs. exists (sren (cswap a b) σ), (eswap a b e'). split; [done|].
      rewrite sends_sren. apply elem_of_map. exists (oswap a b o). by rewrite oswap_involutive.
  Qed.

  Lemma ready_swap W Θ F e : ready _ W(Θ ∣ F, e) → ready _ W(sswap Θ ∣ F, eswap a b e).
  Proof.
    intros H Hs. assert (stable_t e) as Hs'.
    { intros α e' Hst. apply (tstep_eswap a b) in Hst. destruct (Hs _ _ Hst) as [σ Hσ].
      destruct α; simpl in Hσ; try discriminate; eauto. }
    destruct (H Hs') as [H1 H2]. split.
    - intros Hno. rewrite is_val_emap. apply H1.
      intros o Ho. apply (Hno (oswap a b o)), offered_swap.
      by rewrite oswap_involutive.
    - destruct H2 as [(os & e' & Hl)|Hb]; [left|right].
      + apply (tstep_eswap a b) in Hl. by eexists _, _.
      + intros o S x Ho Hx. rewrite sswap_lookup' in Hx. apply offered_swap in Ho.
        destruct (Hb _ _ _ Ho Hx) as [B1 B2]. split; [|done].
        intros o' S' x' Hx' Hno. rewrite sswap_lookup' in Hx'. apply (B1 _ _ _ Hx').
        intros Hoff. by apply Hno, offered_swap.
  Qed.
End swap.

Section rel.
  Context (κ : ctable) (a b : chan).
  Local Abbreviation sw := (sswap a b).
  Local Abbreviation ew := (eswap a b).
  Local Abbreviation ow := (oswap a b).

  Definition VS n T : Prop := ∀ W Θ v, Vrel κ n W Θ T v → Vrel κ n W (sw Θ) T (ew v).
  Definition ES n T : Prop := ∀ W Θ F e, Erel κ n W Θ T F e → Erel κ n W (sw Θ) T F (ew e).

  (** One level of V, given E where the arrow reads it. *)
  Lemma V_step n T :
    (∀ j, j < n → ∀ T, VS j T ∧ ES j T) →
    (∀ T', tsize T' < tsize T → VS n T') →
    (c_beta κ = 0 → ∀ U, tsize U < tsize T → ES n U) →
    VS n T.
  Proof.
    intros IHl IHt IHe W Θ v.
    destruct T as [|ub lb c t h T1 a1 U a2|T1 a1 U a2|T1 a1 U a2|m kk C ub c t U a0|s x|lb m C T1 a0].
    - intros [-> ->]%Vrel_unit_iff. apply Vrel_unit_iff. by rewrite sswap_empty.
    - intros (e & -> & Hfe & Hlb & H)%Vrel_lolli_iff. apply Vrel_lolli_iff.
      exists (ew e). split_and!; [done|by rewrite sswap_dom, fends_eswap, Hfe|by rewrite sswap_heads|].
      intros W' j Θ' w F HW Hj Hd Hub Hw.
      assert (VS j T1) as HV1.
      { destruct (decide (j < n)); [by apply IHl|]. assert (j = n) as -> by lia. apply IHt. simpl; lia. }
      apply HV1 in Hw. rewrite <-(sswap_inv a b Θ'), <-sswap_union, <-(eswap_involutive a b w), <-eswap_subst1.
      assert (ES j U) as HEU.
      { destruct (decide (j < n)); [by apply IHl|]. assert (j = n) as -> by lia. apply IHe; [lia|simpl; lia]. }
      apply HEU, H; [done|done|by apply sswap_disjoint_l|done|done].
    - intros (v1 & v2 & Θ1 & Θ2 & -> & Hd & -> & H1 & H2)%Vrel_prod_iff. apply Vrel_prod_iff.
      exists (ew v1), (ew v2), (sw Θ1), (sw Θ2). split_and!; [done|by apply sswap_disjoint|by rewrite sswap_union| |];
        apply IHt; first [simpl; lia|done].
    - intros [(v' & -> & H)|(v' & -> & H)]%Vrel_sum_iff; apply Vrel_sum_iff; [left|right]; exists (ew v');
        (split; [done|]); apply IHt; first [simpl; lia|done].
    - intros (-> & e & -> & Hfe & H)%Vrel_box_iff. apply Vrel_box_iff. rewrite sswap_empty.
      split; [done|]. exists (ew e). split_and!; [done|by rewrite fends_eswap, Hfe, set_map_empty|].
      intros W' xs ss HW Hxs Hss Hsc HC. rewrite <-eswap_thunk, <-(sswap_empty a b).
      apply IHt; [|by apply H]. rewrite tsize_tthunk. unfold ty_inst. rewrite tsize_sinst, tsize_pinst. simpl. lia.
    - intros (o & s' & -> & -> & Hs)%Vrel_sess_iff. apply Vrel_sess_iff. exists (ow o), s'.
      by rewrite sswap_singleton.
    - intros (Hlb & xs & Hxs & HC & H)%Vrel_ex_iff. apply Vrel_ex_iff. rewrite sswap_heads.
      split; [done|]. exists xs. split_and!; [done|done|]. apply IHt; [|done].
      unfold ty_inst. rewrite tsize_pinst. simpl. lia.
  Qed.

  (** One level of E at T, given V at T and at the payloads of free sends. *)
  Lemma E_step n T :
    (∀ j, j < n → ∀ T, VS j T ∧ ES j T) → VS n T → VS n TUnit →
    (c_give κ = 0 → ∀ T', VS n T') →
    ES n T.
  Proof.
    intros IHl HVT HVU HVP. destruct n as [|n]; [unfold ES; intros; apply Erel_0|].
    intros W Θ F e HE.
    cut (∀ W Θ T0 F e, Erel κ (S n) W Θ T0 F e → T0 = T ∨ T0 = TUnit →
           Erel κ (S n) W (sw Θ) T0 F (ew e)); [intros H; by apply H; [|left]|].
    clear W Θ F e HE.
    refine (Erel_S_ind κ n _ _). intros W Θ T0 F e Hb HT0.
    assert (VS (S n) T0) as HV0 by (destruct HT0 as [->| ->]; done).
    apply Erel_S_iff. intros W1 HW1.
    destruct (Hb W1 HW1) as (Hs & Hr & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10).
    assert (∀ c Θ' e',
      at_cost_E (S n) c (Erel κ) (λ W Θ T0 F e, Erel κ (S n) W Θ T0 F e ∧
          (T0 = T ∨ T0 = TUnit → Erel κ (S n) W (sw Θ) T0 F (ew e))) W1 Θ' T0 F (ew e') →
      at_cost_E (S n) c (Erel κ) (Erel κ (S n)) W1 (sw Θ') T0 F e') as Hac.
    { intros c Θ' e' [A1 A2]. rewrite <-(eswap_involutive a b e'). split.
      - intros Hc. by apply A1.
      - intros Hc. apply (proj2 (IHl (S n - c) ltac:(lia) T0)). by apply A2. }
    split; [|split; [|unfold Esteps; split_and!]].
    - intros Hi. assert (irred e) as Hi'.
      { rewrite <-(eswap_involutive a b e). by apply irred_swap. }
      by apply HV0, Hs.
    - intros Hni. apply ready_swap, Hr. intros Hi. by apply Hni, irred_swap.
    - intros e' Hst. apply tstep_unswap in Hst. by apply Hac, H1.
    - intros ℓ c e' Hst Hc g Hg. apply tstep_unswap in Hst. simpl in Hst.
      rewrite <-(cswap_involutive a b c), cfresh_swap in Hc. apply gfresh_swap in Hg.
      destruct (H2 ℓ _ _ Hst Hc g Hg) as [S HS]. exists S.
      rewrite <-(cswap_involutive a b c) at 1. rewrite <-sswap_new_env. by apply Hac.
    - intros κf o c e' Hst Hc. apply tstep_unswap in Hst. simpl in Hst.
      rewrite <-(cswap_involutive a b c), cfresh_swap in Hc.
      destruct (H3 κf _ _ _ Hst Hc) as (S0 & x & Ho & S & HS).
      exists S0, x. split; [by rewrite sswap_lookup'|]. exists S.
      rewrite <-(cswap_involutive a b c) at 1. rewrite <-sswap_new_env. by apply Hac.
    - intros M v e' Hst. apply tstep_unswap in Hst. simpl in Hst.
      destruct (H4 _ _ _ Hst) as (ΘM & Θr & A1 & -> & A3 & A4 & A5).
      exists (sw ΘM), (sw Θr). split_and!.
      + by apply sswap_disjoint.
      + by rewrite sswap_union.
      + by rewrite sswap_dom, A3, set_map_oswap_inv.
      + destruct A4 as (e0 & Hv & Hfe & H).
        apply (f_equal ew) in Hv. rewrite eswap_involutive in Hv. subst v.
        exists (ew e0). split_and!; [done|by rewrite sswap_dom, fends_eswap, Hfe|].
        intros W' j Θ' w HW Hj Hd. split.
        * intros Hjn [-> ->]%Vrel_unit_iff. rewrite map_union_empty.
          destruct (H W' j ∅ EUnit HW Hj (map_disjoint_empty_r _)) as [B1 _].
          rewrite <-(map_union_empty (sw ΘM)), <-(sswap_empty a b), <-sswap_union.
          change EUnit with (ew EUnit). rewrite <-eswap_subst1.
          apply (proj2 (IHl j Hjn TUnit)). apply B1; [done|by apply Vrel_unit_iff].
        * intros -> [-> ->]. rewrite map_union_empty.
          destruct (H W' (S n) ∅ EUnit HW Hj (map_disjoint_empty_r _)) as [_ B2].
          destruct (B2 eq_refl (conj eq_refl eq_refl)) as [_ B3].
          rewrite <-(map_union_empty (sw ΘM)), <-(sswap_empty a b), <-sswap_union.
          change EUnit with (ew EUnit). rewrite <-eswap_subst1. by apply B3; right.
      + by apply Hac.
    - intros o M w e' Hst. apply tstep_unswap in Hst. simpl in Hst.
      destruct (H5 _ _ _ _ Hst) as (S0 & x & m' & U & b' & S & ΘM & Θr & A1 & A2 & A3 & A4 & A5 & A6 & A7).
      exists S0, x, m', U, b', S, (sw ΘM), (sw Θr). split_and!.
      + by rewrite sswap_lookup'.
      + done.
      + by apply sswap_disjoint.
      + by rewrite <-sswap_union, <-A4, sswap_delete, oswap_involutive.
      + by rewrite sswap_dom, A5, set_map_oswap_inv.
      + destruct A6 as [B1 B2]. rewrite <-(eswap_involutive a b w). split.
        * intros Hc. by apply HVP, B1.
        * intros Hc. by apply (proj1 (IHl (Datatypes.S n - c_give κ) ltac:(lia) _)), B2.
      + rewrite <-(oswap_involutive a b o) at 1. rewrite <-sswap_insert. by apply Hac.
    - intros o w e' Hst. apply tstep_unswap in Hst. simpl in Hst.
      destruct (H6 _ _ _ Hst) as (S0 & x & m' & U & b' & S & A1 & A2 & A3).
      exists S0, x, m', U, b', S. split_and!; [by rewrite sswap_lookup'|done|].
      intros j Θin Hj Hd Hw. pose proof (c_take_pos κ).
      apply (proj1 (IHl j ltac:(lia) _)) in Hw.
      rewrite <-(sswap_inv a b Θin), <-(oswap_involutive a b o) at 1.
      rewrite <-sswap_insert, <-sswap_union, <-(eswap_involutive a b e'). apply (proj2 (IHl j ltac:(lia) _)).
      apply A3; [lia|by apply sswap_disjoint_l|done].
    - intros o e' Hst. apply tstep_unswap in Hst. simpl in Hst.
      destruct (H7 _ _ Hst) as (S0 & x & A1 & A2 & A3).
      exists S0, x. split_and!; [by rewrite sswap_lookup'|done|].
      rewrite <-(oswap_involutive a b o) at 1. rewrite <-sswap_delete. by apply Hac.
    - intros o i e' Hst. apply tstep_unswap in Hst. simpl in Hst.
      destruct (H8 _ _ _ Hst) as (S0 & x & S1 & S2 & A1 & A2 & A3).
      exists S0, x, S1, S2. split_and!; [by rewrite sswap_lookup'|done|].
      rewrite <-(oswap_involutive a b o) at 1. rewrite <-sswap_insert. by apply Hac.
    - intros o i e' Hst. apply tstep_unswap in Hst. simpl in Hst.
      destruct (H9 _ _ _ Hst) as (S0 & x & S1 & S2 & A1 & A2 & A3).
      exists S0, x, S1, S2. split_and!; [by rewrite sswap_lookup'|done|].
      rewrite <-(oswap_involutive a b o) at 1. rewrite <-sswap_insert. by apply Hac.
    - intros os e' Hst. apply tstep_unswap in Hst. simpl in Hst.
      destruct (H10 _ _ Hst) as (o1 & o2 & S1 & S2 & x & A1 & A2 & A3 & A4 & A5 & A6).
      exists (ow o1), (ow o2), S1, S2, x. split_and!.
      + apply (f_equal (set_map (D:=gset cend) ow)) in A1. rewrite set_map_oswap_inv in A1.
        by rewrite A1, set_map_union_L, !set_map_singleton_L.
      + by intros ?%oswap_inj.
      + by rewrite sswap_lookup', oswap_involutive.
      + by rewrite sswap_lookup', oswap_involutive.
      + done.
      + rewrite <-!sswap_delete. by apply Hac.
  Qed.

  Lemma swap_level n : ∀ T, VS n T ∧ ES n T.
  Proof.
    induction n as [n IHn] using lt_wf_ind.
    assert (VS n TUnit) as HVU.
    { apply V_step; [done|intros T' HT|intros _ U HU]; [pose proof (tsize_pos T')|pose proof (tsize_pos U)]; simpl in *; lia. }
    destruct (decide (c_give κ = 0)) as [Hg|Hg].
    - assert (∀ T, VS n T) as HV.
      { intros T. induction T as [T IH] using tsize_ind. apply V_step; [done|done|].
        intros Hb. pose proof (c_give_pos κ Hb). lia. }
      intros T. split; [done|]. by apply E_step.
    - intros T. induction T as [T IH] using tsize_ind.
      assert (VS n T) as HVT.
      { apply V_step; [done| |]; intros; by apply IH. }
      split; [done|]. by apply E_step.
  Qed.
End rel.

Lemma Vrel_swap κ a b n W Θ T v :
  Vrel κ n W Θ T v ↔ Vrel κ n W (sswap a b Θ) T (eswap a b v).
Proof.
  split; [apply swap_level|]. intros H.
  rewrite <-(sswap_inv a b Θ), <-(eswap_involutive a b v). by apply swap_level.
Qed.

Lemma Erel_swap κ a b n W Θ T F e :
  Erel κ n W Θ T F e ↔ Erel κ n W (sswap a b Θ) T F (eswap a b e).
Proof.
  split; [apply swap_level|]. intros H.
  rewrite <-(sswap_inv a b Θ), <-(eswap_involutive a b e). by apply swap_level.
Qed.
