(** * P is closed under fusion (stage S4, decision no-fus, 2026-11-25)

    P reads its clauses at Σ and p (relation/Relation.v). This file
    proves the closure of P under renaming the held ends and under
    restricting dual pairs of the interface as one theorem:

      Prel_gfuse : p ∈ P[κ]^W _ n⟦Σ ⊢ T⟧ → fside D Σ T p → gfuse h D Σ p q →
                   q ∈ P[κ]^W _ n⟦sdrop D (kren h Σ) ⊢ T⟧

    [gfuse h D Σ p q]: h is a fusion of the held ends ([fuse_ok]), the
    restricted channels of q are those of p renamed by h together with
    D, and the threads of q are those of p with every occurrence of a
    held end o replaced by h o and every occurrence of another end by
    any end ([mcrel], compat/Occ.v). [pfuse h D p] is an instance
    ([gfuse_pfuse]). Renaming (D = ∅), internalizing (h = id) and the
    link substitution of P-Connect (h = csub o1 o2) are instances.

    [fside D Σ T p] asks that no restricted channel of p has an end in Σ,
    and, when D is not empty, that T holds no session type ([tfree T])
    and Σ holds no dual pair ([pfree Σ]). Both are needed. A process
    whose final value carries both ends of a channel is in P at a type
    that is not tfree, and restricting that channel breaks P-Stop. The
    fusion clause of the earlier definition of P excluded such a
    process, and the theorem now asks tfree T instead. P-Term asks tfree
    T as well. A τ message on a channel of Σ keeps the interface, so with
    a dual pair in Σ a received end could become restricted in p and stay
    free in q.

    The proof is a strong induction on the level with an induction over
    the steps of cost 0 inside, through the transfer of the clauses
    ([clauses_transfer]). A step of q is matched by a step of p, or, on a
    channel of D, by an offer of p followed by the dual offer of its
    successor. A link of q onto a restricted channel d that p performs
    with an end nobody holds is matched by the link of p with a new map
    that sends the two ends of d to the images of the ends of the
    removed channel. *)

From GV Require Export compat.Occ compat.Connect.
From GV Require Import fuel.FuelMono.

(** ** Fusions of processes *)

Lemma fuse_ok_proc h D Σ (p p' : proc) : p.1 = p'.1 → fuse_ok h D Σ p → fuse_ok h D Σ p'.
Proof. intros E. unfold fuse_ok, pheld. by rewrite E. Qed.

Lemma sdrop_dom D (Σ : senv) o : o ∈ dom (sdrop D Σ) ↔ o ∈ dom Σ ∧ ech o ∉ D.
Proof.
  split.
  - intros [v Hv]%elem_of_dom. apply sdrop_lookup in Hv as [A B]. split; [by eapply elem_of_dom_2|done].
  - intros [[v Hv]%elem_of_dom B]. apply elem_of_dom. exists v. by apply sdrop_lookup.
Qed.

Lemma seqv_dual' s r : seqv s r → seqv (dual s) (dual r).
Proof. unfold seqv. rewrite !sty_df_dual. apply sequiv_dual. Qed.

Lemma chans_of_elem c (Σ : senv) : c ∈ chans_of Σ ↔ ∃ o, o ∈ dom Σ ∧ ech o = c.
Proof. unfold chans_of. rewrite elem_of_map. naive_solver. Qed.

(** An occurrence of an end o stands opposite h o when o or its dual
    end is held. A map of ends that commutes with duality fixes the image
    of the dual end of a held end, and so does the relation. *)
Definition hrel (h : cend → cend) (Σ : senv) (C : gset chan) : cend → cend → Prop :=
  λ o o', (o ∈ dom Σ ∨ edual o ∈ dom Σ ∨ ech o ∈ C) → o' = h o.

Definition gfuse (h : cend → cend) (D : gset chan) (Σ : senv) (p q : proc) : Prop :=
  fuse_ok h D Σ p ∧ q.1 = set_map (gch h) p.1 ∪ D ∧ mcrel (hrel h Σ p.1) p.2 q.2.

Definition fside (D : gset chan) (Σ : senv) (T : ty) (p : proc) : Prop :=
  p.1 ## chans_of Σ ∧ tfree T ∧ pfree Σ.

Lemma gfuse_pfuse h D Σ p : fuse_ok h D Σ p → gfuse h D Σ p (pfuse h D p).
Proof.
  intros Hh. split_and!; [done|done|]. apply mcrel_emapE. by intros e o _ _ _.
Qed.

Lemma gfuse_id Σ p : gfuse id ∅ Σ p p.
Proof.
  split_and!; [apply fuse_ok_id| |].
  - destruct p as [C E]. simpl. rewrite (right_id_L ∅ (∪)). symmetry. apply set_eq. intros c.
    rewrite elem_of_map. unfold gch. simpl. split; [by intros (? & -> & ?)|eauto].
  - rewrite <-(emapE_id_map p.2) at 2. apply mcrel_emapE. by intros e o _ _ _.
Qed.

Lemma pheld_q h D Σ p q o : gfuse h D Σ p q → pheld Σ p o → pheld (sdrop D (kren h Σ)) q (h o).
Proof.
  intros (Hh & Eq & _) Ho. pose proof (pheld_fuse h D Σ p o Hh Ho) as H.
  unfold pheld in *. by rewrite Eq.
Qed.

Lemma gfuse_compose h g D D' Σ p q r :
  gfuse h D Σ p q → gfuse g D' (sdrop D (kren h Σ)) q r →
  gfuse (g ∘ h) (D' ∪ set_map (gch g) D) Σ p r ∧
  sdrop D' (kren g (sdrop D (kren h Σ))) = sdrop (D' ∪ set_map (gch g) D) (kren (g ∘ h) Σ).
Proof.
  intros Hq Hr. pose proof Hq as (Hh & Eq & Mq). pose proof Hr as (Hg & Er & Mr).
  assert (fuse_ok g D' (sdrop D (kren h Σ)) (pfuse h D p)) as Hg'.
  { eapply fuse_ok_proc; [|exact Hg]. by rewrite Eq. }
  split; [split_and!|].
  - by apply fuse_ok_compose.
  - rewrite Er, Eq. pose proof (pfuse_compose h g D D' Σ p Hh Hg') as E.
    unfold pfuse in E. simpl in E. by injection E.
  - eapply mcrel_mono; [|exact (mcrel_compose _ _ _ _ _ Mq Mr)].
    intros e e' _. apply crel_mono. intros o o'' _ (o' & H1 & H2) Ho. simpl.
    rewrite (H1 Ho) in H2. apply H2.
    assert (pheld Σ p o ∨ pheld Σ p (edual o)) as [Ho'|Ho'].
    { unfold pheld. rewrite ech_edual. tauto. }
    + pose proof (pheld_q h D Σ p q o Hq Ho') as [A|A]; [tauto|tauto].
    + pose proof (pheld_q h D Σ p q _ Hq Ho') as A. rewrite (proj1 Hh) in A.
      unfold pheld in A. rewrite ech_edual in A. tauto.
  - exact (fuse_sdrop_compose h g D D' Σ p Hh Hg').
Qed.

(** ** Fusion of every successor *)

Section transfer.
  Context (κ : ctable) (n : Ix) (Hn : olt ozero n).

  (** The obligations a fusion carries to the fused successors. *)
  Definition fclosed (Xs Xt : prel) : Prop :=
    ∀ W Σ T p q h D Σ', Xs W Σ T p → fside D Σ T p → gfuse h D Σ p q →
      senv_eqv (sdrop D (kren h Σ)) Σ' → Xt W Σ' T q.

  Definition flow : Prop :=
    ∀ j, olt j n → fclosed (Prel κ j) (Prel κ j).

  Lemma at_cost_transfer Xs Xt c W Σ T p q h D Σ' :
    flow → fclosed Xs Xt → fside D Σ T p → gfuse h D Σ p q → senv_eqv (sdrop D (kren h Σ)) Σ' →
    at_cost_P n c (Prel κ) Xs W Σ T p →
    at_cost_P n c (Prel κ) Xt W Σ' T q.
  Proof.
    intros HL HX Hs Hf HΣ [A B]. split.
    - intros Hc. eapply HX; [by apply A|done|done|done].
    - intros Hc j Hj. eapply (HL j (oadd_lt _ _ _ Hc Hj)); [by apply B|done|done|done].
  Qed.
End transfer.

(** ** Thread steps of related terms *)

Lemma thread_back (R : cend → cend → Prop) e e' α' f' : crel R e e' → tstep e' α' f' →
  ∃ a a', act e = Some a ∧ act e' = Some a' ∧ arel R a a' ∧ offers a' α'.
Proof.
  intros Hc Hs. destruct (act_step _ _ _ Hs) as (a' & Ha' & Ho).
  destruct (crel_act R e e' Hc) as [[_ E]|(a & a'' & Ha & Ha'' & Har)]; [congruence|].
  rewrite Ha' in Ha''. injection Ha'' as <-. eauto 10.
Qed.

Lemma thread_fwd (R : cend → cend → Prop) e e' a α α' f' : crel R e e' → act e = Some a → offers a α →
  tstep e' α' f' → lmatch R α α' → ∃ f, tstep e α f ∧ crel R f f'.
Proof.
  intros Hc Ha Ho Hs Hl. destruct (act_offer e a α Ha Ho) as [f Hf]. exists f. split; [done|].
  by eapply crel_tstep.
Qed.

Lemma crel_emap2 (R R' : cend → cend → Prop) g g' e e' :
  (∀ o o', o ∈ fends e → R o o' → R' (g o) (g' o')) → crel R e e' → crel R' (emap g e) (emap g' e').
Proof.
  intros H Hc. induction Hc; simpl in *; constructor;
    first [apply H; [set_solver|done]
          |apply IHHc; intros; apply H; [set_solver|done]
          |apply IHHc1; intros; apply H; [set_solver|done]
          |apply IHHc2; intros; apply H; [set_solver|done]
          |apply IHHc3; intros; apply H; [set_solver|done]].
Qed.

Lemma mrel_emap2 (R R' : cend → cend → Prop) g g' M M' :
  (∀ e o o', (∃ i, M !! i = Some e) → o ∈ fends e → R o o' → R' (g o) (g' o')) →
  mrel R M M' → mrel R' (emap g <$> M) (emap g' <$> M').
Proof.
  intros H Hm i. rewrite !lookup_fmap. specialize (Hm i). destruct (M !! i) eqn:E, (M' !! i); simpl; try done.
  apply (crel_emap2 R); [|done]. intros o o' Ho. apply (H e); eauto.
Qed.

Lemma mrel_mono_in (R R' : cend → cend → Prop) M M' :
  (∀ e o o', (∃ i, M !! i = Some e) → o ∈ fends e → R o o' → R' o o') → mrel R M M' → mrel R' M M'.
Proof.
  intros H Hm. rewrite <-(fmap_emap_id M), <-(fmap_emap_id M'). apply (mrel_emap2 R R' id id); [|done].
  intros e o o' He Ho. apply (H e); eauto.
Qed.

(** Lookups after a receive (as compat/ConnectSplit.v, which comes later). *)
Lemma recv_env_lookup' (Σ Θ2 : senv) o v :
  recv_ok Σ Θ2 →
  recv_env Σ Θ2 !! o = Some v ↔
    (Σ !! o = Some v ∧ edual o ∉ dom Θ2) ∨
    (Θ2 !! o = Some v ∧ edual o ∉ dom Σ ∧ edual o ∉ dom Θ2).
Proof.
  intros [Hok _]. unfold recv_env. rewrite lookup_union_Some_raw, !map_lookup_filter_Some, map_lookup_filter_None.
  simpl. split.
  - intros [[A B]|[_ C]]; [by left|by right].
  - intros [[A B]|[A B]].
    + by left.
    + right. split; [|done]. left.
      apply not_elem_of_dom. apply Hok. by eapply elem_of_dom_2.
Qed.

Lemma recv_back_elem' (Σ Θ2 : senv) c :
  c ∈ recv_back Σ Θ2 ↔ ∃ o, o ∈ dom Θ2 ∧ ech o = c ∧ (edual o ∈ dom Σ ∨ edual o ∈ dom Θ2).
Proof.
  unfold recv_back. rewrite elem_of_map. split.
  - intros (o & -> & Ho). apply elem_of_filter in Ho as [A B]. eauto.
  - intros (o & A & <- & B). exists o. split; [done|]. by apply elem_of_filter.
Qed.

(** ** The clauses of a fusion *)

Section clauses.
  Context (κ : ctable) (n : Ix) (Hn : olt ozero n).
  Context (Xs Xt : prel) (HL : flow κ n) (HX : fclosed Xs Xt).
  Context (HXP : ∀ W Σ T p, Xs W Σ T p → Prel κ n W Σ T p).
  Context (W1 : world) (Σ : senv) (T : ty) (p q : proc) (h : cend → cend) (D : gset chan).
  Context (Hf : gfuse h D Σ p q) (Hs : fside D Σ T p).
  Context (HC : Pclauses κ n (Vrel κ) (Prel κ) (Vrel κ n) Xs W1 Σ T p).

  Local Abbreviation Σq := (sdrop D (kren h Σ)).
  Local Abbreviation R := (hrel h Σ p.1).

  (** The ends p holds or whose dual end p holds. *)
  Local Definition hd (o : cend) : Prop := o ∈ dom Σ ∨ edual o ∈ dom Σ ∨ ech o ∈ p.1.

  Local Lemma Hok : fuse_ok h D Σ p.
  Proof. by destruct Hf. Qed.
  Local Lemma Hd : dcomm h.
  Proof. by destruct Hok. Qed.
  Local Lemma Eq1 : q.1 = set_map (gch h) p.1 ∪ D.
  Proof. by destruct Hf as (_ & ? & _). Qed.
  Local Lemma Hm : mcrel R p.2 q.2.
  Proof. by destruct Hf as (_ & _ & ?). Qed.
  Local Lemma HC1 : p.1 ## chans_of Σ.
  Proof. by destruct Hs. Qed.

  Local Lemma hinj a b : pheld Σ p a → pheld Σ p b → h a = h b → a = b.
  Proof. destruct Hok as (_ & Hi & _). apply Hi. Qed.
  Local Lemma hpart a b : pheld Σ p a → pheld Σ p b → h b = edual (h a) → b = edual a ∨ ech (h a) ∈ D.
  Proof. destruct Hok as (_ & _ & Hp & _). apply Hp. Qed.
  Local Lemma HDc : D ## set_map (gch h) p.1.
  Proof. by destruct Hok as (_ & _ & _ & ? & _). Qed.
  Local Lemma Hdp : dpairs D (kren h Σ).
  Proof. by destruct Hok as (_ & _ & _ & _ & ?). Qed.
  Local Lemma Hk : kinj h Σ.
  Proof. apply (fuse_ok_kinj h D Σ p Hok). Qed.

  Local Lemma hd_dual o : hd o ↔ hd (edual o).
  Proof. unfold hd. rewrite edual_edual, ech_edual. tauto. Qed.

  Local Lemma hd_held o : hd o → pheld Σ p o ∨ pheld Σ p (edual o).
  Proof. unfold hd, pheld. rewrite ech_edual. tauto. Qed.

  Local Lemma hR o o' : R o o' → hd o → o' = h o.
  Proof. intros H Ho. by apply H. Qed.

  Local Lemma gch_ech o : ech (h o) = gch h (ech o).
  Proof. apply ech_gch, Hd. Qed.

  Local Lemma notD a : ech a ∈ p.1 → ech (h a) ∉ D.
  Proof.
    intros Ha HD. apply (HDc (ech (h a)) HD). rewrite gch_ech. by apply elem_of_map_2.
  Qed.

  (** An end held up to duality whose image lies on a renamed restricted
      channel is an end of that channel. *)
  Local Lemma hd_chan a c : hd a → c ∈ p.1 → ech (h a) = gch h c → ech a = c.
  Proof.
    intros Ha Hc E. unfold gch in E.
    assert (pheld Σ p (EPos c)) as Hc' by (by right).
    assert (∀ b, pheld Σ p b → ech (h b) = ech (h (EPos c)) → ech b = c) as Hb.
    { intros b Hb' Eb. apply ech_eq in Eb as [Eb|Eb].
      - by rewrite <-(hinj _ _ Hc' Hb' Eb).
      - destruct (hpart b (EPos c) Hb' Hc' Eb) as [E2|HD].
        + rewrite <-(edual_edual b), <-E2. done.
        + exfalso. apply (notD (EPos c) Hc). by rewrite Eb, ech_edual. }
    destruct (hd_held a Ha) as [H|H]; [by apply Hb|].
    rewrite <-ech_edual. apply Hb; [done|]. by rewrite (Hd a), ech_edual.
  Qed.

  Local Lemma hd_inj a b : hd a → hd b → h a = h b → a = b ∨ ech (h a) ∈ D.
  Proof.
    intros Ha Hb E. destruct (hd_held a Ha) as [A|A], (hd_held b Hb) as [B|B].
    - left. by apply hinj.
    - destruct (hpart a (edual b) A B) as [E'|E']; [by rewrite Hd, E| |by right].
      left. apply edual_inj in E'. by symmetry.
    - destruct (hpart b (edual a) B A) as [E'|E']; [by rewrite Hd, E| |right; by rewrite E].
      left. by apply edual_inj in E'.
    - left. apply edual_inj. apply hinj; [done|done|]. by rewrite !Hd, E.
  Qed.

  Local Lemma lookupq o v : Σ !! o = Some v → ech (h o) ∉ D → Σq !! h o = Some v.
  Proof. intros H HD. apply sdrop_lookup. split; [|done]. by apply kren_lookup; [apply Hk|]. Qed.

  Local Lemma lookupq_inv o' v : Σq !! o' = Some v → ∃ o, o' = h o ∧ Σ !! o = Some v ∧ ech o' ∉ D.
  Proof.
    intros H. apply sdrop_lookup in H as [H HD]. destruct (kren_lookup_inv _ _ _ _ H) as (o & -> & Ho). eauto.
  Qed.

  (** A lifting of q has a related lifting of p. *)
  Local Lemma lift (qc : config) : erase qc = q → ∃ M, erase (p.1, M) = p ∧ mrel R M qc.2.
  Proof.
    intros Hq. destruct (mcrel_lift R p.2 q.2 qc.2 Hm) as (M & HM & Hr); [by rewrite <-Hq|].
    exists M. split; [|done]. unfold erase. simpl. rewrite HM. by destruct p.
  Qed.

  (** ** τ steps of q matched by τ steps of p *)

  Local Lemma tau_by (qc' : config) ev pc pc' ev0 h' D' :
    erase pc = p → istep pc ev0 pc' → ev_tau ev0 → ev_cost κ ev0 = ev_cost κ ev →
    (erase pc').1 ## chans_of Σ → (D' ≠ ∅ → D ≠ ∅) →
    gfuse h' D' Σ (erase pc') (erase qc') → senv_eqv (sdrop D' (kren h' Σ)) Σq →
    ∃ W', W1 ⊑ W' ∧ at_cost_P n (ev_cost κ ev) (Prel κ) Xt W' Σq T (erase qc').
  Proof.
    intros Hpc Hst Hτ Hc HC' HD' Hf' HΣ. destruct HC as (_ & _ & H1 & _).
    destruct (H1 pc ev0 pc' Hpc Hst Hτ HC') as (W' & HW' & A). exists W'. split; [done|].
    rewrite <-Hc. eapply at_cost_transfer; [done|done| |exact Hf'|exact HΣ|exact A].
    split; [done|apply Hs].
  Qed.

  Local Lemma gfuse_same M M' : mrel R M M' →
    gfuse h D Σ (p.1, soup M) (q.1, soup M').
  Proof.
    intros Hr. split_and!; [eapply fuse_ok_proc; [|exact Hok]; done|apply Eq1|].
    by apply mcrel_of_mrel.
  Qed.

  Local Lemma offers_beta a α : offers a α → beta_lbl α → a = ABeta ∧ α = LBeta ∨ a = AForce ∧ α = LForce.
  Proof. intros Ho [-> | ->]; destruct a; simpl in Ho; try done; auto. Qed.

  Local Lemma tau_beta M M' i α e' f' : soup M = p.2 → mrel R M M' → M' !! i = Some e' →
    tstep e' α f' → beta_lbl α →
    ∃ W', W1 ⊑ W' ∧ at_cost_P n (ev_cost κ (EvSolo i α PickNone)) (Prel κ) Xt W' Σq T (erase (q.1, <[i := f']> M')).
  Proof.
    intros HM Hr Hi Hs' Hb. destruct (mrel_lookup_r R M M' i e' Hr Hi) as (e & He & Hc).
    destruct (thread_back R e e' α f' Hc Hs') as (a & a' & Ha & Ha' & Har & Ho').
    assert (offers a α) as Ho.
    { destruct (offers_beta a' α Ho' Hb) as [[-> ->]|[-> ->]]; destruct a; simpl in Har; done. }
    destruct (thread_fwd R e e' a α α f' Hc Ha Ho Hs') as (f & Hs0 & Hcf); [by destruct Hb as [-> | ->]|].
    apply (tau_by _ _ (p.1, M) (p.1, <[i := f]> M) (EvSolo i α PickNone) h D).
    - unfold erase. simpl. rewrite HM. by destruct p.
    - by eapply p_act_beta.
    - done.
    - done.
    - apply HC1.
    - done.
    - unfold erase. simpl. apply gfuse_same. by apply mrel_insert.
    - apply senv_eqv_refl.
  Qed.

  Local Lemma erase_p M : soup M = p.2 → erase (p.1, M) = p.
  Proof. intros HM. unfold erase. simpl. rewrite HM. by destruct p. Qed.

  Local Lemma tau_spawn M M' i j v' e' f' : soup M = p.2 → mrel R M M' → M' !! i = Some e' →
    tstep e' (LSpawn v') f' → M' !! j = None →
    ∃ W', W1 ⊑ W' ∧ at_cost_P n (ev_cost κ (EvSolo i (LSpawn v') (PickChild j))) (Prel κ) Xt W' Σq T
      (erase (q.1, <[j := App v' EUnit]> (<[i := f']> M'))).
  Proof.
    intros HM Hr Hi Hs' Hj. destruct (mrel_lookup_r R M M' i e' Hr Hi) as (e & He & Hc).
    destruct (thread_back R e e' _ f' Hc Hs') as (a & a' & Ha & Ha' & Har & Ho').
    destruct a'; simpl in Ho'; try done. subst. destruct a as [| | |v| | | | | |]; simpl in Har; try done.
    destruct (thread_fwd R e e' (ASpawn v) (LSpawn v) (LSpawn v') f' Hc Ha eq_refl Hs' I) as (f & Hs0 & Hcf).
    apply (tau_by _ _ (p.1, M) (p.1, <[j := App v EUnit]> (<[i := f]> M)) (EvSolo i (LSpawn v) (PickChild j)) h D).
    - by apply erase_p.
    - eapply p_act_spawn; [done|done|]. by apply (mrel_none R M M' j Hr).
    - done.
    - done.
    - apply HC1.
    - done.
    - unfold erase. simpl. apply gfuse_same. apply mrel_insert; [by apply mrel_insert|]. auto.
    - apply senv_eqv_refl.
  Qed.

  (** A creation: p creates a channel c fresh for p and Σ, and the new map
      sends its ends to those of the channel c' that q creates. *)
  Local Definition hnew (c c' : chan) (o : cend) : cend :=
    if decide (ech o = c) then cmap (λ _, c') o else h o.

  Local Lemma hnew_dcomm c c' : dcomm (hnew c c').
  Proof.
    intros o. unfold hnew. rewrite ech_edual. case_decide; [apply cmap_edual|apply Hd].
  Qed.

  Local Lemma hnew_ne c c' o : ech o ≠ c → hnew c c' o = h o.
  Proof. intros H. unfold hnew. by rewrite decide_False. Qed.

  Local Lemma hnew_ech c c' o : ech o = c → ech (hnew c c' o) = c'.
  Proof. intros H. unfold hnew. rewrite decide_True by done. by rewrite ech_cmap. Qed.

  (** The image of a held end lies on a channel of q or of Σq. *)
  Local Lemma held_img o : pheld Σ p o → ech (h o) ∈ q.1 ∪ chans_of Σq.
  Proof.
    intros [Ho|Ho].
    - destruct (decide (ech (h o) ∈ D)) as [HD|HD]; [rewrite Eq1; set_solver|].
      apply elem_of_union_r. apply elem_of_dom in Ho as [v Hv]. apply elem_of_chans_of.
      apply elem_of_dom. exists v. by apply lookupq.
    - rewrite Eq1, gch_ech. apply elem_of_union_l, elem_of_union_l. by apply elem_of_map_2.
  Qed.

  Local Lemma tau_new M M' i c' e' f' : soup M = p.2 → mrel R M M' → M' !! i = Some e' →
    tstep e' (LNew c') f' → c' ∉ q.1 → c' ∉ echans (soup M') →
    (q.1 ∪ {[c']}) ## chans_of Σq →
    ∃ W', W1 ⊑ W' ∧ at_cost_P n (ev_cost κ (EvSolo i (LNew c') PickNone)) (Prel κ) Xt W' Σq T
      (erase (q.1 ∪ {[c']}, <[i := f']> M')).
  Proof.
    intros HM Hr Hi Hs' Hc'q Hc'E Hpre. destruct (mrel_lookup_r R M M' i e' Hr Hi) as (e & He & Hc).
    destruct (thread_back R e e' _ f' Hc Hs') as (a & a' & Ha & Ha' & Har & Ho').
    destruct a'; simpl in Ho'; try done. destruct a; simpl in Har; try done. clear Har Ho'.
    destruct (exist_fresh (p.1 ∪ echans (soup M) ∪ chans_of Σ)) as [c Hcf].
    set (h' := hnew c c').
    set (R' := hrel h' Σ (p.1 ∪ {[c]})).
    assert (c' ∉ chans_of Σq) as Hc'Σ by set_solver.
    assert (∀ o, pheld Σ p o → ech (h o) ≠ c') as Himg.
    { intros o Ho E. apply (held_img o) in Ho. rewrite E in Ho. set_solver. }
    assert (∀ o, o ∈ dom Σ → ech o ≠ c) as HΣc.
    { intros o Ho E. apply Hcf. apply elem_of_union_r. rewrite <-E. by apply elem_of_chans_of. }
    assert (∀ e0 o, e0 ∈ soup M → o ∈ fends e0 → ech o ≠ c) as HMc.
    { intros e0 o He0 Ho E. apply Hcf. apply elem_of_union_l, elem_of_union_r, elem_of_echans.
      exists e0. split; [done|]. apply elem_of_fchans. eauto. }
    assert (∀ o, pheld Σ (p.1 ∪ {[c]}, ∅) o ↔ pheld Σ p o ∨ ech o = c) as Hph.
    { intros o. unfold pheld. simpl. set_solver. }
    assert (∀ o, pheld Σ p o → ech o ≠ c) as Hpc.
    { intros o [Ho|Ho] E; [by apply (HΣc o)|]. apply Hcf. set_solver. }
    assert (∀ o, ech o = c → ∀ o2, pheld Σ p o2 → h' o ≠ h' o2 ∧ h' o ≠ edual (h' o2)) as Hsep.
    { intros o Ho o2 Ho2. unfold h'. rewrite (hnew_ne c c' o2) by (by apply Hpc).
      split; intros E; apply (Himg o2 Ho2).
      - rewrite <-E. by apply hnew_ech.
      - rewrite <-(ech_edual (h o2)), <-E. by apply hnew_ech. }
    assert (fuse_ok h' D Σ (p.1 ∪ {[c]}, soup (<[i := e]> M))) as Hok'.
    { destruct Hok as (_ & Hi' & Hp' & HD' & Hdp'). split_and!.
      - apply hnew_dcomm.
      - intros o1 o2 H1 H2 E. apply Hph in H1, H2.
        destruct (decide (ech o1 = c)) as [E1|E1], (decide (ech o2 = c)) as [E2|E2].
        + unfold h', hnew in E. rewrite !decide_True in E by done.
          destruct o1, o2; simpl in *; congruence.
        + exfalso. destruct H2 as [H2|H2]; [|done]. by apply (proj1 (Hsep o1 E1 o2 H2)).
        + exfalso. destruct H1 as [H1|H1]; [|done]. by apply (proj1 (Hsep o2 E2 o1 H1)).
        + destruct H1 as [H1|H1]; [|done]. destruct H2 as [H2|H2]; [|done].
          unfold h' in E. rewrite !hnew_ne in E by done. by apply Hi'.
      - intros o1 o2 H1 H2 E. apply Hph in H1, H2.
        destruct (decide (ech o1 = c)) as [E1|E1], (decide (ech o2 = c)) as [E2|E2].
        + left. unfold h', hnew in E. rewrite !decide_True in E by done.
          destruct o1, o2; simpl in *; congruence.
        + exfalso. destruct H2 as [H2|H2]; [|done]. apply (proj2 (Hsep o1 E1 o2 H2)).
          by rewrite E, edual_edual.
        + exfalso. destruct H1 as [H1|H1]; [|done]. by apply (proj2 (Hsep o2 E2 o1 H1)).
        + destruct H1 as [H1|H1]; [|done]. destruct H2 as [H2|H2]; [|done].
          unfold h' in E. rewrite !hnew_ne in E by done. unfold h'. rewrite hnew_ne by done. by apply Hp'.
      - intros x Hx Hx'. simpl in Hx'. apply elem_of_map in Hx' as (y & -> & Hy).
        apply elem_of_union in Hy as [Hy|Hy].
        + apply (HD' (gch h' y) Hx).
          assert (gch h' y = gch h y) as -> by (unfold gch, h'; rewrite hnew_ne; [done|simpl; set_solver]).
          by apply elem_of_map_2.
        + apply elem_of_singleton in Hy as ->. unfold gch, h' in Hx. rewrite hnew_ech in Hx by done.
          apply Hc'q. rewrite Eq1. set_solver.
      - rewrite (kren_ext h' h Σ); [done|]. intros o Ho. unfold h'. rewrite hnew_ne; [done|]. by apply HΣc. }
    assert (set_map (gch h') (p.1 ∪ {[c]}) ∪ D = q.1 ∪ {[c']}) as EC.
    { rewrite set_map_union_L, set_map_singleton_L, Eq1.
      assert (gch h' c = c') as -> by (unfold gch, h'; by rewrite hnew_ech).
      assert (set_map (gch h') p.1 = (set_map (gch h) p.1 : gset chan)) as ->.
      { apply set_eq. intros x. rewrite !elem_of_map. split; intros (y & -> & Hy); exists y;
          (split; [|done]); unfold gch, h'; rewrite hnew_ne; try done; simpl; set_solver. }
      set_solver. }
    assert (∀ o o', (∃ e0, e0 ∈ soup M ∧ o ∈ fends e0) → R o o' → R' o o') as HRR'.
    { intros o o' (e0 & He0 & Ho) HR HO. assert (ech o ≠ c) as Hoc by (by apply (HMc e0)).
      unfold h'. rewrite hnew_ne by done. apply HR. unfold R', hrel in HO.
      revert HO. rewrite elem_of_union, elem_of_singleton. tauto. }
    assert (∃ f, tstep e (LNew c) f ∧ crel R' f f') as (f & Hs0 & Hcf').
    { apply (thread_fwd R' e e' ANew (LNew c) (LNew c') f'); [|done|done|done|].
      - apply (crel_mono R); [|done]. intros o o' Ho. apply HRR'. exists e. split; [|done].
        apply elem_of_soup. eauto.
      - split; intros _; unfold h', hnew; by rewrite decide_True. }
    apply (tau_by _ _ (p.1, M) (p.1 ∪ {[c]}, <[i := f]> M) (EvSolo i (LNew c) PickNone) h' D).
    - by apply erase_p.
    - eapply p_act_new; [done|done|set_solver|set_solver].
    - done.
    - done.
    - simpl. pose proof HC1. set_solver.
    - done.
    - unfold erase. simpl. split_and!; [|done|].
      + eapply fuse_ok_proc; [|exact Hok']. done.
      + apply mcrel_of_mrel. apply mrel_insert; [|done].
        apply (mrel_mono_in R R'); [|done]. intros e0 o o' (k & Hk) Ho. apply HRR'.
        exists e0. split; [apply elem_of_soup; eauto|done].
    - rewrite (kren_ext h' h Σ); [apply senv_eqv_refl|]. intros o Ho. unfold h'. rewrite hnew_ne; [done|]. by apply HΣc.
  Qed.

  (** ** Links

      q links y1 and y2 and removes the channel of y1. p links the ends
      a1 and a2 opposite them and removes the channel of a restricted end
      b1 among them. The new map is [csub y1 y2 ∘ h]. When the channel of
      y1 is a channel of D, b1 is a2, and the channel of y2 takes its
      place in D. *)

  Local Lemma csub_cases' o1 o2 o : (o = edual o1 ∧ csub o1 o2 o = o2) ∨ (o = o1 ∧ csub o1 o2 o = edual o2) ∨
    (o ≠ edual o1 ∧ o ≠ o1 ∧ csub o1 o2 o = o).
  Proof.
    unfold csub. destruct (decide (o = edual o1)) as [A|A]; [by left|].
    destruct (decide (o = o1)) as [B|B]; [by right; left|by right; right].
  Qed.

  Local Lemma csub_ech y1 y2 o : ech o = ech y1 → ech (csub y1 y2 o) = ech y2.
  Proof.
    intros E. destruct (csub_cases' y1 y2 o) as [(-> & ->)|[(-> & ->)|(N1 & N2 & _)]]; [done|by rewrite ech_edual|].
    exfalso. apply ech_eq in E as [E|E]; subst; [done|]. by rewrite edual_edual in N1.
  Qed.

  Local Lemma csub_inj2 y1 y2 a b : csub y1 y2 a = csub y1 y2 b →
    a = b ∨ (ech a = ech y1 ∧ ech b = ech y2) ∨ (ech a = ech y2 ∧ ech b = ech y1).
  Proof.
    intros E.
    destruct (csub_cases' y1 y2 a) as [(Ea & Ra)|[(Ea & Ra)|(Na1 & Na2 & Ra)]];
    destruct (csub_cases' y1 y2 b) as [(Eb & Rb)|[(Eb & Rb)|(Nb1 & Nb2 & Rb)]];
    rewrite Ra, Rb in E; subst; rewrite ?ech_edual; try tauto.
    - exfalso. by apply (edual_ne y2).
    - exfalso. apply (edual_ne y2). by symmetry.
  Qed.

  Local Lemma tau_link_p M M' i e f f' y1 y2 a1 a2 b1 b2 :
    soup M = p.2 → mrel R M M' → M !! i = Some e →
    tstep e (LSess (SLink ({[b1]} ∪ {[b2]}))) f → crel R f f' →
    R a1 y1 → R a2 y2 → ech b1 ∈ p.1 → (b1 = a1 ∧ b2 = a2) ∨ (b1 = a2 ∧ b2 = a1) →
    ech y1 ∈ q.1 → (ech y1 ∈ D → b1 = a2) →
    ∃ W', W1 ⊑ W' ∧ at_cost_P n (ev_cost κ (EvSolo i (LSess (SLink ({[y1]} ∪ {[y2]}))) (PickLink y1 y2))) (Prel κ) Xt W' Σq T
      (erase (q.1 ∖ {[ech y1]}, emap (csub y1 y2) <$> <[i := f']> M')).
  Proof.
    intros HM Hr He Hs0 Hcf R1 R2 Hb1 Hab Hy1 HyD.
    set (h' := csub y1 y2 ∘ h).
    set (C' := p.1 ∖ {[ech b1]}).
    set (D' := if decide (ech y1 ∈ D) then (D ∖ {[ech y1]}) ∪ {[ech y2]} else D).
    set (R' := hrel h' Σ C').
    pose proof HC1 as HC1'.
    assert (hd b1) as Hhb1 by (right; right; done).
    assert (∀ x, x ∈ dom Σ → ech x ≠ ech b1) as HΣb.
    { intros x Hx E. apply (HC1' (ech b1)); [done|]. rewrite <-E. by apply elem_of_chans_of. }
    assert (∀ x, (x ∈ dom Σ ∨ edual x ∈ dom Σ ∨ ech x ∈ C') → hd x) as Hhd'.
    { intros x Hx. unfold hd, C' in *. set_solver. }
    assert (∀ x, ech x = ech b1 → ¬ (x ∈ dom Σ ∨ edual x ∈ dom Σ ∨ ech x ∈ C')) as Hnb.
    { intros x Ex [Hx|[Hx|Hx]]; [by apply (HΣb x)|apply (HΣb (edual x)); [done|by rewrite ech_edual]|].
      unfold C' in Hx. set_solver. }
    (* the image of b1 *)
    assert ((b1 = a1 ∧ b2 = a2 ∧ y1 = h b1) ∨ (b1 = a2 ∧ b2 = a1 ∧ y2 = h b1)) as Hy.
    { destruct Hab as [[-> ->]|[-> ->]]; [left|right]; split_and!; try done.
      - by apply R1. - by apply R2. }
    (* no held end of p' on the channel of y1 meets one on the channel of y2 *)
    assert (∀ x, (x ∈ dom Σ ∨ ech x ∈ C') → ech (h x) = ech (h b1) → False) as Hoff.
    { intros x Hx E. apply (Hnb x).
      - apply (hd_chan x (ech b1)); [|done|by rewrite <-gch_ech]. apply Hhd'. tauto.
      - tauto. }
    assert (∀ x1 x2, (x1 ∈ dom Σ ∨ ech x1 ∈ C') → (x2 ∈ dom Σ ∨ ech x2 ∈ C') →
      ech (h x1) = ech y1 → ech (h x2) = ech y2 → False) as Hsep.
    { intros x1 x2 H1 H2 E1 E2. destruct Hy as [(_ & _ & ->)|(_ & _ & ->)]; [by apply (Hoff x1)|by apply (Hoff x2)]. }
    (* the relation after the link *)
    assert (∀ x, (x ∈ dom Σ ∨ edual x ∈ dom Σ ∨ ech x ∈ C') → ech x = ech b1 → False) as Hnb'.
    { intros x Hx E. by apply (Hnb x E). }
    assert ((b2 ∈ dom Σ ∨ edual b2 ∈ dom Σ ∨ ech b2 ∈ C') →
      csub y1 y2 (edual (h b1)) = csub y1 y2 (h b2)) as Ebase.
    { intros Hb2. assert (hd b2) as Hhb2 by (by apply Hhd').
      assert (ech b2 ≠ ech b1) as Nb by (intros E; by apply (Hnb' b2)).
      assert (h b2 ≠ h b1) as N1.
      { intros E. destruct (hd_inj b2 b1 Hhb2 Hhb1 E) as [->|HD]; [done|]. rewrite E in HD. by apply (notD b1). }
      assert (h b2 ≠ edual (h b1)) as N2.
      { intros E. rewrite <-Hd in E. destruct (hd_inj b2 (edual b1) Hhb2 (proj1 (hd_dual b1) Hhb1) E) as [->|HD].
        - apply Nb. by rewrite ech_edual.
        - rewrite E, Hd, ech_edual in HD. by apply (notD b1). }
      destruct Hy as [(<- & <- & E1)|(<- & <- & E2)].
      - assert (y2 = h b2) as Ey2 by (by apply R2). rewrite <-E1, <-Ey2.
        destruct (csub_cases' y1 y2 (edual y1)) as [(_ & ->)|[(A & _)|(A & _)]]; [|by destruct (edual_ne y1)|done].
        destruct (decide (ech y2 = ech y1)) as [E|E]; [|by rewrite csub_ne].
        apply ech_eq in E as [E|E]; [exfalso; apply N1; by rewrite <-E1, <-Ey2, E|].
        rewrite E. unfold csub. rewrite edual_edual. by rewrite decide_True.
      - assert (y1 = h b2) as Ey1 by (by apply R1). rewrite <-E2, <-Ey1.
        unfold csub at 2. rewrite decide_False by (intros HH; apply (edual_ne y1); by symmetry). rewrite decide_True by done.
        destruct (decide (ech y2 = ech y1)) as [E|E]; [|rewrite csub_ne; [done|by rewrite ech_edual]].
        exfalso. apply ech_eq in E as [E|E].
        + apply N1. by rewrite <-E2, <-Ey1.
        + apply N2. by rewrite <-E2, <-Ey1. }
    assert (∀ o o', R o o' → R' (csub b1 b2 o) (csub y1 y2 o')) as Hrel.
    { intros o o' Ho Ho'. unfold h'. simpl.
      destruct (csub_cases' b1 b2 o) as [(-> & Ro)|[(-> & Ro)|(N1 & N2 & Ro)]]; rewrite Ro in Ho' |- *.
      - rewrite (Ho (proj1 (hd_dual b1) Hhb1)), Hd. by apply Ebase.
      - rewrite (Ho Hhb1), Hd, csub_dcomm_all, <-Ebase; [by rewrite csub_dcomm_all, edual_edual|].
        revert Ho'. rewrite edual_edual, ech_edual. tauto.
      - by rewrite (Ho (Hhd' o Ho')). }
    (* the channels *)
    assert (∀ x, x ∈ p.1 → gch h' x = if decide (gch h x = ech y1) then ech y2 else gch h x) as Hgch.
    { intros x Hx. unfold gch, h'. simpl. case_decide as E.
      - apply csub_ech. by rewrite gch_ech.
      - rewrite csub_ne; [done|]. by rewrite gch_ech. }
    assert (dcomm h') as Hd'.
    { intros o. unfold h'. simpl. by rewrite Hd, csub_dcomm_all. }
    assert (∀ x, x ∈ dom Σ → ech (h x) ≠ ech y1 → h' x = h x) as HΣh.
    { intros x Hx E. unfold h'. simpl. by rewrite csub_ne. }
    assert (∀ x, x ∈ dom Σ → ech (h x) = ech y1 → ech y1 ∈ D) as HΣy1.
    { intros x Hx E. destruct (decide (ech y1 ∈ D)) as [|HD]; [done|]. exfalso.
      assert (ech y1 ∈ (set_map (gch h) p.1 : gset chan)) as Hg by (rewrite Eq1 in Hy1; set_solver).
      apply elem_of_map in Hg as (c & Hc & Hcp).
      pose proof (hd_chan x c (or_introl Hx) Hcp (eq_trans E Hc)) as Ex.
      apply (HC1' c Hcp). rewrite <-Ex. by apply elem_of_chans_of. }
    (* the new map on held ends *)
    assert (∀ x1 x2, (x1 ∈ dom Σ ∨ ech x1 ∈ C') → (x2 ∈ dom Σ ∨ ech x2 ∈ C') →
      csub y1 y2 (h x1) = csub y1 y2 (h x2) → h x1 = h x2) as Hcinj.
    { intros x1 x2 H1 H2 E. destruct (csub_inj2 y1 y2 _ _ E) as [?|[[E1 E2]|[E1 E2]]]; [done|..].
      - by destruct (Hsep x1 x2).
      - by destruct (Hsep x2 x1). }
    assert (∀ x, (x ∈ dom Σ ∨ ech x ∈ C') → pheld Σ p x) as Hph.
    { intros x [Hx|Hx]; [by left|right]. unfold C' in Hx. set_solver. }
    assert (∀ x1 x2, (x1 ∈ dom Σ ∨ ech x1 ∈ C') → (x2 ∈ dom Σ ∨ ech x2 ∈ C') →
      h' x1 = h' x2 → x1 = x2) as Hinj'.
    { intros x1 x2 H1 H2 E. apply hinj; [by apply Hph|by apply Hph|]. by apply Hcinj. }
    assert (kinj h' Σ) as Hk'.
    { intros x1 x2 v1 v2 H1 H2 E. apply Hinj'; [left; by eapply elem_of_dom_2|left; by eapply elem_of_dom_2|done]. }
    assert (∀ x, ech (h x) ∈ D → ech (h' x) ∈ D') as HDD'.
    { intros x Hx. unfold h', D'. simpl. case_decide as Hy1D.
      - destruct (decide (ech (h x) = ech y1)) as [E|E].
        + rewrite (csub_ech y1 y2 _ E). set_solver.
        + rewrite csub_ne by done. set_solver.
      - rewrite csub_ne; [done|]. intros E. apply Hy1D. by rewrite <-E. }
    assert (fuse_ok h' D' Σ (C', ∅)) as Hok'.
    { split_and!.
      - done.
      - intros x1 x2 H1 H2 E. by apply Hinj'.
      - intros x1 x2 H1 H2 E. unfold h' in E. simpl in E. rewrite <-csub_dcomm_all in E.
        assert (h x2 = edual (h x1)) as E'.
        { destruct (csub_inj2 y1 y2 _ _ E) as [?|[[E1 E2]|[E1 E2]]]; [done|..].
          - destruct (Hsep x2 x1); [done|done|done|by rewrite <-E2, ech_edual].
          - destruct (Hsep x1 x2); [done|done|by rewrite <-E2, ech_edual|done]. }
        destruct (hpart x1 x2 (Hph x1 H1) (Hph x2 H2) E') as [?|HD]; [by left|right]. by apply HDD'.
      - intros c Hc Hc'. simpl in Hc'. apply elem_of_map in Hc' as (x & -> & Hx). unfold C' in Hx.
        assert (x ∈ p.1) as Hxp by set_solver.
        assert (gch h x ≠ ech (h b1)) as Nx.
        { intros E. apply (Hoff (EPos x)); [by right|]. by rewrite gch_ech. }
        rewrite (Hgch x Hxp) in Hc. unfold D' in Hc. case_decide as E; case_decide as Hy1D.
        + apply (HDc (ech y1) Hy1D). rewrite <-E. by apply elem_of_map_2.
        + destruct Hy as [(_ & _ & E1)|(_ & _ & E2)].
          * apply Nx. by rewrite E, E1.
          * apply (notD b1 Hb1). by rewrite <-E2.
        + apply elem_of_union in Hc as [Hc|Hc].
          * apply (HDc (gch h x)); [set_solver|by apply elem_of_map_2].
          * apply elem_of_singleton in Hc. destruct Hy as [(_ & _ & E1)|(_ & _ & E2)].
            -- apply (notD b1 Hb1). by rewrite <-E1.
            -- apply Nx. by rewrite Hc, E2.
        + apply (HDc (gch h x)); [done|by apply elem_of_map_2].
      - intros o Ho.
        assert (∀ o0 v, Σ !! o0 = Some v → kren h' Σ !! h' o0 = Some v) as Hmv.
        { intros o0 v Hv. by apply kren_lookup. }
        assert (csub y1 y2 (edual y1) = y2) as Cs1 by (unfold csub; by rewrite decide_True).
        assert (csub y1 y2 y1 = edual y2) as Cs2.
        { unfold csub. rewrite decide_False by (intros HH; apply (edual_ne y1); by symmetry). by rewrite decide_True. }
        assert (∀ o, ech o ∈ D → ech o ≠ ech y1 →
          ∃ S x S', kren h' Σ !! o = Some (S, x) ∧ kren h' Σ !! edual o = Some (S', x‾) ∧ sdual S S') as Hother.
        { intros o1 HoD Ne. destruct (Hdp o1 HoD) as (S & x & S' & L1 & L2 & Hsd). exists S, x, S'.
          destruct (kren_lookup_inv _ _ _ _ L1) as (u & -> & Hu).
          destruct (kren_lookup_inv _ _ _ _ L2) as (w & Ew & Hw).
          split_and!; [|rewrite Ew|done].
          - rewrite <-(HΣh u) by (by eapply elem_of_dom_2 || done). by apply Hmv.
          - rewrite <-(HΣh w); [by apply Hmv|by eapply elem_of_dom_2|]. by rewrite <-Ew, ech_edual. }
        unfold D' in Ho. case_decide as Hy1D.
        + apply elem_of_union in Ho as [Ho|Ho].
          * apply Hother; set_solver.
          * apply elem_of_singleton in Ho. symmetry in Ho. apply ech_eq in Ho as [Ho|Ho].
            -- destruct (Hdp (edual y1)) as (S & x & S' & L1 & L2 & Hsd); [by rewrite ech_edual|].
               rewrite edual_edual in L2. exists S, x, S'.
               destruct (kren_lookup_inv _ _ _ _ L1) as (u & Eu & Hu).
               destruct (kren_lookup_inv _ _ _ _ L2) as (w & Ew & Hw).
               split_and!; [|subst o|done].
               ++ subst o. replace y2 with (h' u) by (unfold h'; simpl; by rewrite <-Eu). by apply Hmv.
               ++ replace (edual y2) with (h' w) by (unfold h'; simpl; by rewrite <-Ew). by apply Hmv.
            -- destruct (Hdp y1) as (S & x & S' & L1 & L2 & Hsd); [done|]. exists S, x, S'.
               destruct (kren_lookup_inv _ _ _ _ L1) as (u & Eu & Hu).
               destruct (kren_lookup_inv _ _ _ _ L2) as (w & Ew & Hw).
               split_and!; [|subst o; rewrite edual_edual|done].
               ++ subst o. replace (edual y2) with (h' u) by (unfold h'; simpl; by rewrite <-Eu). by apply Hmv.
               ++ replace y2 with (h' w) by (unfold h'; simpl; by rewrite <-Ew). by apply Hmv.
        + apply Hother; [done|]. intros E. apply Hy1D. by rewrite <-E. }
    (* the restricted channels of q' *)
    assert (set_map (gch h') C' ∪ D' = q.1 ∖ {[ech y1]}) as EC.
    { rewrite Eq1. apply set_eq. intros c. split.
      - intros Hc. apply elem_of_union in Hc as [Hc|Hc].
        + apply elem_of_map in Hc as (x & -> & Hx). unfold C' in Hx.
          assert (x ∈ p.1) as Hxp by set_solver.
          assert (gch h x ≠ ech (h b1)) as Nx.
          { intros E. apply (Hoff (EPos x)); [by right|]. by rewrite gch_ech. }
          rewrite (Hgch x Hxp). case_decide as E.
          * destruct Hy as [(_ & _ & E1)|(_ & _ & E2)]; [exfalso; apply Nx; by rewrite E, E1|].
            rewrite E2, gch_ech. apply elem_of_difference. split; [apply elem_of_union_l; by apply elem_of_map_2|].
            rewrite elem_of_singleton. intros E'. apply Nx. by rewrite E, <-E', gch_ech.
          * apply elem_of_difference. split; [apply elem_of_union_l; by apply elem_of_map_2|set_solver].
        + unfold D' in Hc. case_decide as Hy1D; [|].
          * apply elem_of_union in Hc as [Hc|Hc]; [set_solver|]. apply elem_of_singleton in Hc as ->.
            destruct Hy as [(_ & _ & E1)|(_ & _ & E2)]; [exfalso; apply (notD b1 Hb1); by rewrite <-E1|].
            rewrite E2, gch_ech. apply elem_of_difference. split; [apply elem_of_union_l; by apply elem_of_map_2|].
            rewrite elem_of_singleton. intros E. apply (notD b1 Hb1). by rewrite gch_ech, E.
          * apply elem_of_difference. split; [set_solver|]. rewrite elem_of_singleton. intros ->. done.
      - intros Hc. apply elem_of_difference in Hc as [Hc Hne]. rewrite elem_of_singleton in Hne.
        apply elem_of_union in Hc as [Hc|Hc].
        + apply elem_of_map in Hc as (x & -> & Hx).
          destruct (decide (x = ech b1)) as [->|Nxb].
          * destruct Hy as [(_ & _ & E1)|(_ & _ & E2)]; [exfalso; apply Hne; by rewrite E1, gch_ech|].
            unfold D'. case_decide as Hy1D.
            -- apply elem_of_union_r, elem_of_union_r, elem_of_singleton. by rewrite E2, gch_ech.
            -- assert (ech y1 ∈ (set_map (gch h) p.1 : gset chan)) as Hg by (rewrite Eq1 in Hy1; set_solver).
               apply elem_of_map in Hg as (d & Ed & Hd1).
               assert (d ≠ ech b1) as Ndb by (intros ->; apply Hne; done).
               apply elem_of_union_l, elem_of_map. exists d. split; [|unfold C'; set_solver].
               rewrite (Hgch d Hd1), decide_True by done. by rewrite E2, gch_ech.
          * apply elem_of_union_l, elem_of_map. exists x. split; [|unfold C'; set_solver].
            rewrite (Hgch x Hx), decide_False by done. done.
        + apply elem_of_union_r. unfold D'. case_decide; set_solver. }
    (* the interface *)
    assert (sdrop D' (kren h' Σ) = Σq) as EΣ.
    { apply map_eq. intros o'. apply option_eq. intros v. rewrite !sdrop_lookup. split.
      - intros [L N]. destruct (kren_lookup_inv _ _ _ _ L) as (o0 & -> & Ho0).
        assert (ech (h o0) ≠ ech y1) as Ny.
        { intros E. apply N. unfold h'. simpl. rewrite (csub_ech y1 y2 _ E). unfold D'.
          rewrite decide_True; [set_solver|]. by apply (HΣy1 o0); [eapply elem_of_dom_2|]. }
        rewrite HΣh in N |- * by (by eapply elem_of_dom_2 || done). split; [by apply kren_lookup; [apply Hk|]|].
        intros HD. apply N. unfold D'. case_decide; set_solver.
      - intros [L N]. destruct (kren_lookup_inv _ _ _ _ L) as (o0 & -> & Ho0).
        assert (ech (h o0) ≠ ech y1) as Ny.
        { intros E. destruct (decide (ech y1 ∈ D)) as [HD|HD]; [apply N; by rewrite E|].
          apply HD. by apply (HΣy1 o0); [eapply elem_of_dom_2|]. }
        rewrite <-HΣh by (by eapply elem_of_dom_2 || done). split; [by apply kren_lookup|].
        unfold D'. rewrite HΣh by (by eapply elem_of_dom_2 || done). case_decide as Hy1D; [|done].
        rewrite elem_of_union, elem_of_difference, !elem_of_singleton. intros [[? _]|E]; [done|].
        destruct Hy as [(_ & _ & E1)|(_ & _ & E2)].
        + apply (notD b1 Hb1). by rewrite <-E1.
        + apply (Hoff o0); [left; by eapply elem_of_dom_2|]. by rewrite E, E2. }
    apply (tau_by _ _ (p.1, M) (C', emap (csub b1 b2) <$> <[i := f]> M)
      (EvSolo i (LSess (SLink ({[b1]} ∪ {[b2]}))) (PickLink b1 b2)) h' D').
    - by apply erase_p.
    - by eapply p_act_link.
    - done.
    - done.
    - simpl. unfold C'. pose proof HC1'. set_solver.
    - unfold D'. case_decide; [set_solver|done].
    - unfold erase. simpl. split_and!.
      + eapply fuse_ok_proc; [|exact Hok']. done.
      + simpl. by rewrite EC.
      + apply mcrel_of_mrel. apply (mrel_emap2 R R'); [|by apply mrel_insert].
        intros e0 o o' _ _ Hoo'. by apply Hrel.
    - rewrite EΣ. apply senv_eqv_refl.
  Qed.

  Local Lemma senv_eqv_entries (Θ Θ' : senv) :
    (∀ o v, Θ !! o = Some v → ∃ v', Θ' !! o = Some v' ∧ seqe v v') → (∀ o, o ∈ dom Θ' → o ∈ dom Θ) →
    senv_eqv Θ Θ'.
  Proof.
    intros H1 H2 o. destruct (Θ !! o) as [v|] eqn:E.
    - destruct (H1 o v E) as (v' & -> & Hv). by constructor.
    - destruct (Θ' !! o) eqn:E'; [|constructor]. exfalso.
      assert (o ∈ dom Θ) as [? ?]%elem_of_dom by (apply H2; by eapply elem_of_dom_2). congruence.
  Qed.

  Local Lemma csub_collapse y1 y2 a b : csub y1 y2 a = csub y1 y2 b → a = b ∨ a = y1 ∨ a = y2 ∨ b = y1 ∨ b = y2.
  Proof.
    intros E.
    destruct (csub_cases' y1 y2 a) as [(Ea & Ra)|[(Ea & Ra)|(Na1 & Na2 & Ra)]];
    destruct (csub_cases' y1 y2 b) as [(Eb & Rb)|[(Eb & Rb)|(Nb1 & Nb2 & Rb)]];
    rewrite Ra, Rb in E; subst; try tauto.
    all: exfalso; first [by apply (edual_ne y2)|apply (edual_ne y2); by symmetry].
  Qed.

  (** A link that q takes on a channel of D and p offers on two ends of
      its interface. *)
  Local Lemma tau_link_off M M' i e f f' y1 y2 a1 a2 :
    soup M = p.2 → mrel R M M' → M !! i = Some e →
    tstep e (LSess (SLink ({[a1]} ∪ {[a2]}))) f → crel R f f' →
    R a1 y1 → R a2 y2 → ech a1 ∉ p.1 → ech a2 ∉ p.1 → ech y1 ∈ D →
    ∃ W', W1 ⊑ W' ∧ at_cost_P n (ev_cost κ (EvSolo i (LSess (SLink ({[y1]} ∪ {[y2]}))) (PickLink y1 y2))) (Prel κ) Xt W' Σq T
      (erase (q.1 ∖ {[ech y1]}, emap (csub y1 y2) <$> <[i := f']> M')).
  Proof.
    intros HM Hr He Hs0 Hcf R1 R2 Na1 Na2 Hy1D.
    assert (subjs (SLink ({[a1]} ∪ {[a2]})) ## p.1) as Hsj.
    { simpl. rewrite set_map_union_L, !set_map_singleton_L. set_solver. }
    pose proof (p_act_session p.1 M i e (SLink ({[a1]} ∪ {[a2]})) f He Hs0 Hsj) as Hst.
    destruct HC as (_ & _ & _ & _ & _ & _ & _ & _ & H7).
    destruct (H7 _ _ _ _ (erase_p M HM) Hst) as (o1 & o2 & S1 & S2 & x0 & Eos & No & L1 & L2 & Hsd & A).
    simpl in A. rewrite difference_empty_L in A.
    assert (D ≠ ∅) as HDne by set_solver.
    destruct (proj2 Hs) as [HT Hpf].
    assert (a1 ∈ dom Σ ∧ a2 ∈ dom Σ) as [Ha1 Ha2].
    { assert (a1 ∈ ({[o1]} ∪ {[o2]} : gset cend)) as A1 by (rewrite <-Eos; set_solver).
      assert (a2 ∈ ({[o1]} ∪ {[o2]} : gset cend)) as A2 by (rewrite <-Eos; set_solver).
      split; [apply elem_of_union in A1 as [?%elem_of_singleton|?%elem_of_singleton]
             |apply elem_of_union in A2 as [?%elem_of_singleton|?%elem_of_singleton]]; subst;
        eapply elem_of_dom_2; eauto. }
    assert (y1 = h a1) as Ey1 by (apply R1; by left).
    assert (y2 = h a2) as Ey2 by (apply R2; by left).
    assert (a1 ≠ a2) as Na12.
    { intros <-. apply No. assert (o1 ∈ ({[a1]} ∪ {[a1]} : gset cend)) as B1 by (rewrite Eos; set_solver).
      assert (o2 ∈ ({[a1]} ∪ {[a1]} : gset cend)) as B2 by (rewrite Eos; set_solver). set_solver. }
    (* the types: a1 at A1 and point z, a2 at A2 and point z‾ *)
    assert (∃ A1 A2 z, Σ !! a1 = Some (A1, z) ∧ Σ !! a2 = Some (A2, z‾) ∧ sdual A1 A2) as (A1 & A2 & z & La1 & La2 & Hs12).
    { assert ((a1 = o1 ∧ a2 = o2) ∨ (a1 = o2 ∧ a2 = o1)) as [[-> ->]|[-> ->]].
      { assert (a1 ∈ ({[o1]} ∪ {[o2]} : gset cend)) as A1 by (rewrite <-Eos; set_solver).
        apply elem_of_union in A1 as [A1|A1]; apply elem_of_singleton in A1 as ->; [left|right]; split; [done| |done|].
        - assert (a2 ∈ ({[o1]} ∪ {[o2]} : gset cend)) as A2 by (rewrite <-Eos; set_solver). set_solver.
        - assert (a2 ∈ ({[o1]} ∪ {[o2]} : gset cend)) as A2 by (rewrite <-Eos; set_solver). set_solver. }
      - by exists S1, S2, x0.
      - exists S2, S1, x0‾. rewrite pt_dual_dual. split_and!; [done|done|by apply sdual_sym]. }
    assert (delete o1 (delete o2 Σ) = delete a1 (delete a2 Σ)) as EΣ'.
    { assert ((a1 = o1 ∧ a2 = o2) ∨ (a1 = o2 ∧ a2 = o1)) as [[-> ->]|[-> ->]]; [|done|apply delete_delete].
      assert (a1 ∈ ({[o1]} ∪ {[o2]} : gset cend)) as B1 by (rewrite <-Eos; set_solver).
      assert (a2 ∈ ({[o1]} ∪ {[o2]} : gset cend)) as B2 by (rewrite <-Eos; set_solver).
      set_solver. }
    rewrite EΣ' in A. set (Σ' := delete a1 (delete a2 Σ)) in *.
    (* the partner ob of a1 in D *)
    destruct (Hdp y1 Hy1D) as (B1 & u & B2 & K1 & K2 & HsB).
    rewrite Ey1 in K1. apply (kren_lookup_held h Σ a1) in K1; [|apply Hk|done]. rewrite La1 in K1. injection K1 as <- <-.
    destruct (kren_lookup_inv _ _ _ _ K2) as (ob & Eob & Lob).
    assert (ob ∈ dom Σ) as Hob by (by eapply elem_of_dom_2).
    assert (∀ x, x ∈ dom Σ' ↔ x ∈ dom Σ ∧ x ≠ a1 ∧ x ≠ a2) as HdΣ'.
    { intros x. unfold Σ'. rewrite !dom_delete_L. set_solver. }
    assert (∀ x v, Σ' !! x = Some v → Σ !! x = Some v) as HΣ'.
    { intros x v Hv. unfold Σ' in Hv. apply lookup_delete_Some in Hv as [_ Hv]. by apply lookup_delete_Some in Hv as [_ Hv]. }
    assert (∀ x, x ≠ a1 → x ≠ a2 → Σ' !! x = Σ !! x) as HΣ''.
    { intros x N1 N2. unfold Σ'. by rewrite !lookup_delete_ne. }
    set (C := p.1).
    assert (∀ x, (x ∈ dom Σ' ∨ ech x ∈ C) → pheld Σ p x) as Hph'.
    { intros x [Hx|Hx]; [left; by apply HdΣ'|by right]. }
    assert (∀ x, (x ∈ dom Σ' ∨ ech x ∈ C) → h x ≠ y1 ∧ h x ≠ y2) as FA.
    { intros x Hx. split; intros E.
      - assert (x = a1) as -> by (apply hinj; [by apply Hph'|by left|by rewrite E]).
        destruct Hx as [Hx|Hx]; [by apply HdΣ' in Hx as (_ & ? & _)|done].
      - assert (x = a2) as -> by (apply hinj; [by apply Hph'|by left|by rewrite E]).
        destruct Hx as [Hx|Hx]; [by apply HdΣ' in Hx as (_ & _ & ?)|done]. }
    assert (y2 ≠ y1) as Ny21.
    { intros E. apply Na12. apply hinj; [by left|by left|by rewrite <-Ey1, <-Ey2]. }
    assert (ech y1 ∉ (set_map (gch h) C : gset chan)) as Hy1C.
    { intros Hin. by apply (HDc (ech y1)). }
    assert (pfree Σ') as Hpf'.
    { intros x Hx Hx'. apply HdΣ' in Hx as [Hx _]. apply HdΣ' in Hx' as [Hx' _]. by apply (Hpf x). }
    set (D' := D ∖ {[ech y1]}).
    assert (fside D' Σ' T (C, soup (<[i := f]> M))) as Hs'.
    { split; [|exact (conj (proj1 (proj2 Hs)) Hpf')]. simpl. intros c Hc Hc'. apply (HC1 c Hc).
      apply chans_of_elem in Hc' as (x & Hx & <-). apply elem_of_chans_of. by apply HdΣ'. }
    assert (set_map (gch h) C ∪ D' = q.1 ∖ {[ech y1]}) as ECh.
    { rewrite Eq1. unfold D'. set_solver. }
    assert (∀ x, x ∈ dom Σ' → ech (h x) = ech y1 → x = ob) as Hony1.
    { intros x Hx E. apply ech_eq in E as [E|E].
      - exfalso. apply (proj1 (FA x (or_introl Hx))). by symmetry.
      - apply hinj; [by apply Hph'; left|by left|]. by rewrite <-Eob, E, edual_edual. }
    assert (∀ x y, (x ∈ dom Σ' ∨ ech x ∈ C) → (y ∈ dom Σ' ∨ ech y ∈ C) →
      h y = edual (h x) → ech (h x) ∈ D → y = edual x ∨ ech (h x) ∈ D') as Hpart'.
    { intros x y Hx Hy E HD. destruct (decide (ech (h x) = ech y1)) as [E1|E1]; [|right; unfold D'; set_solver].
      exfalso. apply ech_eq in E1 as [E1|E1]; [apply (proj1 (FA x Hx)); by symmetry|].
      apply (proj1 (FA y Hy)). rewrite E. by symmetry. }
    assert (kinj h Σ') as Hk'.
    { apply (kinj_sub h Σ); [|apply Hk]. intros x Hx. by apply HdΣ' in Hx as [? _]. }
    destruct (decide (y2 = edual y1)) as [Eyy|Nyy].
    - (* the link of the two ends of the pair *)
      assert (a2 = ob) as Eab by (apply hinj; [by left|by left|by rewrite <-Ey2, Eyy, Eob]).
      assert (∀ o, csub y1 y2 o = o) as Cid.
      { intros o. rewrite Eyy. unfold csub. repeat case_decide; subst; rewrite ?edual_edual; done. }
      assert (sdrop D' (kren h Σ') = Σq) as EΣq.
      { apply map_eq. intros o'. apply option_eq. intros v. rewrite !sdrop_lookup. split.
        - intros [L N]. destruct (kren_lookup_inv _ _ _ _ L) as (x & -> & Hx).
          assert (ech (h x) ≠ ech y1) as Nx.
          { intros E. pose proof (Hony1 x (elem_of_dom_2 _ _ _ Hx) E) as ->.
            apply elem_of_dom_2 in Hx. apply HdΣ' in Hx as (_ & _ & Hx). apply Hx. by symmetry. }
          split; [apply kren_lookup; [apply Hk|by apply HΣ']|unfold D' in N; set_solver].
        - intros [L N]. destruct (kren_lookup_inv _ _ _ _ L) as (x & -> & Hx).
          assert (x ≠ a1) as Nx1 by (intros ->; apply N; by rewrite <-Ey1).
          assert (x ≠ a2) as Nx2 by (intros ->; apply N; by rewrite <-Ey2, Eyy, ech_edual).
          split; [apply kren_lookup; [done|by rewrite HΣ''] |unfold D'; set_solver]. }
      exists W1. split; [apply wext_refl|]. simpl.
      eapply (at_cost_transfer κ n Xs Xt _ _ _ _ _ _ h D'); [done|done|exact Hs'| |rewrite EΣq; apply senv_eqv_refl|exact A].
      unfold erase. simpl. split_and!.
      + split_and!.
        * apply Hd.
        * intros x1 x2 H1 H2 E. apply hinj; [by apply Hph'|by apply Hph'|done].
        * intros x1 x2 H1 H2 E. destruct (hpart x1 x2 (Hph' x1 H1) (Hph' x2 H2) E) as [?|HD]; [by left|].
          by apply Hpart'.
        * intros c Hc1 Hc2. apply (HDc c); [unfold D' in Hc1; set_solver|done].
        * intros o Ho. destruct (Hdp o) as (S & x & S' & K3 & K4 & Hs3); [unfold D' in Ho; set_solver|].
          exists S, x, S'. split_and!; [| |done].
          -- destruct (kren_lookup_inv _ _ _ _ K3) as (w & -> & Hw).
             assert (w ≠ a1) as N1 by (intros ->; unfold D' in Ho; rewrite <-Ey1 in Ho; set_solver).
             assert (w ≠ a2) as N2 by (intros ->; unfold D' in Ho; rewrite <-Ey2, Eyy, ech_edual in Ho; set_solver).
             apply kren_lookup; [done|by rewrite HΣ''].
          -- destruct (kren_lookup_inv _ _ _ _ K4) as (w & Ew & Hw). rewrite Ew.
             assert (w ≠ a1) as N1 by (intros ->; unfold D' in Ho; rewrite <-ech_edual, Ew, <-Ey1 in Ho; set_solver).
             assert (w ≠ a2) as N2 by (intros ->; unfold D' in Ho; rewrite <-ech_edual, Ew, <-Ey2, Eyy, ech_edual in Ho; set_solver).
             apply kren_lookup; [done|by rewrite HΣ''].
      + simpl. by rewrite ECh.
      + apply mcrel_of_mrel. rewrite (map_fmap_ext (emap (csub y1 y2)) id); [rewrite map_fmap_id|].
        * apply (mrel_mono_in R); [|by apply mrel_insert]. intros e0 o o' _ _ Hoo' Ho. apply Hoo'.
          destruct Ho as [Ho|[Ho|Ho]]; [left; by apply HdΣ'|right; left; by apply HdΣ'|by right; right].
        * intros j0 e0 _. simpl. rewrite <-(emap_id e0) at 2. apply emap_ext. intros o. apply Cid.
    - (* the channel of y2 takes the place of that of y1 opposite ob *)
      assert (ech y2 ≠ ech y1) as Nc.
      { intros E. apply ech_eq in E as [E|E]; [by apply Ny21|]. apply Nyy. by rewrite E, edual_edual. }
      assert (ob ≠ a1) as Nob1 by (intros ->; apply (edual_ne y1); by rewrite Eob, Ey1).
      assert (ob ≠ a2) as Nob2 by (intros ->; apply Nyy; by rewrite Eob, Ey2).
      assert (ob ∈ dom Σ') as Hob' by (apply HdΣ'; auto).
      set (h' := csub y1 y2 ∘ h).
      assert (h' ob = y2) as Hob2 by (unfold h'; simpl; rewrite <-Eob; unfold csub; by rewrite decide_True).
      assert (∀ x, ech (h x) ≠ ech y1 → h' x = h x) as Hh'.
      { intros x E. unfold h'. simpl. by rewrite csub_ne. }
      assert (∀ x, (x ∈ dom Σ' ∨ ech x ∈ C) → x ≠ ob → ech (h x) ≠ ech y1) as Hny1.
      { intros x Hx Nx E. apply ech_eq in E as [E|E]; [apply (proj1 (FA x Hx)); by symmetry|].
        apply Nx. apply hinj; [by apply Hph'|by left|]. by rewrite <-Eob, E, edual_edual. }
      assert (∀ x, (x ∈ dom Σ' ∨ ech x ∈ C) → h x = edual y2 → ech y2 ∈ D) as Hy2D.
      { intros x Hx E. rewrite Ey2 in E. destruct (hpart a2 x (or_introl Ha2) (Hph' x Hx) E) as [->|HD].
        - exfalso. destruct Hx as [Hx|Hx].
          + apply HdΣ' in Hx as [Hx _]. by apply (Hpf a2).
          + apply Na2. by rewrite <-ech_edual.
        - by rewrite Ey2. }
      assert (∀ x1 x2, (x1 ∈ dom Σ' ∨ ech x1 ∈ C) → (x2 ∈ dom Σ' ∨ ech x2 ∈ C) → h' x1 = h' x2 → x1 = x2) as Hinj'.
      { intros x1 x2 H1 H2 E. unfold h' in E. simpl in E.
        destruct (csub_collapse y1 y2 _ _ E) as [E'|[E'|[E'|[E'|E']]]].
        - apply hinj; [by apply Hph'|by apply Hph'|done].
        - by destruct (proj1 (FA x1 H1)).
        - by destruct (proj2 (FA x1 H1)).
        - by destruct (proj1 (FA x2 H2)).
        - by destruct (proj2 (FA x2 H2)). }
      assert (kinj h' Σ') as Hk''.
      { intros x1 x2 v1 v2 K1' K2' E. apply Hinj'; [left; by eapply elem_of_dom_2|left; by eapply elem_of_dom_2|done]. }
      assert (ech y2 ∈ D → ech y2 ∈ D') as Hy2D' by (intros HD; unfold D'; set_solver).
      assert (fuse_ok h' D' Σ' (C, ∅)) as Hok'.
      { split_and!.
        - intros o. unfold h'. simpl. by rewrite Hd, csub_dcomm_all.
        - intros x1 x2 H1 H2 E. by apply Hinj'.
        - intros x1 x2 H1 H2 E. unfold h' in E. simpl in E. rewrite <-csub_dcomm_all in E.
          destruct (csub_collapse y1 y2 _ _ E) as [E'|[E'|[E'|[E'|E']]]].
          + destruct (hpart x1 x2 (Hph' x1 H1) (Hph' x2 H2) E') as [?|HD]; [by left|right].
            destruct (decide (x1 = ob)) as [->|Nx].
            * exfalso. apply (proj1 (FA x2 H2)). by rewrite E', <-Eob, edual_edual.
            * rewrite Hh' by (by apply Hny1). unfold D'. apply elem_of_difference. split; [done|].
              rewrite elem_of_singleton. by apply Hny1.
          + by destruct (proj1 (FA x2 H2)).
          + by destruct (proj2 (FA x2 H2)).
          + assert (x1 = ob) as -> by (apply hinj; [by apply Hph'|by left|by rewrite <-Eob, <-E', edual_edual]).
            right. rewrite Hob2. apply Hy2D'.
            destruct (csub_cases' y1 y2 (h x2)) as [(A1' & A2')|[(A1' & A2')|(A1' & A2' & A3')]].
            * exfalso. rewrite A2', <-Eob, edual_edual in E. unfold csub in E.
              rewrite decide_False in E by (intros HH; apply (edual_ne y1); by symmetry).
              rewrite decide_True in E by done. by apply (edual_ne y2).
            * by destruct (proj1 (FA x2 H2)).
            * apply (Hy2D x2 H2). rewrite <-A3', E, <-Eob, edual_edual. unfold csub.
              rewrite decide_False by (intros HH; apply (edual_ne y1); by symmetry). by rewrite decide_True.
          + right. assert (h x1 = edual y2) as Ex1 by (by rewrite <-E', edual_edual).
            assert (x1 ≠ ob) as Nx.
            { intros ->. apply Ny21. apply edual_inj. by rewrite <-Ex1, <-Eob. }
            rewrite Hh' by (by apply Hny1). rewrite Ex1, ech_edual. by apply Hy2D', (Hy2D x1).
        - intros c Hc1 Hc2. simpl in Hc2. apply elem_of_map in Hc2 as (x & -> & Hx).
          assert (gch h' x = gch h x) as Eg.
          { unfold gch. rewrite Hh'; [done|]. rewrite gch_ech. intros E. apply Hy1C. rewrite <-E. by apply elem_of_map_2. }
          rewrite Eg in Hc1. apply (HDc (gch h x)); [unfold D' in Hc1; set_solver|by apply elem_of_map_2].
        - intros o Ho. assert (ech o ∈ D ∧ ech o ≠ ech y1) as [HoD Hoy1] by (unfold D' in Ho; set_solver).
          assert (∀ w v, Σ' !! w = Some v → kren h' Σ' !! h' w = Some v) as Hmv by (intros; by apply kren_lookup).
          destruct (decide (ech o = ech y2)) as [Eo|Eo].
          + (* the pair of y2: ob and the partner of a2 *)
            destruct (Hdp y2) as (A2' & z2 & C2 & K5 & K6 & Hs5); [by rewrite <-Eo|].
            rewrite Ey2 in K5. apply (kren_lookup_held h Σ a2) in K5; [|apply Hk|done].
            rewrite La2 in K5. injection K5 as <- <-.
            destruct (kren_lookup_inv _ _ _ _ K6) as (a2' & Ea2' & La2').
            assert (a2' ≠ a1) as N1.
            { intros ->. apply Nc. by rewrite Ey1, <-Ea2', ech_edual. }
            assert (a2' ≠ a2) as N2 by (intros ->; apply (edual_ne y2); by rewrite Ea2', Ey2).
            assert (Σ' !! a2' = Some (C2, z‾‾)) as La2'' by (rewrite HΣ''; done).
            assert (Σ' !! ob = Some (B2, z‾)) as Lob' by (rewrite HΣ''; done).
            assert (h' a2' = edual y2) as Ha2'.
            { rewrite Hh'; [done|]. rewrite <-Ea2', ech_edual. done. }
            assert (sdual B2 C2) as HBC.
            { unfold sdual in *. eapply seqv_trans; [exact Hs5|]. apply seqv_sym.
              eapply seqv_trans; [apply seqv_dual'; exact HsB|]. rewrite dual_involutive.
              eapply seqv_trans; [|apply seqv_dual'; apply seqv_sym; exact Hs12]. rewrite dual_involutive. apply seqv_refl. }
            symmetry in Eo. apply ech_eq in Eo as [-> | ->].
            * exists B2, z‾, C2. split_and!; [rewrite <-Hob2; by apply Hmv| |done].
              rewrite <-Ha2', pt_dual_dual. rewrite pt_dual_dual in La2''. by apply Hmv.
            * exists C2, z, B2. rewrite edual_edual. split_and!.
              -- rewrite <-Ha2'. rewrite pt_dual_dual in La2''. by apply Hmv.
              -- rewrite <-Hob2. by apply Hmv.
              -- by apply sdual_sym.
          + destruct (Hdp o HoD) as (S & x & S' & K3 & K4 & Hs3). exists S, x, S'.
            destruct (kren_lookup_inv _ _ _ _ K3) as (w1 & -> & Hw1).
            destruct (kren_lookup_inv _ _ _ _ K4) as (w2 & Ew2 & Hw2).
            assert (∀ w, ech (h w) ≠ ech y1 → ech (h w) ≠ ech y2 → w ≠ a1 ∧ w ≠ a2 ∧ w ≠ ob) as Hw.
            { intros w E1 E2. split_and!; intros ->; [apply E1; by rewrite <-Ey1|apply E2; by rewrite <-Ey2
                |apply E1; by rewrite <-Eob, ech_edual]. }
            destruct (Hw w1) as (W11 & W12 & _); [done|done|].
            destruct (Hw w2) as (W21 & W22 & _); [rewrite <-Ew2, ech_edual; done|rewrite <-Ew2, ech_edual; done|].
            split_and!; [| |done].
            * rewrite <-(Hh' w1) by done. apply Hmv. by rewrite HΣ''.
            * rewrite Ew2, <-(Hh' w2) by (rewrite <-Ew2, ech_edual; done). apply Hmv. by rewrite HΣ''. }
      (* the interface up to ≈ *)
      assert (senv_eqv (sdrop D' (kren h' Σ')) Σq) as HΣq.
      { apply senv_eqv_entries.
        - intros o' v Hv. apply sdrop_lookup in Hv as [L N]. destruct (kren_lookup_inv _ _ _ _ L) as (w & -> & Hw).
          destruct (decide (w = ob)) as [->|Nw].
          + rewrite Hob2 in N |- *. rewrite HΣ'' in Hw by done. rewrite Lob in Hw. injection Hw as <-.
            exists (A2, z‾). split; [|split; [done|]].
            * rewrite Ey2. apply lookupq; [done|]. rewrite <-Ey2. intros HD. apply N. by apply Hy2D'.
            * simpl. unfold sdual in *. eapply seqv_trans; [exact HsB|]. by apply seqv_sym.
          + assert (ech (h w) ≠ ech y1) as Nw1 by (apply Hny1; [left; by eapply elem_of_dom_2|done]).
            rewrite Hh' in N |- * by done. exists v. split; [|split; [done|apply seqv_refl]].
            apply lookupq; [by apply HΣ'|]. intros HD. apply N. unfold D'. set_solver.
        - intros o' Ho'. apply elem_of_dom in Ho' as [v Hv]. destruct (lookupq_inv _ _ Hv) as (w & -> & Hw & N).
          assert (w ≠ a1) as Nw1 by (intros ->; apply N; by rewrite <-Ey1).
          apply elem_of_dom. destruct (decide (w = a2)) as [->|Nw2].
          + rewrite <-Ey2. exists (B2, z‾). apply sdrop_lookup. split.
            * rewrite <-Hob2. apply kren_lookup; [done|]. by rewrite HΣ''.
            * rewrite <-Ey2 in N. unfold D'. set_solver.
          + assert (ech (h w) ≠ ech y1) as Nw by (intros E; apply N; by rewrite E).
            exists v. apply sdrop_lookup. split.
            * rewrite <-(Hh' w) by done. apply kren_lookup; [done|]. by rewrite HΣ''.
            * unfold D'. set_solver. }
      exists W1. split; [apply wext_refl|]. simpl.
      eapply (at_cost_transfer κ n Xs Xt _ _ _ _ _ _ h' D'); [done|done|exact Hs'| |exact HΣq|exact A].
      unfold erase. simpl. split_and!.
      + eapply fuse_ok_proc; [|exact Hok']. done.
      + simpl. rewrite <-ECh. f_equal. apply set_eq. intros c. rewrite !elem_of_map. split; intros (x & -> & Hx);
          exists x; (split; [|done]); unfold gch; rewrite Hh'; try done; rewrite gch_ech; intros E;
          apply Hy1C; rewrite <-E; by apply elem_of_map_2.
      + apply mcrel_of_mrel. rewrite <-(fmap_emap_id (<[i := f]> M)).
        apply (mrel_emap2 R); [|by apply mrel_insert]. intros e0 o o' _ _ Hoo' Ho. simpl.
        rewrite (Hoo'); [done|]. destruct Ho as [Ho|[Ho|Ho]]; [left; by apply HdΣ'|right; left; by apply HdΣ'|by right; right].
  Qed.

  Local Lemma upair_cases (y1 y2 z1 z2 : cend) : ({[y1]} ∪ {[y2]} : gset cend) = {[z1]} ∪ {[z2]} →
    (y1 = z1 ∧ y2 = z2) ∨ (y1 = z2 ∧ y2 = z1).
  Proof.
    intros E. assert (y1 ∈ ({[z1]} ∪ {[z2]} : gset cend)) as A1 by (rewrite <-E; set_solver).
    assert (y2 ∈ ({[z1]} ∪ {[z2]} : gset cend)) as A2 by (rewrite <-E; set_solver).
    assert (z1 ∈ ({[y1]} ∪ {[y2]} : gset cend)) as B1 by (rewrite E; set_solver).
    assert (z2 ∈ ({[y1]} ∪ {[y2]} : gset cend)) as B2 by (rewrite E; set_solver).
    set_solver.
  Qed.

  (** An offer of p on an end it does not hold contradicts its clauses. *)
  Local Lemma offer_held M i σ pc' o : soup M = p.2 → istep (p.1, M) (EvOffer i σ) pc' → ssubj σ = Some o →
    o ∈ dom Σ.
  Proof.
    intros HM Hst Ho. destruct HC as (_ & _ & HS).
    destruct (Psteps_head κ n _ _ _ _ _ _ _ _ HS (p.1, M) i σ pc' o (erase_p M HM) Hst Ho) as (S0 & x & L & _).
    by eapply elem_of_dom_2.
  Qed.

  Local Lemma tau_link M M' i e' f' y1 y2 : soup M = p.2 → mrel R M M' → M' !! i = Some e' →
    tstep e' (LSess (SLink ({[y1]} ∪ {[y2]}))) f' → ech y1 ∈ q.1 →
    ∃ W', W1 ⊑ W' ∧ at_cost_P n (ev_cost κ (EvSolo i (LSess (SLink ({[y1]} ∪ {[y2]}))) (PickLink y1 y2))) (Prel κ) Xt W' Σq T
      (erase (q.1 ∖ {[ech y1]}, emap (csub y1 y2) <$> <[i := f']> M')).
  Proof.
    intros HM Hr Hi Hs' Hy1. destruct (mrel_lookup_r R M M' i e' Hr Hi) as (e & He & Hc).
    destruct (thread_back R e e' _ f' Hc Hs') as (a & a' & Ha & Ha' & Har & Ho').
    destruct a'; simpl in Ho'; try done. destruct a; simpl in Har; try done. destruct Har as [Rb1 Rb2].
    rename o1 into z1, o2 into z2, o0 into b1, o3 into b2.
    assert (∃ a1 a2, R a1 y1 ∧ R a2 y2 ∧ ({[a1]} ∪ {[a2]} : gset cend) = {[b1]} ∪ {[b2]}) as (a1 & a2 & R1 & R2 & Eab).
    { destruct (upair_cases y1 y2 z1 z2 Ho') as [[-> ->]|[-> ->]]; [by exists b1, b2|].
      exists b2, b1. split_and!; [done|done|set_solver]. }
    destruct (thread_fwd R e e' (ALink b1 b2) (LSess (SLink ({[a1]} ∪ {[a2]}))) (LSess (SLink ({[y1]} ∪ {[y2]}))) f' Hc Ha)
      as (f & Hs0 & Hcf); [simpl; by rewrite Eab|done|done|].
    destruct (decide (ech a1 ∈ p.1)) as [Ha1|Na1].
    { apply (tau_link_p M M' i e f f' y1 y2 a1 a2 a1 a2); try done.
      all: first [by left | intros HD; exfalso; apply (notD a1 Ha1); by rewrite <-(R1 (or_intror (or_intror Ha1)))]. }
    destruct (decide (ech a2 ∈ p.1)) as [Ha2|Na2].
    { apply (tau_link_p M M' i e f f' y1 y2 a1 a2 a2 a1); try done.
      all: first [by rewrite (comm_L (∪)) | by right]. }
    destruct (decide (ech y1 ∈ D)) as [HyD|NyD]; [by eapply tau_link_off|].
    exfalso.
    assert (subjs (SLink ({[a1]} ∪ {[a2]})) ## p.1) as Hsj.
    { simpl. rewrite set_map_union_L, !set_map_singleton_L. set_solver. }
    pose proof (p_act_session p.1 M i e (SLink ({[a1]} ∪ {[a2]})) f He Hs0 Hsj) as Hst.
    destruct HC as (_ & _ & _ & _ & _ & _ & _ & _ & H7).
    destruct (H7 _ _ _ _ (erase_p M HM) Hst) as (o1 & o2 & S1 & S2 & x0 & Eos & No & L1 & L2 & _).
    assert (a1 ∈ dom Σ) as Ha1.
    { assert (a1 ∈ ({[o1]} ∪ {[o2]} : gset cend)) as A1 by (rewrite <-Eos; set_solver).
      apply elem_of_union in A1 as [?%elem_of_singleton|?%elem_of_singleton]; subst; by eapply elem_of_dom_2. }
    assert (ech y1 ∈ (set_map (gch h) p.1 : gset chan)) as Hg by (rewrite Eq1 in Hy1; set_solver).
    apply elem_of_map in Hg as (c & Hc1 & Hc2). rewrite (R1 (or_introl Ha1)) in Hc1.
    apply Na1. by rewrite (hd_chan a1 c (or_introl Ha1) Hc2 Hc1).
  Qed.

  (** ** Synchronizations *)

  (** The end a thread of p acts on is held, because an offer on an end
      p does not hold contradicts the clauses of p. *)
  Local Lemma subj_held M i e σ e' o : soup M = p.2 → M !! i = Some e → tstep e (LSess σ) e' →
    ssubj σ = Some o → ech o ∈ p.1 ∨ o ∈ dom Σ.
  Proof.
    intros HM He Hst0 Ho. destruct (decide (ech o ∈ p.1)) as [|Hnp]; [by left|right].
    eapply (offer_held M i σ); [done| |done]. eapply p_act_session; [done|exact Hst0|].
    destruct σ; simpl in *; try discriminate; injection Ho as ->; set_solver.
  Qed.

  Local Lemma hd_of o : ech o ∈ p.1 ∨ o ∈ dom Σ → hd o.
  Proof. unfold hd. tauto. Qed.

  (** ** Offers of q on interface ends *)

  Local Lemma subj_iface M i e σ e1 b y : soup M = p.2 → M !! i = Some e → tstep e (LSess σ) e1 →
    ssubj σ = Some b → R b y → ech y ∉ q.1 → b ∈ dom Σ ∧ y = h b ∧ ech b ∉ p.1 ∧ ech (h b) ∉ D.
  Proof.
    intros HM He Hst Hb Rb Ny. pose proof (subj_held M i e σ e1 b HM He Hst Hb) as Hh.
    assert (y = h b) as -> by (apply Rb, hd_of, Hh).
    assert (ech b ∉ p.1) as Nb.
    { intros Hp. apply Ny. rewrite Eq1, gch_ech. apply elem_of_union_l. by apply elem_of_map_2. }
    split_and!; [by destruct Hh|done|done|]. rewrite Eq1 in Ny. set_solver.
  Qed.

  Local Lemma kren_sdrop_delete b : b ∈ dom Σ → sdrop D (kren h (delete b Σ)) = delete (h b) Σq.
  Proof.
    intros Hb. rewrite kren_delete by (done || apply Hk). unfold sdrop. by rewrite map_filter_delete.
  Qed.

  Local Lemma kren_sdrop_insert b v : b ∈ dom Σ → ech (h b) ∉ D →
    sdrop D (kren h (<[b := v]> Σ)) = <[h b := v]> Σq.
  Proof.
    intros Hb HD. rewrite kren_insert.
    - unfold sdrop. rewrite map_filter_insert_True; [done|done].
    - apply (kinj_sub h Σ); [rewrite dom_insert_L; set_solver|apply Hk].
  Qed.

  Local Lemma gfuse_env Σ1 C1 M0 M0' : dom Σ1 ⊆ dom Σ → C1 ⊆ p.1 →
    (∀ o, o ∈ dom Σ → ech (h o) ∈ D → Σ1 !! o = Σ !! o) → mrel R M0 M0' →
    gfuse h D Σ1 (C1, soup M0) (set_map (gch h) C1 ∪ D, soup M0').
  Proof.
    intros HdΣ HC' Hag Hr. assert (kinj h Σ1) as Hk1 by (by apply (kinj_sub h Σ); [|apply Hk]).
    assert (∀ o, pheld Σ1 (C1, soup M0) o → pheld Σ p o) as Hph.
    { intros o [Ho|Ho]; [left; set_solver|right; simpl in Ho; set_solver]. }
    split_and!.
    - destruct Hok as (A1 & A2 & A3 & A4 & A5). split_and!; [done| | |set_solver|].
      + intros o1 o2 H1 H2. apply A2; by apply Hph.
      + intros o1 o2 H1 H2. apply A3; by apply Hph.
      + intros o Ho. destruct (A5 o Ho) as (S & x & S' & K1 & K2 & Hs'). exists S, x, S'.
        destruct (kren_lookup_inv _ _ _ _ K1) as (u & -> & Hu).
        destruct (kren_lookup_inv _ _ _ _ K2) as (w & Ew & Hw).
        split_and!; [|rewrite Ew|done]; apply kren_lookup; try done.
        * rewrite Hag; [done|by eapply elem_of_dom_2|done].
        * rewrite Hag; [done|by eapply elem_of_dom_2|by rewrite <-Ew, ech_edual].
    - done.
    - apply mcrel_of_mrel. apply (mrel_mono_in R); [|done]. intros e0 o o' _ _ Hoo' Ho. apply Hoo'.
      destruct Ho as [Ho|[Ho|Ho]]; [left; set_solver|right; left; set_solver|right; right; simpl in Ho; set_solver].
  Qed.

  Local Lemma fside_env Σ1 C1 E : dom Σ1 ⊆ dom Σ → C1 ⊆ p.1 → fside D Σ1 T (C1, E).
  Proof.
    intros H1 H2. split.
    - simpl. intros c Hc Hc'. apply (HC1 c); [set_solver|]. apply chans_of_elem in Hc' as (o & Ho & <-).
      apply elem_of_chans_of. set_solver.
    - destruct (proj2 Hs) as [HT Hpf]. split; [done|]. intros o Ho Ho'. apply (Hpf o); set_solver.
  Qed.

  Local Lemma off_close M M' i y e' e1' : soup M = p.2 → mrel R M M' → M' !! i = Some e' →
    tstep e' (LSess (SClose y)) e1' → ech y ∉ q.1 →
    ∃ S0 x, Σq !! y = Some (S0, x) ∧ unfoldS S0 = SEnd ∧
      at_cost_P n (c_give κ) (Prel κ) Xt W1 (delete y Σq) T (erase (q.1 ∖ ∅, <[i := e1']> M')).
  Proof.
    intros HM Hr Hi Hs' Ny. destruct (mrel_lookup_r R M M' i e' Hr Hi) as (e & He & Hc).
    destruct (thread_back R e e' _ e1' Hc Hs') as (a & a' & Ha & Ha' & Har & Ho').
    destruct a'; simpl in Ho'; try done. subst. destruct a as [| | | | | |b| | |]; simpl in Har; try done.
    destruct (thread_fwd R e e' (AClose b) (LSess (SClose b)) (LSess (SClose y)) e1' Hc Ha) as (e1 & Hs1 & Hc1); [done|done|done|].
    destruct (subj_iface M i e _ e1 b y HM He Hs1 eq_refl Har Ny) as (Hb & -> & Nb & ND).
    assert (istep (p.1, M) (EvOffer i (SClose b)) (p.1 ∖ ∅, <[i := e1]> M)) as Hst.
    { eapply p_act_session; [done|done|]. simpl. set_solver. }
    destruct HC as (_ & _ & _ & _ & _ & H4 & _).
    destruct (H4 _ _ _ _ (erase_p M HM) Hst) as (S0 & x & Lb & U & A).
    exists S0, x. split_and!; [by apply lookupq|done|].
    rewrite <-kren_sdrop_delete by done.
    eapply (at_cost_transfer κ n Xs Xt _ _ _ _ _ _ h D); [done|done| | |apply senv_eqv_refl|exact A].
    - apply fside_env; [rewrite dom_delete_L; set_solver|set_solver].
    - unfold erase. simpl. rewrite !difference_empty_L, Eq1. apply gfuse_env; [rewrite dom_delete_L; set_solver|done| |by apply mrel_insert].
      intros o Ho HD. rewrite lookup_delete_ne; [done|]. by intros ->.
  Qed.

  Local Lemma off_sel M M' i y k e' e1' : soup M = p.2 → mrel R M M' → M' !! i = Some e' →
    tstep e' (LSess (SSel y k)) e1' → ech y ∉ q.1 →
    ∃ S0 x S1 S2, Σq !! y = Some (S0, x) ∧ unfoldS S0 = SPlus S1 S2 ∧
      at_cost_P n (c_give κ) (Prel κ) Xt W1 (<[y := (bsel k S1 S2, sel_pt x k)]> Σq) T (erase (q.1 ∖ ∅, <[i := e1']> M')).
  Proof.
    intros HM Hr Hi Hs' Ny. destruct (mrel_lookup_r R M M' i e' Hr Hi) as (e & He & Hc).
    destruct (thread_back R e e' _ e1' Hc Hs') as (a & a' & Ha & Ha' & Har & Ho').
    destruct a'; simpl in Ho'; try done. destruct Ho' as [-> ->].
    destruct a as [| | | | | | | |b k0|]; simpl in Har; try done. destruct Har as [Rb ->].
    destruct (thread_fwd R e e' (ASel b k) (LSess (SSel b k)) (LSess (SSel y k)) e1' Hc Ha) as (e1 & Hs1 & Hc1); [done|done|done|].
    destruct (subj_iface M i e _ e1 b y HM He Hs1 eq_refl Rb Ny) as (Hb & -> & Nb & ND).
    assert (istep (p.1, M) (EvOffer i (SSel b k)) (p.1 ∖ ∅, <[i := e1]> M)) as Hst.
    { eapply p_act_session; [done|done|]. simpl. set_solver. }
    destruct HC as (_ & _ & _ & _ & _ & _ & H5 & _).
    destruct (H5 _ _ _ _ _ (erase_p M HM) Hst) as (S0 & x & S1 & S2 & Lb & U & A).
    exists S0, x, S1, S2. split_and!; [by apply lookupq|done|].
    rewrite <-kren_sdrop_insert by done.
    eapply (at_cost_transfer κ n Xs Xt _ _ _ _ _ _ h D); [done|done| | |apply senv_eqv_refl|exact A].
    - apply fside_env; [rewrite dom_insert_L; set_solver|set_solver].
    - unfold erase. simpl. rewrite !difference_empty_L, Eq1. apply gfuse_env; [rewrite dom_insert_L; set_solver|done| |by apply mrel_insert].
      intros o Ho HD. rewrite lookup_insert_ne; [done|]. by intros ->.
  Qed.

  Local Lemma off_bra M M' i y k e' e1' : soup M = p.2 → mrel R M M' → M' !! i = Some e' →
    tstep e' (LSess (SBra y k)) e1' → ech y ∉ q.1 →
    ∃ S0 x S1 S2, Σq !! y = Some (S0, x) ∧ unfoldS S0 = SWith S1 S2 ∧
      at_cost_P n (c_take κ) (Prel κ) Xt W1 (<[y := (bsel k S1 S2, bra_pt x k)]> Σq) T (erase (q.1 ∖ ∅, <[i := e1']> M')).
  Proof.
    intros HM Hr Hi Hs' Ny. destruct (mrel_lookup_r R M M' i e' Hr Hi) as (e & He & Hc).
    destruct (thread_back R e e' _ e1' Hc Hs') as (a & a' & Ha & Ha' & Har & Ho').
    destruct a'; simpl in Ho'; try done. subst.
    destruct a as [| | | | | | | | |b]; simpl in Har; try done.
    destruct (thread_fwd R e e' (ABra b) (LSess (SBra b k)) (LSess (SBra y k)) e1' Hc Ha) as (e1 & Hs1 & Hc1); [done|done|done|].
    destruct (subj_iface M i e _ e1 b y HM He Hs1 eq_refl Har Ny) as (Hb & -> & Nb & ND).
    assert (istep (p.1, M) (EvOffer i (SBra b k)) (p.1 ∖ ∅, <[i := e1]> M)) as Hst.
    { eapply p_act_session; [done|done|]. simpl. set_solver. }
    destruct HC as (_ & _ & _ & _ & _ & _ & _ & H6 & _).
    destruct (H6 _ _ _ _ _ (erase_p M HM) Hst) as (S0 & x & S1 & S2 & Lb & U & A).
    exists S0, x, S1, S2. split_and!; [by apply lookupq|done|].
    rewrite <-kren_sdrop_insert by done.
    eapply (at_cost_transfer κ n Xs Xt _ _ _ _ _ _ h D); [done|done| | |apply senv_eqv_refl|exact A].
    - apply fside_env; [rewrite dom_insert_L; set_solver|set_solver].
    - unfold erase. simpl. rewrite !difference_empty_L, Eq1. apply gfuse_env; [rewrite dom_insert_L; set_solver|done| |by apply mrel_insert].
      intros o Ho HD. rewrite lookup_insert_ne; [done|]. by intros ->.
  Qed.

  Local Lemma kren_sdrop_delete_gen (Σ0 : senv) b : kinj h Σ0 → b ∈ dom Σ0 →
    sdrop D (kren h (delete b Σ0)) = delete (h b) (sdrop D (kren h Σ0)).
  Proof. intros Hk0 Hb. rewrite kren_delete by done. unfold sdrop. by rewrite map_filter_delete. Qed.

  Local Lemma off_link M M' i y1 y2 e' e1' : soup M = p.2 → mrel R M M' → M' !! i = Some e' →
    tstep e' (LSess (SLink ({[y1]} ∪ {[y2]}))) e1' → subjs (SLink ({[y1]} ∪ {[y2]})) ## q.1 →
    ∃ o1 o2 S1 S2 x, ({[y1]} ∪ {[y2]} : gset cend) = {[o1]} ∪ {[o2]} ∧ o1 ≠ o2 ∧
      Σq !! o1 = Some (S1, x) ∧ Σq !! o2 = Some (S2, x‾) ∧ sdual S1 S2 ∧
      at_cost_P n (c_link κ) (Prel κ) Xt W1 (delete o1 (delete o2 Σq)) T (erase (q.1 ∖ ∅, <[i := e1']> M')).
  Proof.
    intros HM Hr Hi Hs' Hsj. destruct (mrel_lookup_r R M M' i e' Hr Hi) as (e & He & Hc).
    destruct (thread_back R e e' _ e1' Hc Hs') as (a & a' & Ha & Ha' & Har & Ho').
    destruct a'; simpl in Ho'; try done. destruct a; simpl in Har; try done. destruct Har as [Rb1 Rb2].
    rename o1 into z1, o2 into z2, o0 into b1, o3 into b2.
    simpl in Hsj. rewrite set_map_union_L, !set_map_singleton_L in Hsj.
    assert (ech z1 ∉ q.1 ∧ ech z2 ∉ q.1) as [Nz1 Nz2].
    { destruct (upair_cases y1 y2 z1 z2 Ho') as [[-> ->]|[-> ->]]; set_solver. }
    assert (∀ b z, R b z → ech z ∉ q.1 → ech b ∉ p.1) as Hnp.
    { intros b z Rb Nz Hp. apply Nz. rewrite (Rb (or_intror (or_intror Hp))), Eq1, gch_ech.
      apply elem_of_union_l. by apply elem_of_map_2. }
    destruct (thread_fwd R e e' (ALink b1 b2) (LSess (SLink ({[b1]} ∪ {[b2]}))) (LSess (SLink ({[y1]} ∪ {[y2]}))) e1' Hc Ha)
      as (e1 & Hs1 & Hc1); [done|done|done|].
    assert (istep (p.1, M) (EvOffer i (SLink ({[b1]} ∪ {[b2]}))) (p.1 ∖ ∅, <[i := e1]> M)) as Hst.
    { eapply p_act_session; [done|done|]. simpl. rewrite set_map_union_L, !set_map_singleton_L.
      pose proof (Hnp b1 z1 Rb1 Nz1). pose proof (Hnp b2 z2 Rb2 Nz2). set_solver. }
    destruct HC as (_ & _ & _ & _ & _ & _ & _ & _ & H7).
    destruct (H7 _ _ _ _ (erase_p M HM) Hst) as (o1 & o2 & S1 & S2 & x & Eos & No & L1 & L2 & Hsd & A).
    assert (o1 ∈ dom Σ) as Ho1 by (by eapply elem_of_dom_2). assert (o2 ∈ dom Σ) as Ho2 by (by eapply elem_of_dom_2).
    assert (b1 ∈ dom Σ ∧ b2 ∈ dom Σ) as [Hb1 Hb2].
    { destruct (upair_cases b1 b2 o1 o2 Eos) as [[-> ->]|[-> ->]]; by split. }
    assert (z1 = h b1) as -> by (apply Rb1; by left). assert (z2 = h b2) as -> by (apply Rb2; by left).
    assert (({[y1]} ∪ {[y2]} : gset cend) = {[h o1]} ∪ {[h o2]}) as Eys.
    { rewrite Ho'. destruct (upair_cases b1 b2 o1 o2 Eos) as [[-> ->]|[-> ->]]; [done|apply (comm_L (∪))]. }
    assert (ech (h o1) ∉ D ∧ ech (h o2) ∉ D) as [D1 D2].
    { assert (∀ z, ech z ∉ q.1 → ech z ∉ D) as HqD.
      { intros z Nz HzD. apply Nz. rewrite Eq1. by apply elem_of_union_r. }
      destruct (upair_cases b1 b2 o1 o2 Eos) as [[<- <-]|[<- <-]]; split; by apply HqD. }
    exists (h o1), (h o2), S1, S2, x. split_and!; [done| |by apply lookupq|by apply lookupq|done|].
    { intros E. apply No. apply hinj; [by left|by left|done]. }
    assert (kinj h (delete o2 Σ)) as Hk2 by (apply (kinj_sub h Σ); [rewrite dom_delete_L; set_solver|apply Hk]).
    rewrite <-(kren_sdrop_delete_gen Σ o2), <-kren_sdrop_delete_gen; [| |rewrite dom_delete_L; set_solver|apply Hk|done]; [|done].
    eapply (at_cost_transfer κ n Xs Xt _ _ _ _ _ _ h D); [done|done| | |apply senv_eqv_refl|exact A].
    - apply fside_env; [rewrite !dom_delete_L; set_solver|set_solver].
    - unfold erase. simpl. rewrite !difference_empty_L, Eq1. apply gfuse_env; [rewrite !dom_delete_L; set_solver|done| |by apply mrel_insert].
      intros o Ho HD. rewrite !lookup_delete_ne; [done| |]; intros ->; [apply D2|apply D1]; done.
  Qed.

  (** ** Sends of q *)

  Local Lemma kren_iff (X : senv) o' v : kinj h X → kren h X !! o' = Some v ↔ ∃ o, o' = h o ∧ X !! o = Some v.
  Proof. intros Hx. split; [apply kren_lookup_inv|]. intros (o & -> & Ho). by apply kren_lookup. Qed.

  Local Lemma crel_emap_eq e e' : crel R e e' → (∀ o, o ∈ fends e → hd o) → e' = emap h e.
  Proof.
    induction 1; simpl; intros Hall; f_equal;
      try (apply IHcrel; intros; apply Hall; set_solver);
      try (apply IHcrel1; intros; apply Hall; set_solver);
      try (apply IHcrel2; intros; apply Hall; set_solver);
      try (apply IHcrel3; intros; apply Hall; set_solver).
    match goal with H : R ?o ?o' |- ?o' = h ?o => apply H, Hall; set_solver end.
  Qed.

  Local Lemma off_send M M' i y w' e' e1' : soup M = p.2 → mrel R M M' → M' !! i = Some e' →
    tstep e' (LSess (SSend y w')) e1' → ech y ∉ q.1 →
    ∃ S0 x m U S Σv Σr Θe Σe, Σq !! y = Some (S0, x) ∧
      unfoldS S0 = SSeq (SSnd m U) S ∧
      Σv ##ₘ Σr ∧ delete y Σq = Σv ∪ Σr ∧
      (∀ o', o' ∈ dom Θe ↔ o' ∈ fends w' ∧ ech o' ∈ q.1) ∧
      send_split Σq Σe Θe ∧
      at_cost_V n (c_give κ) (Vrel κ) (Vrel κ n) W1 (Σv ∪ Θe) (payload_at m U x) w' ∧
      at_cost_P n (c_give κ) (Prel κ) Xt W1 (<[y := (S, x⁺)]> (Σr ∪ Σe)) T (erase (q.1 ∖ fchans w', <[i := e1']> M')).
  Proof.
    intros HM Hr Hi Hs' Ny. destruct (mrel_lookup_r R M M' i e' Hr Hi) as (e & He & Hc).
    destruct (thread_back R e e' _ e1' Hc Hs') as (a & a' & Ha & Ha' & Har & Ho').
    destruct a'; simpl in Ho'; try done. destruct Ho' as [-> ->].
    destruct a as [| | | | |b w| | | |]; simpl in Har; try done. destruct Har as [Rb Rw].
    destruct (thread_fwd R e e' (ASend b w) (LSess (SSend b w)) (LSess (SSend y w')) e1' Hc Ha) as (e1 & Hs1 & Hc1); [done|done|done|].
    destruct (subj_iface M i e _ e1 b y HM He Hs1 eq_refl Rb Ny) as (Hb & -> & Nb & ND).
    assert (istep (p.1, M) (EvOffer i (SSend b w)) (p.1 ∖ fchans w, <[i := e1]> M)) as Hst.
    { eapply p_act_session; [done|done|]. simpl. set_solver. }
    destruct HC as (_ & _ & _ & H2 & _).
    destruct (H2 _ _ _ _ _ (erase_p M HM) Hst)
      as (S0 & x & m & U & S & Σv & Σr & Θe & Σe & Lb & U0 & Dvr & Edel & HΘe & Hss & AV & AP).
    assert (∀ o, o ∈ dom Θe → ech o ∈ p.1) as HΘp by (intros o Ho; by apply HΘe in Ho as [_ ?]).
    destruct Hss as (Ss1 & Ss2 & Ss3).
    assert (∀ o, o ∈ dom Σe → ech o ∈ p.1) as HΣep.
    { intros o Ho. apply Ss2 in Ho as [Ho _]. rewrite <-ech_edual. by apply HΘp. }
    assert (∀ o v, Σv !! o = Some v → Σ !! o = Some v ∧ o ≠ b) as Lv.
    { intros o v Hv. assert ((Σv ∪ Σr) !! o = Some v) as H' by (by apply lookup_union_Some_l).
      rewrite <-Edel in H'. apply lookup_delete_Some in H' as [? ?]. done. }
    assert (∀ o v, Σr !! o = Some v → Σ !! o = Some v ∧ o ≠ b) as Lr.
    { intros o v Hv. assert ((Σv ∪ Σr) !! o = Some v) as H' by (by apply lookup_union_Some_r).
      rewrite <-Edel in H'. apply lookup_delete_Some in H' as [? ?]. done. }
    assert (∀ o v, Σ !! o = Some v → o ≠ b → Σv !! o = Some v ∨ Σr !! o = Some v) as Lvr.
    { intros o v Hv Nob. assert ((Σv ∪ Σr) !! o = Some v) as H' by (rewrite <-Edel; by apply lookup_delete_Some).
      apply lookup_union_Some in H' as [?|?]; auto. }
    assert (∀ X : senv, (∀ o, o ∈ dom X → pheld Σ p o) → kinj h X) as Hkh.
    { intros X HXh o1 o2 v1 v2 K1 K2 E. apply hinj; [apply HXh; by eapply elem_of_dom_2|apply HXh; by eapply elem_of_dom_2|done]. }
    assert (∀ o, o ∈ dom Σv → o ∈ dom Σ) as DvΣ by (intros o [v Hv]%elem_of_dom; eapply elem_of_dom_2, Lv; eauto).
    assert (∀ o, o ∈ dom Σr → o ∈ dom Σ) as DrΣ by (intros o [v Hv]%elem_of_dom; eapply elem_of_dom_2, Lr; eauto).
    assert (∀ o, o ∈ dom Σ → ech o ∉ p.1) as HΣC.
    { intros o Ho Hp. apply (HC1 (ech o) Hp). by apply elem_of_chans_of. }
    (* the value and its ends *)
    assert (∃ j, Vrel κ j W1 (Σv ∪ Θe) (payload_at m U x) w) as [jv HVj].
    { destruct AV as [A0 A1]. destruct (decide (c_give κ = 0)) as [Hz|Hz]; [exists n; by apply A0|].
      exists ozero. apply A1; [done|done|by right]. }
    pose proof (Vrel_exact κ _ _ _ _ _ HVj) as Hfw. rewrite dom_union_L in Hfw.
    assert (w' = emap h w) as ->.
    { apply (crel_emap_eq w w' Rw). intros o Ho. rewrite <-Hfw in Ho. apply elem_of_union in Ho as [Ho|Ho].
      - left. by apply DvΣ. - right; right. by apply HΘp. }
    (* the images *)
    assert (kinj h (Σv ∪ Σr ∪ Θe ∪ Σe)) as Hkall.
    { apply Hkh. intros o Ho. rewrite !dom_union_L, !elem_of_union in Ho.
      destruct Ho as [[[Ho|Ho]|Ho]|Ho]; [left; by apply DvΣ|left; by apply DrΣ|right; by apply HΘp|right; by apply HΣep]. }
    assert (∀ X : senv, (∀ o, o ∈ dom X → o ∈ dom (Σv ∪ Σr ∪ Θe ∪ Σe)) → kinj h X) as Hksub.
    { intros X HXs. by apply (kinj_sub h (Σv ∪ Σr ∪ Θe ∪ Σe)). }
    set (KV := kren h Σv). set (KR := kren h Σr). set (KE := kren h Σe). set (KΘ := kren h Θe).
    assert (kinj h Σv ∧ kinj h Σr ∧ kinj h Θe ∧ kinj h Σe) as (Kv & Kr & Kt & Ke).
    { split_and!; apply Hksub; intros o Ho; rewrite !dom_union_L, !elem_of_union; tauto. }
    set (VD := filter (λ oe : cend * (sty * point), ech oe.1 ∈ D) KV).
    set (DS := set_map ech (dom VD) : gset chan).
    set (RP := filter (λ oe : cend * (sty * point), ech oe.1 ∈ DS) KR).
    set (D' := D ∖ DS).
    (* lookups *)
    assert (∀ o' v, KV !! o' = Some v ↔ ∃ o, o' = h o ∧ Σv !! o = Some v) as LKV by (intros; by apply kren_iff).
    assert (∀ o' v, KR !! o' = Some v ↔ ∃ o, o' = h o ∧ Σr !! o = Some v) as LKR by (intros; by apply kren_iff).
    assert (∀ o' v, KE !! o' = Some v ↔ ∃ o, o' = h o ∧ Σe !! o = Some v) as LKE by (intros; by apply kren_iff).
    assert (∀ o' v, KΘ !! o' = Some v ↔ ∃ o, o' = h o ∧ Θe !! o = Some v) as LKΘ by (intros; by apply kren_iff).
    (* an image of an end of Σ lies on a channel of D or on no channel of q *)
    assert (∀ o, o ∈ dom Σ → ech (h o) ∉ (set_map (gch h) p.1 : gset chan)) as HΣq.
    { intros o Ho Hin. apply elem_of_map in Hin as (c & Ec & Zc). apply (HΣC o Ho).
      by rewrite (hd_chan o c (or_introl Ho) Zc Ec). }
    assert (∀ o, ech o ∈ p.1 → ech (h o) ∈ (set_map (gch h) p.1 : gset chan)) as HCq.
    { intros o Ho. rewrite gch_ech. by apply elem_of_map_2. }
    assert (∀ o, o ∈ dom Σv → o ∈ dom Σ ∧ o ≠ b) as Fv.
    { intros o [v Hv]%elem_of_dom. destruct (Lv o v Hv) as [A B]. split; [by eapply elem_of_dom_2|done]. }
    assert (∀ o, o ∈ dom Σr → o ∈ dom Σ ∧ o ≠ b) as Fr.
    { intros o [v Hv]%elem_of_dom. destruct (Lr o v Hv) as [A B]. split; [by eapply elem_of_dom_2|done]. }
    assert (∀ u1 u2, pheld Σ p u1 → pheld Σ p u2 → h u1 = h u2 → u1 = u2) as Zi by (intros; by apply hinj).
    assert (∀ o' v, VD !! o' = Some v ↔ (∃ o, o' = h o ∧ Σv !! o = Some v) ∧ ech o' ∈ D) as LVD.
    { intros o' v. unfold VD. rewrite map_lookup_filter_Some, LKV. done. }
    assert (∀ o' v, RP !! o' = Some v ↔ (∃ o, o' = h o ∧ Σr !! o = Some v) ∧ ech o' ∈ DS) as LRP.
    { intros o' v. unfold RP. rewrite map_lookup_filter_Some, LKR. done. }
    assert (∀ c, c ∈ DS ↔ ∃ o v, Σv !! o = Some v ∧ ech (h o) = c ∧ c ∈ D) as LDS.
    { intros c. unfold DS. rewrite elem_of_map. split.
      - intros (o' & -> & [v Hv]%elem_of_dom). apply LVD in Hv as ((o & -> & Ho) & HD). eauto.
      - intros (o & v & Ho & <- & HD). exists (h o). split; [done|]. apply elem_of_dom. exists v. apply LVD. eauto. }
    assert (DS ⊆ D) as HDS by (intros c (? & ? & _ & _ & ?)%LDS; done).
    (* O2, O3 *)
    assert (sdrop D KV ##ₘ sdrop D KR) as O2.
    { apply map_disjoint_spec. intros o' v1 v2 A1 A2. apply sdrop_lookup in A1 as [A1 _], A2 as [A2 _].
      apply LKV in A1 as (u1 & -> & U1). apply LKR in A2 as (u2 & E2 & U2).
      assert (u1 = u2) as <- by (apply Zi; [left; apply (Fv u1); by eapply elem_of_dom_2|left; apply (Fr u2); by eapply elem_of_dom_2|done]).
      exact (proj1 (map_disjoint_spec Σv Σr) Dvr u1 _ _ U1 U2). }
    assert (delete (h b) Σq = sdrop D KV ∪ sdrop D KR) as O3.
    { apply map_eq. intros o'. apply option_eq. intros v. rewrite lookup_delete_Some, (lookup_union_Some _ _ _ _ O2), !sdrop_lookup, LKV, LKR.
      split.
      - intros [Nb' [L ND']]. destruct (kren_lookup_inv _ _ _ _ L) as (u & -> & Lu).
        assert (u ≠ b) as Nub by (intros ->; done).
        destruct (Lvr u v Lu Nub) as [?|?]; [left|right]; eauto.
      - intros [[(u & -> & Lu) ND']|[(u & -> & Lu) ND']].
        + destruct (Lv u v Lu) as [Lu' Nub]. split; [|split; [by apply kren_lookup; [apply Hk|]|done]].
          intros E. apply Nub. apply Zi; [left; by eapply elem_of_dom_2|by left|done].
        + destruct (Lr u v Lu) as [Lu' Nub]. split; [|split; [by apply kren_lookup; [apply Hk|]|done]].
          intros E. apply Nub. apply Zi; [left; by eapply elem_of_dom_2|by left|done]. }
    (* the channels of the parts *)
    assert (∀ o', o' ∈ dom KΘ → ech o' ∈ (set_map (gch h) p.1 : gset chan)) as CΘ.
    { intros o' [v Hv]%elem_of_dom. apply LKΘ in Hv as (u & -> & Hu). apply HCq, HΘp. by eapply elem_of_dom_2. }
    assert (∀ o', o' ∈ dom KE → ech o' ∈ (set_map (gch h) p.1 : gset chan)) as CE.
    { intros o' [v Hv]%elem_of_dom. apply LKE in Hv as (u & -> & Hu). apply HCq, HΣep. by eapply elem_of_dom_2. }
    assert (∀ o', o' ∈ dom VD → ech o' ∈ D) as CV by (intros o' [v Hv]%elem_of_dom; by apply LVD in Hv as [_ ?]).
    assert (∀ o', o' ∈ dom RP → ech o' ∈ D) as CR by (intros o' [v Hv]%elem_of_dom; apply LRP in Hv as [_ ?]; by apply HDS).
    assert (∀ c, c ∈ D → c ∈ (set_map (gch h) p.1 : gset chan) → False) as CDC by (intros c ? ?; by apply (HDc c)).
    assert (KΘ ##ₘ VD) as DΘV.
    { apply map_disjoint_dom. intros o' A B. by apply (CDC (ech o')); [apply CV|apply CΘ]. }
    assert (KE ##ₘ RP) as DER.
    { apply map_disjoint_dom. intros o' A B. by apply (CDC (ech o')); [apply CR|apply CE]. }
    assert (∀ t, t ∈ dom Σv → t ∉ dom Σr) as Nvr.
    { intros t A B. apply elem_of_dom in A as [? A], B as [? B].
      exact (proj1 (map_disjoint_spec Σv Σr) Dvr t _ _ A B). }
    assert (∀ u, u ∈ dom Σ → ech (h u) ∈ D → ∃ v T1 z T2, h v = edual (h u) ∧ Σ !! u = Some (T1, z) ∧
        Σ !! v = Some (T2, z‾) ∧ sdual T1 T2 ∧ v ≠ b) as Hpart.
    { intros u Hu HD. destruct (Hdp (h u) HD) as (T1 & z & T2 & K3 & K4 & Hs3).
      destruct (kren_lookup_inv _ _ _ _ K4) as (v & Ev & Lv'). exists v, T1, z, T2. split_and!; [done| |done|done|].
      - by apply (kren_lookup_held h Σ u) in K3; [|apply Hk|done].
      - intros ->. apply ND. by rewrite <-Ev, ech_edual. }
    (* O4 *)
    assert (∀ o', o' ∈ dom (KΘ ∪ VD) ↔ o' ∈ fends (emap h w) ∧ ech o' ∈ q.1) as O4.
    { intros o'. rewrite dom_union_L, elem_of_union, fends_emap, <-Hfw, elem_of_map, Eq1. split.
      - intros [A|A].
        + split; [|apply elem_of_union_l; by apply CΘ]. apply elem_of_dom in A as [v A]. apply LKΘ in A as (u & -> & A).
          exists u. split; [done|]. apply elem_of_union_r. by eapply elem_of_dom_2.
        + split; [|apply elem_of_union_r; by apply CV]. apply elem_of_dom in A as [v A]. apply LVD in A as ((u & -> & A) & _).
          exists u. split; [done|]. apply elem_of_union_l. by eapply elem_of_dom_2.
      - intros [(u & -> & Hu) Hq]. apply elem_of_union in Hu as [Hu|Hu].
        + right. apply elem_of_dom in Hu as [v Hv]. apply elem_of_dom. exists v. apply LVD. split; [eauto|].
          apply elem_of_union in Hq as [Hq|Hq]; [|done]. exfalso. apply (HΣq u); [by apply Fv; eapply elem_of_dom_2|done].
        + left. apply elem_of_dom in Hu as [v Hv]. apply elem_of_dom. exists v. apply LKΘ. eauto. }
    (* O5 *)
    assert (∀ o', o' ∈ dom Σq → ech o' ∉ D ∧ ech o' ∉ (set_map (gch h) p.1 : gset chan)) as CΣq.
    { intros o' [v Hv]%elem_of_dom. destruct (lookupq_inv o' v Hv) as (u & -> & Lu & ND'). split; [done|].
      apply HΣq. by eapply elem_of_dom_2. }
    assert (send_split Σq (KE ∪ RP) (KΘ ∪ VD)) as O5.
    { split_and!.
      - intros o' Ho'. rewrite dom_union_L, elem_of_union in Ho'.
        split; intros A; apply CΣq in A as [A1 A2]; rewrite ?ech_edual in A1, A2;
          destruct Ho' as [Ho'|Ho']; [apply A2, CΘ|apply A1, CV|apply A2, CΘ|apply A1, CV]; done.
      - intros o'. rewrite !dom_union_L, !elem_of_union. split.
        + intros [A|A].
          * apply elem_of_dom in A as [v A]. apply LKE in A as (u & -> & A).
            assert (u ∈ dom Σe) as A' by (by eapply elem_of_dom_2). apply Ss2 in A' as [B1 B2].
            split.
            -- left. apply elem_of_dom in B1 as [v' B1]. apply elem_of_dom. exists v'. apply LKΘ. exists (edual u). by rewrite Hd.
            -- intros [C1|C1].
               ++ apply elem_of_dom in C1 as [v' C1]. apply LKΘ in C1 as (u' & E' & C1).
                  apply B2. assert (u = u') as -> by (apply Zi; [right; apply HΣep; by eapply elem_of_dom_2|right; apply HΘp; by eapply elem_of_dom_2|done]).
                  by eapply elem_of_dom_2.
               ++ apply (CDC (ech (h u))); [by apply CV|apply HCq, HΣep; by eapply elem_of_dom_2].
          * apply elem_of_dom in A as [v A]. apply LRP in A as ((u & -> & A) & HDSu).
            apply LDS in HDSu as (t & vt & Ht & Et & HDt). symmetry in Et. apply ech_eq in Et as [Et|Et].
            -- exfalso. apply (Nvr t); [by eapply elem_of_dom_2|].
               assert (u = t) as <- by (apply Zi; [left; apply Fr; by eapply elem_of_dom_2|left; apply Fv; by eapply elem_of_dom_2|done]).
               by eapply elem_of_dom_2.
            -- split.
               ++ right. apply elem_of_dom. exists vt. apply LVD. split; [exists t; split; [by rewrite Et|done]|].
                  by rewrite ech_edual.
               ++ intros [C1|C1].
                  ** apply (CDC (ech (h u))); [done|by apply CΘ].
                  ** apply elem_of_dom in C1 as [v' C1]. apply LVD in C1 as ((t' & E' & C1) & _).
                     assert (u = t') as <- by (apply Zi; [left; apply Fr; by eapply elem_of_dom_2|left; apply Fv; by eapply elem_of_dom_2|done]).
                     apply (Nvr u); by eapply elem_of_dom_2.
        + intros [[A|A] N]; apply Decidable.not_or in N as [N1 N2].
          * apply elem_of_dom in A as [v A]. apply LKΘ in A as (t & Et & A).
            assert (edual t ∈ dom Σe) as B.
            { apply Ss2. rewrite edual_edual. split; [by eapply elem_of_dom_2|]. intros C.
              apply N1. apply elem_of_dom in C as [v' C]. apply elem_of_dom. exists v'. apply LKΘ. exists (edual t).
              by rewrite Hd, <-Et, edual_edual. }
            left. apply elem_of_dom in B as [v' B]. apply elem_of_dom. exists v'. apply LKE. exists (edual t).
            by rewrite Hd, <-Et, edual_edual.
          * apply elem_of_dom in A as [v A]. apply LVD in A as ((t & Et & A) & HDt).
            rewrite Et in HDt. destruct (Hpart t (proj1 (Fv t (elem_of_dom_2 _ _ _ A))) HDt) as (u & T1 & z & T2 & Eu & _ & Lu & _ & Nub).
            assert (o' = h u) as Eo' by (by rewrite Eu, <-Et, edual_edual).
            destruct (Lvr u _ Lu Nub) as [Lu'|Lu'].
            -- exfalso. apply N2. apply elem_of_dom. exists (T2, z‾). apply LVD. split; [eauto|]. by rewrite Eo', Eu, ech_edual.
            -- right. apply elem_of_dom. exists (T2, z‾). apply LRP. split; [eauto|]. apply LDS.
               exists t, v. split_and!; [done|by rewrite Eo', Eu, ech_edual|by rewrite Eo', Eu, ech_edual].
      - intros o' S1 z1 A. rewrite (lookup_union_Some _ _ _ _ DΘV) in A. destruct A as [A|A].
        + apply LKΘ in A as (t & -> & A). destruct (Ss3 t S1 z1 A) as (S1' & B & Hsd1). exists S1'. split; [|done].
          rewrite <-Hd. apply lookup_union_Some_raw in B as [B|[B0 B]].
          * apply lookup_union_Some_l. apply lookup_union_Some_l. apply LKE. eauto.
          * apply lookup_union_Some_raw. right. split; [|apply lookup_union_Some_l; apply LKΘ; eauto].
            apply lookup_union_None. split.
            -- apply eq_None_not_Some. intros [v' C]. apply LKE in C as (u & E' & C).
               assert (edual t = u) as <- by (apply Zi; [right; rewrite ech_edual; apply HΘp; by eapply elem_of_dom_2
                 |right; apply HΣep; by eapply elem_of_dom_2|done]). congruence.
            -- apply eq_None_not_Some. intros [v' C]. apply (CDC (ech (h (edual t)))).
               ++ apply CR. by eapply elem_of_dom_2.
               ++ apply HCq. rewrite ech_edual. apply HΘp. by eapply elem_of_dom_2.
        + apply LVD in A as ((t & -> & A) & HDt).
          destruct (Hpart t (proj1 (Fv t (elem_of_dom_2 _ _ _ A))) HDt) as (u & T1 & z & T2 & Eu & Lt & Lu & Hsd & Nub).
          destruct (Lv t _ A) as [At _]. rewrite At in Lt. injection Lt as <- <-.
          exists T2. split; [|done]. rewrite <-Eu.
          assert (KE !! h u = None) as NE.
          { apply eq_None_not_Some. intros [v' C]. apply (CDC (ech (h u))); [rewrite Eu, ech_edual; done|apply CE; by eapply elem_of_dom_2]. }
          destruct (Lvr u _ Lu Nub) as [Lu'|Lu'].
          * apply lookup_union_Some_raw. right. split.
            -- apply lookup_union_None. split; [done|]. apply eq_None_not_Some. intros [v' C]. apply LRP in C as ((r & Er & C) & _).
               assert (u = r) as <- by (apply Zi; [left; apply Fv; by eapply elem_of_dom_2|left; apply Fr; by eapply elem_of_dom_2|done]).
               apply (Nvr u); by eapply elem_of_dom_2.
            -- apply lookup_union_Some_raw. right. split.
               ++ apply eq_None_not_Some. intros [v' C]. apply (CDC (ech (h u))); [rewrite Eu, ech_edual; done|apply CΘ; by eapply elem_of_dom_2].
               ++ apply LVD. split; [eauto|]. by rewrite Eu, ech_edual.
          * apply lookup_union_Some_l. apply lookup_union_Some_raw. right. split; [done|].
            apply LRP. split; [eauto|]. apply LDS. exists t, (S1, z1). split_and!; [done|by rewrite Eu, ech_edual|by rewrite Eu, ech_edual]. }
    (* O6: the payload *)
    assert (kren h (Σv ∪ Θe) = sdrop D KV ∪ (KΘ ∪ VD)) as O6.
    { assert (kinj h (Σv ∪ Θe)) as K by (apply Hksub; intros o Ho; rewrite !dom_union_L in *; set_solver).
      rewrite kren_union by done. fold KV KΘ.
      rewrite <-(map_filter_union_complement (λ oe : cend * (sty * point), ech oe.1 ∈ D) KV) at 1. fold VD.
      change (filter (λ oe : cend * (sty * point), ¬ ech oe.1 ∈ D) KV) with (sdrop D KV).
      assert (VD ##ₘ sdrop D KV) as DV by apply map_disjoint_filter_complement.
      assert (KV ##ₘ KΘ) as DVT.
      { apply map_disjoint_spec. intros o' v1 v2 A B. apply LKV in A as (u & -> & A). apply LKΘ in B as (u' & E' & B).
        assert (u = u') as <- by (apply Zi; [left; apply Fv; by eapply elem_of_dom_2|right; apply HΘp; by eapply elem_of_dom_2|done]).
        apply (HΣC u); [apply Fv; by eapply elem_of_dom_2|apply HΘp; by eapply elem_of_dom_2]. }
      rewrite (map_union_comm VD) by done. rewrite <-(assoc_L (∪)). f_equal. apply map_union_comm.
      by apply map_disjoint_sym. }
    (* O7: the successor *)
    set (Σ1 := <[b := (S, x⁺)]> (Σr ∪ Σe)).
    assert (Σr ##ₘ Σe) as Dre.
    { apply map_disjoint_dom. intros o A B. apply (HΣC o); [by apply Fr|by apply HΣep]. }
    assert (∀ o, o ∈ dom Σ1 ↔ o = b ∨ o ∈ dom Σr ∨ o ∈ dom Σe) as DΣ1.
    { intros o. unfold Σ1. rewrite dom_insert_L, dom_union_L. set_solver. }
    assert (∀ o, o ∈ dom Σ1 → pheld Σ p o) as HΣ1.
    { intros o Ho. apply DΣ1 in Ho as [->|[Ho|Ho]]; [by left|left; by apply Fr|right; by apply HΣep]. }
    assert (kinj h Σ1) as K1 by (by apply Hkh).
    assert (∀ o, o ∈ dom Σv → o ∉ dom Σ1 ∧ ech o ∉ p.1) as Vout.
    { intros o Ho. split.
      - intros Hin. apply DΣ1 in Hin as [->|[Hin|Hin]].
        + by apply (Fv b Ho).
        + by apply (Nvr o).
        + by apply (HΣC o); [apply Fv|apply HΣep].
      - apply HΣC. by apply Fv. }
    set (C1 := p.1 ∖ fchans w).
    assert (sdrop D' (kren h Σ1) = <[h b := (S, x⁺)]> (sdrop D KR ∪ (KE ∪ RP))) as EΣ1.
    { assert (sdrop D KR ##ₘ KE ∪ RP) as DRE.
      { apply map_disjoint_union_r. split.
        - apply map_disjoint_spec. intros o' v1 v2 A B. apply sdrop_lookup in A as [A _].
          apply LKR in A as (u & -> & A). apply LKE in B as (u' & E' & B).
          assert (u = u') as <- by (apply Zi; [left; apply Fr; by eapply elem_of_dom_2|right; apply HΣep; by eapply elem_of_dom_2|done]).
          apply (HΣC u); [apply Fr; by eapply elem_of_dom_2|apply HΣep; by eapply elem_of_dom_2].
        - apply map_disjoint_spec. intros o' v1 v2 A B. apply sdrop_lookup in A as [_ A]. apply A, CR. by eapply elem_of_dom_2. }
      apply map_eq. intros o'. apply option_eq. intros v. rewrite sdrop_lookup, kren_iff by done.
      rewrite lookup_insert_Some, (lookup_union_Some _ _ _ _ DRE), (lookup_union_Some _ _ _ _ DER), sdrop_lookup, LKR, LKE, LRP.
      split.
      - intros [(u & -> & Lu) Nu]. unfold Σ1 in Lu. apply lookup_insert_Some in Lu as [[<- <-]|[Nub Lu]]; [by left|right].
        split; [intros E; apply Nub; apply Zi; [by left|apply HΣ1; unfold Σ1; rewrite dom_insert_L; apply elem_of_union_r; by eapply elem_of_dom_2|done]|].
        rewrite (lookup_union_Some _ _ _ _ Dre) in Lu. destruct Lu as [Lu|Lu].
        + destruct (decide (ech (h u) ∈ D)) as [HD|HD]; [right; right; split; [eauto|]|left; split; [eauto|done]].
          unfold D' in Nu. destruct (decide (ech (h u) ∈ DS)); [done|]. exfalso. apply Nu. by apply elem_of_difference.
        + right. left. eauto.
      - intros [[<- <-]|[Nb' [[(u & -> & Lu) ND']|[(u & -> & Lu)|((u & -> & Lu) & HDS')]]]].
        + split; [exists b; split; [done|apply lookup_insert_eq]|]. unfold D'. intros [? _]%elem_of_difference. done.
        + split; [exists u; split; [done|]|unfold D'; intros [? _]%elem_of_difference; done].
          unfold Σ1. rewrite lookup_insert_ne by (intros ->; done). by apply lookup_union_Some_l.
        + split; [exists u; split; [done|]|].
          * unfold Σ1. rewrite lookup_insert_ne by (intros ->; done). apply lookup_union_Some_r; [done|done].
          * unfold D'. intros [HD _]%elem_of_difference. apply (CDC (ech (h u))); [done|apply HCq, HΣep; by eapply elem_of_dom_2].
        + split; [exists u; split; [done|]|].
          * unfold Σ1. rewrite lookup_insert_ne by (intros ->; done). by apply lookup_union_Some_l.
          * unfold D'. intros [_ ?]%elem_of_difference. done. }
    assert (∀ c, c ∈ fchans w ↔ ∃ u, (u ∈ dom Σv ∨ u ∈ dom Θe) ∧ ech u = c) as Lfw.
    { intros c. unfold fchans. rewrite <-Hfw, elem_of_map. setoid_rewrite elem_of_union. naive_solver. }
    assert (∀ c, c ∈ fchans (emap h w) ↔ ∃ u, (u ∈ dom Σv ∨ u ∈ dom Θe) ∧ ech (h u) = c) as Lfw'.
    { intros c. unfold fchans. rewrite fends_emap, <-Hfw, elem_of_map. setoid_rewrite elem_of_map.
      setoid_rewrite elem_of_union. naive_solver. }
    assert (set_map (gch h) C1 ∪ D' = q.1 ∖ fchans (emap h w)) as EC1.
    { rewrite Eq1. apply set_eq. intros c. rewrite elem_of_difference, Lfw', !elem_of_union. unfold C1, D'.
      rewrite elem_of_difference. split.
      - intros [(x1 & -> & Hx)%elem_of_map|Zc].
        + apply elem_of_difference in Hx as [Hx Nx]. split; [left; by apply elem_of_map_2|].
          intros (u & [Hu|Hu] & Eu).
          * apply (HΣq u); [by apply Fv|]. rewrite Eu. by apply elem_of_map_2.
          * apply Nx. apply Lfw. exists u. split; [by right|]. by apply (hd_chan u x1); [right; right; apply HΘp|done|].
        + destruct Zc as [ZcD ZcS]. split; [by right|]. intros (u & [Hu|Hu] & Eu).
          * apply ZcS. apply LDS. apply elem_of_dom in Hu as [v Hv]. exists u, v. split_and!; [done|done|done].
          * apply (CDC c); [done|]. rewrite <-Eu. apply HCq, HΘp, Hu.
      - intros [[(x1 & -> & Hx)%elem_of_map|Zc] N].
        + left. apply elem_of_map. exists x1. split; [done|]. apply elem_of_difference. split; [done|].
          intros (u & [Hu|Hu] & <-)%Lfw.
          * by apply (HΣC u); [apply Fv|].
          * apply N. exists u. split; [by right|]. by rewrite gch_ech.
        + right. split; [done|]. intros (u & v & Hu & Eu & _)%LDS. apply N. exists u. split; [left; by eapply elem_of_dom_2|done]. }
    assert (gfuse h D' Σ1 (C1, soup (<[i := e1]> M)) (q.1 ∖ fchans (emap h w), soup (<[i := e1']> M'))) as Gf.
    { assert (∀ o, pheld Σ1 (C1, soup (<[i := e1]> M)) o → pheld Σ p o) as Hph.
      { intros o [Ho|Ho]; [by apply HΣ1|right]. simpl in Ho. unfold C1 in Ho. set_solver. }
      split_and!.
      - split_and!.
        + apply Hd.
        + intros o1 o2 A B. apply Zi; by apply Hph.
        + intros o1 o2 A B E. destruct (hpart o1 o2 (Hph _ A) (Hph _ B) E) as [?|HD]; [by left|right].
          unfold D'. apply elem_of_difference. split; [done|]. intros (t & vt & Ht & Et & _)%LDS.
          assert (o1 = t ∨ o2 = t) as Ot.
          { symmetry in Et. apply ech_eq in Et as [Et|Et].
            - left. apply Zi; [by apply Hph|left; apply Fv; by eapply elem_of_dom_2|done].
            - right. apply Zi; [by apply Hph|left; apply Fv; by eapply elem_of_dom_2|by rewrite E, Et]. }
          assert (t ∈ dom Σv) as Ht' by (by eapply elem_of_dom_2). destruct (Vout t Ht') as [V1 V2].
          destruct Ot as [<-|<-]; [destruct A as [A|A]|destruct B as [B|B]]; try done; simpl in *; unfold C1 in *; set_solver.
        + intros c A B. apply elem_of_map in B as (x1 & -> & Hx). apply (HDc (gch h x1)); [unfold D' in A; set_solver|].
          apply elem_of_map_2. unfold C1 in Hx. set_solver.
        + intros o' Ho'. assert (ech o' ∈ D ∧ ech o' ∉ DS) as [HD HN] by (unfold D' in Ho'; set_solver).
          destruct (Hdp o' HD) as (T1 & z & T2 & K3 & K4 & Hs3). exists T1, z, T2.
          assert (∀ o'' v, kren h Σ !! o'' = Some v → ech o'' = ech o' → kren h Σ1 !! o'' = Some v) as Hmv.
          { intros o'' v A Eo. destruct (kren_lookup_inv _ _ _ _ A) as (u & -> & Au).
            apply kren_lookup; [done|]. assert (u ≠ b) as Nub by (intros ->; apply ND; by rewrite Eo).
            destruct (Lvr u v Au Nub) as [Av|Ar].
            - exfalso. apply HN. apply LDS. exists u, v. split_and!; [done|done|done].
            - unfold Σ1. rewrite lookup_insert_ne by done. by apply lookup_union_Some_l. }
          split_and!; [by apply Hmv|apply Hmv; [done|by rewrite ech_edual]|done].
      - simpl. by rewrite EC1.
      - apply mcrel_of_mrel. apply (mrel_mono_in R); [|by apply mrel_insert]. intros e0 o o' _ _ Hoo' Ho. apply Hoo'.
        destruct Ho as [Ho|[Ho|Ho]].
        + destruct (Hph o (or_introl Ho)) as [?|?]; [by left|by right; right].
        + destruct (Hph (edual o) (or_introl Ho)) as [?|?]; [by right; left|right; right; by rewrite <-ech_edual].
        + right; right. simpl in Ho. unfold C1 in Ho. set_solver. }
    assert (fside D' Σ1 T (C1, soup (<[i := e1]> M))) as Fs1.
    { split.
      - simpl. intros c Zc Zc'. apply chans_of_elem in Zc' as (o & Ho & <-). unfold C1 in Zc.
        apply elem_of_difference in Zc as [Zc Nc]. apply DΣ1 in Ho as [->|[Ho|Ho]].
        + by apply (HΣC b).
        + by apply (HΣC o); [apply Fr|].
        + apply Nc. apply Lfw. exists (edual o). split; [right; by apply Ss2|by rewrite ech_edual].
      - destruct (proj2 Hs) as [HT Hpf].
        split; [done|]. intros o Ho Ho'. apply DΣ1 in Ho, Ho'.
        destruct Ho as [->|[Ho|Ho]], Ho' as [Ho'|[Ho'|Ho']].
        + by apply (edual_ne b).
        + by apply (Hpf b); [|apply Fr].
        + by apply (HΣC b); [|rewrite <-ech_edual; apply HΣep].
        + by apply (Hpf o); [apply Fr|subst].
        + by apply (Hpf o); [apply Fr|apply Fr].
        + by apply (HΣC o); [apply Fr|rewrite <-ech_edual; apply HΣep].
        + apply (HΣC b Hb). rewrite <-Ho', ech_edual. by apply HΣep.
        + by apply (HΣC (edual o)); [apply Fr|rewrite ech_edual; apply HΣep].
        + apply Ss2 in Ho as [_ Ho]. apply Ss2 in Ho' as [Ho' _]. by rewrite edual_edual in Ho'. }
    assert (kinj h (Σv ∪ Θe)) as KvΘ by (apply Hksub; intros o Ho; rewrite !dom_union_L in *; set_solver).
    exists S0, x, m, U, S, (sdrop D KV), (sdrop D KR), (KΘ ∪ VD), (KE ∪ RP). split_and!.
    - by apply lookupq.
    - done.
    - exact O2.
    - exact O3.
    - exact O4.
    - exact O5.
    - rewrite <-O6. destruct AV as [A0 A1]. split.
      + intros Hz. apply (proj1 (rename_level κ n (payload_at m U x))); [done|by apply A0].
      + intros Hz j Hj Hj'. apply (proj1 (rename_level κ j (payload_at m U x))); [done|by apply A1].
    - rewrite <-EΣ1. eapply (at_cost_transfer κ n Xs Xt _ _ _ _ _ _ h D'); [done|done|exact Fs1|exact Gf|apply senv_eqv_refl|exact AP].
  Qed.
  Local Lemma fuse_ok_sub (Σ2 : senv) (C2 : gset chan) E2 (D' : gset chan) : dom Σ2 ⊆ dom Σ → C2 ⊆ p.1 → D' ⊆ D →
    (∀ o1 o2, pheld Σ2 (C2, E2) o1 → pheld Σ2 (C2, E2) o2 → ech (h o1) ∈ D → h o2 = edual (h o1) →
      o2 = edual o1 ∨ ech (h o1) ∈ D') →
    dpairs D' (kren h Σ2) → fuse_ok h D' Σ2 (C2, E2).
  Proof.
    intros H1 H2 H3 Hpp Hdp'. destruct Hok as (A1 & A2 & A3 & A4 & A5).
    assert (∀ o, pheld Σ2 (C2, E2) o → pheld Σ p o) as Hph.
    { intros o [Ho|Ho]; [left; set_solver|right; simpl in Ho; set_solver]. }
    split_and!; [done| | |set_solver|done].
    - intros o1 o2 B1 B2. apply A2; by apply Hph.
    - intros o1 o2 B1 B2 E. destruct (A3 o1 o2 (Hph _ B1) (Hph _ B2) E) as [?|HD']; [by left|]. by apply Hpp.
  Qed.

  Local Lemma lvl_cost (X : prel) m c W Σ0 T0 p0 j :
    (∀ W Σ T p, X W Σ T p → Prel κ m W Σ T p) →
    at_cost_P m c (Prel κ) X W Σ0 T0 p0 → ole (oadd j c) m → Prel κ j W Σ0 T0 p0.
  Proof.
    intros XP [A0 A1] Hj. destruct (decide (c = 0)) as [->|Hz].
    - eapply Prel_down; [rewrite oadd_0 in Hj; exact Hj|by apply XP, A0].
    - by apply A1.
  Qed.

  Local Lemma lvl_split jj : ole (oadd jj (c_give κ + c_take κ)) n →
    ole (oadd (oadd jj (c_take κ)) (c_give κ)) n ∧ olt ozero (oadd jj (c_take κ)) ∧
    ole (oadd jj (c_give κ)) (oadd jj (c_take κ)) ∧ ole (oadd jj (c_take κ)) (oadd jj (c_take κ)) ∧ olt jj n.
  Proof.
    intros Hjj. pose proof (c_take_pos κ) as Ht. pose proof (c_give_take κ) as Hgt. split_and!.
    - rewrite oadd_add. by rewrite Nat.add_comm.
    - apply (ole_trans_lt ozero jj); [done|]. apply (oadd_lt jj (c_take κ)); [lia|apply ole_refl].
    - by apply oadd_mono_r.
    - apply ole_refl.
    - apply (oadd_lt jj (c_give κ + c_take κ)); [lia|exact Hjj].
  Qed.

  (** A close on both ends of a channel of D. *)
  Local Lemma self_close M M' i j b b' e e1 e1' g g1 g1' :
    soup M = p.2 → mrel R M M' → i ≠ j → M !! i = Some e → M !! j = Some g →
    tstep e (LSess (SClose b)) e1 → tstep g (LSess (SClose b')) g1 →
    crel R e1 e1' → crel R g1 g1' → b ∈ dom Σ → b' ∈ dom Σ → ech (h b) ∈ D → h b' = edual (h b) →
    ∀ jj, ole (oadd jj (c_give κ + c_take κ)) n →
      Prel κ jj W1 Σq T (erase (q.1 ∖ {[ech (h b)]}, <[j := g1']> (<[i := e1']> M'))).
  Proof.
    intros HM Hr Hij He Hg Hs1 Hs2 Hc1 Hc2 Hb Hb' HD Ebb jj Hjj.
    destruct (lvl_split jj Hjj) as (L1 & L2 & L3 & L4 & L5).
    assert (ech b ∉ p.1) as Nb by (intros Hp; by apply (notD b Hp)).
    assert (ech b' ∉ p.1) as Nb' by (intros Hp; apply (notD b' Hp); by rewrite Ebb, ech_edual).
    assert (b ≠ b') as Nbb by (intros <-; apply (edual_ne (h b)); by rewrite <-Ebb).
    pose proof HC as (_ & _ & _ & _ & _ & H4 & _).
    assert (istep (p.1, M) (EvOffer i (SClose b)) (p.1 ∖ ∅, <[i := e1]> M)) as St1.
    { eapply p_act_session; [done|done|]. simpl. set_solver. }
    destruct (H4 _ _ _ _ (erase_p M HM) St1) as (S0 & x & Lb & U0 & A1).
    pose proof (lvl_cost Xs n _ _ _ _ _ _ HXP A1 L1) as P1.
    destruct (Prel_clauses κ _ _ _ _ _ L2 P1 W1 (wext_refl W1)) as (_ & _ & _ & _ & _ & H4' & _).
    assert (istep (p.1 ∖ ∅, <[i := e1]> M) (EvOffer j (SClose b')) (p.1 ∖ ∅ ∖ ∅, <[j := g1]> (<[i := e1]> M))) as St2.
    { eapply p_act_session; [by rewrite lookup_insert_ne|done|]. simpl. set_solver. }
    destruct (H4' _ _ _ _ eq_refl St2) as (S0' & x' & Lb' & U0' & A2).
    pose proof (lvl_cost (Prel κ (oadd jj (c_take κ))) _ _ _ _ _ _ _ (λ _ _ _ _ H, H) A2 L3) as P2.
    unfold erase in P2. simpl in P2. rewrite !difference_empty_L in P2.
    set (Σ2 := delete b' (delete b Σ)). set (D' := D ∖ {[ech (h b)]}).
    assert (∀ u, pheld Σ p u → ech (h u) = ech (h b) → u = b ∨ u = b') as Hon.
    { intros u Hu E. apply ech_eq in E as [E|E].
      - left. symmetry. apply hinj; [by left|done|done].
      - right. apply hinj; [done|by left|by rewrite Ebb, E, edual_edual]. }
    assert (∀ o, o ∈ dom Σ2 ↔ o ∈ dom Σ ∧ o ≠ b ∧ o ≠ b') as DΣ2.
    { intros o. unfold Σ2. rewrite !dom_delete_L. set_solver. }
    apply (HL jj L5 W1 Σ2 T (p.1, soup (<[j := g1]> (<[i := e1]> M))) _ h D' Σq P2).
    - split.
      + intros c Hc Hc'. apply (HC1 c Hc). apply chans_of_elem in Hc' as (o & Ho & <-). apply elem_of_chans_of.
        by apply DΣ2 in Ho as [? _].
      + destruct (proj2 Hs) as [HT Hpf]. split; [done|].
        intros o Ho Ho'. apply DΣ2 in Ho as [Ho _]. apply DΣ2 in Ho' as [Ho' _]. by apply (Hpf o).
    - split_and!.
      + apply fuse_ok_sub.
        * intros o Ho. by apply DΣ2 in Ho as [? _].
        * done.
        * unfold D'. intros c Hc0. by apply elem_of_difference in Hc0 as [? _].
        * intros o1 o2 B1 B2 HD1 E. right. unfold D'. apply elem_of_difference. split; [done|].
          rewrite elem_of_singleton. intros E1.
          assert (pheld Σ p o1) as B1' by (destruct B1 as [B1|B1]; [left; by apply DΣ2 in B1 as [? _]|by right]).
          destruct B1 as [B1|B1]; [|apply (notD o1 B1); by rewrite E1]. apply DΣ2 in B1 as (_ & N1 & N2). by destruct (Hon o1 B1' E1).
        * intros o Ho. assert (ech o ∈ D ∧ ech o ≠ ech (h b)) as [HoD Hob] by (unfold D' in Ho; apply elem_of_difference in Ho as [A B]; rewrite elem_of_singleton in B; done).
          destruct (Hdp o HoD) as (T1 & z & T2 & K3 & K4 & Hs3). exists T1, z, T2.
          assert (∀ o'' v, kren h Σ !! o'' = Some v → ech o'' = ech o → kren h Σ2 !! o'' = Some v) as Hmv.
          { intros o'' v A Eo. destruct (kren_lookup_inv _ _ _ _ A) as (u & -> & Au).
            assert (u ≠ b ∧ u ≠ b') as [N1 N2].
            { split; intros ->; apply Hob; rewrite <-Eo; [done|by rewrite Ebb, ech_edual]. }
            apply kren_lookup; [apply (kinj_sub h Σ); [intros x0 Hx0; by apply DΣ2 in Hx0 as [? _]|apply Hk]|].
            unfold Σ2. by rewrite !lookup_delete_ne. }
          split_and!; [by apply Hmv|apply Hmv; [done|by rewrite ech_edual]|done].
      + simpl. rewrite Eq1. unfold D'.
        assert (ech (h b) ∉ (set_map (gch h) p.1 : gset chan)) as Nbg by (intros A; by apply (HDc (ech (h b)))).
        apply set_eq. intros c. rewrite !elem_of_difference, !elem_of_union, !elem_of_difference, elem_of_singleton.
        split; [intros [[A|A] N]; [by left|by right]|intros [A|[A N]]; [split; [by left|intros ->; done]|split; [by right|done]]].
      + apply mcrel_of_mrel. apply (mrel_mono_in R); [|apply mrel_insert; [apply mrel_insert|]; done].
        intros e0 o o' _ _ Hoo' Ho. apply Hoo'. destruct Ho as [Ho|[Ho|Ho]];
          [left; by apply DΣ2 in Ho as [? _]|right; left; by apply DΣ2 in Ho as [? _]|by right; right].
    - cut (sdrop D' (kren h Σ2) = Σq); [intros ->; apply senv_eqv_refl|]. apply map_eq. intros o'. apply option_eq. intros v. rewrite !sdrop_lookup.
      assert (kinj h Σ2) as K2 by (apply (kinj_sub h Σ); [intros x0 Hx0; by apply DΣ2 in Hx0 as [? _]|apply Hk]).
      rewrite (kren_iff Σ2) by done. rewrite (kren_iff Σ) by apply Hk. split.
      + intros [(u & -> & Lu) Nu]. unfold Σ2 in Lu. apply lookup_delete_Some in Lu as [N1 Lu].
        apply lookup_delete_Some in Lu as [N2 Lu]. split; [eauto|]. intros HD1. apply Nu. unfold D'.
        apply elem_of_difference. split; [done|]. rewrite elem_of_singleton. intros E.
        destruct (Hon u (or_introl (elem_of_dom_2 _ _ _ Lu)) E); congruence.
      + intros [(u & -> & Lu) Nu]. assert (u ≠ b) as N1 by (intros ->; done).
        assert (u ≠ b') as N2 by (intros ->; apply Nu; by rewrite Ebb, ech_edual).
        split; [exists u; split; [done|unfold Σ2; by rewrite !lookup_delete_ne]|]. unfold D'. rewrite elem_of_difference, elem_of_singleton. tauto.
  Qed.


  (** The two ends of a channel of D move on together. *)
  Local Lemma pair_update b b' S S' z E M0 M0' : b ∈ dom Σ → b' ∈ dom Σ → ech (h b) ∈ D → h b' = edual (h b) →
    sdual S S' → mrel R M0 M0' →
    fside D (<[b' := (S', z‾)]> (<[b := (S, z)]> Σ)) T (p.1, E) ∧
    gfuse h D (<[b' := (S', z‾)]> (<[b := (S, z)]> Σ)) (p.1, soup M0) (q.1, soup M0') ∧
    sdrop D (kren h (<[b' := (S', z‾)]> (<[b := (S, z)]> Σ))) = Σq.
  Proof.
    intros Hb Hb' HD Ebb Hsd Hr. set (Σ2 := <[b' := (S', z‾)]> (<[b := (S, z)]> Σ)).
    assert (b ≠ b') as Nbb by (intros <-; apply (edual_ne (h b)); by rewrite <-Ebb).
    assert (dom Σ2 = dom Σ) as DΣ2.
    { unfold Σ2. rewrite !dom_insert_L. apply set_eq. intros o. rewrite !elem_of_union, !elem_of_singleton. naive_solver. }
    assert (kinj h Σ2) as K2 by (apply (kinj_sub h Σ); [by rewrite DΣ2|apply Hk]).
    assert (∀ u, u ≠ b → u ≠ b' → Σ2 !! u = Σ !! u) as LΣ2 by (intros u N1 N2; unfold Σ2; by rewrite !lookup_insert_ne).
    assert (∀ u, u ∈ dom Σ → ech (h u) = ech (h b) → u = b ∨ u = b') as Hon.
    { intros u Hu E0. apply ech_eq in E0 as [E0|E0].
      - left. symmetry. apply hinj; [by left|by left|done].
      - right. apply hinj; [by left|by left|by rewrite Ebb, E0, edual_edual]. }
    split_and!.
    - split; [simpl; intros c Hc Hc'; apply (HC1 c Hc); unfold chans_of in *; by rewrite <-DΣ2|].
      destruct (proj2 Hs) as [HT Hpf]. split; [done|]. intros o. rewrite DΣ2. apply Hpf.
    - split_and!; [|apply Eq1|].
      + apply fuse_ok_sub; [by rewrite DΣ2|done|done|by intros; right|].
        intros o Ho. destruct (Hdp o Ho) as (T1 & y & T2 & K3 & K4 & Hs3).
        destruct (kren_lookup_inv _ _ _ _ K3) as (u & -> & Lu).
        destruct (kren_lookup_inv _ _ _ _ K4) as (w & Ew & Lw).
        destruct (decide (ech (h u) = ech (h b))) as [E0|E0].
        * assert (u = b ∨ u = b') as [->| ->] by (apply Hon; [by eapply elem_of_dom_2|done]).
          -- exists S, z, S'. rewrite <-Ebb. split_and!; [|apply kren_lookup; [done|unfold Σ2; apply lookup_insert_eq]|done].
             apply kren_lookup; [done|]. unfold Σ2. rewrite lookup_insert_ne by done. apply lookup_insert_eq.
          -- exists S', z‾, S. rewrite pt_dual_dual, Ebb, edual_edual. split_and!; [| |by apply sdual_sym].
             ++ rewrite <-Ebb. apply kren_lookup; [done|]. apply lookup_insert_eq.
             ++ apply kren_lookup; [done|]. unfold Σ2. rewrite lookup_insert_ne by done. apply lookup_insert_eq.
        * exists T1, y, T2. assert (u ≠ b ∧ u ≠ b') as [N1 N2].
          { split; intros ->; apply E0; [done|by rewrite Ebb, ech_edual]. }
          assert (w ≠ b ∧ w ≠ b') as [N3 N4].
          { split; intros ->; apply E0; rewrite <-(ech_edual (h u)), Ew; [done|by rewrite Ebb, ech_edual]. }
          split_and!; [apply kren_lookup; [done|by rewrite LΣ2]|rewrite Ew; apply kren_lookup; [done|by rewrite LΣ2]|done].
      + apply mcrel_of_mrel. apply (mrel_mono_in R); [|done]. intros e0 o o' _ _ Hoo' Ho. apply Hoo'.
        by rewrite <-!DΣ2.
    - apply map_eq. intros o'. apply option_eq. intros v. rewrite !sdrop_lookup, (kren_iff Σ2), (kren_iff Σ) by (done || apply Hk).
      split.
      + intros [(u & -> & Lu) N]. assert (u ≠ b ∧ u ≠ b') as [N1 N2].
        { split; intros ->; apply N; [done|by rewrite Ebb, ech_edual]. }
        rewrite LΣ2 in Lu by done. eauto.
      + intros [(u & -> & Lu) N]. assert (u ≠ b ∧ u ≠ b') as [N1 N2].
        { split; intros ->; apply N; [done|by rewrite Ebb, ech_edual]. }
        split; [exists u; by rewrite LΣ2|done].
  Qed.

  (** A select on one end of a channel of D and a branch on the other. *)
  Local Lemma self_choice M M' i j b b' k e e1 e1' g g1 g1' :
    soup M = p.2 → mrel R M M' → i ≠ j → M !! i = Some e → M !! j = Some g →
    tstep e (LSess (SSel b k)) e1 → tstep g (LSess (SBra b' k)) g1 →
    crel R e1 e1' → crel R g1 g1' → b ∈ dom Σ → b' ∈ dom Σ → ech (h b) ∈ D → h b' = edual (h b) →
    ∀ jj, ole (oadd jj (c_give κ + c_take κ)) n →
      Prel κ jj W1 Σq T (erase (q.1, <[j := g1']> (<[i := e1']> M'))).
  Proof.
    intros HM Hr Hij He Hg Hs1 Hs2 Hc1 Hc2 Hb Hb' HD Ebb jj Hjj.
    destruct (lvl_split jj Hjj) as (L1 & L2 & L3 & L4 & L5).
    assert (ech b ∉ p.1) as Nb by (intros Hp; by apply (notD b Hp)).
    assert (ech b' ∉ p.1) as Nb' by (intros Hp; apply (notD b' Hp); by rewrite Ebb, ech_edual).
    assert (b ≠ b') as Nbb by (intros <-; apply (edual_ne (h b)); by rewrite <-Ebb).
    pose proof HC as (_ & _ & _ & _ & _ & _ & H5 & _).
    assert (istep (p.1, M) (EvOffer i (SSel b k)) (p.1 ∖ ∅, <[i := e1]> M)) as St1.
    { eapply p_act_session; [done|done|]. simpl. intros c A B. apply elem_of_singleton in A as ->. done. }
    destruct (H5 _ _ _ _ _ (erase_p M HM) St1) as (S0 & x & S1 & S2 & Lb & U0 & A1).
    pose proof (lvl_cost Xs n _ _ _ _ _ _ HXP A1 L1) as P1.
    destruct (Prel_clauses κ _ _ _ _ _ L2 P1 W1 (wext_refl W1)) as (_ & _ & _ & _ & _ & _ & _ & H6' & _).
    assert (istep (p.1 ∖ ∅, <[i := e1]> M) (EvOffer j (SBra b' k)) (p.1 ∖ ∅ ∖ ∅, <[j := g1]> (<[i := e1]> M))) as St2.
    { eapply p_act_session; [by rewrite lookup_insert_ne|done|]. simpl. rewrite difference_empty_L.
      intros c A B. apply elem_of_singleton in A as ->. done. }
    destruct (H6' _ _ _ _ _ eq_refl St2) as (S0' & x' & S1' & S2' & Lb' & U0' & A2).
    pose proof (lvl_cost (Prel κ (oadd jj (c_take κ))) _ _ _ _ _ _ _ (λ _ _ _ _ H, H) A2 L4) as P2.
    unfold erase in P2. simpl in P2. rewrite !difference_empty_L in P2.
    rewrite lookup_insert_ne in Lb' by done.
    destruct (Hdp (h b) HD) as (T1 & y & T2 & K3 & K4 & Hs3).
    apply (kren_lookup_held h Σ b) in K3; [|apply Hk|done]. rewrite Lb in K3. injection K3 as <- <-.
    rewrite <-Ebb in K4. apply (kren_lookup_held h Σ b') in K4; [|apply Hk|done]. rewrite Lb' in K4. injection K4 as <- ->.
    destruct (sdual_plus _ _ _ _ Hs3 U0) as (S1'' & S2'' & U1 & Hd1 & Hd2).
    rewrite U0' in U1. injection U1 as <- <-.
    rewrite <-sel_bra_pt in P2.
    destruct (pair_update b b' (bsel k S1 S2) (bsel k S1' S2') (sel_pt x k) (soup (<[j := g1]> (<[i := e1]> M)))
      (<[j := g1]> (<[i := e1]> M)) (<[j := g1']> (<[i := e1']> M'))) as (F & G & EΣ); try done.
    - by apply sdual_bsel.
    - apply mrel_insert; [apply mrel_insert|]; done.
    - rewrite <-EΣ. exact (HL jj L5 W1 _ T _ _ h D _ P2 F G (senv_eqv_refl _)).
  Qed.

  (** A message from one end of a channel of D to the other. *)
  Local Lemma self_msg M M' i j b b' w e e1 e1' g g1 g1' :
    soup M = p.2 → mrel R M M' → i ≠ j → M !! i = Some e → M !! j = Some g →
    tstep e (LSess (SSend b w)) e1 → tstep g (LSess (SRecv b' w)) g1 →
    crel R e1 e1' → crel R g1 g1' → b ∈ dom Σ → b' ∈ dom Σ → ech (h b) ∈ D → h b' = edual (h b) →
    ∀ jj, ole (oadd jj (c_give κ + c_take κ)) n →
      Prel κ jj W1 Σq T (erase (q.1, <[j := g1']> (<[i := e1']> M'))).
  Proof.
    intros HM Hr Hij He Hg Hs1 Hs2 Hc1 Hc2 Hb Hb' HD Ebb jj Hjj.
    destruct (lvl_split jj Hjj) as (L1 & L2 & L3 & L4 & L5).
    assert (ech b ∉ p.1) as Nb by (intros Hp; by apply (notD b Hp)).
    assert (ech b' ∉ p.1) as Nb' by (intros Hp; apply (notD b' Hp); by rewrite Ebb, ech_edual).
    assert (b ≠ b') as Nbb by (intros <-; apply (edual_ne (h b)); by rewrite <-Ebb).
    assert (D ≠ ∅) as HDne by (intros E0; rewrite E0 in HD; by apply not_elem_of_empty in HD).
    destruct (proj2 Hs) as [HT Hpf].
    pose proof HC as (_ & _ & _ & H2 & _).
    assert (istep (p.1, M) (EvOffer i (SSend b w)) (p.1 ∖ fchans w, <[i := e1]> M)) as St1.
    { eapply p_act_session; [done|done|]. simpl. intros c A B. apply elem_of_singleton in A as ->. done. }
    destruct (H2 _ _ _ _ _ (erase_p M HM) St1)
      as (S0 & x & m & U & S & Σv & Σr & Θe & Σe & Lb & U0 & Dvr & Edel & HΘe & Hss & AV & AP).
    pose proof (lvl_cost Xs n _ _ _ _ _ _ HXP AP L1) as P1.
    destruct (Prel_clauses κ _ _ _ _ _ L2 P1 W1 (wext_refl W1)) as (_ & _ & _ & _ & H3' & _).
    assert (istep (p.1 ∖ fchans w, <[i := e1]> M) (EvOffer j (SRecv b' w)) ((p.1 ∖ fchans w) ∖ ∅, <[j := g1]> (<[i := e1]> M))) as St2.
    { eapply p_act_session; [by rewrite lookup_insert_ne|done|]. simpl.
      intros c A B. apply elem_of_singleton in A as ->. apply elem_of_difference in B as [? _]. done. }
    destruct (H3' _ _ _ _ _ eq_refl St2) as (S0' & x' & m' & U' & S' & Lb' & U0' & AR).
    rewrite lookup_insert_ne in Lb' by done.
    (* facts about the send *)
    assert (∀ o, o ∈ dom Θe → ech o ∈ p.1) as HΘp by (intros o Ho; by apply HΘe in Ho as [_ ?]).
    destruct Hss as (Ss1 & Ss2 & Ss3).
    assert (∀ o, o ∈ dom Σe → ech o ∈ p.1) as HΣep.
    { intros o Ho. apply Ss2 in Ho as [Ho _]. rewrite <-ech_edual. by apply HΘp. }
    assert (∀ o v, Σv !! o = Some v → Σ !! o = Some v ∧ o ≠ b) as Lv.
    { intros o v Hv. assert ((Σv ∪ Σr) !! o = Some v) as H' by (by apply lookup_union_Some_l).
      rewrite <-Edel in H'. apply lookup_delete_Some in H' as [? ?]. done. }
    assert (∀ o v, Σr !! o = Some v → Σ !! o = Some v ∧ o ≠ b) as Lr.
    { intros o v Hv. assert ((Σv ∪ Σr) !! o = Some v) as H' by (by apply lookup_union_Some_r).
      rewrite <-Edel in H'. apply lookup_delete_Some in H' as [? ?]. done. }
    assert (∀ o v, Σ !! o = Some v → o ≠ b → Σv !! o = Some v ∨ Σr !! o = Some v) as Lvr.
    { intros o v Hv Nob. assert ((Σv ∪ Σr) !! o = Some v) as H' by (rewrite <-Edel; by apply lookup_delete_Some).
      apply lookup_union_Some in H' as [?|?]; auto. }
    assert (∀ o, o ∈ dom Σ → ech o ∉ p.1) as HΣC.
    { intros o Ho Hp. apply (HC1 (ech o) Hp). by apply elem_of_chans_of. }
    assert (∀ o, o ∈ dom Σv → o ∈ dom Σ) as DvΣ by (intros o [v Hv]%elem_of_dom; eapply elem_of_dom_2, Lv; eauto).
    assert (∀ o, o ∈ dom Σr → o ∈ dom Σ) as DrΣ by (intros o [v Hv]%elem_of_dom; eapply elem_of_dom_2, Lr; eauto).
    assert (∀ t, t ∈ dom Σv → t ∉ dom Σr) as Nvr.
    { intros t A B. apply elem_of_dom in A as [? A], B as [? B].
      exact (proj1 (map_disjoint_spec Σv Σr) Dvr t _ _ A B). }
    assert (Σ !! b' = Some (S0', x')) as Lb''.
    { apply lookup_union_Some_raw in Lb' as [A|[_ A]]; [by apply Lr in A as [? _]|].
      exfalso. apply (HΣC b' Hb'). apply HΣep. by eapply elem_of_dom_2. }
    assert (b' ∈ dom Σr) as Hbr.
    { destruct (Lvr b' _ Lb'' (not_eq_sym Nbb)) as [A|A]; [|by eapply elem_of_dom_2].
      exfalso. apply lookup_union_Some_raw in Lb' as [A'|[A0 A']].
      - apply (Nvr b'); by eapply elem_of_dom_2.
      - apply (HΣC b' Hb'). apply HΣep. by eapply elem_of_dom_2. }
    (* the types of the pair *)
    destruct (Hdp (h b) HD) as (T1 & y & T2 & K3 & K4 & Hs3).
    apply (kren_lookup_held h Σ b) in K3; [|apply Hk|done]. rewrite Lb in K3. injection K3 as <- <-.
    rewrite <-Ebb in K4. apply (kren_lookup_held h Σ b') in K4; [|apply Hk|done]. rewrite Lb'' in K4. injection K4 as <- ->.
    destruct (sdual_snd _ _ _ _ _ Hs3 U0) as (U'' & S'' & U1 & Hteq & HdS).
    rewrite U0' in U1. injection U1 as -> <- <-.
    (* the payload *)
    assert (∃ jv, Vrel κ jv W1 (Σv ∪ Θe) (payload_at m U x) w) as [jv HVj].
    { destruct AV as [A0 A1]. destruct (decide (c_give κ = 0)) as [Hz|Hz]; [exists n; by apply A0|].
      exists ozero. apply A1; [done|done|by right]. }
    pose proof (Vrel_exact κ _ _ _ _ _ HVj) as Hfw. rewrite dom_union_L in Hfw.
    assert (Vrel κ jj W1 (Σv ∪ Θe) (payload_at m U' x‾) w) as HV.
    { rewrite payload_at_dual. apply (Vrel_teq κ _ _ _ _ _ _ (teq_payload m U U' x Hteq)).
      destruct AV as [A0 A1]. assert (ole (oadd jj (c_give κ)) n) as Lg by (eapply ole_trans; [|exact Hjj]; apply oadd_mono_r; lia).
      destruct (decide (c_give κ = 0)) as [Hz|Hz].
      - eapply Vrel_down; [|by apply A0]. rewrite Hz, oadd_0 in Lg. exact Lg.
      - apply A1; [done|exact (oadd_lt _ _ _ Hz Lg)|by left]. }
    set (Θ2 := Σv ∪ Θe). set (Σ1' := <[b' := (S', x‾⁺)]> (<[b := (S, x⁺)]> (Σr ∪ Σe))).
    assert (∀ o, o ∈ dom Θ2 ↔ o ∈ dom Σv ∨ o ∈ dom Θe) as DΘ2 by (intros o; unfold Θ2; by rewrite dom_union_L, elem_of_union).
    assert (∀ o, o ∈ dom Σv → o ∈ dom Σ ∧ o ≠ b ∧ o ≠ b') as Fv.
    { intros o Ho. split_and!; [by apply DvΣ| |].
      - intros ->. apply elem_of_dom in Ho as [v Hv]. by destruct (Lv b v Hv).
      - intros ->. by apply (Nvr b'). }
    assert (∀ o, o ∈ dom Σ → edual o ∉ dom Σ) as Pf by (intros o Ho; by apply Hpf).
    (* the receiver's view *)
    assert (set_map ech (dom Θ2) ## p.1 ∖ fchans w) as Hdj.
    { intros c (o & -> & Ho)%elem_of_map Hc.
      apply elem_of_difference in Hc as [_ Hc]. apply Hc. unfold fchans. rewrite <-Hfw.
      apply elem_of_map. exists o. split; [done|]. apply elem_of_union. by apply DΘ2. }
    assert (∀ o, o ∈ dom Θe → o ∉ dom Σ) as ΘΣ by (intros o Ho Ho'; by apply (HΣC o Ho'), HΘp).
    assert (∀ o, o ∈ dom Σe → o ∉ dom Σ) as EΣ by (intros o Ho Ho'; by apply (HΣC o Ho'), HΣep).
    assert (∀ o, o ∈ dom Σ1' ↔ o = b' ∨ o = b ∨ o ∈ dom Σr ∨ o ∈ dom Σe) as DΣ1'.
    { intros o. unfold Σ1'. rewrite !dom_insert_L, dom_union_L, !elem_of_union, !elem_of_singleton. tauto. }
    assert (recv_ok Σ1' Θ2) as Hok2.
    { split.
      - intros o Ho Ho'. apply DΣ1' in Ho'. apply DΘ2 in Ho as [Ho|Ho].
        + destruct (Fv o Ho) as (Ho1 & N1 & N2). destruct Ho' as [?|[?|[Ho'|Ho']]]; [done|done| |].
          * by apply (Nvr o).
          * by apply (EΣ o Ho').
        + destruct Ho' as [->|[->|[Ho'|Ho']]].
          * by apply (ΘΣ b').
          * by apply (ΘΣ b).
          * apply (ΘΣ o Ho). by apply DrΣ.
          * apply Ss2 in Ho' as [_ Ho']. done.
      - intros o S1 y1 S1' y1' Q1 Q2. unfold Θ2 in Q1. apply lookup_union_Some_raw in Q1 as [Q1|[Q10 Q1]].
        + exfalso. assert (o ∈ dom Σv) as Ho by (by eapply elem_of_dom_2). destruct (Fv o Ho) as (Ho' & _ & _).
          assert (edual o ∈ dom (Σ1' ∪ Θ2)) as Hee by (by eapply elem_of_dom_2).
          rewrite dom_union_L, elem_of_union, DΣ1', DΘ2 in Hee.
          destruct Hee as [[E|[E|[E|E]]]|[E|E]].
          * apply (Pf o Ho'). by rewrite E.
          * apply (Pf o Ho'). by rewrite E.
          * apply (Pf o Ho'). by apply DrΣ.
          * apply (HΣC o Ho'). rewrite <-ech_edual. by apply HΣep.
          * apply (Pf o Ho'). by apply DvΣ.
          * apply (HΣC o Ho'). rewrite <-ech_edual. by apply HΘp.
        + assert (o ∈ dom Θe) as Ho by (by eapply elem_of_dom_2).
          assert (edual o ∉ dom Σ) as No by (intros A; apply (HΣC _ A); rewrite ech_edual; by apply HΘp).
          destruct (Ss3 o S1 y1 Q1) as (S1'' & B & HsB).
          assert (Σ1' !! edual o = Σe !! edual o) as E1.
          { unfold Σ1'. rewrite !lookup_insert_ne by (intros E; apply No; rewrite <-E; done).
            rewrite lookup_union. destruct (Σr !! edual o) eqn:Er; [|by destruct (Σe !! edual o)].
            exfalso. apply No. apply (DrΣ (edual o)). by eapply elem_of_dom_2. }
          assert (Θ2 !! edual o = Θe !! edual o) as E2.
          { unfold Θ2. rewrite lookup_union. destruct (Σv !! edual o) eqn:Ev; [|by destruct (Θe !! edual o)].
            exfalso. apply No. apply (DvΣ (edual o)). by eapply elem_of_dom_2. }
          rewrite lookup_union, E1, E2, <-lookup_union in Q2. rewrite Q2 in B. injection B as <- <-. done. }
    pose proof (AR jj Θ2 L4 Hdj Hok2 HV) as P2.
    (* the environment after the receive *)
    set (Σ2 := <[b' := (S', x‾⁺)]> (<[b := (S, x⁺)]> Σ)).
    assert (recv_env Σ1' Θ2 = Σ2) as Erv.
    { apply map_eq. intros o. apply option_eq. intros v. rewrite (recv_env_lookup' _ _ _ _ Hok2). unfold Σ2.
      rewrite !lookup_insert_Some. split.
      - intros [[A N]|[A N]].
        + unfold Σ1' in A. rewrite !lookup_insert_Some in A.
          destruct A as [[-> <-]|[Nb1 [[-> <-]|[Nb2 A]]]]; [by left|right; split; [done|by left]|].
          right. split; [done|]. right. split; [done|].
          apply lookup_union_Some_raw in A as [A|[_ A]]; [by apply Lr in A as [? _]|].
          exfalso. apply N. apply DΘ2. right. apply Ss2. by eapply elem_of_dom_2.
        + destruct N as [N1 N2]. unfold Θ2 in A. apply lookup_union_Some_raw in A as [A|[A0 A]].
          * destruct (Fv o (elem_of_dom_2 _ _ _ A)) as (_ & Nb1 & Nb2). right. split; [done|]. right.
            split; [done|]. by apply Lv in A as [? _].
          * exfalso. destruct v as [vS vy]. destruct (Ss3 o _ _ A) as (S1'' & B & _). apply lookup_union_Some_raw in B as [B|[_ B]].
            -- apply N1. apply DΣ1'. right. right. right. by eapply elem_of_dom_2.
            -- apply N2. apply DΘ2. right. by eapply elem_of_dom_2.
      - assert (edual b' ∉ dom Θ2 ∧ edual b ∉ dom Θ2) as [Nb1' Nb2'].
        { split; intros A; apply DΘ2 in A as [A|A].
          - apply (Pf b' Hb'). by apply DvΣ.
          - apply (HΣC b' Hb'). rewrite <-ech_edual. by apply HΘp.
          - apply (Pf b Hb). by apply DvΣ.
          - apply (HΣC b Hb). rewrite <-ech_edual. by apply HΘp. }
        intros [[-> <-]|[Nb1 [[-> <-]|[Nb2 A]]]].
        + left. split; [unfold Σ1'; apply lookup_insert_eq|done].
        + left. split; [unfold Σ1'; rewrite lookup_insert_ne by done; apply lookup_insert_eq|done].
        + destruct (Lvr o v A (not_eq_sym Nb2)) as [Av|Ar].
          * right. split; [by apply lookup_union_Some_l|]. split.
            -- rewrite DΣ1'. intros [E|[E|[E|E]]].
               ++ apply (Pf b' Hb'). rewrite <-E, edual_edual. by apply DvΣ; eapply elem_of_dom_2.
               ++ apply (Pf b Hb). rewrite <-E, edual_edual. by apply DvΣ; eapply elem_of_dom_2.
               ++ apply (Pf o); [by apply DvΣ; eapply elem_of_dom_2|by apply DrΣ].
               ++ apply (HΣC o); [by apply DvΣ; eapply elem_of_dom_2|rewrite <-ech_edual; by apply HΣep].
            -- intros E. apply DΘ2 in E as [E|E].
               ++ apply (Pf o); [by apply DvΣ; eapply elem_of_dom_2|by apply DvΣ].
               ++ apply (HΣC o); [by apply DvΣ; eapply elem_of_dom_2|rewrite <-ech_edual; by apply HΘp].
          * left. split.
            -- unfold Σ1'. rewrite !lookup_insert_ne by done. by apply lookup_union_Some_l.
            -- intros E. apply DΘ2 in E as [E|E].
               ++ apply (Pf o); [by apply DrΣ; eapply elem_of_dom_2|by apply DvΣ].
               ++ apply (HΣC o); [by apply DrΣ; eapply elem_of_dom_2|rewrite <-ech_edual; by apply HΘp]. }
    assert ((p.1 ∖ fchans w) ∖ ∅ ∪ recv_back Σ1' Θ2 = p.1) as Erb.
    { rewrite difference_empty_L. apply set_eq. intros c. rewrite elem_of_union, elem_of_difference, recv_back_elem'. split.
      - intros [[? _]|(o & Ho & <- & Eo)]; [done|]. apply DΘ2 in Ho as [Ho|Ho].
        + exfalso. destruct (Fv o Ho) as (Ho' & _ & _).
          destruct Eo as [Eo|Eo]; [rewrite DΣ1' in Eo; destruct Eo as [E|[E|[E|E]]]|apply DΘ2 in Eo as [E|E]].
          * apply (Pf b' Hb'). by rewrite <-E, edual_edual.
          * apply (Pf b Hb). by rewrite <-E, edual_edual.
          * apply (Pf o Ho'). by apply DrΣ.
          * apply (HΣC o Ho'). rewrite <-ech_edual. by apply HΣep.
          * apply (Pf o Ho'). by apply DvΣ.
          * apply (HΣC o Ho'). rewrite <-ech_edual. by apply HΘp.
        + by apply HΘp.
      - intros Hc. destruct (decide (c ∈ fchans w)) as [Hw|Hw]; [right|by left].
        unfold fchans in Hw. rewrite <-Hfw in Hw. apply elem_of_map in Hw as (o & -> & Ho). apply elem_of_union in Ho as [Ho|Ho].
        + exfalso. apply (HΣC o); [by apply DvΣ|done].
        + exists o. split; [by apply DΘ2; right|]. split; [done|]. destruct (decide (edual o ∈ dom Θe)) as [E|E]; [by right; apply DΘ2; right|].
          left. apply DΣ1'. right. right. right. apply Ss2. rewrite edual_edual. done. }
    assert (Prel κ jj W1 Σ2 T (p.1, soup (<[j := g1]> (<[i := e1]> M)))) as P2'.
    { rewrite <-Erv, <-Erb. exact P2. }
    clear P2. rename P2' into P2. unfold Σ2 in P2. rewrite (pt_dual_shift 1 x) in P2.
    destruct (pair_update b b' S S' (x⁺) (soup (<[j := g1]> (<[i := e1]> M)))
      (<[j := g1]> (<[i := e1]> M)) (<[j := g1']> (<[i := e1']> M'))) as (F & G & EΣq); try done.
    - apply mrel_insert; [apply mrel_insert|]; done.
    - rewrite <-EΣq. exact (HL jj L5 W1 _ T _ _ h D _ P2 F G (senv_eqv_refl _)).
  Qed.


  (** ** Receives of q *)

  (** The value q receives is pulled back to fresh channels; a received
      end whose dual end q holds becomes a channel of D. *)
  Local Lemma off_recv M M' i y w' e' e1' : soup M = p.2 → mrel R M M' → M' !! i = Some e' →
    tstep e' (LSess (SRecv y w')) e1' → ech y ∉ q.1 →
    ∃ S0 x m U S, Σq !! y = Some (S0, x) ∧ unfoldS S0 = SSeq (SRcv m U) S ∧
      ∀ j Θ2', ole (oadd j (c_take κ)) n → set_map ech (dom Θ2') ## q.1 ∖ ∅ →
        recv_ok (<[y := (S, x⁺)]> Σq) Θ2' → Vrel κ j W1 Θ2' (payload_at m U x) w' →
        Prel κ j W1 (recv_env (<[y := (S, x⁺)]> Σq) Θ2') T
          ((q.1 ∖ ∅) ∪ recv_back (<[y := (S, x⁺)]> Σq) Θ2', soup (<[i := e1']> M')).
  Proof.
    intros HM Hr Hi Hs' Ny. destruct (mrel_lookup_r R M M' i e' Hr Hi) as (e & He & Hc).
    destruct (thread_back R e e' _ e1' Hc Hs') as (a & a' & Ha & Ha' & Har & Ho').
    destruct a'; simpl in Ho'; try done. destruct Ho' as [-> Hw'].
    destruct a as [| | | |b| | | | |]; simpl in Har; try done.
    destruct (act_offer e (ARecv b) (LSess (SRecv b w')) Ha (conj eq_refl Hw')) as [f0 Hf0].
    destruct (subj_iface M i e _ f0 b y HM He Hf0 eq_refl Har Ny) as (Hb & -> & Nb & ND).
    assert (∀ w0 f, tstep e (LSess (SRecv b w0)) f →
      istep (p.1, M) (EvOffer i (SRecv b w0)) (p.1 ∖ ∅, <[i := f]> M)) as Hst.
    { intros w0 f Hff. eapply p_act_session; [done|exact Hff|]. simpl. intros c A B. apply elem_of_singleton in A as ->. done. }
    pose proof HC as (_ & _ & _ & _ & H3 & _).
    destruct (H3 _ _ _ _ _ (erase_p M HM) (Hst _ _ Hf0)) as (S0 & x & m & U & S & Lb & U0 & _).
    exists S0, x, m, U, S. split_and!; [by apply lookupq|done|].
    intros j Θ2' Hj Hdj HokQ HV.
    set (Σ' := <[b := (S, x⁺)]> Σ). set (Σq' := <[h b := (S, x⁺)]> Σq).
    assert (Σq' = sdrop D (kren h Σ')) as EΣq' by (unfold Σq', Σ'; by rewrite kren_sdrop_insert).
    set (X := p.1 ∪ chans_of Σ ∪ echans (soup M) ∪ q.1).
    assert (kren h Σ ##ₘ Θ2') as Hd2.
    { apply map_disjoint_spec. intros o' v1 v2 A B. destruct (kren_lookup_inv _ _ _ _ A) as (u & -> & Au).
      destruct (decide (ech (h u) ∈ D)) as [HD'|HD'].
      - apply (Hdj (ech (h u))); [apply elem_of_map; exists (h u); split; [done|by eapply elem_of_dom_2]|].
        rewrite difference_empty_L, Eq1. by apply elem_of_union_r.
      - apply (proj1 HokQ (h u)); [by eapply elem_of_dom_2|]. unfold Σq'. rewrite dom_insert_L.
        apply elem_of_union_r. apply elem_of_dom. eexists. by apply lookupq. }
    destruct (pull_value κ j W1 (payload_at m U x) h Σ Θ2' w' X (proj1 (rename_level κ j _)) Hk)
      as (h' & w0 & Θ0 & HV0 & HdΣ0 & Ew0 & Hext & Hk' & Hren & Hd' & Hfr & Hcl); [|done|done|].
    { intros c (o & -> & Ho)%elem_of_map. unfold X. apply elem_of_union_l, elem_of_union_l, elem_of_union_r.
      by apply elem_of_chans_of. }
    pose proof (Vrel_exact κ _ _ _ _ _ HV0) as Hf0d.
    assert (∀ o, o ∈ dom Θ0 → ech o ∉ p.1 ∧ ech o ∉ chans_of Σ ∧ ech o ∉ echans (soup M) ∧ ech o ∉ q.1) as Fr.
    { intros o Ho. pose proof (Hfr o Ho) as N. unfold X in N. set_solver. }
    (* the step of p receiving w0 *)
    set (Rs := λ o o', (o ∈ dom Σ ∨ edual o ∈ dom Σ ∨ ech o ∈ p.1 → o' = h o) ∧ (o ∈ dom Θ0 ∨ edual o ∈ dom Θ0 → o' = h' o)).
    assert (crel Rs e e') as Hcs.
    { apply (crel_mono R); [|done]. intros o o' Ho Hoo'. split; [done|]. intros Ho0.
      exfalso. assert (∃ o0, o0 ∈ dom Θ0 ∧ ech o0 = ech o) as (o0 & Ho0' & E0).
      { destruct Ho0 as [?|?]; [by exists o|exists (edual o); by rewrite ech_edual]. }
      apply (proj1 (proj2 (proj2 (Fr o0 Ho0')))). apply elem_of_echans. exists e.
      split; [apply elem_of_soup; eauto|]. apply elem_of_fchans. rewrite E0. eauto. }
    assert (crel Rs w0 w') as Hcw.
    { rewrite <-Ew0. apply crel_emap. intros o Ho. rewrite <-Hf0d in Ho. split; [|by intros _].
      intros Hh. exfalso. destruct (Fr o Ho) as (F1 & F2 & _). destruct Hh as [A|[A|A]].
      - apply F2. by apply elem_of_chans_of.
      - apply F2. rewrite <-ech_edual. by apply elem_of_chans_of.
      - done. }
    destruct (thread_fwd Rs e e' (ARecv b) (LSess (SRecv b w0)) (LSess (SRecv (h b) w')) e1' Hcs Ha) as (f & Hff & Hcf);
      [split; [done|by eapply Vrel_val]|done|done|].
    destruct (H3 _ _ _ _ _ (erase_p M HM) (Hst _ _ Hff)) as (S0' & x' & m' & U' & S'' & Lb' & U0' & AR).
    rewrite Lb in Lb'. injection Lb' as <- <-. rewrite U0 in U0'. injection U0' as <- <- <-.
    (* the pulled back environment *)
    assert (∀ o, o ∈ dom Σ → h' o = h o) as HhΣ.
    { intros o Ho. apply Hext. unfold X. apply elem_of_union_l, elem_of_union_l, elem_of_union_r. by apply elem_of_chans_of. }
    assert (∀ o v, Θ0 !! o = Some v → Θ2' !! h' o = Some v) as L02.
    { intros o v Hv. assert (kren h' (Σ ∪ Θ0) !! h' o = Some v) as A.
      { apply kren_lookup; [done|]. by apply lookup_union_Some_r. }
      rewrite Hren in A. apply lookup_union_Some_raw in A as [A|[_ A]]; [|done]. exfalso.
      destruct (kren_lookup_inv _ _ _ _ A) as (u & Eu & Au). rewrite <-HhΣ in Eu by (by eapply elem_of_dom_2).
      assert (o = u) as -> by (apply (Hk' o u v v); [by apply lookup_union_Some_r|by apply lookup_union_Some_l|done]).
      exact (proj1 (map_disjoint_spec Σ Θ0) HdΣ0 u _ _ Au Hv). }
    assert (∀ y2 v, Θ2' !! y2 = Some v → ∃ o, y2 = h' o ∧ Θ0 !! o = Some v) as L20.
    { intros y2 v Hv. assert ((kren h Σ ∪ Θ2') !! y2 = Some v) as A by (apply lookup_union_Some_r; done).
      rewrite <-Hren in A. destruct (kren_lookup_inv _ _ _ _ A) as (o & -> & Ao).
      apply lookup_union_Some_raw in Ao as [Ao|[_ Ao]]; [|eauto]. exfalso.
      rewrite HhΣ in Hv by (by eapply elem_of_dom_2).
      apply (proj1 (map_disjoint_spec (kren h Σ) Θ2') Hd2 (h o) v v); [apply kren_lookup; [apply Hk|done]|exact Hv]. }
    assert (dcomm h') as Hdh' by (apply Hd'; apply Hd).
    assert (∀ y2, y2 ∈ dom Θ2' → ech y2 ∉ q.1) as Nq2.
    { intros y2 Hy2 Hq. apply (Hdj (ech y2)); [by apply elem_of_map_2|]. by rewrite difference_empty_L. }
    assert (∀ y2, y2 ∈ dom Θ2' → y2 ∉ dom Σq') as NΣq2 by (intros y2 Hy2; by apply (proj1 HokQ)).
    assert (dom Σ' = dom Σ) as DΣ'.
    { unfold Σ'. rewrite dom_insert_L. apply set_eq. intros o. rewrite elem_of_union, elem_of_singleton. naive_solver. }
    assert (∀ o, o ∈ dom Θ0 → o ∉ dom Σ ∧ edual o ∉ dom Σ) as FΣ.
    { intros o Ho. destruct (Fr o Ho) as (_ & F2 & _). split; intros A; apply F2; [|rewrite <-ech_edual]; by apply elem_of_chans_of. }
    assert (∀ o v, Θ0 !! o = Some v → Θ2' !! h' o = Some v) as L02' by done.
    assert (∀ o, o ∈ dom Θ0 → h' o ∈ dom Θ2') as D02 by (intros o [v Hv]%elem_of_dom; eapply elem_of_dom_2, L02; eauto).
    (* recv_ok on the side of p *)
    assert (recv_ok Σ' Θ0) as Hok0.
    { split.
      - intros o Ho. rewrite DΣ'. by apply FΣ.
      - intros o S1 y1 S1' y1' Q1 Q2. assert (o ∈ dom Θ0) as Ho by (by eapply elem_of_dom_2).
        apply lookup_union_Some_raw in Q2 as [Q2|[_ Q2]].
        { exfalso. apply (proj2 (FΣ o Ho)). rewrite <-DΣ'. by eapply elem_of_dom_2. }
        apply (proj2 HokQ (h' o) S1 y1 S1' y1'); [by apply L02|].
        apply lookup_union_Some_raw. right. split.
        + apply not_elem_of_dom. intros A. apply (NΣq2 (edual (h' o))); [|done].
          rewrite <-Hdh'. apply D02. by eapply elem_of_dom_2.
        + rewrite <-Hdh'. by apply L02. }
    assert (set_map ech (dom Θ0) ## p.1) as Hdj0 by (intros c (o & -> & Ho)%elem_of_map; by apply Fr).
    pose proof (AR j Θ0 Hj Hdj0 Hok0 HV0) as P2. unfold erase in P2. simpl in P2.
    (* the new channels of D *)
    set (RB := set_map (λ o, ech (h' o)) (filter (λ o, edual (h' o) ∈ dom Σq') (dom Θ0)) : gset chan).
    assert (∀ c, c ∈ RB ↔ ∃ o, o ∈ dom Θ0 ∧ ech (h' o) = c ∧ edual (h' o) ∈ dom Σq') as LRB.
    { intros c. unfold RB. rewrite elem_of_map. setoid_rewrite elem_of_filter. naive_solver. }
    set (D' := D ∪ RB).
    set (Σ2 := recv_env Σ' Θ0). set (C2 := (p.1 ∖ ∅) ∪ recv_back Σ' Θ0).
    assert (∀ u, u ∈ dom Σ → edual u ∉ dom Θ0) as NΣ0.
    { intros u Hu A. apply (proj2 (FΣ (edual u) A)). by rewrite edual_edual. }
    assert (∀ u v, Σ2 !! u = Some v ↔ Σ' !! u = Some v ∨ (Θ0 !! u = Some v ∧ edual u ∉ dom Θ0)) as LΣ2.
    { intros u v. unfold Σ2. rewrite (recv_env_lookup' _ _ _ _ Hok0). split.
      - intros [[A _]|[A [_ B]]]; [by left|by right].
      - intros [A|[A B]].
        + left. split; [done|]. apply NΣ0. rewrite <-DΣ'. by eapply elem_of_dom_2.
        + right. split_and!; [done| |done]. rewrite DΣ'. by apply FΣ; eapply elem_of_dom_2. }
    assert (∀ u, u ∈ dom Σ2 → u ∈ dom Σ ∨ u ∈ dom Θ0) as DΣ2.
    { intros u [v Hv]%elem_of_dom. apply LΣ2 in Hv as [A|[A _]]; [left; rewrite <-DΣ'|right]; by eapply elem_of_dom_2. }
    assert (∀ c, c ∈ recv_back Σ' Θ0 ↔ ∃ o, o ∈ dom Θ0 ∧ ech o = c ∧ edual o ∈ dom Θ0) as LRb.
    { intros c. rewrite recv_back_elem'. split; [|naive_solver]. intros (o & A & B & [C|C]); [|eauto].
      exfalso. apply (proj2 (FΣ o A)). by rewrite <-DΣ'. }
    assert (∀ u, pheld Σ2 (C2, ∅) u → pheld Σ p u ∨ u ∈ dom Θ0) as Hph2.
    { intros u [Hu|Hu]; [destruct (DΣ2 u Hu); [left; by left|by right]|]. unfold C2 in Hu.
      simpl in Hu. rewrite difference_empty_L in Hu. apply elem_of_union in Hu as [Hu|Hu]; [left; by right|right].
      apply LRb in Hu as (o & Ho & Eo & Ho'). apply ech_eq in Eo as [<-| ->]; [done|done]. }
    assert (∀ u, pheld Σ p u → h' u = h u) as Hhp.
    { intros u [Hu|Hu]; apply Hext; unfold X; [apply elem_of_union_l, elem_of_union_l, elem_of_union_r; by apply elem_of_chans_of|set_solver]. }
    assert (∀ u, u ∈ dom Θ0 → ech (h' u) ∉ q.1) as N0q by (intros u Hu; apply Nq2, D02, Hu).
    assert (∀ u, pheld Σ p u → u ∈ dom Θ0 → False) as Np0.
    { intros u [Hu|Hu] Hu0; [by apply (proj1 (FΣ u Hu0))|by apply (proj1 (Fr u Hu0))]. }
    assert (∀ u o, pheld Σ p u → o ∈ dom Θ0 → ech (h u) = ech (h' o) → u ∈ dom Σ ∧ ech (h u) ∉ D ∧ h u ∈ dom Σq) as Hcross.
    { intros u o Hu Ho E. destruct Hu as [Hu|Hu].
      - assert (ech (h u) ∉ D) as ND'.
        { intros HDu. apply (N0q o Ho). rewrite <-E, Eq1. by apply elem_of_union_r. }
        split_and!; [done|done|]. apply elem_of_dom in Hu as [v Hv]. apply elem_of_dom. exists v. by apply lookupq.
      - exfalso. apply (N0q o Ho). rewrite <-E, Eq1, gch_ech. apply elem_of_union_l. by apply elem_of_map_2. }
    assert (dom Σq ⊆ dom Σq') as DΣq by (unfold Σq'; rewrite dom_insert_L; set_solver).
    assert (fuse_ok h' D' Σ2 (C2, ∅)) as Hok2.
    { destruct Hok as (A1 & A2 & A3 & A4 & A5). split_and!.
      - done.
      - intros u1 u2 B1 B2 E. destruct (Hph2 u1 B1) as [P1|P1], (Hph2 u2 B2) as [P2'|P2'].
        + rewrite !Hhp in E by done. by apply A2.
        + exfalso. rewrite Hhp in E by done. apply (N0q u2 P2'). rewrite <-E.
          destruct (decide (u1 ∈ dom Σ)) as [Hu1|Hu1].
          * exfalso. apply elem_of_dom in Hu1 as [v Hv]. apply elem_of_dom in P2' as [v' Hv'].
            apply (proj1 (map_disjoint_spec (kren h Σ) Θ2') Hd2 (h u1) v v'); [apply kren_lookup; [apply Hk|done]|by rewrite E; apply L02].
          * destruct P1 as [?|P1]; [done|]. rewrite Eq1, gch_ech. apply elem_of_union_l. by apply elem_of_map_2.
        + exfalso. rewrite (Hhp u2) in E by done. apply (N0q u1 P1). rewrite E.
          destruct (decide (u2 ∈ dom Σ)) as [Hu2|Hu2].
          * exfalso. apply elem_of_dom in Hu2 as [v Hv]. apply elem_of_dom in P1 as [v' Hv'].
            apply (proj1 (map_disjoint_spec (kren h Σ) Θ2') Hd2 (h u2) v v'); [apply kren_lookup; [apply Hk|done]|by rewrite <-E; apply L02].
          * destruct P2' as [?|P2']; [done|]. rewrite Eq1, gch_ech. apply elem_of_union_l. by apply elem_of_map_2.
        + apply elem_of_dom in P1 as [v1 V1]. apply elem_of_dom in P2' as [v2 V2].
          apply (Hk' u1 u2 v1 v2); [by apply lookup_union_Some_r|by apply lookup_union_Some_r|done].
      - intros u1 u2 B1 B2 E. destruct (Hph2 u1 B1) as [P1|P1], (Hph2 u2 B2) as [P2'|P2'].
        + rewrite !Hhp in E by done. destruct (A3 u1 u2 P1 P2' E) as [?|?]; [by left|right; rewrite (Hhp u1) by done; by apply elem_of_union_l].
        + right. rewrite (Hhp u1) in E |- * by done. destruct (Hcross u1 u2 P1 P2') as (Hu1 & _ & Hq1); [by rewrite E, ech_edual|].
          apply elem_of_union_r, LRB. exists u2. split_and!; [done|by rewrite E, ech_edual|rewrite E, edual_edual; by apply DΣq].
        + right. rewrite (Hhp u2) in E by done. destruct (Hcross u2 u1 P2' P1) as (Hu2 & _ & Hq2); [by rewrite E, ech_edual|].
          apply elem_of_union_r, LRB. exists u1. split_and!; [done|done|rewrite <-E; by apply DΣq].
        + left. assert (edual u1 ∈ dom Θ0) as Hd1.
          { apply Hcl; [done|]. rewrite <-E. by apply D02. }
          apply elem_of_dom in P2' as [v2 V2]. apply elem_of_dom in Hd1 as [v1 V1].
          apply (Hk' u2 (edual u1) v2 v1); [by apply lookup_union_Some_r|by apply lookup_union_Some_r|by rewrite Hdh'].
      - intros c Hc1 Hc2. simpl in Hc2. apply elem_of_map in Hc2 as (u & -> & Hu).
        unfold C2 in Hu. rewrite difference_empty_L in Hu. apply elem_of_union in Hu as [Hu|Hu].
        + assert (gch h' u = gch h u) as Eg by (unfold gch; rewrite Hhp; [done|by right]).
          rewrite Eg in Hc1. apply elem_of_union in Hc1 as [Hc1|Hc1]; [apply (A4 _ Hc1); by apply elem_of_map_2|].
          apply LRB in Hc1 as (o & Ho & Eo & _). apply (N0q o Ho). rewrite Eo, Eq1. apply elem_of_union_l. by apply elem_of_map_2.
        + apply LRb in Hu as (o & Ho & <- & Ho'). unfold gch in Hc1.
          assert (ech (h' (EPos (ech o))) = ech (h' o)) as Eo.
          { destruct o as [c0|c0]; simpl; [done|]. change (ENeg c0) with (edual (EPos c0)). by rewrite Hdh', ech_edual. }
          rewrite Eo in Hc1. apply elem_of_union in Hc1 as [Hc1|Hc1].
          * apply (N0q o Ho). rewrite Eq1. by apply elem_of_union_r.
          * apply LRB in Hc1 as (o2 & Ho2 & E2 & Hq2). symmetry in E2. apply ech_eq in E2 as [E2|E2].
            -- apply (NΣq2 (edual (h' o2))); [|done]. rewrite E2, <-Hdh'. by apply D02.
            -- apply (NΣq2 (edual (h' o2))); [|done]. rewrite E2, edual_edual. by apply D02.
      - intros o' Ho'. assert (kinj h' Σ2) as K2.
        { apply (kinj_sub h' (Σ ∪ Θ0)); [|done]. intros u Hu. rewrite dom_union_L, elem_of_union. by apply DΣ2. }
        apply elem_of_union in Ho' as [HoD|HoRB].
        + destruct (A5 o' HoD) as (T1 & z & T2 & K3 & K4 & Hs3). exists T1, z, T2.
          assert (∀ o'' v, kren h Σ !! o'' = Some v → ech o'' ∈ D → kren h' Σ2 !! o'' = Some v) as Hmv.
          { intros o'' v A HD'. destruct (kren_lookup_inv _ _ _ _ A) as (u & -> & Au).
            assert (u ≠ b) as Nub by (intros ->; done).
            rewrite <-(Hhp u) by (left; by eapply elem_of_dom_2). apply kren_lookup; [done|]. apply LΣ2. left.
            unfold Σ'. by rewrite lookup_insert_ne. }
          split_and!; [by apply Hmv|apply Hmv; [done|by rewrite ech_edual]|done].
        + apply LRB in HoRB as (o & Ho & Eo & Hq). apply elem_of_dom in Hq as [[S1' y1'] Hq]. pose proof Hq as Hq0.
          rewrite EΣq' in Hq. apply sdrop_lookup in Hq as [Hq NDq]. destruct (kren_lookup_inv _ _ _ _ Hq) as (u & Eu & Lu).
          apply elem_of_dom in Ho as [[S1 y1] Lo] .
          destruct (proj2 HokQ (h' o) S1 y1 S1' y1') as [Ey Hsy]; [by apply L02| |].
          { by apply lookup_union_Some_l. }
          subst y1'.
          assert (u ∈ dom Σ) as Hu by (rewrite <-DΣ'; by eapply elem_of_dom_2).
          assert (Σ2 !! u = Some (S1', y1‾)) as LuΣ2 by (apply LΣ2; by left).
          assert (Σ2 !! o = Some (S1, y1)) as LoΣ2.
          { apply LΣ2. right. split; [done|]. intros A. apply (NΣq2 (edual (h' o))).
            - rewrite <-Hdh'. by apply D02.
            - by eapply elem_of_dom_2. }
          assert (h' u = edual (h' o)) as Ehu by (rewrite Hhp by (by left); by rewrite Eu).
          apply ech_eq in Eo as [-> | ->].
          * exists S1, y1, S1'. split_and!; [by apply kren_lookup|rewrite <-Ehu; by apply kren_lookup|done].
          * exists S1', y1‾, S1. rewrite edual_edual, pt_dual_dual. split_and!; [rewrite <-Ehu; by apply kren_lookup|by apply kren_lookup|by apply sdual_sym]. }
    assert (kinj h' Σ2) as K2.
    { apply (kinj_sub h' (Σ ∪ Θ0)); [|done]. intros u Hu. rewrite dom_union_L, elem_of_union. by apply DΣ2. }
    assert (∀ u, u ∈ dom Σ2 → u ∈ dom Σ ∨ (u ∈ dom Θ0 ∧ edual u ∉ dom Θ0)) as DΣ2'.
    { intros u [v Hv]%elem_of_dom. apply LΣ2 in Hv as [A|[A B]]; [left; rewrite <-DΣ'|right; split]; [by eapply elem_of_dom_2..|done]. }
    assert (∀ u, (u ∈ dom Σ ∨ edual u ∈ dom Σ ∨ ech u ∈ p.1) → h' u = h u) as Hhd.
    { intros u [Hu|[Hu|Hu]]; [apply Hhp; by left| |apply Hhp; by right].
      apply edual_inj. rewrite <-!Hdh', <-Hd. apply Hhp. by left. }
    assert (∀ u, u ∈ dom Σ2 ∨ edual u ∈ dom Σ2 ∨ ech u ∈ C2 →
      (u ∈ dom Σ ∨ edual u ∈ dom Σ ∨ ech u ∈ p.1) ∨ (u ∈ dom Θ0 ∨ edual u ∈ dom Θ0)) as Hhd2.
    { intros u [Hu|[Hu|Hu]].
      - destruct (DΣ2' u Hu) as [?|[? _]]; [left; by left|right; by left].
      - destruct (DΣ2' _ Hu) as [?|[? _]]; [left; right; by left|right; by right].
      - unfold C2 in Hu. rewrite difference_empty_L in Hu. apply elem_of_union in Hu as [Hu|Hu]; [left; right; by right|].
        apply LRb in Hu as (o & Ho & Eo & Ho'). right. apply ech_eq in Eo as [<-| ->]; [by left|by left]. }
    apply (HL j (c_take_lt κ n j Hj) W1 Σ2 T (C2, soup (<[i := f]> M)) _ h' D' _ P2).
    - split_and!.
      + simpl. intros c Zc Zc'. apply chans_of_elem in Zc' as (u & Hu & <-). unfold C2 in Zc.
        rewrite difference_empty_L in Zc. destruct (DΣ2' u Hu) as [Hu'|[Hu' Nu]].
        * apply elem_of_union in Zc as [Zc|Zc].
          -- apply (HC1 (ech u) Zc). by apply elem_of_chans_of.
          -- apply LRb in Zc as (o & Ho & Eo & _). apply (proj1 (proj2 (Fr o Ho))). rewrite Eo. by apply elem_of_chans_of.
        * apply elem_of_union in Zc as [Zc|Zc]; [by apply (proj1 (Fr u Hu'))|].
          apply LRb in Zc as (o & Ho & Eo & Ho'). apply ech_eq in Eo as [<-| ->]; [done|by rewrite edual_edual in Nu].
      + by destruct (proj2 Hs).
      + destruct (proj2 Hs) as [_ Hpf]. intros u Hu Hu'.
        destruct (DΣ2' u Hu) as [A|[A B]], (DΣ2' _ Hu') as [A'|[A' B']].
        * by apply (Hpf u).
        * by apply (NΣ0 u).
        * by apply (proj2 (FΣ u A)).
        * by rewrite edual_edual in B'.
    - split_and!.
      + eapply fuse_ok_proc; [|exact Hok2]. done.
      + simpl. apply set_eq. intros c. rewrite !elem_of_union, difference_empty_L, recv_back_elem'.
        unfold C2. rewrite set_map_union_L, difference_empty_L, elem_of_union, Eq1, elem_of_union.
        assert (∀ x0, x0 ∈ p.1 → gch h' x0 = gch h x0) as Eg.
        { intros x0 Hx0. unfold gch. rewrite Hhp; [done|by right]. }
        assert (set_map (gch h') p.1 = (set_map (gch h) p.1 : gset chan)) as ->.
        { apply set_eq. intros c0. rewrite !elem_of_map. split; intros (x0 & -> & Hx0); exists x0; by rewrite Eg. }
        rewrite (elem_of_map (gch h') (recv_back Σ' Θ0)). unfold D'. rewrite elem_of_union. split.
        * intros [[A|A]|(y2 & Hy2 & <- & B)]; [by left; left|by right; left|].
          apply elem_of_dom in Hy2 as [v Hv]. destruct (L20 _ _ Hv) as (o & -> & Lo).
          destruct B as [B|B].
          -- right. right. apply LRB. exists o. split_and!; [by eapply elem_of_dom_2|done|done].
          -- left. right. exists (ech o). split; [apply (ech_gch h' o Hdh')|].
             apply LRb. exists o. split_and!; [by eapply elem_of_dom_2|done|]. apply Hcl; [by eapply elem_of_dom_2|done].
        * intros [[A|(x0 & -> & Hx0)]|[A|A]]; [by left; left| |by left; right|].
          -- apply LRb in Hx0 as (o & Ho & <- & Ho'). right. exists (h' o). split_and!; [by apply D02| |].
             ++ apply (ech_gch h' o Hdh').
             ++ right. rewrite <-Hdh'. by apply D02.
          -- apply LRB in A as (o & Ho & <- & B). right. exists (h' o). split_and!; [by apply D02|done|by left].
      + apply mcrel_of_mrel. apply mrel_insert.
        * apply (mrel_mono_in R); [|done]. intros e0 o o' (k0 & Hk0) Ho Hoo' Ho2.
          assert (¬ (o ∈ dom Θ0 ∨ edual o ∈ dom Θ0)) as Nf.
          { intros Hfr0. assert (∃ o0, o0 ∈ dom Θ0 ∧ ech o0 = ech o) as (o0 & Ho0 & E0).
            { destruct Hfr0 as [?|?]; [by exists o|exists (edual o); by rewrite ech_edual]. }
            apply (proj1 (proj2 (proj2 (Fr o0 Ho0)))). apply elem_of_echans. exists e0.
            split; [apply elem_of_soup; eauto|]. apply elem_of_fchans. rewrite E0. eauto. }
          destruct (Hhd2 o Ho2) as [A|A]; [|done]. rewrite Hhd by done. by apply Hoo'.
        * apply (crel_mono Rs); [|done]. intros o o' _ [A B] Ho2. destruct (Hhd2 o Ho2) as [C|C]; [|by apply B].
          rewrite Hhd by done. by apply A.
    - assert (kinj h Σ') as KΣ' by (apply (kinj_sub h Σ); [by rewrite DΣ'|apply Hk]).
      assert (∀ o', o' ∈ dom Σq' → o' ∈ dom Θ2' → False) as NQ by (intros o' A B; by apply (NΣq2 o')).
      cut (sdrop D' (kren h' Σ2) = recv_env Σq' Θ2'); [intros ->; apply senv_eqv_refl|].
      apply map_eq. intros o'. apply option_eq. intros v. rewrite sdrop_lookup, (recv_env_lookup' Σq' Θ2' o' v HokQ).
      unfold D'. rewrite elem_of_union. split.
      + intros [L N]. apply Decidable.not_or in N as [N1 N2].
        destruct (kren_lookup_inv _ _ _ _ L) as (u & -> & Lu). apply LΣ2 in Lu as [Lu|[Lu Nu]].
        * assert (u ∈ dom Σ) as Hu by (rewrite <-DΣ'; by eapply elem_of_dom_2).
          rewrite Hhp by (by left). rewrite Hhp in N1, N2 by (by left). left. split.
          -- rewrite EΣq'. apply sdrop_lookup. split; [by apply kren_lookup|done].
          -- intros A. apply elem_of_dom in A as [v' A]. destruct (L20 _ _ A) as (o & Eo & Ao). apply N2. apply LRB.
             exists o. split_and!; [by eapply elem_of_dom_2|by rewrite <-Eo, ech_edual|].
             rewrite <-Eo, edual_edual. apply elem_of_dom. exists v. rewrite EΣq'. apply sdrop_lookup. split; [by apply kren_lookup|done].
        * right. split_and!.
          -- by apply L02.
          -- intros A. apply N2. apply LRB. exists u. split_and!; [by eapply elem_of_dom_2|done|done].
          -- intros A. apply Nu. apply Hcl; [by eapply elem_of_dom_2|done].
      + intros [[L N]|[L [N1 N2]]].
        * pose proof L as L'. rewrite EΣq' in L'. apply sdrop_lookup in L' as [L' ND'].
          destruct (kren_lookup_inv _ _ _ _ L') as (u & -> & Lu).
          assert (u ∈ dom Σ) as Hu by (rewrite <-DΣ'; by eapply elem_of_dom_2).
          split.
          -- rewrite <-(Hhp u) by (by left). apply kren_lookup; [done|]. apply LΣ2. by left.
          -- intros [HD'|HRB]; [done|]. apply LRB in HRB as (o & Ho & Eo & Hq). symmetry in Eo. apply ech_eq in Eo as [Eo|Eo].
             ++ apply (NQ (h u)); [by eapply elem_of_dom_2|]. rewrite <-Eo. by apply D02.
             ++ apply N. rewrite <-Eo. by apply D02.
        * apply elem_of_dom_2 in L as L0. apply elem_of_dom in L0 as [v0 L0]. destruct (L20 _ _ L) as (u & -> & Lu).
          assert (edual u ∉ dom Θ0) as Nu by (intros A; apply N2; rewrite <-Hdh'; by apply D02).
          split.
          -- apply kren_lookup; [done|]. apply LΣ2. by right.
          -- intros [HD'|HRB].
             ++ apply (N0q u); [by eapply elem_of_dom_2|]. rewrite Eq1. by apply elem_of_union_r.
             ++ apply LRB in HRB as (o & Ho & Eo & Hq). symmetry in Eo. apply ech_eq in Eo as [Eo|Eo].
                ** apply N1. by rewrite <-Eo.
                ** apply (NQ (h' u)); [by rewrite Eo, edual_edual in Hq|by eapply elem_of_dom_2].
  Qed.

  Local Lemma at_cost_sync X Σ' T' q' : (∀ jj, ole (oadd jj (c_give κ + c_take κ)) n → Prel κ jj W1 Σ' T' q') →
    at_cost_P n (c_give κ + c_take κ) (Prel κ) X W1 Σ' T' q'.
  Proof.
    intros H. split; [intros Hz; pose proof (c_take_pos κ) as Ht; lia|]. intros _ jj Hjj. by apply H.
  Qed.

  Local Lemma tau_msg M M' i j y w' e' e1' g' g1' : soup M = p.2 → mrel R M M' → i ≠ j →
    M' !! i = Some e' → M' !! j = Some g' →
    tstep e' (LSess (SSend y w')) e1' → tstep g' (LSess (SRecv (edual y) w')) g1' →
    ∃ W', W1 ⊑ W' ∧ at_cost_P n (ev_cost κ (EvSync i j (SSend y w'))) (Prel κ) Xt W' Σq T
      (erase (q.1, <[j := g1']> (<[i := e1']> M'))).
  Proof.
    intros HM Hr Hij Hi Hj Hse Hsg.
    destruct (mrel_lookup_r R M M' i e' Hr Hi) as (e & He & Hce).
    destruct (mrel_lookup_r R M M' j g' Hr Hj) as (g & Hg & Hcg).
    destruct (thread_back R e e' _ e1' Hce Hse) as (a & a' & Ha & Ha' & Har & Ho').
    destruct a'; simpl in Ho'; try done. destruct Ho' as [-> ->].
    destruct a as [| | | | |b w| | | |]; simpl in Har; try done. destruct Har as [Rb Rw].
    destruct (thread_back R g g' _ g1' Hcg Hsg) as (c & c' & Hc & Hc' & Hcr & Hco').
    destruct c'; simpl in Hco'; try done. destruct Hco' as [-> Hw'].
    destruct c as [| | | |b'| | | | |]; simpl in Hcr; try done.
    assert (is_val w) as Hw by (apply is_val_of_true; rewrite (crel_val _ _ _ Rw); by apply is_val_true).
    destruct (thread_fwd R e e' (ASend b w) (LSess (SSend b w)) (LSess (SSend y w')) e1' Hce Ha) as (e1 & Hs1 & Hc1); [done|done|done|].
    destruct (thread_fwd R g g' (ARecv b') (LSess (SRecv b' w)) (LSess (SRecv (edual y) w')) g1' Hcg Hc) as (g1 & Hs2 & Hc2); [done|done|done|].
    pose proof (subj_held M i e _ e1 b HM He Hs1 eq_refl) as Hb.
    pose proof (subj_held M j g _ g1 b' HM Hg Hs2 eq_refl) as Hb'.
    assert (y = h b) as Ey by (apply Rb, hd_of, Hb).
    assert (edual y = h b') as Ey' by (apply Hcr, hd_of, Hb').
    destruct (decide (ech y ∈ D)) as [HD|ND].
    - exists W1. split; [apply wext_refl|]. simpl. apply at_cost_sync. intros jj Hjj.
      assert (ech b ∉ p.1) as Nb by (intros Hp; apply (notD b Hp); by rewrite <-Ey).
      assert (ech b' ∉ p.1) as Nb' by (intros Hp; apply (notD b' Hp); by rewrite <-Ey', ech_edual).
      apply (self_msg M M' i j b b' w e e1 e1' g g1 g1'); try done.
      + by destruct Hb.
      + by destruct Hb'.
      + by rewrite <-Ey.
      + by rewrite <-Ey', <-Ey.
    - assert (b' = edual b) as ->.
      { destruct (hd_inj b' (edual b) (hd_of b' Hb') (proj1 (hd_dual b) (hd_of b Hb))) as [?|HD']; [by rewrite Hd, <-Ey, <-Ey'|done|].
        exfalso. apply ND. by rewrite <-ech_edual, Ey'. }
      apply (tau_by _ _ (p.1, M) (p.1, <[j := g1]> (<[i := e1]> M)) (EvSync i j (SSend b w)) h D).
      + by apply erase_p.
      + by eapply p_act_msg.
      + done.
      + done.
      + apply HC1.
      + done.
      + unfold erase. simpl. apply gfuse_same. apply mrel_insert; [|done]. by apply mrel_insert.
      + apply senv_eqv_refl.
  Qed.

  Local Lemma fuse_ok_subC (C' : gset chan) E' : C' ⊆ p.1 → fuse_ok h D Σ (C', E').
  Proof.
    intros HC'. destruct Hok as (A1 & A2 & A3 & A4 & A5). split_and!; [done| | |set_solver|done].
    - intros o1 o2 H1 H2. apply A2; unfold pheld in *; simpl in *; set_solver.
    - intros o1 o2 H1 H2. apply A3; unfold pheld in *; simpl in *; set_solver.
  Qed.

  Local Lemma gch_minus c : c ∈ p.1 → set_map (gch h) (p.1 ∖ {[c]}) ∪ D = q.1 ∖ {[gch h c]}.
  Proof.
    intros Hc. rewrite Eq1. apply set_eq. intros x. split.
    - intros [(z & -> & Hz)%elem_of_map|HxD]%elem_of_union.
      + apply elem_of_difference. split; [apply elem_of_union_l; apply elem_of_map_2; set_solver|].
        rewrite elem_of_singleton. intros E. assert (z ∈ p.1 ∧ z ≠ c) as [Hz1 Hz2] by set_solver.
        apply Hz2. apply (hd_chan (EPos z) c); [right; right; done|done|]. by rewrite gch_ech.
      + apply elem_of_difference. split; [set_solver|]. rewrite elem_of_singleton. intros ->.
        apply (HDc (gch h c) HxD). by apply elem_of_map_2.
    - intros [Hx Nx]%elem_of_difference. rewrite elem_of_singleton in Nx.
      apply elem_of_union in Hx as [(z & -> & Hz)%elem_of_map|HxD]; [|by apply elem_of_union_r].
      apply elem_of_union_l, elem_of_map. exists z. split; [done|]. set_solver.
  Qed.

  Local Lemma tau_close M M' i j y e' e1' g' g1' : soup M = p.2 → mrel R M M' → i ≠ j →
    M' !! i = Some e' → M' !! j = Some g' →
    tstep e' (LSess (SClose y)) e1' → tstep g' (LSess (SClose (edual y))) g1' → ech y ∈ q.1 →
    ∃ W', W1 ⊑ W' ∧ at_cost_P n (ev_cost κ (EvSync i j (SClose y))) (Prel κ) Xt W' Σq T
      (erase (q.1 ∖ {[ech y]}, <[j := g1']> (<[i := e1']> M'))).
  Proof.
    intros HM Hr Hij Hi Hj Hse Hsg Hy.
    destruct (mrel_lookup_r R M M' i e' Hr Hi) as (e & He & Hce).
    destruct (mrel_lookup_r R M M' j g' Hr Hj) as (g & Hg & Hcg).
    destruct (thread_back R e e' _ e1' Hce Hse) as (a & a' & Ha & Ha' & Har & Ho').
    destruct a'; simpl in Ho'; try done. subst.
    destruct a as [| | | | | |b| | |]; simpl in Har; try done.
    destruct (thread_back R g g' _ g1' Hcg Hsg) as (c & c' & Hc & Hc' & Hcr & Hco').
    destruct c'; simpl in Hco'; try done. subst.
    destruct c as [| | | | | |b'| | |]; simpl in Hcr; try done.
    destruct (thread_fwd R e e' (AClose b) (LSess (SClose b)) (LSess (SClose y)) e1' Hce Ha) as (e1 & Hs1 & Hc1); [done|done|done|].
    destruct (thread_fwd R g g' (AClose b') (LSess (SClose b')) (LSess (SClose (edual y))) g1' Hcg Hc) as (g1 & Hs2 & Hc2); [done|done|done|].
    pose proof (subj_held M i e _ e1 b HM He Hs1 eq_refl) as Hb.
    pose proof (subj_held M j g _ g1 b' HM Hg Hs2 eq_refl) as Hb'.
    assert (y = h b) as Ey by (apply Har, hd_of, Hb).
    assert (edual y = h b') as Ey' by (apply Hcr, hd_of, Hb').
    destruct (decide (ech y ∈ D)) as [HD|ND].
    - exists W1. split; [apply wext_refl|]. simpl. apply at_cost_sync. intros jj Hjj.
      assert (ech b ∉ p.1) as Nb by (intros Hp; apply (notD b Hp); by rewrite <-Ey).
      assert (ech b' ∉ p.1) as Nb' by (intros Hp; apply (notD b' Hp); by rewrite <-Ey', ech_edual).
      rewrite Ey. apply (self_close M M' i j b b' e e1 e1' g g1 g1'); try done.
      + by destruct Hb.
      + by destruct Hb'.
      + by rewrite <-Ey.
      + by rewrite <-Ey', <-Ey.
    - assert (b' = edual b) as ->.
      { destruct (hd_inj b' (edual b) (hd_of b' Hb') (proj1 (hd_dual b) (hd_of b Hb))) as [?|HD']; [by rewrite Hd, <-Ey, <-Ey'|done|].
        exfalso. apply ND. by rewrite <-ech_edual, Ey'. }
      assert (ech y ∈ (set_map (gch h) p.1 : gset chan)) as Hg' by (rewrite Eq1 in Hy; set_solver).
      apply elem_of_map in Hg' as (c0 & Ec0 & Hc0).
      assert (ech b = c0) as <- by (apply (hd_chan b c0 (hd_of b Hb) Hc0); by rewrite <-Ey).
      apply (tau_by _ _ (p.1, M) (p.1 ∖ {[ech b]}, <[j := g1]> (<[i := e1]> M)) (EvSync i j (SClose b)) h D).
      + by apply erase_p.
      + by eapply p_act_close.
      + done.
      + done.
      + simpl. pose proof HC1. set_solver.
      + done.
      + unfold erase. simpl. split_and!.
        * apply fuse_ok_subC. set_solver.
        * rewrite Ec0. symmetry. by apply gch_minus.
        * apply mcrel_of_mrel. apply (mrel_mono_in R); [|apply mrel_insert; [|done]; by apply mrel_insert].
          intros e0 o o' _ _ Hoo' Ho. apply Hoo'. revert Ho. set_solver.
      + apply senv_eqv_refl.
  Qed.

  Local Lemma tau_choice M M' i j y k e' e1' g' g1' : soup M = p.2 → mrel R M M' → i ≠ j →
    M' !! i = Some e' → M' !! j = Some g' →
    tstep e' (LSess (SSel y k)) e1' → tstep g' (LSess (SBra (edual y) k)) g1' →
    ∃ W', W1 ⊑ W' ∧ at_cost_P n (ev_cost κ (EvSync i j (SSel y k))) (Prel κ) Xt W' Σq T
      (erase (q.1, <[j := g1']> (<[i := e1']> M'))).
  Proof.
    intros HM Hr Hij Hi Hj Hse Hsg.
    destruct (mrel_lookup_r R M M' i e' Hr Hi) as (e & He & Hce).
    destruct (mrel_lookup_r R M M' j g' Hr Hj) as (g & Hg & Hcg).
    destruct (thread_back R e e' _ e1' Hce Hse) as (a & a' & Ha & Ha' & Har & Ho').
    destruct a'; simpl in Ho'; try done. destruct Ho' as [-> ->].
    destruct a as [| | | | | | | |b k0|]; simpl in Har; try done. destruct Har as [Rb ->].
    destruct (thread_back R g g' _ g1' Hcg Hsg) as (c & c' & Hc & Hc' & Hcr & Hco').
    destruct c'; simpl in Hco'; try done. subst.
    destruct c as [| | | | | | | | |b']; simpl in Hcr; try done.
    destruct (thread_fwd R e e' (ASel b k) (LSess (SSel b k)) (LSess (SSel y k)) e1' Hce Ha) as (e1 & Hs1 & Hc1); [done|done|done|].
    destruct (thread_fwd R g g' (ABra b') (LSess (SBra b' k)) (LSess (SBra (edual y) k)) g1' Hcg Hc) as (g1 & Hs2 & Hc2); [done|done|done|].
    pose proof (subj_held M i e _ e1 b HM He Hs1 eq_refl) as Hb.
    pose proof (subj_held M j g _ g1 b' HM Hg Hs2 eq_refl) as Hb'.
    assert (y = h b) as Ey by (apply Rb, hd_of, Hb).
    assert (edual y = h b') as Ey' by (apply Hcr, hd_of, Hb').
    destruct (decide (ech y ∈ D)) as [HD|ND].
    - exists W1. split; [apply wext_refl|]. simpl. apply at_cost_sync. intros jj Hjj.
      apply (self_choice M M' i j b b' k e e1 e1' g g1 g1'); try done.
      + by destruct Hb; [exfalso; apply (notD b); [|by rewrite <-Ey]|].
      + by destruct Hb'; [exfalso; apply (notD b'); [|by rewrite <-Ey', ech_edual]|].
      + by rewrite <-Ey.
      + by rewrite <-Ey', <-Ey.
    - assert (b' = edual b) as ->.
      { destruct (hd_inj b' (edual b) (hd_of b' Hb') (proj1 (hd_dual b) (hd_of b Hb))) as [?|HD']; [by rewrite Hd, <-Ey, <-Ey'|done|].
        exfalso. apply ND. by rewrite <-ech_edual, Ey'. }
      apply (tau_by _ _ (p.1, M) (p.1, <[j := g1]> (<[i := e1]> M)) (EvSync i j (SSel b k)) h D).
      + by apply erase_p.
      + by eapply p_act_choice.
      + done.
      + done.
      + apply HC1.
      + done.
      + unfold erase. simpl. apply gfuse_same. apply mrel_insert; [|done]. by apply mrel_insert.
      + apply senv_eqv_refl.
  Qed.

  Local Lemma lift' C0 M0 : erase (C0, M0) = q → C0 = q.1 ∧ ∃ M, soup M = p.2 ∧ mrel R M M0.
  Proof.
    intros Hq. split; [by rewrite <-Hq|]. destruct (lift (C0, M0) Hq) as (M & HM & Hr).
    exists M. split; [|done]. by rewrite <-HM.
  Qed.

  Local Lemma tau_clause qc ev qc' : erase qc = q → istep qc ev qc' → ev_tau ev →
    (erase qc').1 ## chans_of Σq →
    ∃ W', W1 ⊑ W' ∧ at_cost_P n (ev_cost κ ev) (Prel κ) Xt W' Σq T (erase qc').
  Proof.
    intros Hq Hst Hτ Hpre.
    destruct Hst as [C0 M0 i α e e' Hi Hs0 Hα|C0 M0 i e c e' Hi Hs0 Hc HcE|C0 M0 i j e v e' Hi Hs0 Hj
      |C0 M0 i j o v e e' f f' Hij Hi Hj He Hf0|C0 M0 i j o e e' f f' Hij Hi Hj He Hf0 HCC0
      |C0 M0 i j o b e e' f f' Hij Hi Hj He Hf0|C0 M0 i e o1 o2 e' Hi Hs0 HCC0|C0 M0 i e σ e' Hi Hs0 HCC0];
      try (by unfold ev_tau in Hτ); destruct (lift' C0 M0 Hq) as (-> & M & HM & Hr).
    - by eapply tau_beta.
    - eapply tau_new; [done|done|done|done|done|done|]. done.
    - by eapply tau_spawn.
    - by eapply tau_msg.
    - by eapply tau_close.
    - by eapply tau_choice.
    - by eapply tau_link.
  Qed.

  (** ** Stability and readiness

      A τ step of p yields one of q, and so does an offer of p on an end
      whose image is no end of a channel of D. *)

  Local Lemma HCq' o : ech o ∈ p.1 → ech (h o) ∈ (set_map (gch h) p.1 : gset chan).
  Proof. intros Ho. rewrite gch_ech. by apply elem_of_map_2. Qed.

  Local Lemma fwd_act M M' i e : mrel R M M' → M !! i = Some e →
    ∀ a, act e = Some a → ∃ e' a', M' !! i = Some e' ∧ crel R e e' ∧ act e' = Some a' ∧ arel R a a'.
  Proof.
    intros Hr He a Ha. destruct (mrel_lookup R M M' i e Hr He) as (e' & He' & Hc).
    destruct (crel_act R e e' Hc) as [[E _]|(a0 & a' & E & Ha' & Har)]; [congruence|].
    rewrite Ha in E. injection E as <-. eauto 10.
  Qed.

  Local Lemma fwd_tau M M' ev pc' : soup M = p.2 → mrel R M M' → istep (p.1, M) ev pc' → ev_tau ev →
    ∃ ev' qc', istep (q.1, M') ev' qc' ∧ ev_tau ev'.
  Proof.
    intros HM Hr Hst Hτ. remember (p.1, M) as pc0 eqn:Epc.
    destruct Hst as [C0 M0 i α e e1 Hi Hs0 Hα|C0 M0 i e c e1 Hi Hs0 Hc0 HcE|C0 M0 i j e v e1 Hi Hs0 Hj
      |C0 M0 i j o v e e1 g g1 Hij Hi Hj He0 Hg0|C0 M0 i j o e e1 g g1 Hij Hi Hj He0 Hg0 HCo
      |C0 M0 i j o k e e1 g g1 Hij Hi Hj He0 Hg0|C0 M0 i e o1 o2 e1 Hi Hs0 HCo|C0 M0 i e σ e1 Hi Hs0 HCo];
      try (by unfold ev_tau in Hτ); injection Epc as -> ->.
    - destruct (act_step _ _ _ Hs0) as (a & Ha & Hoa). destruct (fwd_act M M' i e Hr Hi a Ha) as (e' & a' & Hi' & _ & Ha' & Har).
      destruct (act_offer e' a' α Ha') as [e1' He1']; [destruct Hα as [-> | ->]; destruct a; simpl in Hoa; try done; destruct a'; simpl in Har; done|].
      eexists _, _. split; [by eapply p_act_beta|done].
    - destruct (act_step _ _ _ Hs0) as (a & Ha & Hoa). apply offers_new in Hoa as ->.
      destruct (fwd_act M M' i e Hr Hi ANew Ha) as (e' & a' & Hi' & _ & Ha' & Har). destruct a'; simpl in Har; try done.
      destruct (exist_fresh (q.1 ∪ echans (soup M'))) as [c' Hc'].
      destruct (act_offer e' ANew (LNew c') Ha' I) as [e1' He1'].
      eexists _, _. split; [eapply p_act_new; [done|done|set_solver|set_solver]|done].
    - destruct (act_step _ _ _ Hs0) as (a & Ha & Hoa). destruct a; simpl in Hoa; try done. subst.
      destruct (fwd_act M M' i e Hr Hi _ Ha) as (e' & a' & Hi' & _ & Ha' & Har). destruct a'; simpl in Har; try done.
      destruct (act_offer e' (ASpawn v0) (LSpawn v0) Ha' eq_refl) as [e1' He1'].
      eexists _, _. split; [eapply p_act_spawn; [done|done|by apply (mrel_none R M M' j Hr)]|done].
    - pose proof (subj_held M i e _ e1 o HM Hi He0 eq_refl) as Ho.
      pose proof (subj_held M j g _ g1 (edual o) HM Hj Hg0 eq_refl) as Ho'.
      destruct (act_step _ _ _ He0) as (a & Ha & Hoa). apply offers_send in Hoa as ->.
      destruct (act_step _ _ _ Hg0) as (c & Hc1 & Hoc). apply offers_recv in Hoc as ->.
      destruct (fwd_act M M' i e Hr Hi _ Ha) as (e' & a' & Hi' & _ & Ha' & Har). destruct a'; simpl in Har; try done.
      destruct (fwd_act M M' j g Hr Hj _ Hc1) as (g' & c' & Hj' & _ & Hc' & Hcr). destruct c'; simpl in Hcr; try done.
      destruct Har as [Ro Rv]. rename o0 into y, v0 into v'.
      assert (y = h o) as -> by (apply Ro, hd_of, Ho).
      assert (o1 = edual (h o)) as -> by (rewrite <-Hd; apply Hcr, hd_of, Ho').
      assert (is_val v') as Hv' by (eapply act_send_val; exact Ha').
      destruct (act_offer e' _ (LSess (SSend (h o) v')) Ha' (conj eq_refl eq_refl)) as [e1' He1'].
      destruct (act_offer g' _ (LSess (SRecv (edual (h o)) v')) Hc' (conj eq_refl Hv')) as [g1' Hg1'].
      eexists _, _. split; [by eapply p_act_msg|done].
    - pose proof (subj_held M i e _ e1 o HM Hi He0 eq_refl) as Ho.
      pose proof (subj_held M j g _ g1 (edual o) HM Hj Hg0 eq_refl) as Ho'.
      destruct (act_step _ _ _ He0) as (a & Ha & Hoa). apply offers_close in Hoa as ->.
      destruct (act_step _ _ _ Hg0) as (c & Hc1 & Hoc). apply offers_close in Hoc as ->.
      destruct (fwd_act M M' i e Hr Hi _ Ha) as (e' & a' & Hi' & _ & Ha' & Har). destruct a'; simpl in Har; try done.
      destruct (fwd_act M M' j g Hr Hj _ Hc1) as (g' & c' & Hj' & _ & Hc' & Hcr). destruct c'; simpl in Hcr; try done.
      rename o0 into y.
      assert (y = h o) as -> by (apply Har, hd_of, Ho).
      assert (o1 = edual (h o)) as -> by (rewrite <-Hd; apply Hcr, hd_of, Ho').
      destruct (act_offer e' _ (LSess (SClose (h o))) Ha' eq_refl) as [e1' He1'].
      destruct (act_offer g' _ (LSess (SClose (edual (h o)))) Hc' eq_refl) as [g1' Hg1'].
      eexists _, _. split; [eapply p_act_close; try done|done]. rewrite Eq1. apply elem_of_union_l. by apply HCq'.
    - pose proof (subj_held M i e _ e1 o HM Hi He0 eq_refl) as Ho.
      pose proof (subj_held M j g _ g1 (edual o) HM Hj Hg0 eq_refl) as Ho'.
      destruct (act_step _ _ _ He0) as (a & Ha & Hoa). apply offers_sel in Hoa as ->.
      destruct (act_step _ _ _ Hg0) as (c & Hc1 & Hoc). apply offers_bra in Hoc as ->.
      destruct (fwd_act M M' i e Hr Hi _ Ha) as (e' & a' & Hi' & _ & Ha' & Har). destruct a'; simpl in Har; try done.
      destruct (fwd_act M M' j g Hr Hj _ Hc1) as (g' & c' & Hj' & _ & Hc' & Hcr). destruct c'; simpl in Hcr; try done.
      destruct Har as [Ro <-]. rename o0 into y.
      assert (y = h o) as -> by (apply Ro, hd_of, Ho).
      assert (o1 = edual (h o)) as -> by (rewrite <-Hd; apply Hcr, hd_of, Ho').
      destruct (act_offer e' _ (LSess (SSel (h o) k)) Ha' (conj eq_refl eq_refl)) as [e1' He1'].
      destruct (act_offer g' _ (LSess (SBra (edual (h o)) k)) Hc' eq_refl) as [g1' Hg1'].
      eexists _, _. split; [by eapply p_act_choice|done].
    - destruct (act_step _ _ _ Hs0) as (a & Ha & Hoa). destruct (offers_link _ _ Hoa) as (b1 & b2 & -> & Eb).
      destruct (fwd_act M M' i e Hr Hi _ Ha) as (e' & a' & Hi' & _ & Ha' & Har).
      destruct a' as [| | |v0|o0|o0 v0|o0|z1 z2|o0 k0|o0]; simpl in Har; try done.
      destruct Har as [R1 R2].
      assert (∃ z, (z = z1 ∨ z = z2) ∧ ech z ∈ q.1) as (z & Ez & Hz).
      { assert (o1 = b1 ∨ o1 = b2) as [<-|<-] by (assert (o1 ∈ ({[b1]} ∪ {[b2]} : gset cend)) by (rewrite <-Eb; set_solver); set_solver).
        - exists z1. split; [by left|]. rewrite (R1 (or_intror (or_intror HCo))). rewrite Eq1. apply elem_of_union_l. by apply HCq'.
        - exists z2. split; [by right|]. rewrite (R2 (or_intror (or_intror HCo))). rewrite Eq1. apply elem_of_union_l. by apply HCq'. }
      destruct (act_offer e' _ (LSess (SLink ({[z1]} ∪ {[z2]}))) Ha' eq_refl) as [e1' He1'].
      destruct Ez as [->| ->].
      + eexists _, _. split; [by eapply p_act_link|done].
      + eexists _, _. split; [eapply p_act_link; [done|by rewrite (comm_L (∪))|done]|done].
  Qed.

  Local Lemma eraseq M' : soup M' = q.2 → erase (q.1, M') = q.
  Proof. intros HM. unfold erase. simpl. rewrite HM. by destruct q. Qed.

  Local Lemma not_stable_q M' ev qc' : soup M' = q.2 → istep (q.1, M') ev qc' → ev_tau ev → ¬ stable_p q.
  Proof. intros HM Hst Hτ Hstb. apply (Hstb (erase qc')). exists (q.1, M'), ev, qc'. split_and!; [by apply eraseq|done|done|exact Hτ]. Qed.

  (** An offer of p on an end of Σ whose image is no end of D is an offer
      of q, unless q takes a τ step. *)
  Local Lemma fwd_off M M' i σ pc' o : soup M = p.2 → soup M' = q.2 → mrel R M M' →
    istep (p.1, M) (EvOffer i σ) pc' → o ∈ sends σ → o ∈ dom Σ → ech (h o) ∉ D →
    offered_p Σq q (h o) ∨ ¬ stable_p q.
  Proof.
    intros HM HM' Hr Hst Ho HoΣ ND'. remember (p.1, M) as pc0 eqn:Epc. remember (EvOffer i σ) as ev eqn:Eev.
    destruct Hst; try discriminate. injection Epc as -> ->. injection Eev as -> ->.
    rename e into e0, e' into e1, H into Hi, H0 into Hs0, H1 into Hsj.
    assert (ech (h o) ∉ q.1) as Nq.
    { rewrite Eq1. intros [A|A]%elem_of_union; [|done]. apply elem_of_map in A as (c & Ec & Hc0).
      apply (HC1 c Hc0). rewrite <-(hd_chan o c (or_introl HoΣ) Hc0 Ec). by apply elem_of_chans_of. }
    assert (h o ∈ dom Σq) as HoΣq by (apply elem_of_dom in HoΣ as [v Hv]; apply elem_of_dom; exists v; by apply lookupq).
    destruct (act_step _ _ _ Hs0) as (a & Ha & Hoa). destruct (fwd_act M M' i e0 Hr Hi a Ha) as (e' & a' & Hi' & _ & Ha' & Har).
    destruct (act_offer e' a' (alabel a') Ha' (offers_alabel a')) as [e1' He1'].
    assert (∀ σ', alabel a' = LSess σ' → h o ∈ sends σ' → subjs σ' ## q.1 → offered_p Σq q (h o)) as Hoff.
    { intros σ' Ea Hos Hsj'. split; [done|]. exists σ', (erase (q.1 ∖ sentc σ', <[i := e1']> M')). split; [|done].
      exists (q.1, M'), (EvOffer i σ'), (q.1 ∖ sentc σ', <[i := e1']> M'). split_and!; [by apply eraseq| |done|done].
      eapply p_act_session; [done|by rewrite <-Ea|done]. }
    destruct σ as [o1 w|o1 w|o1|o1 k|o1 k|os]; simpl in Ho.
    1-5: apply elem_of_singleton in Ho as ->;
      assert (∃ y σ', R o1 y ∧ alabel a' = LSess σ' ∧ sends σ' = {[y]} ∧ subjs σ' = {[ech y]}) as (y & σ' & Ry & Ea & Es & Esj)
        by (destruct a; simpl in Hoa; try done; destruct a'; simpl in Har; try done;
            repeat (match goal with H : _ ∧ _ |- _ => destruct H end); subst; eexists _, _;
            split_and!; [eassumption|reflexivity|reflexivity|reflexivity]);
      left; rewrite (Ry (hd_of o1 (or_intror HoΣ))) in Es, Esj;
      apply (Hoff σ' Ea); [rewrite Es; set_solver|rewrite Esj; set_solver].
    destruct (offers_link _ _ Hoa) as (b1 & b2 & -> & Eb).
    destruct a' as [| | |v0|o0|o0 v0|o0|z1 z2|o0 k0|o0]; simpl in Har; try done. destruct Har as [R1 R2].
    assert (o = b1 ∨ o = b2) as Ob by (rewrite Eb in Ho; set_solver).
    assert (b1 ∈ dom Σ ∨ ech b1 ∈ p.1 → z1 = h b1) as E1 by (intros [?|?]; apply R1; [left|right; right]; done).
    assert (b2 ∈ dom Σ ∨ ech b2 ∈ p.1 → z2 = h b2) as E2 by (intros [?|?]; apply R2; [left|right; right]; done).
    destruct (decide (ech z1 ∈ q.1)) as [Q1|Q1].
    { right. eapply (not_stable_q M' (EvSolo i (LSess (SLink ({[z1]} ∪ {[z2]}))) (PickLink z1 z2))); [done| |done].
      by eapply p_act_link. }
    destruct (decide (ech z2 ∈ q.1)) as [Q2|Q2].
    { right. eapply (not_stable_q M' (EvSolo i (LSess (SLink ({[z2]} ∪ {[z1]}))) (PickLink z2 z1))); [done| |done].
      eapply p_act_link; [done|by rewrite (comm_L (∪) {[z2]})|done]. }
    left. apply (Hoff (SLink ({[z1]} ∪ {[z2]}))); [done| |simpl; rewrite set_map_union_L, !set_map_singleton_L; set_solver].
    simpl. destruct Ob as [->| ->]; [rewrite <-E1 by (by left)|rewrite <-E2 by (by left)]; set_solver.
  Qed.

  Local Lemma offers_sends' a σ σ' : offers a (LSess σ) → offers a (LSess σ') → sends σ = sends σ'.
  Proof. destruct a, σ, σ'; simpl; intros; destruct_and?; subst; done. Qed.

  Local Lemma offered_lift M o : soup M = p.2 → offered_p Σ p o →
    ∃ i σ pc', istep (p.1, M) (EvOffer i σ) pc' ∧ o ∈ sends σ.
  Proof.
    intros HM [_ (σ & p' & Hps & Ho)]. rewrite <-(erase_p M HM) in Hps.
    destruct (pstep_lift _ _ _ Hps) as (ev & pc' & Hst & Hl & _). destruct ev; try discriminate.
    injection Hl as ->. eauto.
  Qed.

  Local Lemma offer_thread M i σ pc' : istep (p.1, M) (EvOffer i σ) pc' →
    ∃ e e1, M !! i = Some e ∧ tstep e (LSess σ) e1.
  Proof.
    intros Hst. remember (p.1, M) as pc0 eqn:Epc. remember (EvOffer i σ) as ev eqn:Eev.
    destruct Hst; try discriminate. injection Epc as -> ->. injection Eev as -> ->. eauto.
  Qed.

  (** A link of p on an end whose image lies on a channel of q is a τ step of q. *)
  Local Lemma link_q M M' i e e1 os o : soup M' = q.2 → mrel R M M' → M !! i = Some e →
    tstep e (LSess (SLink os)) e1 → o ∈ os → o ∈ dom Σ → ech (h o) ∈ q.1 → ¬ stable_p q.
  Proof.
    intros HM' Hr Hi Hs0 Ho HoΣ Hq. destruct (act_step _ _ _ Hs0) as (a & Ha & Hoa).
    destruct (offers_link _ _ Hoa) as (b1 & b2 & -> & Eb).
    destruct (fwd_act M M' i e Hr Hi _ Ha) as (e' & a' & Hi' & _ & Ha' & Har).
    destruct a' as [| | |v0|o0|o0 v0|o0|z1 z2|o0 k0|o0]; simpl in Har; try done. destruct Har as [R1 R2].
    destruct (act_offer e' _ (LSess (SLink ({[z1]} ∪ {[z2]}))) Ha' eq_refl) as [e1' He1'].
    assert (o = b1 ∨ o = b2) as [->| ->] by (rewrite Eb in Ho; set_solver).
    - rewrite <-(R1 (or_introl HoΣ)) in Hq. eapply (not_stable_q M' (EvSolo i _ (PickLink z1 z2))); [done| |done].
      by eapply p_act_link.
    - rewrite <-(R2 (or_introl HoΣ)) in Hq. eapply (not_stable_q M' (EvSolo i _ (PickLink z2 z1))); [done| |done].
      eapply p_act_link; [done|by rewrite (comm_L (∪) {[z2]})|done].
  Qed.

  (** Offers on the two ends of a channel of D meet in q. *)
  Local Lemma fwd_sync M M' i j σ1 σ2 pc1 pc2 o o' : soup M = p.2 → soup M' = q.2 → mrel R M M' →
    istep (p.1, M) (EvOffer i σ1) pc1 → istep (p.1, M) (EvOffer j σ2) pc2 →
    o ∈ sends σ1 → o' ∈ sends σ2 → o ∈ dom Σ → o' ∈ dom Σ → ech (h o) ∈ D → h o' = edual (h o) → ¬ stable_p q.
  Proof.
    intros HM HM' Hr S1 S2 Ho1 Ho2 HoΣ Ho'Σ HD Eo'.
    assert (ech (h o) ∈ q.1) as Hq by (rewrite Eq1; by apply elem_of_union_r).
    destruct (offer_thread M i σ1 pc1 S1) as (e & e1 & Hi & He).
    destruct (offer_thread M j σ2 pc2 S2) as (g & g1 & Hj & Hg).
    destruct (sends_ssubj _ _ Ho1) as [[os ->]|E1]; [by eapply (link_q M M' i e e1 os o)|].
    destruct (sends_ssubj _ _ Ho2) as [[os ->]|E2].
    { eapply (link_q M M' j g g1 os o'); try done. by rewrite Eo', ech_edual. }
    pose proof HC as (_ & _ & HS).
    destruct (Psteps_head κ n _ _ _ _ _ _ _ _ HS (p.1, M) i σ1 pc1 o (erase_p M HM) S1 E1) as (S0 & x & L1 & D1).
    destruct (Psteps_head κ n _ _ _ _ _ _ _ _ HS (p.1, M) j σ2 pc2 o' (erase_p M HM) S2 E2) as (S0' & x' & L2 & D2).
    destruct (Hdp (h o) HD) as (T1 & z & T2 & K3 & K4 & Hs3).
    apply (kren_lookup_held h Σ o) in K3; [|apply Hk|done]. rewrite L1 in K3. injection K3 as <- <-.
    rewrite <-Eo' in K4. apply (kren_lookup_held h Σ o') in K4; [|apply Hk|done]. rewrite L2 in K4. injection K4 as <- ->.
    assert (sync σ1 σ2) as Hsy by (eapply hd_ok_sync; [exact Hs3|exact D1|exact D2|congruence|congruence]).
    assert (i ≠ j) as Hij.
    { intros ->. rewrite Hi in Hj. injection Hj as <-. destruct (act_step _ _ _ He) as (a & Ha & Hoa).
      destruct (act_step _ _ _ Hg) as (a2 & Ha2 & Hoa2). rewrite Ha in Ha2. injection Ha2 as <-.
      pose proof (offers_sends' a σ1 σ2 Hoa Hoa2) as Es.
      destruct σ1, σ2; simpl in E1, E2, Es; try discriminate; injection E1 as ->; injection E2 as ->;
        (assert (o = o') as <- by set_solver); apply (edual_ne (h o)); by rewrite <-Eo'. }
    destruct (act_step _ _ _ He) as (a & Ha & Hoa). destruct (act_step _ _ _ Hg) as (c & Hc1 & Hoc).
    destruct (fwd_act M M' i e Hr Hi _ Ha) as (e' & a' & Hi' & _ & Ha' & Har).
    destruct (fwd_act M M' j g Hr Hj _ Hc1) as (g' & c' & Hj' & _ & Hc' & Hcr).
    assert (hd o ∧ hd o') as [Hho Hho'] by (split; left; done).
    destruct σ1 as [o1 w|o1 w|o1|o1 k|o1 k|], σ2 as [o2 w2|o2 w2|o2|o2 k2|o2 k2|]; simpl in Hsy; try done;
      simpl in E1, E2; injection E1 as ->; injection E2 as ->.
    - apply offers_send in Hoa as ->. apply offers_recv in Hoc as ->.
      destruct a' as [| | |v0|o0|y v'|o0|z1 z2|o0 k0|o0]; simpl in Har; try done. destruct Har as [Ry _].
      destruct c' as [| | |v0|y'|o0 v0|o0|z1 z2|o0 k0|o0]; simpl in Hcr; try done.
      rewrite (Ry Hho) in Ha'. rewrite (Hcr Hho'), Eo' in Hc'.
      assert (is_val v') as Hv' by (eapply act_send_val; exact Ha').
      destruct (act_offer e' _ (LSess (SSend (h o) v')) Ha' (conj eq_refl eq_refl)) as [e1' He1'].
      destruct (act_offer g' _ (LSess (SRecv (edual (h o)) v')) Hc' (conj eq_refl Hv')) as [g1' Hg1'].
      eapply (not_stable_q M' (EvSync i j (SSend (h o) v'))); [done| |done]. by eapply p_act_msg.
    - apply offers_recv in Hoa as ->. apply offers_send in Hoc as ->.
      destruct a' as [| | |v0|y|o0 v0|o0|z1 z2|o0 k0|o0]; simpl in Har; try done.
      destruct c' as [| | |v0|o0|y' v'|o0|z1 z2|o0 k0|o0]; simpl in Hcr; try done. destruct Hcr as [Ry' _].
      rewrite (Har Hho) in Ha'. rewrite (Ry' Hho'), Eo' in Hc'.
      assert (is_val v') as Hv' by (eapply act_send_val; exact Hc').
      destruct (act_offer g' _ (LSess (SSend (edual (h o)) v')) Hc' (conj eq_refl eq_refl)) as [g1' Hg1'].
      destruct (act_offer e' _ (LSess (SRecv (h o) v')) Ha' (conj eq_refl Hv')) as [e1' He1'].
      eapply (not_stable_q M' (EvSync j i (SSend (edual (h o)) v'))); [done| |done].
      eapply p_act_msg; [done|done|done|done|]. by rewrite edual_edual.
    - apply offers_close in Hoa as ->. apply offers_close in Hoc as ->.
      destruct a' as [| | |v0|o0|o0 v0|y|z1 z2|o0 k0|o0]; simpl in Har; try done.
      destruct c' as [| | |v0|o0|o0 v0|y'|z1 z2|o0 k0|o0]; simpl in Hcr; try done.
      rewrite (Har Hho) in Ha'. rewrite (Hcr Hho'), Eo' in Hc'.
      destruct (act_offer e' _ (LSess (SClose (h o))) Ha' eq_refl) as [e1' He1'].
      destruct (act_offer g' _ (LSess (SClose (edual (h o)))) Hc' eq_refl) as [g1' Hg1'].
      eapply (not_stable_q M' (EvSync i j (SClose (h o)))); [done| |done]. by eapply p_act_close.
    - apply offers_sel in Hoa as ->. apply offers_bra in Hoc as ->.
      destruct a' as [| | |v0|o0|o0 v0|o0|z1 z2|y k'|o0]; simpl in Har; try done. destruct Har as [Ry <-].
      destruct c' as [| | |v0|o0|o0 v0|o0|z1 z2|o0 k0|y']; simpl in Hcr; try done.
      rewrite (Ry Hho) in Ha'. rewrite (Hcr Hho'), Eo' in Hc'.
      destruct (act_offer e' _ (LSess (SSel (h o) k)) Ha' (conj eq_refl eq_refl)) as [e1' He1'].
      destruct (act_offer g' _ (LSess (SBra (edual (h o)) k)) Hc' eq_refl) as [g1' Hg1'].
      eapply (not_stable_q M' (EvSync i j (SSel (h o) k))); [done| |done]. by eapply p_act_choice.
    - apply offers_bra in Hoa as ->. apply offers_sel in Hoc as ->.
      destruct a' as [| | |v0|o0|o0 v0|o0|z1 z2|o0 k0|y]; simpl in Har; try done.
      destruct c' as [| | |v0|o0|o0 v0|o0|z1 z2|y' k'|o0]; simpl in Hcr; try done. destruct Hcr as [Ry' <-].
      rewrite (Har Hho) in Ha'. rewrite (Ry' Hho'), Eo' in Hc'.
      destruct (act_offer g' _ (LSess (SSel (edual (h o)) k2)) Hc' (conj eq_refl eq_refl)) as [g1' Hg1'].
      destruct (act_offer e' _ (LSess (SBra (h o) k2)) Ha' eq_refl) as [e1' He1'].
      eapply (not_stable_q M' (EvSync j i (SSel (edual (h o)) k2))); [done| |done].
      eapply p_act_choice; [done|done|done|done|]. by rewrite edual_edual.
  Qed.

  Local Lemma chain M M' : soup M = p.2 → soup M' = q.2 → mrel R M M' →
    above_offered W1 Σ (offered_p Σ p) → stable_p q →
    ∀ y, Acc (λ a b, a ∈ pts Σ ∧ W1 ⊢ a ≺ b) y → ∀ o S0, Σ !! o = Some (S0, y) → offered_p Σ p o → ech (h o) ∈ D →
    ∃ o2 S2 y2, Σ !! o2 = Some (S2, y2) ∧ offered_p Σ p o2 ∧ ech (h o2) ∉ D ∧ W1 ⊢ y2 ≺ y.
  Proof.
    intros HM HM' Hr Hab Hstq y Hacc. induction Hacc as [y _ IH]. intros o S0 Lo Hoff HD.
    destruct (Hdp (h o) HD) as (T1 & z & T2 & K3 & K4 & Hs3).
    apply (kren_lookup_held h Σ o) in K3; [|apply Hk|by eapply elem_of_dom_2]. rewrite Lo in K3. injection K3 as <- <-.
    destruct (kren_lookup_inv _ _ _ _ K4) as (o' & Eo' & Lo').
    assert (¬ offered_p Σ p o') as Noff.
    { intros Hoff'. destruct (offered_lift M o HM Hoff) as (i & σ1 & pc1 & S1 & Ho1).
      destruct (offered_lift M o' HM Hoff') as (j & σ2 & pc2 & S2 & Ho2).
      apply (fwd_sync M M' i j σ1 σ2 pc1 pc2 o o' HM HM' Hr S1 S2 Ho1 Ho2); try done;
        [by eapply elem_of_dom_2|by eapply elem_of_dom_2]. }
    destruct (Hab o' T2 y‾ Lo' Noff) as (o2 & S2 & y2 & Hoff2 & Lo2 & Hlt). rewrite pt_dual_dual in Hlt.
    destruct (decide (ech (h o2) ∈ D)) as [HD2|HD2]; [|by exists o2, S2, y2].
    destruct (IH y2 (conj (pts_elem _ _ _ _ Lo2) Hlt) o2 S2 Lo2 Hoff2 HD2) as (o3 & S3 & y3 & Lo3 & Hoff3 & HD3 & Hlt3).
    exists o3, S3, y3. split_and!; [done|done|done|]. by eapply w_lt_trans.
  Qed.

  (** An offered end of p has an offered end of p below or at its point
      whose image is no end of D. *)
  Local Lemma chain' M M' o S0 y : soup M = p.2 → soup M' = q.2 → mrel R M M' →
    above_offered W1 Σ (offered_p Σ p) → stable_p q → Σ !! o = Some (S0, y) → offered_p Σ p o →
    ∃ o2 S2 y2, Σ !! o2 = Some (S2, y2) ∧ offered_p Σ p o2 ∧ ech (h o2) ∉ D ∧ (y2 = y ∨ W1 ⊢ y2 ≺ y).
  Proof.
    intros HM HM' Hr Hab Hstq Lo Hoff. destruct (decide (ech (h o) ∈ D)) as [HD|HD]; [|exists o, S0, y; eauto].
    destruct (chain M M' HM HM' Hr Hab Hstq y (finite_lt_acc W1 (pts Σ) y) o S0 Lo Hoff HD) as (o2 & S2 & y2 & ?).
    exists o2, S2, y2. naive_solver.
  Qed.

  Local Lemma fwd_link M M' i os pc' : soup M = p.2 → soup M' = q.2 → mrel R M M' →
    istep (p.1, M) (EvOffer i (SLink os)) pc' → link_p q ∨ ¬ stable_p q.
  Proof.
    intros HM HM' Hr Hst. pose proof HC as (_ & _ & _ & _ & _ & _ & _ & _ & H7).
    destruct (H7 _ _ _ _ (erase_p M HM) Hst) as (o1 & o2 & S1 & S2 & x0 & Eos & _ & L1 & L2 & _).
    destruct (offer_thread M i _ pc' Hst) as (e & e1 & Hi & He).
    destruct (act_step _ _ _ He) as (a & Ha & Hoa). destruct (offers_link _ _ Hoa) as (b1 & b2 & -> & Eb).
    destruct (fwd_act M M' i e Hr Hi _ Ha) as (e' & a' & Hi' & _ & Ha' & Har).
    destruct a' as [| | |v0|o0|o0 v0|o0|z1 z2|o0 k0|o0]; simpl in Har; try done. destruct Har as [R1 R2].
    assert (b1 ∈ dom Σ ∧ b2 ∈ dom Σ) as [Hb1 Hb2].
    { destruct (upair_cases b1 b2 o1 o2 (eq_trans (eq_sym Eb) Eos)) as [[-> ->]|[-> ->]]; split; by eapply elem_of_dom_2. }
    destruct (act_offer e' _ (LSess (SLink ({[z1]} ∪ {[z2]}))) Ha' eq_refl) as [e1' He1'].
    destruct (decide (ech z1 ∈ q.1)) as [Q1|Q1].
    { right. eapply (not_stable_q M' (EvSolo i _ (PickLink z1 z2))); [done| |done]. by eapply p_act_link. }
    destruct (decide (ech z2 ∈ q.1)) as [Q2|Q2].
    { right. eapply (not_stable_q M' (EvSolo i _ (PickLink z2 z1))); [done| |done].
      eapply p_act_link; [done|by rewrite (comm_L (∪) {[z2]})|done]. }
    left. exists ({[z1]} ∪ {[z2]}), (erase (q.1 ∖ ∅, <[i := e1']> M')).
    exists (q.1, M'), (EvOffer i (SLink ({[z1]} ∪ {[z2]}))), (q.1 ∖ ∅, <[i := e1']> M').
    split_and!; [by apply eraseq| |done|done]. eapply p_act_session; [done|done|].
    simpl. rewrite set_map_union_L, !set_map_singleton_L. set_solver.
  Qed.

  Local Lemma stable_pq M M' : soup M = p.2 → soup M' = q.2 → mrel R M M' → stable_p q → stable_p p.
  Proof.
    intros HM HM' Hr Hstq p' Hps. unfold preduction in Hps. rewrite <-(erase_p M HM) in Hps.
    destruct (pstep_lift _ _ _ Hps) as (ev & pc' & Hst & Hl & _).
    destruct (fwd_tau M M' ev pc' HM Hr Hst Hl) as (ev' & qc' & Hst' & Hτ').
    by apply (not_stable_q M' ev' qc' HM' Hst' Hτ').
  Qed.

  Local Lemma crel_noends e e' : crel R e e' → fends e = ∅ → e' = e.
  Proof.
    intros Hc He. rewrite (crel_emap_eq e e' Hc) by (intros o Ho; set_solver).
    rewrite <-(emap_id e) at 2. apply emap_ext_on. intros o Ho. set_solver.
  Qed.

  (** When p stops, so does q, and they agree. *)
  Local Lemma pirred_q : pirred p → q = p ∧ Σq = ∅ ∧ Σ = ∅.
  Proof.
    intros Hi. destruct HC as (Hs0 & _ & _). destruct (Hs0 Hi) as (v & E & Ep & Hv & HE).
    pose proof (Vrel_tfree_empty κ _ _ _ _ _ (proj1 (proj2 Hs)) Hv) as EΣ.
    assert (D = ∅) as HD0.
    { apply dpairs_empty. rewrite <-(kren_empty h), <-EΣ. apply Hdp. }
    assert (∀ e, e ∈ p.2 → fends e = ∅) as Hnoe.
    { intros e He. rewrite Ep in He. simpl in He. apply gmultiset_elem_of_disj_union in He as [He|He].
      - apply gmultiset_elem_of_singleton in He as ->. by rewrite <-(Vrel_exact κ _ _ _ _ _ Hv), EΣ, dom_empty_L.
      - by rewrite (HE e He). }
    split_and!; [|by rewrite HD0, EΣ, kren_empty, sdrop_empty|done].
    destruct Hm as (M0 & M0' & HM0 & HM0' & Hr0).
    assert (M0' = M0) as EM.
    { apply map_eq. intros k0. specialize (Hr0 k0). destruct (M0 !! k0) as [e|] eqn:E0, (M0' !! k0) as [e'|]; try done.
      f_equal. apply (crel_noends e e' Hr0). apply Hnoe. rewrite <-HM0. apply elem_of_soup. eauto. }
    rewrite (surjective_pairing q), (surjective_pairing p). f_equal.
    - rewrite Eq1, HD0, Ep. simpl. set_solver.
    - by rewrite <-HM0', EM, HM0.
  Qed.

  Local Lemma offer_q qc i σ qc' : erase qc = q → istep qc (EvOffer i σ) qc' →
    ∃ M M' e' e1', soup M = p.2 ∧ mrel R M M' ∧ M' !! i = Some e' ∧ tstep e' (LSess σ) e1' ∧
      subjs σ ## q.1 ∧ qc' = (q.1 ∖ sentc σ, <[i := e1']> M').
  Proof.
    intros Hq Hst. remember (EvOffer i σ) as ev eqn:Eev. destruct Hst; try discriminate. injection Eev as -> ->.
    destruct (lift' C M Hq) as (-> & M0 & HM0 & Hr0). exists M0, M, e, e'. split_and!; done.
  Qed.

  (** The clauses of q. *)
  Lemma clauses_q : Pclauses κ n (Vrel κ) (Prel κ) (Vrel κ n) Xt W1 Σq T q.
  Proof.
    destruct (soup_surj q.2) as [M' HM'].
    destruct (lift (q.1, M') (eraseq M' HM')) as (M & HMe & Hr). simpl in Hr.
    assert (soup M = p.2) as HM by (by rewrite <-HMe).
    pose proof HC as (Hstop & Hrdy & _).
    assert (∀ o, offered_p Σ p o → ech (h o) ∉ D → offered_p Σq q (h o) ∨ ¬ stable_p q) as Hfo.
    { intros o Hoff ND'. destruct (offered_lift M o HM Hoff) as (i & σ & pc' & Hst & Ho).
      apply (fwd_off M M' i σ pc' o HM HM' Hr Hst Ho); [by destruct Hoff|done]. }
    assert (∀ i os pc', istep (p.1, M) (EvOffer i (SLink os)) pc' → link_p q ∨ ¬ stable_p q) as Hfl
      by (intros; by eapply fwd_link).
    assert (link_p p → stable_p q → link_p q) as Hll.
    { intros (os & p'' & Hps2) Sq. rewrite <-(erase_p M HM) in Hps2.
      destruct (pstep_lift _ _ _ Hps2) as (ev & pc2 & Hst2 & Hl2 & _). destruct ev; try discriminate.
      injection Hl2 as ->. by destruct (Hfl _ _ _ Hst2). }
    (* an offer of p meets a step of q *)
    assert (∀ i σ pc' o, istep (p.1, M) (EvOffer i σ) pc' → ssubj σ = Some o → stable_p q →
      (∀ o', offered_p Σq q o' → False) → (link_p q → False) → False) as Hcon.
    { intros i σ pc' o Hst Eo Sq Noq Nlq. pose proof (offer_held M i σ pc' o HM Hst Eo) as HoΣ.
      assert (offered_p Σ p o) as Hoffo.
      { split; [done|]. exists σ, (erase pc'). split.
        - exists (p.1, M), (EvOffer i σ), pc'. split_and!; [by apply erase_p|done|done|done].
        - destruct σ; simpl in Eo; try discriminate; injection Eo as ->; simpl; set_solver. }
      destruct (decide (ech (h o) ∈ D)) as [HD|ND'].
      - assert (¬ pirred p) as Nip.
        { intros Hip. destruct Hoffo as [_ (σ' & p'' & Hps & _)]. by apply (Hip _ _ Hps). }
        destruct (Hrdy Nip (stable_pq M M' HM HM' Hr Sq)) as [Hl|[_ HB]]; [by apply Nlq, Hll|].
        apply elem_of_dom in HoΣ as [[S0 y] Lo].
        destruct (chain' M M' o S0 y HM HM' Hr HB Sq Lo Hoffo) as (o2 & S2 & y2 & Lo2 & Hoff2 & ND2 & _).
        destruct (Hfo o2 Hoff2 ND2); [by apply (Noq (h o2))|done].
      - destruct (Hfo o Hoffo ND'); [by apply (Noq (h o))|done]. }
    assert (pirred q → pirred p) as Hpirr.
    { intros Hiq π p' Hps. assert (stable_p q) as Sq by (intros p'' H; exact (Hiq PTau p'' H)).
      assert (∀ o, offered_p Σq q o → False) as Noq by (intros o [_ (σ & q' & Hq & _)]; exact (Hiq _ q' Hq)).
      assert (link_p q → False) as Nlq by (intros (os & q' & Hq); exact (Hiq _ q' Hq)).
      pose proof Hps as Hps'. rewrite <-(erase_p M HM) in Hps'. destruct (pstep_lift _ _ _ Hps') as (ev & pc' & Hst & Hl & _).
      destruct ev as [i α k|i j σ|i σ].
      - destruct (fwd_tau M M' _ pc' HM Hr Hst eq_refl) as (ev' & qc' & Hst' & Hτ'). by apply (not_stable_q M' ev' qc' HM' Hst' Hτ').
      - destruct (fwd_tau M M' _ pc' HM Hr Hst eq_refl) as (ev' & qc' & Hst' & Hτ'). by apply (not_stable_q M' ev' qc' HM' Hst' Hτ').
      - destruct σ as [o0 w0|o0 w0|o0|o0 k0|o0 k0|os]; try (by apply (Hcon i _ pc' o0 Hst eq_refl Sq Noq Nlq)).
        by destruct (Hfl i os pc' Hst). }
    split; [|split].
    - (* P-Stop *)
      intros Hiq. pose proof (Hpirr Hiq) as Hip. destruct (pirred_q Hip) as (Eq & EΣq & EΣ).
      destruct (Hstop Hip) as (v & E & Ep & Hv & HE). exists v, E. split_and!; [by rewrite Eq|..|done].
      rewrite EΣq. by rewrite EΣ in Hv.
    - (* P-Ready *)
      intros Hniq Sq. assert (¬ pirred p) as Hnip by (intros Hip; destruct (pirred_q Hip) as (Eq & _); apply Hniq; by rewrite Eq).
      destruct (Hrdy Hnip (stable_pq M M' HM HM' Hr Sq)) as [Hl|[HA HB]]; [left; by apply Hll|right].
      split.
      + intros Hno. exfalso. apply Hnip.
        assert (∀ o, ¬ offered_p Σ p o) as Hnop.
        { intros o Hoff. destruct Hoff as [HoΣ Hex]. apply elem_of_dom in HoΣ as [[S0 y] Lo].
          destruct (chain' M M' o S0 y HM HM' Hr HB Sq Lo (conj (elem_of_dom_2 _ _ _ Lo) Hex)) as (o2 & S2 & y2 & Lo2 & Hoff2 & ND2 & _).
          destruct (Hfo o2 Hoff2 ND2); [by apply (Hno (h o2))|done]. }
        destruct (HA Hnop) as (v & E & Ep & Hv & HE). apply all_vals_pirred. intros e He. rewrite Ep in He. simpl in He.
        apply gmultiset_elem_of_disj_union in He as [He|He]; [by apply gmultiset_elem_of_singleton in He as ->|].
        by rewrite (HE e He).
      + intros o' S x Lo' Noff. destruct (lookupq_inv o' _ Lo') as (o & -> & Lo & ND').
        assert (¬ offered_p Σ p o) as Noffp by (intros Hoff; by destruct (Hfo o Hoff ND')).
        destruct (HB o S x Lo Noffp) as (o1 & S1 & y1 & Hoff1 & Lo1 & Hlt1).
        destruct (chain' M M' o1 S1 y1 HM HM' Hr HB Sq Lo1 Hoff1) as (o2 & S2 & y2 & Lo2 & Hoff2 & ND2 & Hle).
        destruct (Hfo o2 Hoff2 ND2) as [Hq|Hq]; [|done].
        exists (h o2), S2, y2. split_and!; [done|by apply lookupq|]. destruct Hle as [->|Hle]; [done|by eapply w_lt_trans].
    - (* P-Step *)
      split_and!.
      + intros qc ev qc' Hq Hst Hτ. exact (tau_clause qc ev qc' Hq Hst Hτ).
      + intros qc i o w qc' Hq Hst. destruct (offer_q qc i _ qc' Hq Hst) as (M0 & M0' & e' & e1' & HM0 & Hr0 & Hi & Hs0 & Hsj & ->).
        apply (off_send M0 M0' i o w e' e1'); try done. simpl in Hsj. set_solver.
      + intros qc i o w qc' Hq Hst. destruct (offer_q qc i _ qc' Hq Hst) as (M0 & M0' & e' & e1' & HM0 & Hr0 & Hi & Hs0 & Hsj & ->).
        destruct (off_recv M0 M0' i o w e' e1') as (S0 & x & m & U & S & A1 & A2 & A3); try done; [simpl in Hsj; set_solver|].
        exists S0, x, m, U, S. split_and!; [done|done|]. intros j Θ2 Hj Hdj Hok' HV. apply A3; try done.
        by rewrite difference_empty_L.
      + intros qc i o qc' Hq Hst. destruct (offer_q qc i _ qc' Hq Hst) as (M0 & M0' & e' & e1' & HM0 & Hr0 & Hi & Hs0 & Hsj & ->).
        apply (off_close M0 M0' i o e' e1'); try done. simpl in Hsj. set_solver.
      + intros qc i o b qc' Hq Hst. destruct (offer_q qc i _ qc' Hq Hst) as (M0 & M0' & e' & e1' & HM0 & Hr0 & Hi & Hs0 & Hsj & ->).
        apply (off_sel M0 M0' i o b e' e1'); try done. simpl in Hsj. set_solver.
      + intros qc i o b qc' Hq Hst. destruct (offer_q qc i _ qc' Hq Hst) as (M0 & M0' & e' & e1' & HM0 & Hr0 & Hi & Hs0 & Hsj & ->).
        apply (off_bra M0 M0' i o b e' e1'); try done. simpl in Hsj. set_solver.
      + intros qc i os qc' Hq Hst. destruct (offer_q qc i _ qc' Hq Hst) as (M0 & M0' & e' & e1' & HM0 & Hr0 & Hi & Hs0 & Hsj & ->).
        destruct (tstep_link_shape _ _ _ Hs0) as (y1 & y2 & ->).
        apply (off_link M0 M0' i y1 y2 e' e1'); try done.
  Qed.
End clauses.

(** ** The theorem *)

Section theorem.
  Context (κ : ctable).

  Lemma Prel_gfuse_lvl n : fclosed (Prel κ n) (Prel κ n).
  Proof.
    induction n as [n IHn] using oind.
    intros W Σ T p q h D Σ' HP Hs Hf HΣ.
    apply (Prel_conv κ n W (sdrop D (kren h Σ)) Σ' T q HΣ). clear Σ' HΣ.
    apply Prel_iff. intros Hn0. revert W Σ T p HP q h D Hs Hf.
    refine (Prel_ind κ n (λ W Σ T p, ∀ q h D, fside D Σ T p → gfuse h D Σ p q →
      Pbody κ n (Vrel κ) (Prel κ) (Vrel κ n) (Prel κ n) W (sdrop D (kren h Σ)) T q) Hn0 _).
    intros W Σ T p B q h D Hs Hf W1 HW1.
    eapply (clauses_q κ n Hn0 (λ W Σ T p, Prel κ n W Σ T p ∧ (∀ q h D, fside D Σ T p → gfuse h D Σ p q →
      Pbody κ n (Vrel κ) (Prel κ) (Vrel κ n) (Prel κ n) W (sdrop D (kren h Σ)) T q)) (Prel κ n)).
    - intros j Hj. by apply IHn.
    - intros W' Σ0 T0 p0 q0 h0 D0 Σ0' [_ Hb] Hs0 Hf0 HΣ0. apply (Prel_conv κ n W' _ Σ0' T0 q0 HΣ0).
      apply Prel_iff. intros _. by apply Hb.
    - by intros ? ? ? ? [? _].
    - exact Hf.
    - exact Hs.
    - by apply B.
  Qed.

  (** Decision no-fus: P is closed under fusion, as a theorem. *)
  Theorem Prel_gfuse n W Σ T p q h D :
    p ∈ P[κ]^W _ n⟦Σ ⊢ T⟧ → fside D Σ T p → gfuse h D Σ p q →
    q ∈ P[κ]^W _ n⟦sdrop D (kren h Σ) ⊢ T⟧.
  Proof. intros HP Hs Hf. eapply (Prel_gfuse_lvl n); [done|done|done|apply senv_eqv_refl]. Qed.

  Theorem Prel_fuse n W Σ T p h D :
    fuse_ok h D Σ p → fside D Σ T p → p ∈ P[κ]^W _ n⟦Σ ⊢ T⟧ → pfuse h D p ∈ P[κ]^W _ n⟦sdrop D (kren h Σ) ⊢ T⟧.
  Proof. intros Hh Hs HP. apply (Prel_gfuse n W Σ T p); [done|done|by apply gfuse_pfuse]. Qed.

  (** Renaming the held ends. *)
  Theorem Prel_rename n W Σ T p h :
    pren_ok h Σ p → fside ∅ Σ T p → p ∈ P[κ]^W _ n⟦Σ ⊢ T⟧ → pmap h p ∈ P[κ]^W _ n⟦kren h Σ ⊢ T⟧.
  Proof.
    intros Hh Hs HP. rewrite <-(pfuse_empty h p), <-(sdrop_empty (kren h Σ)).
    apply Prel_fuse; [by apply pren_fuse_ok|done|done].
  Qed.
End theorem.

(** ** Induction over the steps of cost 0, closed under fusion (P-Connect) *)

Lemma senv_eqv_trans (Θ1 Θ2 Θ3 : senv) : senv_eqv Θ1 Θ2 → senv_eqv Θ2 Θ3 → senv_eqv Θ1 Θ3.
Proof.
  intros H1 H2 o. specialize (H1 o). specialize (H2 o).
  inversion H1 as [a b [E1 S1] Ea Eb|Ea Eb]; inversion H2 as [b' c [E2 S2] Eb' Ec|Eb' Ec]; try congruence; constructor.
  rewrite <-Eb in Eb'. injection Eb' as <-. split; [congruence|by eapply seqv_trans].
Qed.

Lemma gfuse_conv h D Σ Σ' p q : senv_eqv Σ Σ' → gfuse h D Σ' p q → gfuse h D Σ p q.
Proof.
  intros HΣ (Hh & Eq & Hm). split_and!; [by eapply fuse_ok_conv|done|].
  eapply mcrel_mono; [|exact Hm]. intros e e' _. apply crel_mono. intros o o' _ H Ho. apply H.
  unfold hrel in *. by rewrite <-!(senv_eqv_dom _ _ HΣ).
Qed.

Definition Φfuse (Φ : prel) : prel :=
  λ W Σ T p, ∀ h D q Σ', fside D Σ T p → gfuse h D Σ p q → senv_eqv (sdrop D (kren h Σ)) Σ' → Φ W Σ' T q.

Section fuse_ind.
  Context (κ : ctable).

  Lemma Φfuse_closed n (Φ : prel) :
    fclosed (λ W Σ T p, Prel κ n W Σ T p ∧ Φfuse Φ W Σ T p) (λ W Σ T p, Prel κ n W Σ T p ∧ Φfuse Φ W Σ T p).
  Proof.
    intros W Σ T p q h D Σ1 [HP HΦ] Hs Hf HΣ1. split; [by eapply Prel_gfuse_lvl|].
    intros h2 D2 r Σ'' Hs2 Hf2 HΣ''.
    assert (gfuse h2 D2 (sdrop D (kren h Σ)) q r) as Hf2' by (by eapply gfuse_conv).
    destruct (gfuse_compose h h2 D D2 Σ p q r Hf Hf2') as [Hf' Eenv].
    apply (HΦ (h2 ∘ h) (D2 ∪ set_map (gch h2) D) r Σ''); [exact Hs|exact Hf'|]. rewrite <-Eenv.
    eapply senv_eqv_trans; [|exact HΣ'']. apply senv_eqv_sdrop, senv_eqv_kren; [|done].
    destruct Hf2' as (Hh2 & _). by eapply fuse_ok_kinj.
  Qed.

  Lemma Pbody_gfuse n (X : prel) W Σ T p q h D : olt ozero n → fclosed X X →
    (∀ W Σ T p, X W Σ T p → Prel κ n W Σ T p) → fside D Σ T p → gfuse h D Σ p q →
    Pbody κ n (Vrel κ) (Prel κ) (Vrel κ n) X W Σ T p →
    Pbody κ n (Vrel κ) (Prel κ) (Vrel κ n) X W (sdrop D (kren h Σ)) T q.
  Proof.
    intros Hn HX HXP Hs Hf B W1 HW1.
    eapply (clauses_q κ n Hn X X); [intros j Hj; apply Prel_gfuse_lvl|done|done|exact Hf|exact Hs|by apply B].
  Qed.

  Lemma Prel_ind_fuse n (Φ : prel) : olt ozero n →
    (∀ W Σ Σ' T p, senv_eqv Σ Σ' → Φ W Σ T p → Φ W Σ' T p) →
    (∀ W Σ T p, Pbody κ n (Vrel κ) (Prel κ) (Vrel κ n) (λ W Σ T p, Prel κ n W Σ T p ∧ Φfuse Φ W Σ T p) W Σ T p →
      Φ W Σ T p) →
    ∀ W Σ T p, Prel κ n W Σ T p → Φfuse Φ W Σ T p.
  Proof.
    intros Hn HΦc Hind. refine (Prel_ind κ n _ Hn _). intros W Σ T p B h D q Σ' Hs Hf HΣ'.
    apply (HΦc _ _ Σ' _ _ HΣ'). apply Hind.
    apply (Pbody_gfuse n _ W Σ T p q h D Hn (Φfuse_closed n Φ)); [by intros ? ? ? ? [? _]|done|done|done].
  Qed.

  Lemma Φfuse_id (Φ : prel) W Σ T p : fside ∅ Σ T p → Φfuse Φ W Σ T p → Φ W Σ T p.
  Proof.
    intros Hs H. apply (H id ∅ p Σ Hs (gfuse_id Σ p)). rewrite sdrop_empty, kren_id_map. apply senv_eqv_refl.
  Qed.
End fuse_ind.
