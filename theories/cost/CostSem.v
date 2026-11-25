(** * The semantic cost judgment (stage S7, proposal §2.11, decisions Q11, Q15)

      Θ ; Δ ⊨^N e : T ▷ c        [csem N Θ Δ e T c]

    The cost half of the merged judgment. For every level n, every
    renaming g of the ends of Θ and every grounding γ of Δ by values of
    [Vfuel] at N and n, the instance subst γ (emap g e) is in FuelE at N
    and n, at the result T and frame c, with the maps of the renamed Θ
    and of the grounding.

    Θ enters through [thfuel]: each end o of Θ becomes g o, with the
    session type of Θ, a counter at or above its credit and the tickets
    of Θ. Δ enters
    through [gfuel]: each entry gets a value of [Vfuel] at its type with
    its own part of the maps. [envf] bundles the two.

    The judgment reads no point, no world, no hypothesis context and no
    future, so the facts of Γ and the static future F of the typing
    judgment play no part. Like FuelE it reads no syntax of the term. *)

From GV Require Export fuel.FuelSub cost.Exact.

(** ** The ends of Θ *)

Definition thfuel (Θ : tenv) (g : cend → cend) (Π : penv) (φ : cenv) : Prop :=
  (∀ o1 o2, o1 ∈ dom Θ → o2 ∈ dom Θ → g o1 = g o2 → o1 = o2) ∧
  dom Π = set_map g (dom Θ) ∧ dom φ = dom Π ∧
  ∀ o te, Θ !! o = Some te →
    Π !! g o = Some (te_sty te) ∧ ∃ f, φ !! g o = Some f ∧ fle (te_cr te) f.1 ∧ f.2 = te_tk te.

(** ** Groundings *)

Fixpoint gfuel (N : fuel) (n : Ix) (Δ : lenv) (γ : nat → expr) (Π : penv) (φ : cenv) : Prop :=
  match Δ with
  | [] => Π = ∅ ∧ φ = ∅
  | None :: Δ' => gfuel N n Δ' (λ x, γ (S x)) Π φ
  | Some T :: Δ' =>
      ∃ Π1 Π2 φ1 φ2, Π1 ##ₘ Π2 ∧ φ1 ##ₘ φ2 ∧ Π = Π1 ∪ Π2 ∧ φ = φ1 ∪ φ2 ∧
        γ 0 ∈ FV^N _ n⟦RTy T⟧(Π1, φ1) ∧ gfuel N n Δ' (λ x, γ (S x)) Π2 φ2
  end.

Definition envf (N : fuel) (n : Ix) (Θ : tenv) (Δ : lenv) (g : cend → cend) (γ : nat → expr)
    (Π : penv) (φ : cenv) : Prop :=
  ∃ ΠΘ φΘ Πγ φγ, thfuel Θ g ΠΘ φΘ ∧ gfuel N n Δ γ Πγ φγ ∧ ΠΘ ##ₘ Πγ ∧ φΘ ##ₘ φγ ∧
    Π = ΠΘ ∪ Πγ ∧ φ = φΘ ∪ φγ.

(** ** The judgment *)

Definition csem (N : fuel) (Θ : tenv) (Δ : lenv) (e : expr) (T : ty) (c : fuel) : Prop :=
  ∀ n g γ Π φ, envf N n Θ Δ g γ Π φ →
    subst γ (emap g e) ∈ F^N _ n⟦RTy T ▷ c⟧(Π, φ).

Notation "Θ ; Δ ⊨^ N e : T ▷ c" := (csem N Θ Δ e T c)
  (at level 74, Δ at level 60, N at level 0, e at level 60, T at level 29,
   c at level 60,
   format "Θ  ;  Δ  ⊨^ N  e  :  T  ▷  c").

(** ** Arithmetic *)

Lemma fle_fadd_l' a b : fle a (fadd a b).
Proof. destruct a, b; simpl; lia. Qed.
Lemma fle_fadd_r' a b : fle b (fadd a b).
Proof. destruct a, b; simpl; lia. Qed.

(** ** Facts about values *)

Lemma Vfuel_unl_empty N n U Π φ v : unlimited U → v ∈ FV^N _ n⟦RTy U⟧(Π, φ) → Π = ∅ ∧ φ = ∅.
Proof. destruct U; try done. intros _. rewrite Vfuel_eq. simpl. by intros (? & _ & _ & -> & -> & _). Qed.

Section above.
  Context (El : Ix → epred) (Vl : Ix → vpred).

  (** Aging by c leaves every counter of an end that is not idle at or
      above c. An end and a closure cover c by their credit, which their
      counters are at or above. An idle end ages by truncation
      ([age_idle]) and may hold less. *)
  Lemma Vty_age_above N n c T T' Π φ v :
    tage c T T' → Vty N El Vl n T Π φ v → fabove c Π φ.
  Proof.
    intros Ha. revert Π φ v.
    induction Ha as [T Hf|S x a mt Hle|S x a mt Hi|ub lb c0 T U a Hle
                    |T1 T2 T1' T2' H1 IH1 H2 IH2|T1 T2 T1' T2' H1 IH1 H2 IH2|lb m C T T' H1 IH1];
      intros Π φ v; simpl.
    - intros Hv. destruct (Vty_tfree _ _ _ _ _ Hf _ _ _ Hv) as (-> & -> & _). intros o f. by rewrite lookup_empty.
    - intros (o' & S' & f' & _ & _ & -> & _ & Hf) o f Ho _.
      apply lookup_singleton_Some in Ho as [<- <-]. simpl. by eapply fle_trans.
    - intros (o' & S' & f' & _ & -> & -> & Hs & _) o f Ho Hn.
      apply lookup_singleton_Some in Ho as [<- <-]. exfalso. apply Hn.
      exists S'. rewrite lookup_singleton_eq. split; [done|]. by apply (idle_ssub _ _ Hs).
    - intros (e & _ & _ & _ & Hf & _) o f Ho Hn. eapply fle_trans; [exact Hle|exact (Hf o f Ho Hn)].
    - intros (v1 & v2 & Π1 & Π2 & φ1 & φ2 & _ & HdΠ & _ & -> & -> & Hv1 & Hv2) o f Ho Hn.
      apply lookup_union_Some_raw in Ho as [Ho|[_ Ho]];
        [apply (IH1 _ _ _ Hv1 o f Ho)|apply (IH2 _ _ _ Hv2 o f Ho)];
        intros (S0 & HS0 & Hi0); apply Hn; exists S0; split; try done;
        [by apply lookup_union_Some_l|by apply lookup_union_Some; [|right]].
    - intros [(v' & _ & Hv)|(v' & _ & Hv)]; [exact (IH1 _ _ _ Hv)|exact (IH2 _ _ _ Hv)].
    - intros Hv. exact (IH1 _ _ _ Hv).
  Qed.

End above.

Lemma Vfuel_age_above N n c T T' Π φ v :
  tage c T T' → v ∈ FV^N _ n⟦RTy T⟧(Π, φ) → fabove c Π φ.
Proof. rewrite Vfuel_eq. intros Ha. apply (Vty_age_above _ _ N n c T T'). done. Qed.

Lemma fabove_union c Π1 Π2 φ1 φ2 :
  Π1 ##ₘ Π2 → fabove c Π1 φ1 → fabove c Π2 φ2 → fabove c (Π1 ∪ Π2) (φ1 ∪ φ2).
Proof.
  intros Hd H1 H2 o f Ho Hn. apply lookup_union_Some_raw in Ho as [Ho|[_ Ho]];
    [apply (H1 o f Ho)|apply (H2 o f Ho)]; intros (S0 & HS0 & Hi0); apply Hn; exists S0; split; try done;
    [by apply lookup_union_Some_l|by apply lookup_union_Some; [|right]].
Qed.

Lemma fabove_of c Π φ : (∀ o f, φ !! o = Some f → fle c f.1) → fabove c Π φ.
Proof. intros H o f Ho _. exact (H o f Ho). Qed.

(** ** Facts about groundings *)

Lemma gfuel_dom N n Δ : ∀ γ Π φ, gfuel N n Δ γ Π φ → dom Π = dom φ.
Proof.
  induction Δ as [|[T|] Δ IH]; intros γ Π φ; simpl.
  - intros [-> ->]. by rewrite !dom_empty_L.
  - intros (Π1 & Π2 & φ1 & φ2 & _ & _ & -> & -> & Hv & HG).
    rewrite !dom_union_L, (Vfuel_dom _ _ _ _ _ _ Hv). by erewrite IH.
  - apply IH.
Qed.

Lemma gfuel_unl N n Δ : ∀ γ Π φ, lenv_unl Δ → gfuel N n Δ γ Π φ → Π = ∅ ∧ φ = ∅.
Proof.
  induction Δ as [|o Δ IH]; intros γ Π φ HΔ; simpl; [done|].
  assert (lenv_unl Δ) as HΔ' by (intros o' Ho'; apply HΔ; by right).
  destruct (HΔ o ltac:(left)) as [->|(U & -> & Hu)]; [by apply IH|].
  intros (Π1 & Π2 & φ1 & φ2 & _ & _ & -> & -> & Hv & HG).
  destruct (Vfuel_unl_empty _ _ _ _ _ _ Hu Hv) as [-> ->].
  destruct (IH _ _ _ HΔ' HG) as [-> ->]. by rewrite !map_empty_union.
Qed.

Lemma gfuel_only N n Δ x T γ Π φ :
  lenv_only Δ x T → gfuel N n Δ γ Π φ → γ x ∈ FV^N _ n⟦RTy T⟧(Π, φ).
Proof.
  intros [Hx Ho]. revert x γ Π φ Hx Ho. induction Δ as [|o Δ IH]; intros x γ Π φ Hx Ho; [done|].
  destruct x as [|x]; simpl in Hx.
  - injection Hx as ->. intros (Π1 & Π2 & φ1 & φ2 & _ & _ & -> & -> & Hv & HG).
    assert (lenv_unl Δ) as HΔ.
    { intros o' Ho'. destruct o' as [U|]; [|by left]. apply list_elem_of_lookup in Ho' as [y Hy].
      right. exists U. split; [done|]. exact (Ho (S y) U ltac:(done) Hy). }
    destruct (gfuel_unl _ _ _ _ _ _ HΔ HG) as [-> ->]. by rewrite !map_union_empty.
  - assert (∀ y σ', y ≠ x → Δ !! y = Some (Some σ') → unlimited σ') as Ho'.
    { intros y σ' Hne Hσ. apply (Ho (S y) σ'); [lia|done]. }
    destruct o as [U|]; simpl.
    + intros (Π1 & Π2 & φ1 & φ2 & _ & _ & -> & -> & Hv & HG).
      destruct (Vfuel_unl_empty _ _ _ _ _ _ (Ho 0 U ltac:(done) eq_refl) Hv) as [-> ->].
      rewrite !map_empty_union. exact (IH x (λ y, γ (S y)) _ _ Hx Ho' HG).
    + intros HG. exact (IH x (λ y, γ (S y)) _ _ Hx Ho' HG).
Qed.

Lemma gfuel_split N n Δ Δ1 Δ2 γ Π φ :
  lenv_split Δ Δ1 Δ2 → gfuel N n Δ γ Π φ →
  ∃ Π1 Π2 φ1 φ2, Π1 ##ₘ Π2 ∧ φ1 ##ₘ φ2 ∧ Π = Π1 ∪ Π2 ∧ φ = φ1 ∪ φ2 ∧
    gfuel N n Δ1 γ Π1 φ1 ∧ gfuel N n Δ2 γ Π2 φ2.
Proof.
  intros Hs. revert γ Π φ.
  induction Hs as [|Δ Δ1 Δ2 Hs IH|T Δ Δ1 Δ2 Hs IH|T Δ Δ1 Δ2 Hs IH|U Δ Δ1 Δ2 Hu Hs IH];
    intros γ Π φ; simpl.
  - intros [-> ->]. exists ∅, ∅, ∅, ∅. rewrite !map_empty_union. split_and!; try done; apply map_disjoint_empty_l.
  - apply IH.
  - intros (Πa & Πb & φa & φb & Hd1 & Hd2 & -> & -> & Hv & HG).
    destruct (IH _ _ _ HG) as (Π1 & Π2 & φ1 & φ2 & D1 & D2 & -> & -> & G1 & G2).
    exists (Πa ∪ Π1), Π2, (φa ∪ φ1), φ2.
    apply map_disjoint_union_r in Hd1 as [Hd1 Hd1']. apply map_disjoint_union_r in Hd2 as [Hd2 Hd2'].
    split_and!; [by apply map_disjoint_union_l|by apply map_disjoint_union_l
                |by rewrite map_union_assoc|by rewrite map_union_assoc| |done].
    exists Πa, Π1, φa, φ1. by split_and!.
  - intros (Πa & Πb & φa & φb & Hd1 & Hd2 & -> & -> & Hv & HG).
    destruct (IH _ _ _ HG) as (Π1 & Π2 & φ1 & φ2 & D1 & D2 & -> & -> & G1 & G2).
    exists Π1, (Πa ∪ Π2), φ1, (φa ∪ φ2).
    apply map_disjoint_union_r in Hd1 as [Hd1 Hd1']. apply map_disjoint_union_r in Hd2 as [Hd2 Hd2'].
    split_and!; [by apply map_disjoint_union_r; split; [apply map_disjoint_sym|]
                |by apply map_disjoint_union_r; split; [apply map_disjoint_sym|]
                |rewrite !map_union_assoc; f_equal; by apply map_union_comm
                |rewrite !map_union_assoc; f_equal; by apply map_union_comm|done|].
    exists Πa, Π2, φa, φ2. by split_and!.
  - intros (Πa & Πb & φa & φb & Hd1 & Hd2 & -> & -> & Hv & HG).
    destruct (Vfuel_unl_empty _ _ _ _ _ _ Hu Hv) as [-> ->]. rewrite !map_empty_union.
    destruct (IH _ _ _ HG) as (Π1 & Π2 & φ1 & φ2 & D1 & D2 & -> & -> & G1 & G2).
    exists Π1, Π2, φ1, φ2. split_and!; try done.
    + exists ∅, Π1, ∅, φ1. rewrite !map_empty_union. split_and!; try done; apply map_disjoint_empty_l.
    + exists ∅, Π2, ∅, φ2. rewrite !map_empty_union. split_and!; try done; apply map_disjoint_empty_l.
Qed.

Lemma gfuel_mono N n m Δ : ∀ γ Π φ φ', ole m n → cle φ φ' →
  gfuel N n Δ γ Π φ → gfuel N m Δ γ Π φ'.
Proof.
  induction Δ as [|[T|] Δ IH]; intros γ Π φ φ' Hm Hc; simpl.
  - intros [-> ->]. split; [done|by apply cle_empty_l].
  - intros (Π1 & Π2 & φ1 & φ2 & Hd1 & Hd2 & -> & -> & Hv & HG).
    destruct (cle_union_split _ _ _ Hd2 Hc) as (φ1' & φ2' & -> & Hd' & C1 & C2).
    exists Π1, Π2, φ1', φ2'. split_and!; try done.
    + eapply Vfuel_down; [exact Hm|]. by eapply Vfuel_mono.
    + by eapply IH.
  - apply IH; done.
Qed.

Lemma gfuel_age N n c Δ Δ' : lage c Δ Δ' → ∀ γ Π φ, gfuel N n Δ γ Π φ → gfuel N n Δ' γ Π (fminus c <$> φ).
Proof.
  induction 1 as [|Δ Δ' _ IH|T T' Δ Δ' Ha _ IH]; intros γ Π φ; simpl.
  - intros [-> ->]. by rewrite fmap_empty.
  - apply IH.
  - intros (Π1 & Π2 & φ1 & φ2 & Hd1 & Hd2 & -> & -> & Hv & HG).
    exists Π1, Π2, (fminus c <$> φ1), (fminus c <$> φ2). split_and!; try done.
    + by apply map_disjoint_fmap.
    + by rewrite map_fmap_union.
    + by eapply Vfuel_age.
    + by apply IH.
Qed.

Lemma gfuel_age_above N n c Δ Δ' : lage c Δ Δ' → ∀ γ Π φ, gfuel N n Δ γ Π φ →
  fabove c Π φ.
Proof.
  induction 1 as [|Δ Δ' _ IH|T T' Δ Δ' Ha _ IH]; intros γ Π φ; simpl.
  - intros [-> ->] o f. by rewrite lookup_empty.
  - apply IH.
  - intros (Π1 & Π2 & φ1 & φ2 & Hd1 & Hd2 & -> & -> & Hv & HG).
    apply fabove_union; [done|exact (Vfuel_age_above _ _ _ _ _ _ _ _ Ha Hv)|exact (IH _ _ _ HG)].
Qed.

Lemma gfuel_rename N n Δ : ∀ γ Π φ (g : cend → cend) Π' φ',
  kinj g Π → kinj g φ → renk g Π Π' → renk g φ φ' →
  gfuel N n Δ γ Π φ → gfuel N n Δ (λ x, emap g (γ x)) Π' φ'.
Proof.
  induction Δ as [|[T|] Δ IH]; intros γ Π φ g Π' φ' Hk1 Hk2 R1 R2; simpl.
  - intros [-> ->]. split; [by apply (renk_empty g)|by apply (renk_empty g)].
  - intros (Π1 & Π2 & φ1 & φ2 & Hd1 & Hd2 & -> & -> & Hv & HG).
    destruct (renk_union_split g Π1 Π2 Π' Hk1 Hd1 R1) as (Π1' & Π2' & -> & R11 & R12 & Hd').
    destruct (renk_union_split g φ1 φ2 φ' Hk2 Hd2 R2) as (φ1' & φ2' & -> & R21 & R22 & Hd'').
    exists Π1', Π2', φ1', φ2'. split_and!; try done.
    + eapply Vfuel_rename; [| |exact R11|exact R21|exact Hv].
      * apply (kinj_dom g (Π1 ∪ Π2)); [rewrite dom_union_L; set_solver|done].
      * apply (kinj_dom g (φ1 ∪ φ2)); [rewrite dom_union_L; set_solver|done].
    + eapply IH; [| |exact R12|exact R22|exact HG].
      * apply (kinj_dom g (Π1 ∪ Π2)); [rewrite dom_union_L; set_solver|done].
      * apply (kinj_dom g (φ1 ∪ φ2)); [rewrite dom_union_L; set_solver|done].
  - eapply IH; eassumption.
Qed.

Lemma gfuel_pinst N n ρ Δ : ∀ γ Π φ, gfuel N n (lenv_pinst ρ Δ) γ Π φ ↔ gfuel N n Δ γ Π φ.
Proof.
  induction Δ as [|[T|] Δ IH]; intros γ Π φ; simpl; [done| |apply IH].
  split; intros (Π1 & Π2 & φ1 & φ2 & Hd1 & Hd2 & -> & -> & Hv & HG); exists Π1, Π2, φ1, φ2;
    split_and!; try done; try (by apply IH); by apply Vfuel_pinst in Hv || apply Vfuel_pinst.
Qed.

(** The ends of a grounding: every value mentions only ends of the
    grounding, and every end of the grounding is mentioned by the value
    of an entry that is not unlimited. *)
Lemma gfuel_ends N n Δ : ∀ γ Π φ, gfuel N n Δ γ Π φ →
  (∀ x σ, Δ !! x = Some (Some σ) → fends (γ x) ⊆ dom Π) ∧
  (∀ o, o ∈ dom Π → ∃ x T, Δ !! x = Some (Some T) ∧ ¬ unlimited T ∧ o ∈ fends (γ x)).
Proof.
  induction Δ as [|[T|] Δ IH]; intros γ Π φ; simpl.
  - intros [-> _]. split; [intros x σ; by rewrite lookup_nil|intros o; rewrite dom_empty_L; set_solver].
  - intros (Π1 & Π2 & φ1 & φ2 & Hd1 & Hd2 & -> & -> & Hv & HG).
    destruct (IH _ _ _ HG) as [A B]. pose proof (Vfuel_exact _ _ _ _ _ _ Hv) as Hx. split.
    + intros [|x] σ Hx'; simpl in Hx'; rewrite dom_union_L; [rewrite Hx; set_solver|].
      specialize (A x σ Hx'). set_solver.
    + intros o. rewrite dom_union_L. intros [Ho|Ho]%elem_of_union.
      * exists 0, T. split_and!; [done| |by rewrite Hx].
        intros Hu. destruct (Vfuel_unl_empty _ _ _ _ _ _ Hu Hv) as [-> _]. set_solver.
      * destruct (B o Ho) as (x & T' & ? & ? & ?). by exists (S x), T'.
  - intros HG. destruct (IH _ _ _ HG) as [A B]. split.
    + intros [|x] σ Hx'; simpl in Hx'; [done|]. by apply (A x σ).
    + intros o Ho. destruct (B o Ho) as (x & T' & ? & ? & ?). by exists (S x), T'.
Qed.

(** ** Facts about the ends of Θ *)

Lemma thfuel_dom Θ g Π φ : thfuel Θ g Π φ → dom Π = dom φ.
Proof. by intros (_ & _ & -> & _). Qed.

Lemma thfuel_empty g Π φ : thfuel ∅ g Π φ → Π = ∅ ∧ φ = ∅.
Proof.
  intros (_ & HΠ & Hφ & _). rewrite dom_empty_L, set_map_empty in HΠ.
  apply dom_empty_inv_L in HΠ as ->. rewrite dom_empty_L in Hφ. apply dom_empty_inv_L in Hφ as ->. done.
Qed.

Lemma thfuel_single o te g Π φ :
  thfuel {[o := te]} g Π φ → Π = {[g o := te_sty te]} ∧ ∃ f, φ = {[g o := f]} ∧ fle (te_cr te) f.1 ∧ f.2 = te_tk te.
Proof.
  intros (_ & HΠ & Hφ & H). destruct (H o te ltac:(by rewrite lookup_singleton_eq)) as (Hp & f & Hf & Hle & Hm).
  rewrite dom_singleton_L, set_map_singleton_L in HΠ.
  assert (∀ {Y} (m : gmap cend Y) y, dom m = {[g o]} → m !! g o = Some y → m = {[g o := y]}) as Hs.
  { intros Y m y Hd Hy. apply map_eq. intros o'. destruct (decide (g o = o')) as [<-|Hne];
      [by rewrite lookup_singleton_eq|]. rewrite lookup_singleton_ne by done.
    apply not_elem_of_dom. set_solver. }
  split; [by apply Hs|]. exists f. split; [|done]. apply Hs; [congruence|done].
Qed.

Lemma thfuel_lookup Θ g Π φ o : thfuel Θ g Π φ → o ∈ dom Π → ∃ o0 te, o = g o0 ∧ Θ !! o0 = Some te.
Proof.
  intros (_ & HΠ & _ & _) Ho. rewrite HΠ in Ho. apply elem_of_map in Ho as (o0 & -> & Ho0).
  apply elem_of_dom in Ho0 as [te Hte]. eauto.
Qed.

Lemma thfuel_split Θ Θ1 Θ2 g Π φ :
  tsplit Θ Θ1 Θ2 → thfuel Θ g Π φ →
  ∃ Π1 Π2 φ1 φ2, Π1 ##ₘ Π2 ∧ φ1 ##ₘ φ2 ∧ Π = Π1 ∪ Π2 ∧ φ = φ1 ∪ φ2 ∧
    thfuel Θ1 g Π1 φ1 ∧ thfuel Θ2 g Π2 φ2.
Proof.
  intros [Hd ->] (Hi & HΠ & Hφ & H).
  set (X1 := set_map g (dom Θ1) : gset cend). set (X2 := set_map g (dom Θ2) : gset cend).
  assert (X1 ## X2) as HX.
  { intros o' Ho1 Ho2. apply elem_of_map in Ho1 as (o1 & -> & Ho1). apply elem_of_map in Ho2 as (o2 & Heq & Ho2).
    assert (o1 = o2) as <-. { apply Hi; [rewrite dom_union_L; set_solver|rewrite dom_union_L; set_solver|done]. }
    apply map_disjoint_dom in Hd. set_solver. }
  assert (dom Π = X1 ∪ X2) as HΠ'. { rewrite HΠ, dom_union_L. unfold X1, X2. apply set_map_union_L. }
  exists (mres X1 Π), (mres X2 Π), (mres X1 φ), (mres X2 φ). split_and!.
  - apply map_disjoint_dom. rewrite !dom_mres. set_solver.
  - apply map_disjoint_dom. rewrite !dom_mres. set_solver.
  - apply map_eq. intros o. rewrite lookup_union, !lookup_mres.
    destruct (Π !! o) eqn:E; [|repeat case_decide; done].
    assert (o ∈ X1 ∪ X2) as Ho by (rewrite <-HΠ'; by eapply elem_of_dom_2).
    repeat case_decide; simpl; try done; set_solver.
  - apply map_eq. intros o. rewrite lookup_union, !lookup_mres.
    destruct (φ !! o) eqn:E; [|repeat case_decide; done].
    assert (o ∈ X1 ∪ X2) as Ho by (rewrite <-HΠ', <-Hφ; by eapply elem_of_dom_2).
    repeat case_decide; simpl; try done; set_solver.
  - split_and!.
    + intros o1 o2 H1 H2. apply Hi; rewrite dom_union_L; set_solver.
    + rewrite dom_mres, HΠ'. set_solver.
    + rewrite !dom_mres, Hφ. done.
    + intros o te Ho. assert (g o ∈ X1) as Hg by (apply elem_of_map_2; by eapply elem_of_dom_2).
      destruct (H o te ltac:(by apply lookup_union_Some_l)) as (Hp & f & Hf & Hle).
      rewrite !lookup_mres, !decide_True by done. eauto.
  - split_and!.
    + intros o1 o2 H1 H2. apply Hi; rewrite dom_union_L; set_solver.
    + rewrite dom_mres, HΠ'. set_solver.
    + rewrite !dom_mres, Hφ. done.
    + intros o te Ho. assert (g o ∈ X2) as Hg by (apply elem_of_map_2; by eapply elem_of_dom_2).
      destruct (H o te ltac:(by apply lookup_union_Some_r)) as (Hp & f & Hf & Hle).
      rewrite !lookup_mres, !decide_True by done. eauto.
Qed.

Lemma thage_lookup c Θ Θ' o te' : thage c Θ Θ' → Θ' !! o = Some te' →
  ∃ te, Θ !! o = Some te ∧ te_sty te' = te_sty te ∧ te_tk te' = te_tk te ∧
    (fle c (te_cr te) ∨ idle (te_sty te)) ∧ te_cr te' = fsub (te_cr te) c.
Proof. intros H Ho. specialize (H o). rewrite Ho in H. destruct (Θ !! o); naive_solver. Qed.

Lemma thfuel_age c Θ Θ' g Π φ : thage c Θ Θ' → thfuel Θ g Π φ → thfuel Θ' g Π (fminus c <$> φ).
Proof.
  intros Ha (Hi & HΠ & Hφ & H). pose proof (thage_dom _ _ _ Ha) as Hd. split_and!.
  - rewrite Hd. done.
  - by rewrite Hd.
  - by rewrite dom_fmap_L.
  - intros o te' Ho. destruct (thage_lookup _ _ _ _ _ Ha Ho) as (te & Hte & Hs & Hm & Hc & Hcr).
    destruct (H o te Hte) as (Hp & f & Hf & Hle & Hfm). split; [by rewrite Hs|].
    exists (fminus c f). rewrite lookup_fmap, Hf. split; [done|]. rewrite Hcr, Hm. split; [by apply fle_fsub_mono|done].
Qed.

(** An end of Θ that is not idle covers c by its credit, which its
    counter is at or above. An idle end of Θ ages by truncation. *)
Lemma thfuel_age_above c Θ Θ' g Π φ : thage c Θ Θ' → thfuel Θ g Π φ → fabove c Π φ.
Proof.
  intros Ha Ht o f Ho Hn. pose proof Ht as (Hi & HΠ & Hφ & H).
  destruct (thfuel_lookup Θ g Π φ o Ht ltac:(rewrite <-Hφ; by eapply elem_of_dom_2)) as (o0 & te & -> & Hte).
  destruct (H o0 te Hte) as (Hp & f' & Hf' & Hle & _). rewrite Ho in Hf'. injection Hf' as <-.
  specialize (Ha o0). rewrite Hte in Ha. destruct (Θ' !! o0); [|done].
  destruct Ha as (_ & _ & _ & [Hc|Hid] & _); [by eapply fle_trans|].
  exfalso. apply Hn. by exists (te_sty te).
Qed.

Lemma thfuel_cle Θ g Π φ φ' : cle φ φ' → thfuel Θ g Π φ → thfuel Θ g Π φ'.
Proof.
  intros Hc (Hi & HΠ & Hφ & H). split_and!; [done|done|by rewrite <-(cle_dom _ _ Hc)|].
  intros o te Hte. destruct (H o te Hte) as (Hp & f & Hf & Hle & Hm). split; [done|].
  destruct (cle_lookup _ _ _ _ Hc Hf) as (f' & Hf' & [Hle' E]). exists f'. split; [done|].
  split; [by eapply fle_trans|congruence].
Qed.

Lemma thfuel_rename Θ g Π φ (g' : cend → cend) Π' φ' :
  kinj g' Π → renk g' Π Π' → renk g' φ φ' → thfuel Θ g Π φ → thfuel Θ (g' ∘ g) Π' φ'.
Proof.
  intros Hk R1 R2 (Hi & HΠ & Hφ & H). split_and!.
  - intros o1 o2 H1 H2 Heq. apply Hi; [done|done|]. apply (kinj_elem g' Π); [done| | |done];
      rewrite HΠ; by apply elem_of_map_2.
  - rewrite (renk_dom _ _ _ R1), HΠ. apply set_eq. intros o. rewrite !elem_of_map.
    split; [intros (o1 & -> & (o0 & -> & Ho0)%elem_of_map); by exists o0|intros (o0 & -> & Ho0); exists (g o0); split; [done|by apply elem_of_map_2]].
  - by rewrite (renk_dom _ _ _ R1), (renk_dom _ _ _ R2), Hφ.
  - intros o te Hte. destruct (H o te Hte) as (Hp & f & Hf & Hle). split; [by apply R1|].
    exists f. split; [by apply R2|done].
Qed.

Lemma thfuel_pinst ρ Θ g Π φ : thfuel (tenv_pinst ρ Θ) g Π φ ↔ thfuel Θ g Π φ.
Proof.
  unfold thfuel, tenv_pinst. rewrite dom_fmap_L. setoid_rewrite lookup_fmap.
  split; intros (Hi & HΠ & Hφ & H); split_and!; try done; intros o te Hte.
  - destruct (H o (tentry_pinst ρ te)) as (Hp & f & Hf & Hle); [by rewrite Hte|]. eauto.
  - destruct (Θ !! o) as [te0|] eqn:E; simpl in Hte; [|done]. injection Hte as <-. exact (H o te0 E).
Qed.

(** ** Facts about environments *)

Lemma envf_dom N n Θ Δ g γ Π φ : envf N n Θ Δ g γ Π φ → dom Π = dom φ.
Proof.
  intros (ΠΘ & φΘ & Πγ & φγ & HT & HG & _ & _ & -> & ->).
  rewrite !dom_union_L, (thfuel_dom _ _ _ _ HT). by erewrite gfuel_dom.
Qed.

Lemma envf_intro N n Θ Δ g γ ΠΘ φΘ Πγ φγ :
  thfuel Θ g ΠΘ φΘ → gfuel N n Δ γ Πγ φγ → ΠΘ ##ₘ Πγ → envf N n Θ Δ g γ (ΠΘ ∪ Πγ) (φΘ ∪ φγ).
Proof.
  intros HT HG Hd. exists ΠΘ, φΘ, Πγ, φγ. split_and!; try done.
  apply map_disjoint_dom. rewrite <-(thfuel_dom _ _ _ _ HT), <-(gfuel_dom _ _ _ _ _ _ HG).
  by apply map_disjoint_dom.
Qed.

Lemma envf_split N n Θ Θ1 Θ2 Δ Δ1 Δ2 g γ Π φ :
  tsplit Θ Θ1 Θ2 → lenv_split Δ Δ1 Δ2 → envf N n Θ Δ g γ Π φ →
  ∃ Π1 Π2 φ1 φ2, Π1 ##ₘ Π2 ∧ φ1 ##ₘ φ2 ∧ Π = Π1 ∪ Π2 ∧ φ = φ1 ∪ φ2 ∧
    envf N n Θ1 Δ1 g γ Π1 φ1 ∧ envf N n Θ2 Δ2 g γ Π2 φ2.
Proof.
  intros Hs Hl (ΠΘ & φΘ & Πγ & φγ & HT & HG & Hd1 & Hd2 & -> & ->).
  destruct (thfuel_split _ _ _ _ _ _ Hs HT) as (A1 & A2 & a1 & a2 & DA & Da & -> & -> & T1 & T2).
  destruct (gfuel_split _ _ _ _ _ _ _ _ Hl HG) as (B1 & B2 & b1 & b2 & DB & Db & -> & -> & G1 & G2).
  apply map_disjoint_union_l in Hd1 as [H1 H2]. apply map_disjoint_union_r in H1 as [H11 H12].
  apply map_disjoint_union_r in H2 as [H21 H22].
  apply map_disjoint_union_l in Hd2 as [K1 K2]. apply map_disjoint_union_r in K1 as [K11 K12].
  apply map_disjoint_union_r in K2 as [K21 K22].
  exists (A1 ∪ B1), (A2 ∪ B2), (a1 ∪ b1), (a2 ∪ b2). split_and!.
  - apply map_disjoint_union_l. split; apply map_disjoint_union_r; split; try done; by apply map_disjoint_sym.
  - apply map_disjoint_union_l. split; apply map_disjoint_union_r; split; try done; by apply map_disjoint_sym.
  - rewrite <-!map_union_assoc. f_equal. rewrite !map_union_assoc. f_equal. by apply map_union_comm.
  - rewrite <-!map_union_assoc. f_equal. rewrite !map_union_assoc. f_equal. by apply map_union_comm.
  - exists A1, a1, B1, b1. by split_and!.
  - exists A2, a2, B2, b2. by split_and!.
Qed.

Lemma envf_age N n c Θ Θ' Δ Δ' g γ Π φ :
  thage c Θ Θ' → lage c Δ Δ' → envf N n Θ Δ g γ Π φ → envf N n Θ' Δ' g γ Π (fminus c <$> φ).
Proof.
  intros HaT HaD (ΠΘ & φΘ & Πγ & φγ & HT & HG & Hd1 & Hd2 & -> & ->).
  exists ΠΘ, (fminus c <$> φΘ), Πγ, (fminus c <$> φγ). split_and!.
  - by eapply thfuel_age.
  - by eapply gfuel_age.
  - done.
  - by apply map_disjoint_fmap.
  - done.
  - by rewrite map_fmap_union.
Qed.

Lemma envf_age_above N n c Θ Θ' Δ Δ' g γ Π φ :
  thage c Θ Θ' → lage c Δ Δ' → envf N n Θ Δ g γ Π φ → fabove c Π φ.
Proof.
  intros HaT HaD (ΠΘ & φΘ & Πγ & φγ & HT & HG & Hd1 & Hd2 & -> & ->).
  apply fabove_union; [done|exact (thfuel_age_above _ _ _ _ _ _ HaT HT)|exact (gfuel_age_above _ _ _ _ _ HaD _ _ _ HG)].
Qed.

Lemma envf_rename N n Θ Δ g γ Π φ (g' : cend → cend) Π' φ' :
  kinj g' Π → kinj g' φ → renk g' Π Π' → renk g' φ φ' →
  envf N n Θ Δ g γ Π φ → envf N n Θ Δ (g' ∘ g) (λ x, emap g' (γ x)) Π' φ'.
Proof.
  intros Hk1 Hk2 R1 R2 (ΠΘ & φΘ & Πγ & φγ & HT & HG & Hd1 & Hd2 & -> & ->).
  destruct (renk_union_split g' ΠΘ Πγ Π' Hk1 Hd1 R1) as (A & B & -> & RA & RB & DAB).
  destruct (renk_union_split g' φΘ φγ φ' Hk2 Hd2 R2) as (a & b & -> & Ra & Rb & Dab).
  exists A, a, B, b. split_and!; try done.
  - eapply thfuel_rename; [|exact RA|exact Ra|exact HT].
    apply (kinj_dom g' (ΠΘ ∪ Πγ)); [rewrite dom_union_L; set_solver|done].
  - eapply gfuel_rename; [| |exact RB|exact Rb|exact HG].
    + apply (kinj_dom g' (ΠΘ ∪ Πγ)); [rewrite dom_union_L; set_solver|done].
    + apply (kinj_dom g' (φΘ ∪ φγ)); [rewrite dom_union_L; set_solver|done].
Qed.

Lemma envf_mono N n m Θ Δ g γ Π φ φ' :
  ole m n → cle φ φ' → envf N n Θ Δ g γ Π φ → envf N m Θ Δ g γ Π φ'.
Proof.
  intros Hm Hc (ΠΘ & φΘ & Πγ & φγ & HT & HG & Hd1 & Hd2 & -> & ->).
  destruct (cle_union_split _ _ _ Hd2 Hc) as (a & b & -> & Dab & Ca & Cb).
  exists ΠΘ, a, Πγ, b. split_and!; try done; [by eapply thfuel_cle|by eapply gfuel_mono].
Qed.

Lemma envf_down N n m Θ Δ g γ Π φ : ole m n → envf N n Θ Δ g γ Π φ → envf N m Θ Δ g γ Π φ.
Proof. intros Hm. apply envf_mono; [done|apply cle_refl]. Qed.

Lemma envf_unl N n Δ g γ Π φ : lenv_unl Δ → envf N n ∅ Δ g γ Π φ → Π = ∅ ∧ φ = ∅.
Proof.
  intros HΔ (ΠΘ & φΘ & Πγ & φγ & HT & HG & Hd1 & Hd2 & -> & ->).
  destruct (thfuel_empty _ _ _ HT) as [-> ->]. destruct (gfuel_unl _ _ _ _ _ _ HΔ HG) as [-> ->].
  by rewrite !map_empty_union.
Qed.

Lemma envf_only N n Δ x T g γ Π φ :
  lenv_only Δ x T → envf N n ∅ Δ g γ Π φ → γ x ∈ FV^N _ n⟦RTy T⟧(Π, φ).
Proof.
  intros Ho (ΠΘ & φΘ & Πγ & φγ & HT & HG & Hd1 & Hd2 & -> & ->).
  destruct (thfuel_empty _ _ _ HT) as [-> ->]. rewrite !map_empty_union. by eapply gfuel_only.
Qed.

Lemma envf_single N n o te Δ g γ Π φ :
  lenv_unl Δ → envf N n {[o := te]} Δ g γ Π φ →
  Π = {[g o := te_sty te]} ∧ ∃ f, φ = {[g o := f]} ∧ fle (te_cr te) f.1 ∧ f.2 = te_tk te.
Proof.
  intros HΔ (ΠΘ & φΘ & Πγ & φγ & HT & HG & Hd1 & Hd2 & -> & ->).
  destruct (gfuel_unl _ _ _ _ _ _ HΔ HG) as [-> ->]. rewrite !map_union_empty.
  by apply thfuel_single.
Qed.

Lemma envf_cons N n Θ Δ g γ Π φ T v Πv φv :
  envf N n Θ Δ g γ Π φ → v ∈ FV^N _ n⟦RTy T⟧(Πv, φv) → Π ##ₘ Πv → φ ##ₘ φv →
  envf N n Θ (Some T :: Δ) g (v .: γ) (Π ∪ Πv) (φ ∪ φv).
Proof.
  intros (ΠΘ & φΘ & Πγ & φγ & HT & HG & Hd1 & Hd2 & -> & ->) Hv HdΠ Hdφ.
  apply map_disjoint_union_l in HdΠ as [A1 A2]. apply map_disjoint_union_l in Hdφ as [B1 B2].
  exists ΠΘ, φΘ, (Πv ∪ Πγ), (φv ∪ φγ). split_and!.
  - done.
  - exists Πv, Πγ, φv, φγ. split_and!; try done; by apply map_disjoint_sym.
  - by apply map_disjoint_union_r.
  - by apply map_disjoint_union_r.
  - rewrite <-!map_union_assoc. f_equal. by apply map_union_comm.
  - rewrite <-!map_union_assoc. f_equal. by apply map_union_comm.
Qed.

Lemma envf_pinst N n ρ Θ Δ g γ Π φ :
  envf N n Θ Δ g γ Π φ → envf N n (tenv_pinst ρ Θ) (lenv_pinst ρ Δ) g γ Π φ.
Proof.
  intros (ΠΘ & φΘ & Πγ & φγ & HT & HG & Hd1 & Hd2 & -> & ->).
  exists ΠΘ, φΘ, Πγ, φγ. split_and!; try done; [by apply thfuel_pinst|by apply gfuel_pinst].
Qed.

Lemma gfuel_open N n Δ i lb m C T T' : ∀ γ Π φ,
  Δ !! i = Some (Some (TEx lb m C T)) → T' = T →
  gfuel N n Δ γ Π φ → gfuel N n (<[i := Some T']> Δ) γ Π φ.
Proof.
  revert i. induction Δ as [|o Δ IH]; intros i γ Π φ Hi ->; [done|].
  destruct i as [|i]; simpl in Hi |- *.
  - injection Hi as ->. intros (Π1 & Π2 & φ1 & φ2 & Hd1 & Hd2 & -> & -> & Hv & HG).
    exists Π1, Π2, φ1, φ2. split_and!; try done. rewrite Vfuel_eq in Hv |- *. exact Hv.
  - destruct o as [U|].
    + intros (Π1 & Π2 & φ1 & φ2 & Hd1 & Hd2 & -> & -> & Hv & HG).
      exists Π1, Π2, φ1, φ2. split_and!; try done. by eapply IH.
    + by apply IH.
Qed.

Lemma gfuel_replace N n Δ i T1 T2 :
  (∀ Π φ v, v ∈ FV^N _ n⟦RTy T1⟧(Π, φ) → v ∈ FV^N _ n⟦RTy T2⟧(Π, φ)) →
  ∀ γ Π φ, gfuel N n (<[i := Some T1]> Δ) γ Π φ → gfuel N n (<[i := Some T2]> Δ) γ Π φ.
Proof.
  intros HV. revert i. induction Δ as [|o Δ IH]; intros i γ Π φ; [done|].
  destruct i as [|i]; simpl.
  - intros (Π1 & Π2 & φ1 & φ2 & Hd1 & Hd2 & -> & -> & Hv & HG).
    exists Π1, Π2, φ1, φ2. split_and!; auto.
  - destruct o as [U|]; simpl; [|apply IH].
    intros (Π1 & Π2 & φ1 & φ2 & Hd1 & Hd2 & -> & -> & Hv & HG).
    exists Π1, Π2, φ1, φ2. split_and!; auto.
Qed.

Lemma envf_open N n Θ Δ i lb m C T g γ Π φ ρ :
  Δ !! i = Some (Some (TEx lb m C T)) → envf N n Θ Δ g γ Π φ →
  envf N n (tenv_pinst ρ Θ) (<[i := Some T]> (lenv_pinst ρ Δ)) g γ Π φ.
Proof.
  intros Hi (ΠΘ & φΘ & Πγ & φγ & HT & HG & Hd1 & Hd2 & -> & ->).
  exists ΠΘ, φΘ, Πγ, φγ. split_and!; try done; [by apply thfuel_pinst|].
  assert (lenv_pinst ρ Δ !! i = Some (Some (TEx (lb_map (pt_inst ρ) lb) m (bcs_inst ρ C)
            (pinst_ty (pup m ρ) T)))) as Hi'.
  { rewrite lenv_pinst_lookup, Hi. done. }
  assert (gfuel N n (lenv_pinst ρ Δ) γ Πγ φγ) as HG' by by apply gfuel_pinst.
  pose proof (gfuel_open _ _ _ _ _ _ _ _ _ γ Πγ φγ Hi' eq_refl HG') as H.
  eapply gfuel_replace; [|exact H]. intros Π0 φ0 v Hv. by apply Vfuel_pinst in Hv.
Qed.

(** ** The ends of a grounded instance (Q15) *)

Lemma envf_exact N n Θ Δ g γ Π φ e :
  tfacts Θ Δ e → envf N n Θ Δ g γ Π φ → fends (subst γ (emap g e)) = dom Π.
Proof.
  intros (Hf & Hv1 & Hv2) (ΠΘ & φΘ & Πγ & φγ & HT & HG & Hd1 & Hd2 & -> & ->).
  destruct (gfuel_ends _ _ _ _ _ _ HG) as [A B]. pose proof HT as (_ & HΠ & _).
  rewrite dom_union_L, HΠ, <-Hf, <-fends_emap. apply fends_subst_eq.
  - intros x Hx. apply freevar_emap in Hx. destruct (Hv1 x Hx) as [σ Hσ]. exact (A x σ Hσ).
  - intros o Ho. destruct (B o Ho) as (x & T & Hx & Hu & Ho'). exists x. split; [|done].
    apply freevar_emap. by apply (Hv2 x T).
Qed.
