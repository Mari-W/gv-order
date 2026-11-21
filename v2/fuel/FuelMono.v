(** * Fuel: the clauses, downward closure, monotonicity and renaming (stage S6)

    - The clauses of FuelE at index n + 1 at the identity renaming
      ([fuel_val], [fuel_obl], F-Wait, F-Tick, the hand-over, a link's
      ticket) and the two facts adequacy reads at counter 0
      ([fuel_zero_act], [fuel_zero_nospawn]).
    - Downward closure in the index ([FuelE_down], [Vfuel_down]).
    - F4, [FuelE_mono]: FuelE is monotone in the refill N, in the
      counters ([cle]), the frame and the tickets, and antitone in the
      reserve. [Vfuel_mono] is the same for values.
    - [FuelE_rename]: closure under injective renamings of ends. *)

From GV Require Export fuel.Fuel.

(** ** Counters at or above *)

(** φ' has the ends of φ, each at a counter at least as large. *)
Definition cle (φ φ' : cenv) : Prop :=
  ∀ o, match φ !! o, φ' !! o with
       | Some f, Some f' => fle f f'
       | None, None => True
       | _, _ => False
       end.

Lemma cle_refl φ : cle φ φ.
Proof. intros o. destruct (φ !! o); [apply fle_refl|done]. Qed.

Lemma cle_dom φ φ' : cle φ φ' → dom φ = dom φ'.
Proof.
  intros H. apply set_eq. intros o. rewrite !elem_of_dom. specialize (H o).
  destruct (φ !! o), (φ' !! o); naive_solver.
Qed.

Lemma cle_lookup φ φ' o f : cle φ φ' → φ !! o = Some f → ∃ f', φ' !! o = Some f' ∧ fle f f'.
Proof. intros H Hf. specialize (H o). rewrite Hf in H. destruct (φ' !! o); naive_solver. Qed.

Lemma cle_lookup_r φ φ' o f' : cle φ φ' → φ' !! o = Some f' → ∃ f, φ !! o = Some f ∧ fle f f'.
Proof. intros H Hf. specialize (H o). rewrite Hf in H. destruct (φ !! o); naive_solver. Qed.

Lemma cle_empty_l φ' : cle ∅ φ' → φ' = ∅.
Proof.
  intros H. apply map_eq. intros o. specialize (H o). rewrite lookup_empty in H |- *.
  by destruct (φ' !! o).
Qed.

Lemma cle_insert φ φ' o f f' : fle f f' → cle φ φ' → cle (<[o := f]> φ) (<[o := f']> φ').
Proof.
  intros Hf H o'. destruct (decide (o = o')) as [<-|Hne].
  - by rewrite !lookup_insert_eq.
  - rewrite !lookup_insert_ne by done. apply H.
Qed.

Lemma cle_delete φ φ' o : cle φ φ' → cle (delete o φ) (delete o φ').
Proof.
  intros H o'. destruct (decide (o = o')) as [<-|Hne].
  - by rewrite !lookup_delete_eq.
  - rewrite !lookup_delete_ne by done. apply H.
Qed.

Lemma fle_ftick f f' : fle f f' → fle (ftick f) (ftick f').
Proof. destruct f, f'; simpl; lia. Qed.

Lemma cle_tick φ φ' : cle φ φ' → cle (ftick <$> φ) (ftick <$> φ').
Proof.
  intros H o. rewrite !lookup_fmap. specialize (H o).
  destruct (φ !! o), (φ' !! o); simpl; try done. by apply fle_ftick.
Qed.

Lemma lookup_mres {Y : Type} (X : gset cend) (m : gmap cend Y) o :
  mres X m !! o = if decide (o ∈ X) then m !! o else None.
Proof.
  destruct (mres X m !! o) as [v|] eqn:E.
  - apply lookup_mres_Some in E as [E Hx]. by rewrite decide_True.
  - case_decide as Hx; [|done]. destruct (m !! o) as [v|] eqn:E'; [|done].
    exfalso. assert (mres X m !! o = Some v) as E2 by (by apply lookup_mres_Some). congruence.
Qed.

Lemma lookup_mrem {Y : Type} (X : gset cend) (m : gmap cend Y) o :
  mrem X m !! o = if decide (o ∈ X) then None else m !! o.
Proof.
  destruct (mrem X m !! o) as [v|] eqn:E.
  - apply lookup_mrem_Some in E as [E Hx]. by rewrite decide_False.
  - case_decide as Hx; [done|]. destruct (m !! o) as [v|] eqn:E'; [|done].
    exfalso. assert (mrem X m !! o = Some v) as E2 by (by apply lookup_mrem_Some). congruence.
Qed.

Lemma cle_mres φ φ' X : cle φ φ' → cle (mres X φ) (mres X φ').
Proof. intros H o. rewrite !lookup_mres. case_decide; [apply H|done]. Qed.

Lemma cle_mrem φ φ' X : cle φ φ' → cle (mrem X φ) (mrem X φ').
Proof. intros H o. rewrite !lookup_mrem. case_decide; [done|apply H]. Qed.

Lemma cle_union φ1 φ2 φ1' φ2' : cle φ1 φ1' → cle φ2 φ2' → cle (φ1 ∪ φ2) (φ1' ∪ φ2').
Proof.
  intros H1 H2 o. rewrite !lookup_union. specialize (H1 o). specialize (H2 o).
  destruct (φ1 !! o), (φ1' !! o), (φ2 !! o), (φ2' !! o); simpl; done.
Qed.

Lemma cle_refill N o φ φ' : cle φ φ' → cle (refill N o φ) (refill N o φ').
Proof. intros H. apply cle_insert; [apply fle_refl|]. by apply cle_tick, cle_delete. Qed.

Lemma cle_fhand M φ φ' : cle φ φ' → cle (fhand M φ) (fhand M φ').
Proof. intros H. by apply cle_tick, cle_mres. Qed.

Lemma cle_cnew N c φ φ' : cle φ φ' → cle (cnew N c φ) (cnew N c φ').
Proof. intros H. apply cle_insert; [apply fle_refl|]. apply cle_insert; [apply fle_refl|done]. Qed.

Lemma map_disjoint_cle_r (m : cenv) φ φ' : cle φ φ' → m ##ₘ φ' → m ##ₘ φ.
Proof. intros H. rewrite !map_disjoint_dom. by rewrite (cle_dom φ φ' H). Qed.

(** The counters above a disjoint union split along it. *)
Lemma cle_union_split φ1 φ2 φ' :
  φ1 ##ₘ φ2 → cle (φ1 ∪ φ2) φ' →
  ∃ φ1' φ2', φ' = φ1' ∪ φ2' ∧ φ1' ##ₘ φ2' ∧ cle φ1 φ1' ∧ cle φ2 φ2'.
Proof.
  intros Hd H. exists (mres (dom φ1) φ'), (mres (dom φ2) φ').
  split_and!.
  - apply map_eq. intros o. rewrite lookup_union, !lookup_mres. specialize (H o).
    rewrite lookup_union in H.
    destruct (φ1 !! o) eqn:E1, (φ2 !! o) eqn:E2, (φ' !! o) eqn:E;
      repeat case_decide; simpl in *; try done;
      repeat match goal with
      | Hx : _ ∈ dom _ |- _ => apply elem_of_dom in Hx as [? ?]; simplify_eq
      | Hx : _ ∉ dom _ |- _ => apply not_elem_of_dom in Hx; simplify_eq
      end; try done.
    all: exfalso; by eapply (map_disjoint_spec φ1 φ2).
  - apply map_disjoint_dom. rewrite !dom_mres. apply map_disjoint_dom in Hd. set_solver.
  - intros o. specialize (H o). rewrite lookup_union in H. rewrite lookup_mres.
    destruct (φ1 !! o) eqn:E1.
    + rewrite decide_True by (by apply elem_of_dom_2 in E1).
      assert (φ2 !! o = None) as E2 by (by eapply map_disjoint_Some_l).
      by rewrite E2 in H.
    + rewrite decide_False by (by apply not_elem_of_dom). done.
  - intros o. specialize (H o). rewrite lookup_union in H. rewrite lookup_mres.
    destruct (φ2 !! o) eqn:E2.
    + rewrite decide_True by (by apply elem_of_dom_2 in E2).
      assert (φ1 !! o = None) as E1 by (by eapply map_disjoint_Some_r).
      by rewrite E1 in H.
    + rewrite decide_False by (by apply not_elem_of_dom). done.
Qed.

(** ** Renamings and counters *)

Lemma kinj_dom {Y Z : Type} (g : cend → cend) (m : gmap cend Y) (m1 : gmap cend Z) :
  dom m1 ⊆ dom m → kinj g m → kinj g m1.
Proof.
  intros Hd Hk o1 o2 v1 v2 H1 H2 Heq.
  apply elem_of_dom_2 in H1, H2. apply Hd, elem_of_dom in H1 as [w1 W1], H2 as [w2 W2].
  exact (Hk o1 o2 w1 w2 W1 W2 Heq).
Qed.

Lemma renk_exists {Y : Type} (g : cend → cend) (m : gmap cend Y) : kinj g m → ∃ m', renk g m m'.
Proof.
  induction m as [|o v m Hno IH] using map_ind; intros Hk.
  - exists ∅. split; intros ? ?; by rewrite lookup_empty.
  - destruct IH as [m' [A B]].
    { intros o1 o2 v1 v2 H1 H2 Heq. apply (Hk o1 o2 v1 v2); [| |done];
        rewrite lookup_insert_ne; [done| |done|]; intros ->; congruence. }
    exists (<[g o := v]> m'). split.
    + intros o1 v1 Ho1. destruct (decide (o1 = o)) as [->|Hne].
      * rewrite lookup_insert_eq in Ho1. simplify_eq. by rewrite lookup_insert_eq.
      * rewrite lookup_insert_ne in Ho1 by done. rewrite lookup_insert_ne; [by apply A|].
        intros Heq. apply Hne. apply (Hk o1 o v1 v);
          [by rewrite lookup_insert_ne|by rewrite lookup_insert_eq|done].
    + intros o' v' Ho'. destruct (decide (g o = o')) as [<-|Hne].
      * rewrite lookup_insert_eq in Ho'. simplify_eq. exists o.
        split; [done|by rewrite lookup_insert_eq].
      * rewrite lookup_insert_ne in Ho' by done. destruct (B o' v' Ho') as (o1 & -> & Ho1).
        exists o1. split; [done|]. rewrite lookup_insert_ne; [done|]. intros ->. congruence.
Qed.

Lemma renk_dom {Y : Type} (g : cend → cend) (m m' : gmap cend Y) :
  renk g m m' → dom m' = set_map g (dom m).
Proof.
  intros [A B]. apply set_eq. intros o'. rewrite elem_of_map. split.
  - intros [v Hv]%elem_of_dom. destruct (B o' v Hv) as (o & -> & Ho).
    exists o. split; [done|]. by apply elem_of_dom_2 in Ho.
  - intros (o & -> & [v Hv]%elem_of_dom). apply elem_of_dom. eauto.
Qed.

(** Renaming two maps above each other keeps them above each other. *)
Lemma renk_cle (g : cend → cend) φ φ' φ0 φ0' :
  kinj g φ' → cle φ φ' → renk g φ φ0 → renk g φ' φ0' → cle φ0 φ0'.
Proof.
  intros Hk H [A B] [A' B'] o'.
  destruct (φ0 !! o') as [f|] eqn:E0.
  - destruct (B o' f E0) as (o & -> & Ho).
    destruct (cle_lookup _ _ _ _ H Ho) as (f' & Hf' & Hle). by rewrite (A' o f' Hf').
  - destruct (φ0' !! o') as [f'|] eqn:E0'; [|done].
    destruct (B' o' f' E0') as (o & -> & Ho).
    destruct (cle_lookup_r _ _ _ _ H Ho) as (f & Hf & _). by rewrite (A o f Hf) in E0.
Qed.

(** ** Values: monotonicity, downward closure *)

Section vty.
  Context (El : nat → epred) (Vl : nat → vpred).

  Lemma Vty_dom N n T Π φ v : Vty N El Vl n T Π φ v → dom Π = dom φ.
  Proof.
    revert Π φ v.
    induction T as [|ub lb c t T1 IH1 U IH2 a|T1 IH1 T2 IH2|T1 IH1 T2 IH2
                   |m k C ub c t U IH|s x a|lb m C T1 IH];
      intros Π φ v; simpl.
    - intros (_ & -> & ->). by rewrite !dom_empty_L.
    - by intros (e & _ & _ & Hd & _).
    - intros (v1 & v2 & Π1 & Π2 & φ1 & φ2 & _ & _ & _ & -> & -> & H1 & H2).
      rewrite !dom_union_L. by erewrite IH1, IH2.
    - intros [(v' & _ & H)|(v' & _ & H)]; eauto.
    - intros (e & _ & _ & -> & -> & _). by rewrite !dom_empty_L.
    - intros (o & S' & f & _ & -> & -> & _). by rewrite !dom_singleton_L.
    - eauto.
  Qed.

  Lemma Vty_counters N n T Π φ φ' v :
    cle φ φ' → Vty N El Vl n T Π φ v → Vty N El Vl n T Π φ' v.
  Proof.
    revert Π φ φ' v.
    induction T as [|ub lb c t T1 IH1 U IH2 a|T1 IH1 T2 IH2|T1 IH1 T2 IH2
                   |m k C ub c t U IH|s x a|lb m C T1 IH];
      intros Π φ φ' v Hc; simpl.
    - intros (-> & -> & ->). by rewrite (cle_empty_l _ Hc).
    - intros (e & -> & Hx & Hd & Hf & H). exists e. split_and!; [done|done|by rewrite <-(cle_dom _ _ Hc)| |].
      + intros o f' Ho Hi. destruct (cle_lookup_r _ _ _ _ Hc Ho) as (f & Hf' & Hle).
        eapply fle_trans; [|exact Hle]. exact (Hf o f Hf' Hi).
      + intros N' j φ2 Πu φu u r tk HN Hj Hd2 Hh2. apply H; [done|done|by rewrite (cle_dom _ _ Hc)|].
        intros o f f2 Hf' Hf2. destruct (cle_lookup _ _ _ _ Hc Hf') as (f' & Hf'' & Hle).
        eapply fle_trans; [by apply fsub_mono_l|exact (Hh2 o f' f2 Hf'' Hf2)].
    - intros (v1 & v2 & Π1 & Π2 & φ1 & φ2 & -> & HΠ & Hφ & -> & -> & H1 & H2).
      destruct (cle_union_split _ _ _ Hφ Hc) as (φ1' & φ2' & -> & Hd' & C1 & C2).
      exists v1, v2, Π1, Π2, φ1', φ2'. split_and!; try done.
      + eapply IH1; [exact C1|exact H1].
      + eapply IH2; [exact C2|exact H2].
    - intros [(v' & -> & H)|(v' & -> & H)]; [left|right]; exists v'; split; try done.
      + eapply IH1; [exact Hc|exact H].
      + eapply IH2; [exact Hc|exact H].
    - intros (e & -> & Hx & -> & -> & H). rewrite (cle_empty_l _ Hc). exists e. by split_and!.
    - intros (o & S' & f & -> & -> & -> & Hs & Hf).
      destruct (cle_lookup _ _ o f Hc ltac:(by rewrite lookup_singleton_eq)) as (f' & Hf' & Hle).
      exists o, S', f'. split_and!; try done.
      + apply map_eq. intros o'. specialize (Hc o').
        destruct (decide (o = o')) as [<-|Hne]; [by rewrite lookup_singleton_eq|].
        rewrite lookup_singleton_ne in Hc |- * by done. by destruct (φ' !! o').
      + by eapply fle_trans.
    - intros H. eapply IH; [exact Hc|exact H].
  Qed.

  Lemma Vty_refill_mono N N1 n T Π φ v :
    rle N N1 → Vty N El Vl n T Π φ v → Vty N1 El Vl n T Π φ v.
  Proof.
    intros HN. revert Π φ v.
    induction T as [|ub lb c t T1 IH1 U IH2 a|T1 IH1 T2 IH2|T1 IH1 T2 IH2
                   |m k C ub c t U IH|s x a|lb m C T1 IH];
      intros Π φ v; simpl; try done.
    - intros (e & -> & Hx & Hd & Hf & H). exists e. split_and!; [done|done|done|done|].
      intros N' j φ' Πu φu u r tk HN'. apply H. by eapply rle_trans.
    - intros (v1 & v2 & Π1 & Π2 & φ1 & φ2 & -> & HΠ & Hφ & -> & -> & H1 & H2).
      exists v1, v2, Π1, Π2, φ1, φ2. split_and!; auto.
    - intros [(v' & -> & H)|(v' & -> & H)]; [left|right]; eauto.
    - intros (e & -> & Hx & -> & -> & H). exists e. split_and!; [done|done|done|done|].
      intros N' j ss r tk HN'. apply H. by eapply rle_trans.
    - auto.
  Qed.

  Lemma Vty_down N m n T Π φ v :
    m ≤ n → Vty N El Vl n T Π φ v → Vty N El Vl m T Π φ v.
  Proof.
    intros Hmn. revert Π φ v.
    induction T as [|ub lb c t T1 IH1 U IH2 a|T1 IH1 T2 IH2|T1 IH1 T2 IH2
                   |k0 k C ub c t U IH|s x a|lb k0 C T1 IH];
      intros Π φ v; simpl; try done.
    - intros (e & -> & Hx & Hd & Hf & H). exists e. split_and!; [done|done|done|done|].
      intros N' j φ' Πu φu u r tk HN' Hj. apply H; [done|lia].
    - intros (v1 & v2 & Π1 & Π2 & φ1 & φ2 & -> & HΠ & Hφ & -> & -> & H1 & H2).
      exists v1, v2, Π1, Π2, φ1, φ2. split_and!; auto.
    - intros [(v' & -> & H)|(v' & -> & H)]; [left|right]; eauto.
    - intros (e & -> & Hx & -> & -> & H). exists e. split_and!; [done|done|done|done|].
      intros N' j ss r tk HN' Hj. apply H; [done|lia].
    - auto.
  Qed.

  Lemma Vty_val N n T Π φ v : Vty N El Vl n T Π φ v → is_val v.
  Proof.
    revert Π φ v.
    induction T as [|ub lb c t T1 IH1 U IH2 a|T1 IH1 T2 IH2|T1 IH1 T2 IH2
                   |m k C ub c t U IH|s x a|lb m C T1 IH];
      intros Π φ v; simpl.
    - by intros (-> & _ & _).
    - by intros (e & -> & _).
    - intros (v1 & v2 & Π1 & Π2 & φ1 & φ2 & -> & _ & _ & _ & _ & H1 & H2). simpl.
      apply andb_True. split; eauto.
    - intros [(v' & -> & H)|(v' & -> & H)]; simpl; eauto.
    - by intros (e & -> & _).
    - by intros (o & S' & f & -> & _).
    - eauto.
  Qed.

  (** Q15. A value of [Vfuel] mentions exactly the ends of its map. *)
  Lemma Vty_exact N n T Π φ v : Vty N El Vl n T Π φ v → fends v = dom Π.
  Proof.
    revert Π φ v.
    induction T as [|ub lb c t T1 IH1 U IH2 a|T1 IH1 T2 IH2|T1 IH1 T2 IH2
                   |m k C ub c t U IH|s x a|lb m C T1 IH];
      intros Π φ v; simpl.
    - intros (-> & -> & _). by rewrite dom_empty_L.
    - by intros (e & -> & Hx & _).
    - intros (v1 & v2 & Π1 & Π2 & φ1 & φ2 & -> & _ & _ & -> & _ & H1 & H2). simpl.
      rewrite dom_union_L. by erewrite IH1, IH2.
    - intros [(v' & -> & H)|(v' & -> & H)]; simpl; eauto.
    - intros (e & -> & Hx & -> & _). simpl. by rewrite Hx, dom_empty_L.
    - intros (o & S' & f & -> & -> & _). simpl. by rewrite dom_singleton_L.
    - eauto.
  Qed.
End vty.

Lemma Vfuel_dom N n T Π φ v : v ∈ FV^N _ n⟦RTy T⟧(Π, φ) → dom Π = dom φ.
Proof. rewrite Vfuel_eq. apply Vty_dom. Qed.

Lemma Vfuel_val N n T Π φ v : v ∈ FV^N _ n⟦RTy T⟧(Π, φ) → is_val v.
Proof. rewrite Vfuel_eq. apply Vty_val. Qed.

Lemma Vfuel_exact N n T Π φ v : v ∈ FV^N _ n⟦RTy T⟧(Π, φ) → fends v = dom Π.
Proof. rewrite Vfuel_eq. apply Vty_exact. Qed.

(** F5, monotonicity of values: a larger refill, larger counters. *)
Lemma Vfuel_mono N N' n σ Π φ φ' v :
  rle N N' → cle φ φ' → v ∈ FV^N _ n⟦σ⟧(Π, φ) → v ∈ FV^N' _ n⟦σ⟧(Π, φ').
Proof.
  intros HN Hc. rewrite !Vfuel_eq. destruct σ as [T|]; simpl.
  - intros H. eapply Vty_refill_mono; [exact HN|]. eapply Vty_counters; [exact Hc|exact H].
  - intros [-> ->]. by rewrite (cle_empty_l _ Hc).
Qed.

Lemma Vfuel_down N m n σ Π φ v :
  m ≤ n → v ∈ FV^N _ n⟦σ⟧(Π, φ) → v ∈ FV^N _ m⟦σ⟧(Π, φ).
Proof.
  intros Hmn. rewrite !Vfuel_eq. destruct σ; simpl; [|done]. by apply Vty_down.
Qed.

(** ** The clauses at the identity *)

Section clauses.
  Context (N : fuel) (n : nat) {σ : rty} {d : fuel} {r : nat} (Π : penv) (φ : cenv)
    (tk : nat) (e : expr).
  Context (HF : e ∈ F^N _ (S n)⟦σ ▷ d ; r⟧(Π, φ, tk)).

  Local Lemma fuel_self :
    (is_val e → r ≤ tk ∧ Vres N (λ j N, FuelE N j) (λ j N, Vfuel N j) (S n) σ Π φ e) ∧
    ∀ α e', tstep e α e' → Fobl N (λ j N, FuelE N j) (λ j N, Vfuel N j) n σ d r Π φ tk α e'.
  Proof.
    apply FuelE_S in HF.
    pose proof (HF N id Π φ (rle_refl N) (kinj_id Π) (kinj_id φ) (renk_id Π) (renk_id φ)) as H.
    by rewrite emap_id in H.
  Qed.

  (** (step). *)
  Lemma fuel_obl α e' :
    tstep e α e' → Fobl N (λ j N, FuelE N j) (λ j N, Vfuel N j) n σ d r Π φ tk α e'.
  Proof. intros Hst. destruct fuel_self as [_ Hs]. by apply Hs. Qed.

  (** The end of a session action, and whether the action ticks. *)
  Definition act_end (s : slabel) : option cend :=
    match s with
    | SSend o _ | SRecv o _ | SClose o | SSel o _ | SBra o _ => Some o
    | SLink _ => None
    end.

  Lemma fuel_act s e' o :
    tstep e (LSess s) e' → act_end s = Some o →
    f_act d Π φ o.
  Proof.
    intros Hst Ho. pose proof (fuel_obl _ _ Hst) as H.
    destruct s; simpl in Ho; simplify_eq; simpl in H; by destruct H.
  Qed.

  (** F-Wait: the end of an action is held and not idle. *)
  Lemma fuel_wait s e' o :
    tstep e (LSess s) e' → act_end s = Some o → ¬ idle_at Π o ∧ o ∈ dom φ.
  Proof. intros Hst Ho. by destruct (fuel_act s e' o Hst Ho) as (H1 & H2 & _). Qed.

  (** F-Tick: every other end that is not idle has a unit to spare. *)
  Lemma fuel_tick s e' o :
    tstep e (LSess s) e' → act_end s = Some o → fspare Π φ (dom φ ∖ {[o]}).
  Proof. intros Hst Ho. by destruct (fuel_act s e' o Hst Ho) as (_ & _ & H & _). Qed.

  (** A spawn hands on held ends with a unit to spare. *)
  Lemma fuel_spawn_hand v e' : tstep e (LSpawn v) e' → fends v ⊆ dom φ ∧ fspare Π φ (fends v).
  Proof. intros Hst. by pose proof (fuel_obl _ _ Hst) as (H1 & H2 & _). Qed.

  (** A link needs a ticket. *)
  Lemma fuel_link os e' : tstep e (LSess (SLink os)) e' → 1 ≤ tk ∧ os ⊆ dom φ.
  Proof. intros Hst. by pose proof (fuel_obl _ _ Hst) as (_ & H1 & H2 & _). Qed.

  (** ** At counter 0 *)

End clauses.

(** ** Downward closure in the index *)

Lemma FuelE_S_down N n σ d r Π φ tk e :
  e ∈ F^N _ (S n)⟦σ ▷ d ; r⟧(Π, φ, tk) → e ∈ F^N _ n⟦σ ▷ d ; r⟧(Π, φ, tk).
Proof.
  revert N σ d r Π φ tk e. induction n as [|n IH]; intros N σ d r Π φ tk e H; [apply FuelE_0|].
  apply FuelE_S. apply FuelE_S in H. intros N' g Π' φ' HN Hk1 Hk2 Hr1 Hr2.
  destruct (H N' g Π' φ' HN Hk1 Hk2 Hr1 Hr2) as [Hv Hs]. split.
  { intros Hval. destruct (Hv Hval) as [Hr HV]. split; [done|].
    apply Vfuel_eq. apply (Vfuel_down _ (S n) (S (S n))); [lia|]. by apply Vfuel_eq. }
  intros α e' Hst. specialize (Hs α e' Hst).
  destruct α as [|ℓ c|κ o c|v|[o w|o w|o|o i|o i|os]]; simpl in Hs |- *;
    unfold f_beta, f_new, f_spawn, f_send, f_recv, f_close, f_select, f_branch, f_link in *.
  - by apply IH.
  - intros Hf. destruct (Hs Hf) as [Sn HS]. exists Sn. by apply IH.
  - intros Hf. destruct (Hs Hf) as [Sn HS]. exists Sn. by apply IH.
  - destruct Hs as (H1 & H2 & H3 & H4). split_and!; auto.
  - destruct Hs as (Ha & S0 & m & T & Sc & H1 & H2 & H3 & H4 & H5 & H6).
    split; [done|]. exists S0, m, T, Sc. split_and!; auto. by apply (Vfuel_down _ n (S n)); [lia|].
  - destruct Hs as (Ha & S0 & m & T & Sc & H1 & H2 & H3).
    split; [done|]. exists S0, m, T, Sc. split_and!; [done|done|].
    intros j Πi φi Hj. apply H3. lia.
  - destruct Hs as (Ha & S0 & H1 & H2 & H3). split; [done|]. exists S0. split_and!; auto.
  - destruct Hs as (Ha & S0 & S1 & S2 & H1 & H2 & H3). split; [done|]. exists S0, S1, S2. split_and!; auto.
  - destruct Hs as (Ha & S0 & S1 & S2 & H1 & H2 & H3). split; [done|]. exists S0, S1, S2. split_and!; auto.
  - destruct Hs as (H0 & H1 & H2 & H3). split_and!; auto.
Qed.

Lemma FuelE_down N m n σ d r Π φ tk e :
  m ≤ n → e ∈ F^N _ n⟦σ ▷ d ; r⟧(Π, φ, tk) → e ∈ F^N _ m⟦σ ▷ d ; r⟧(Π, φ, tk).
Proof. induction 1; eauto using FuelE_S_down. Qed.

(** ** F4: monotonicity *)

Lemma div2_mono a b : a ≤ b → Nat.div2 a ≤ Nat.div2 b.
Proof. intros H. rewrite !Nat.div2_div. by apply Nat.Div0.div_le_mono. Qed.

Lemma fspare_mono Π φ φ' X : cle φ φ' → fspare Π φ X → fspare Π φ' X.
Proof.
  intros Hc H o f' Ho Hf' Hi. destruct (cle_lookup_r _ _ _ _ Hc Hf') as (f & Hf & Hle).
  eapply fle_trans; [|exact Hle]. by apply (H o).
Qed.

Lemma ffresh_cle c Π φ φ' : cle φ φ' → ffresh c Π φ' → ffresh c Π φ.
Proof. intros Hc. unfold ffresh. by rewrite (cle_dom _ _ Hc). Qed.

(** FuelE^N is monotone in the refill N and the counters, the frame and
    the tickets, and antitone in the reserve. More counters never hurt,
    because every check asks a lower bound (G3). *)
Lemma FuelE_mono n : ∀ N N' σ d d' r r' Π φ φ' tk tk' e,
  rle N N' → cle φ φ' → fle d d' → r' ≤ r → tk ≤ tk' →
  e ∈ F^N _ n⟦σ ▷ d ; r⟧(Π, φ, tk) → e ∈ F^N' _ n⟦σ ▷ d' ; r'⟧(Π, φ', tk').
Proof.
  induction n as [n IH] using lt_wf_ind.
  intros N N1 σ d d' r r' Π φ φ1 tk tk' e HN Hc Hd Hr Htk H.
  destruct n as [|n]; [apply FuelE_0|].
  apply FuelE_S. apply FuelE_S in H. intros N' g Π' φ' HN' Hk1 Hk2 Hr1 Hr2.
  assert (Hkφ : kinj g φ) by (apply (kinj_dom g φ1); [by rewrite (cle_dom _ _ Hc)|done]).
  destruct (renk_exists g φ Hkφ) as [φ0 Hr0].
  assert (Hc0 : cle φ0 φ') by exact (renk_cle g φ φ1 φ0 φ' Hk2 Hc Hr0 Hr2).
  destruct (H N' g Π' φ0 ltac:(by eapply rle_trans) Hk1 Hkφ Hr1 Hr0) as [Hv Hs].
  assert (IHn : ∀ j, j ≤ n → ∀ N σ d d' r r' Π φ φ' tk tk' e,
    fle d d' → r' ≤ r → tk ≤ tk' → cle φ φ' →
    e ∈ F^N _ j⟦σ ▷ d ; r⟧(Π, φ, tk) → e ∈ F^N _ j⟦σ ▷ d' ; r'⟧(Π, φ', tk')).
  { intros j Hj N0 σ0 d0 d0' r0 r0' Π0 φ2 φ2' tk0 tk0' e0 H1 H2 H3 H4.
    apply (IH j ltac:(lia)); [apply rle_refl|done..]. }
  split.
  { intros Hval. destruct (Hv Hval) as [Hr0' HV]. split; [lia|].
    apply Vfuel_eq. eapply Vfuel_mono; [apply rle_refl|exact Hc0|]. by apply Vfuel_eq. }
  intros α e' Hst. specialize (Hs α e' Hst).
  assert (Hdd := fle_ftick _ _ Hd).
  assert (Hact : ∀ o, f_act d Π' φ0 o → f_act d' Π' φ' o).
  { intros o (H1 & H2 & H3 & H4). split_and!; [done|by rewrite <-(cle_dom _ _ Hc0)| |by eapply fle_trans].
    rewrite <-(cle_dom _ _ Hc0). by eapply fspare_mono. }
  destruct α as [|ℓ c|κ o c|v|[o w|o w|o|o i|o i|os]]; simpl in Hs |- *;
    unfold f_beta, f_new, f_spawn, f_send, f_recv, f_close, f_select, f_branch, f_link in *.
  - eapply IHn; [lia|done..].
  - intros Hf. destruct (Hs (ffresh_cle _ _ _ _ Hc0 Hf)) as [Sn HS]. exists Sn.
    eapply IHn; [lia|done|done|done|by apply cle_cnew|done].
  - intros Hf. destruct (Hs (ffresh_cle _ _ _ _ Hc0 Hf)) as [Sn HS]. exists Sn.
    eapply IHn; [lia|done|done|done|by apply cle_cnew|done].
  - destruct Hs as (H1 & H2 & H3 & H4). split_and!.
    + by rewrite <-(cle_dom _ _ Hc0).
    + by eapply fspare_mono.
    + eapply IHn; [lia|apply fle_refl|lia| |by apply cle_fhand|exact H3].
      apply (div2_mono (S tk) (S tk')). lia.
    + eapply IHn; [lia|done|done|by apply div2_mono|by apply cle_mrem|exact H4].
  - destruct Hs as (Ha & S0 & m & T & Sc & H1 & H2 & H3 & H4 & H5 & H6).
    split; [by apply Hact|]. exists S0, m, T, Sc. split_and!; try done.
    + by rewrite <-(cle_dom _ _ Hc0).
    + by eapply fspare_mono.
    + eapply Vfuel_mono; [apply rle_refl|by apply cle_fhand|exact H5].
    + eapply IHn; [lia|done|done|done|by apply cle_refill, cle_mrem|exact H6].
  - destruct Hs as (Ha & S0 & m & T & Sc & H1 & H2 & H3).
    split; [by apply Hact|]. exists S0, m, T, Sc. split_and!; [done|done|].
    intros j Πi φi Hj HΠi Hφi Hw.
    eapply IHn; [lia|done|done|done| |].
    + apply cle_union; [by apply cle_refill|apply cle_refl].
    + apply H3; try done. eapply map_disjoint_cle_r; [|exact Hφi]. by apply cle_refill.
  - destruct Hs as (Ha & S0 & H1 & H2 & H3). split; [by apply Hact|]. exists S0. split_and!; try done.
    eapply IHn; [lia|done|done|done|by apply cle_tick, cle_delete|exact H3].
  - destruct Hs as (Ha & S0 & S1 & S2 & H1 & H2 & H3). split; [by apply Hact|].
    exists S0, S1, S2. split_and!; try done.
    eapply IHn; [lia|done|done|done|by apply cle_refill|exact H3].
  - destruct Hs as (Ha & S0 & S1 & S2 & H1 & H2 & H3). split; [by apply Hact|].
    exists S0, S1, S2. split_and!; try done.
    eapply IHn; [lia|done|done|done|by apply cle_refill|exact H3].
  - destruct Hs as (H0 & H1 & H2 & H3). split_and!; [done| | |].
    + by rewrite <-(cle_dom _ _ Hc0).
    + lia.
    + eapply (IHn n); [lia|exact Hd|exact Hr| |by apply cle_mrem|exact H3]. lia.
Qed.

Lemma FuelE_refill_mono N N' n σ d r Π φ tk e :
  rle N N' → e ∈ F^N _ n⟦σ ▷ d ; r⟧(Π, φ, tk) → e ∈ F^N' _ n⟦σ ▷ d ; r⟧(Π, φ, tk).
Proof. intros HN. apply FuelE_mono; [done|apply cle_refl|apply fle_refl|lia|lia]. Qed.

Lemma FuelE_frame_mono N n σ d d' r Π φ tk e :
  fle d d' → e ∈ F^N _ n⟦σ ▷ d ; r⟧(Π, φ, tk) → e ∈ F^N _ n⟦σ ▷ d' ; r⟧(Π, φ, tk).
Proof. intros Hd. apply FuelE_mono; [apply rle_refl|apply cle_refl|done|lia|lia]. Qed.

(** ** Renaming of ends (a link renames the partner of its removed end) *)

Lemma FuelE_rename N n σ d r Π φ tk e (h : cend → cend) Π1 φ1 :
  kinj h Π → kinj h φ → renk h Π Π1 → renk h φ φ1 →
  e ∈ F^N _ n⟦σ ▷ d ; r⟧(Π, φ, tk) → emap h e ∈ F^N _ n⟦σ ▷ d ; r⟧(Π1, φ1, tk).
Proof.
  destruct n as [|n]; [intros; apply FuelE_0|]. rewrite !FuelE_S.
  intros Hi1 Hi2 H1 H2 HF N' g Π' φ' HN Hg1 Hg2 G1 G2. rewrite emap_emap.
  apply HF; [done| | |eapply renk_compose; eauto|eapply renk_compose; eauto].
  - by apply (kinj_compose g h Π Π1).
  - by apply (kinj_compose g h φ φ1).
Qed.
