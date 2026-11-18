(** * Fuel: the bind lemma (stage S6, F1)

    A hole e runs in an evaluation context K. The hole holds Π1, φ1 and
    the context ΠK, φK, apart from the hole's. The hole has frame c1: it
    acts at most c1 times before it returns. Each action of the hole
    ticks the context's counters ([kupd]) and spends a unit of the
    composite's frame d, so the counters of the context's ends that are
    not idle must be at least c1 ([fabove]). The continuation ([fkont])
    holds after any i ≤ c1 actions of the hole, for every value the hole
    returns at its result type σ1 with reserve r1, at every refill
    N′ ≥ N and under every injective renaming of the context, because
    FuelE quantifies over both. Tickets flow unchanged, the child of a
    spawn is the hole's child, and a receive adds ends to the hole. *)

From GV Require Export fuel.FuelValues.

(** ** Maps along unions *)

Lemma mres_union_l {Y : Type} (X : gset cend) (m1 m2 : gmap cend Y) :
  X ## dom m2 → mres X (m1 ∪ m2) = mres X m1.
Proof.
  intros Hd. apply map_eq. intros o. rewrite !lookup_mres, lookup_union.
  case_decide as Ho; [|done]. assert (m2 !! o = None) as -> by (apply not_elem_of_dom; set_solver).
  by destruct (m1 !! o).
Qed.

Lemma mrem_union_l {Y : Type} (X : gset cend) (m1 m2 : gmap cend Y) :
  X ## dom m2 → mrem X (m1 ∪ m2) = mrem X m1 ∪ m2.
Proof.
  intros Hd. apply map_eq. intros o. rewrite lookup_union, !lookup_mrem, lookup_union.
  case_decide as Ho; [|done]. assert (m2 !! o = None) as -> by (apply not_elem_of_dom; set_solver).
  done.
Qed.

Lemma delete_union_l {Y : Type} o (m1 m2 : gmap cend Y) :
  o ∉ dom m2 → delete o (m1 ∪ m2) = delete o m1 ∪ m2.
Proof. intros Hd. rewrite delete_union. f_equal. apply delete_id. by apply not_elem_of_dom. Qed.

Lemma refill_union N o (φ1 φK : cenv) :
  o ∉ dom φK → refill N o (φ1 ∪ φK) = refill N o φ1 ∪ (ftick <$> φK).
Proof.
  intros Ho. unfold refill. rewrite delete_union_l by done.
  by rewrite map_fmap_union, insert_union_l.
Qed.

Lemma dom_refill N o (φ : cenv) : dom (refill N o φ) = {[o]} ∪ dom φ.
Proof.
  unfold refill. rewrite dom_insert_L, dom_fmap_L, dom_delete_L.
  apply set_eq. intros o'. destruct (decide (o' = o)); set_solver.
Qed.

Lemma union_swap {Y : Type} (m1 m2 m3 : gmap cend Y) : m2 ##ₘ m3 → (m1 ∪ m2) ∪ m3 = (m1 ∪ m3) ∪ m2.
Proof. intros Hd. rewrite <-!(assoc_L (∪)). f_equal. by apply map_union_comm. Qed.

Lemma lookup_union_l' {Y : Type} (m1 m2 : gmap cend Y) o : o ∉ dom m2 → (m1 ∪ m2) !! o = m1 !! o.
Proof.
  intros Ho. rewrite lookup_union. apply not_elem_of_dom in Ho. rewrite Ho. by destruct (m1 !! o).
Qed.

Lemma lookup_union_r' {Y : Type} (m1 m2 : gmap cend Y) o : o ∉ dom m1 → (m1 ∪ m2) !! o = m2 !! o.
Proof.
  intros Ho. rewrite lookup_union. apply not_elem_of_dom in Ho. rewrite Ho. by destruct (m2 !! o).
Qed.

Lemma idle_at_union_l Π1 ΠK o : o ∉ dom ΠK → idle_at (Π1 ∪ ΠK) o ↔ idle_at Π1 o.
Proof. intros Ho. unfold idle_at. by rewrite lookup_union_l'. Qed.

Lemma idle_at_union_r Π1 ΠK o : o ∉ dom Π1 → idle_at (Π1 ∪ ΠK) o ↔ idle_at ΠK o.
Proof. intros Ho. unfold idle_at. by rewrite lookup_union_r'. Qed.

(** ** Actions and the context's update *)

(** The frame and the context's counters after a step of the hole: an
    action spends one unit of each. *)
Definition is_act (α : tlabel) : Prop :=
  match α with LSess s => act_end s ≠ None | _ => False end.

Definition dupd (d : fuel) (α : tlabel) : fuel :=
  match α with LSess s => match act_end s with Some _ => ftick d | None => d end | _ => d end.

Definition kupd (α : tlabel) (φ : cenv) : cenv :=
  match α with LSess s => match act_end s with Some _ => ftick <$> φ | None => φ end | _ => φ end.

(** The counters of the context's ends that are not idle: each at least c. *)
Definition fabove (c : fuel) (Π : penv) (φ : cenv) : Prop :=
  ∀ o f, φ !! o = Some f → ¬ idle_at Π o → fle c f.

Lemma dom_kupd α φ : dom (kupd α φ) = dom φ.
Proof. destruct α as [| | | |s]; simpl; try done. destruct (act_end s); [apply dom_fmap_L|done]. Qed.

Lemma fabove_kupd c Π φ α : fabove c Π φ → fabove (dupd c α) Π (kupd α φ).
Proof.
  intros H. destruct α as [| | | |s]; simpl; try done. destruct (act_end s); [|done].
  intros o f Ho Hi. apply lookup_fmap_Some in Ho as (f0 & <- & Ho). apply fle_ftick. by apply (H o).
Qed.

Lemma fle_dupd c d α : fle c d → fle (dupd c α) (dupd d α).
Proof. intros H. destruct α as [| | | |s]; simpl; try done. destruct (act_end s); [by apply fle_ftick|done]. Qed.

Lemma fabove_rename c Π φ (g : cend → cend) Π' φ' :
  kinj g Π → renk g Π Π' → renk g φ φ' → dom Π = dom φ → fabove c Π φ → fabove c Π' φ'.
Proof.
  intros Hk HΠ Hφ Hd H o' f Ho' Hi. destruct (proj2 Hφ o' f Ho') as (o & -> & Ho).
  apply (H o f Ho). intros (S & HS & Hid). apply Hi. exists S. split; [|done]. by apply HΠ.
Qed.

Lemma fminus_0_map (m : cenv) : fminus (Some 0) <$> m = m.
Proof.
  rewrite <-(map_fmap_id m) at 2. apply map_fmap_ext. intros o f _. unfold fminus.
  destruct f; simpl; [f_equal; lia|done].
Qed.

Lemma fsub_0 d : fsub d (Some 0) = d.
Proof. destruct d; simpl; [f_equal; lia|done]. Qed.

Lemma fminus_tick i f : fminus (Some i) (ftick f) = fminus (Some (S i)) f.
Proof. unfold fminus, ftick. destruct f; simpl; [f_equal; lia|done]. Qed.

(** ** The continuation

    After i ≤ c1 actions of the hole, for every value v the hole returns
    at σ1 with protocols Π1 and counters φ1, at every level j ≤ n, every
    ticket count that holds the reserve r1, every refill N′ ≥ N and every
    injective renaming of the context. *)
Definition fkont (n : nat) (N : fuel) (σ1 : rty) (r1 : nat) (σ : rty) (r : nat) (c1 d : fuel)
    (ΠK : penv) (φK : cenv) (K : ectx) : Prop :=
  ∀ N' (g : cend → cend) ΠK' φK' i j v Π1 φ1 tk,
    rle N N' → kinj g ΠK → kinj g φK → renk g ΠK ΠK' → renk g φK φK' →
    fle (Some i) c1 → j ≤ n → is_val v → r1 ≤ tk →
    Π1 ##ₘ ΠK' → φ1 ##ₘ φK' → v ∈ FV^N' _ j⟦σ1⟧(Π1, φ1) →
    efill (kemap g K) v ∈ F^N' _ j⟦σ ▷ fsub d (Some i) ; r⟧(Π1 ∪ ΠK', φ1 ∪ (fminus (Some i) <$> φK'), tk).

Lemma fkont_down m n N σ1 r1 σ r c1 d ΠK φK K :
  m ≤ n → fkont n N σ1 r1 σ r c1 d ΠK φK K → fkont m N σ1 r1 σ r c1 d ΠK φK K.
Proof. intros Hmn H N' g ΠK' φK' i j v Π1 φ1 tk HN Hk1 Hk2 H1 H2 Hi Hj. apply H; try done. lia. Qed.

Lemma fkont_rename n N σ1 r1 σ r c1 d ΠK φK K N0 (g : cend → cend) ΠK0 φK0 :
  rle N N0 → kinj g ΠK → kinj g φK → renk g ΠK ΠK0 → renk g φK φK0 →
  fkont n N σ1 r1 σ r c1 d ΠK φK K → fkont n N0 σ1 r1 σ r c1 d ΠK0 φK0 (kemap g K).
Proof.
  intros HN Hk1 Hk2 HΠ Hφ H N' g' ΠK' φK' i j v Π1 φ1 tk HN' Hk1' Hk2' HΠ' Hφ'.
  rewrite kemap_kemap. apply (H N' (g' ∘ g) ΠK' φK').
  - by eapply rle_trans.
  - by apply (kinj_compose g' g ΠK ΠK0).
  - by apply (kinj_compose g' g φK φK0).
  - by apply (renk_compose g' g ΠK ΠK0 ΠK').
  - by apply (renk_compose g' g φK φK0 φK').
Qed.

Lemma fkont_tick n N σ1 r1 σ r c1 d ΠK φK K :
  fle (Some 1) c1 →
  fkont n N σ1 r1 σ r c1 d ΠK φK K → fkont n N σ1 r1 σ r (ftick c1) (ftick d) ΠK (ftick <$> φK) K.
Proof.
  intros H1 H N' g ΠK' φK'' i j v Π1 φ1 tk HN Hk1 Hk2 HΠ Hφ Hi.
  assert (kinj g φK) as HkK by (apply (kinj_dom g (ftick <$> φK)); [by rewrite dom_fmap_L|done]).
  destruct (renk_exists g φK HkK) as [φK' HφK].
  assert (φK'' = ftick <$> φK') as -> by (eapply renk_functional; [exact Hφ|by apply renk_fmap]).
  assert (Heq : fminus (Some i) <$> (ftick <$> φK') = fminus (Some (S i)) <$> φK').
  { rewrite <-map_fmap_compose. apply map_fmap_ext. intros o f _. apply fminus_tick. }
  assert (Hd : fsub (ftick d) (Some i) = fsub d (Some (S i))) by apply fminus_tick.
  intros Hj Hv Hr HdΠ Hdφ HV. rewrite Heq, Hd.
  apply (H N' g ΠK' φK' (S i)); try done.
  - destruct c1; simpl in *; lia.
  - by rewrite map_disjoint_dom, dom_fmap_L, <-map_disjoint_dom in Hdφ.
Qed.

Lemma fkont_upd n N σ1 r1 σ r c1 d ΠK φK K α :
  (is_act α → fle (Some 1) c1) →
  fkont n N σ1 r1 σ r c1 d ΠK φK K → fkont n N σ1 r1 σ r (dupd c1 α) (dupd d α) ΠK (kupd α φK) K.
Proof.
  intros H1 H. destruct α as [| | | |s]; simpl; try done.
  destruct (act_end s) as [o|] eqn:E; [|done]. apply fkont_tick; [|done].
  apply H1. simpl. by rewrite E.
Qed.

(** ** One step of the hole is one step of the composite *)

Section obl_bind.
  Context (n : nat) (N : fuel) (σ1 σ : rty) (r1 r : nat) (Π1 ΠK : penv) (φ1 φK : cenv)
    (tk : nat) (c1 d : fuel) (K : ectx).
  Context (HdΠ1 : dom Π1 = dom φ1) (HdΠK : dom ΠK = dom φK) (Hd : dom φ1 ## dom φK)
    (Hab : fabove c1 ΠK φK) (Hcd : fle c1 d).

  Let El := (λ j N, FuelE N j).
  Let Vl := (λ j N, Vfuel N j).

  Lemma not_in_K o : o ∈ dom φ1 → (o ∉ dom ΠK) ∧ (o ∉ dom φK).
  Proof. intros Ho. rewrite HdΠK. set_solver. Qed.

  Lemma f_act_bind o : f_act c1 Π1 φ1 o → f_act d (Π1 ∪ ΠK) (φ1 ∪ φK) o.
  Proof.
    intros (Hi & Ho & Hs & H1). destruct (not_in_K o Ho) as [HoΠ HoK].
    split_and!.
    - by rewrite idle_at_union_l.
    - rewrite dom_union_L. set_solver.
    - intros o' f Ho' Hf Hi'. rewrite dom_union_L in Ho'.
      apply lookup_union_Some_raw in Hf as [Hf|[Hn Hf]].
      + apply (Hs o' f); [apply elem_of_difference; split; [by eapply elem_of_dom_2|set_solver]|done|].
        intros Hi2. apply Hi'. apply idle_at_union_l; [|done].
        rewrite HdΠK. apply elem_of_dom_2 in Hf. set_solver.
      + eapply fle_trans; [exact H1|]. apply (Hab o' f Hf). intros Hi2. apply Hi'.
        apply idle_at_union_r; [|done]. rewrite HdΠ1. by apply not_elem_of_dom.
    - by eapply fle_trans.
  Qed.

  Lemma fspare_bind M : M ⊆ dom φ1 → fspare Π1 φ1 M → fspare (Π1 ∪ ΠK) (φ1 ∪ φK) M.
  Proof.
    intros HM Hs o f Ho Hf Hi. assert (o ∈ dom φ1) as Ho1 by set_solver.
    destruct (not_in_K o Ho1) as [HoΠ HoK]. rewrite lookup_union_l' in Hf by done.
    apply (Hs o f Ho Hf). intros Hi2. apply Hi. by apply idle_at_union_l.
  Qed.

  Context (Hcont : ∀ α j tk' Πh φh e3, j ≤ n → dom Πh = dom φh → dom φh ## dom φK →
     (is_act α → fle (Some 1) c1) →
     e3 ∈ F^N _ j⟦σ1 ▷ dupd c1 α ; r1⟧(Πh, φh, tk') →
     efill K e3 ∈ F^N _ j⟦σ ▷ dupd d α ; r⟧(Πh ∪ ΠK, φh ∪ kupd α φK, tk')).

  Lemma Fobl_bind α e3 :
    Fobl N El Vl n σ1 c1 r1 Π1 φ1 tk α e3 →
    Fobl N El Vl n σ d r (Π1 ∪ ΠK) (φ1 ∪ φK) tk α (efill K e3).
  Proof.
    unfold El, Vl.
    destruct α as [|ℓ c|κ o0 c|v|[o w|o w|o|o i|o i|os]]; simpl;
      unfold f_beta, f_new, f_spawn, f_send, f_recv, f_close, f_select, f_branch, f_link.
    - intros H. apply (Hcont LBeta n tk Π1 φ1 e3); [lia|done|done|by intros []|exact H].
    - intros H Hf. destruct H as [S HS].
      { destruct Hf as (H1 & H2 & H3 & H4). rewrite dom_union_L in *. unfold ffresh. set_solver. }
      exists S. destruct Hf as (H1 & H2 & H3 & H4). rewrite !dom_union_L in *.
      pose proof (Hcont (LNew ℓ c) n tk (pnew c S Π1) (cnew N c φ1) e3 ltac:(lia)) as HC.
      unfold pnew, cnew in *. rewrite !insert_union_l. apply HC; [| |by intros []|exact HS].
      + rewrite !dom_insert_L. set_solver.
      + rewrite !dom_insert_L. set_solver.
    - intros H Hf. destruct H as [S HS].
      { destruct Hf as (H1 & H2 & H3 & H4). rewrite dom_union_L in *. unfold ffresh. set_solver. }
      exists S. destruct Hf as (H1 & H2 & H3 & H4). rewrite !dom_union_L in *.
      pose proof (Hcont (LNewAt κ o0 c) n tk (pnew c S Π1) (cnew N c φ1) e3 ltac:(lia)) as HC.
      unfold pnew, cnew in *. rewrite !insert_union_l. apply HC; [| |by intros []|exact HS].
      + rewrite !dom_insert_L. set_solver.
      + rewrite !dom_insert_L. set_solver.
    - intros (HM & Hs & Hch & Hpar). assert (HMK : fends v ## dom φK) by set_solver.
      split_and!.
      + rewrite dom_union_L. set_solver.
      + by apply fspare_bind.
      + unfold fhand. rewrite mres_union_l, (mres_union_l _ φ1) by (rewrite ?HdΠK; done). exact Hch.
      + rewrite mrem_union_l, (mrem_union_l _ φ1) by (rewrite ?HdΠK; done).
        apply (Hcont (LSpawn v) n); [lia| | |by intros []|exact Hpar].
        * by rewrite !dom_mrem, HdΠ1.
        * rewrite dom_mrem. set_solver.
    - intros (Ha & S0 & m & T & b & Sc & H1 & H2 & H3 & H4 & H5 & H6).
      assert (Ho : o ∈ dom φ1) by (by destruct Ha as (_ & Ho & _)).
      destruct (not_in_K o Ho) as [HoΠ HoK]. assert (HMK : fends w ## dom φK) by set_solver.
      split; [by apply f_act_bind|]. exists S0, m, T, b, Sc. split_and!.
      + by rewrite lookup_union_l'.
      + done.
      + rewrite dom_union_L. set_solver.
      + apply fspare_bind; [set_solver|done].
      + unfold fhand. rewrite mres_union_l, (mres_union_l _ φ1) by (rewrite ?HdΠK; done). exact H5.
      + rewrite mrem_union_l, (mrem_union_l _ φ1) by (rewrite ?HdΠK; done).
        rewrite refill_union by done. rewrite insert_union_l.
        apply (Hcont (LSess (SSend o w)) n); [lia| | | |exact H6].
        * rewrite dom_insert_L, dom_refill, !dom_mrem, HdΠ1. done.
        * rewrite dom_refill, dom_mrem. set_solver.
        * intros _. by destruct Ha as (_ & _ & _ & ?).
    - intros (Ha & S0 & m & T & b & Sc & H1 & H2 & H3).
      assert (Ho : o ∈ dom φ1) by (by destruct Ha as (_ & Ho & _)).
      destruct (not_in_K o Ho) as [HoΠ HoK].
      split; [by apply f_act_bind|]. exists S0, m, T, b, Sc.
      split_and!; [by rewrite lookup_union_l'|done|].
      intros j Πi φi Hj HΠi Hφi Hw.
      rewrite insert_union_l in HΠi |- *. rewrite refill_union in Hφi |- * by done.
      apply map_disjoint_union_r in HΠi as [HΠi1 HΠiK].
      apply map_disjoint_union_r in Hφi as [Hφi1 HφiK].
      rewrite (union_swap _ ΠK Πi), (union_swap _ (ftick <$> φK) φi) by (by apply map_disjoint_sym).
      assert (HdΠi := Vfuel_dom _ _ _ _ _ _ _ Hw).
      apply (Hcont (LSess (SRecv o w)) j); [lia| | | |by apply H3].
      + rewrite !dom_union_L, dom_insert_L, dom_refill, HdΠ1, HdΠi. done.
      + apply map_disjoint_dom in HφiK. rewrite dom_fmap_L in HφiK.
        rewrite dom_union_L, dom_refill. set_solver.
      + intros _. by destruct Ha as (_ & _ & _ & ?).
    - intros (Ha & S0 & H1 & H2 & H3).
      assert (Ho : o ∈ dom φ1) by (by destruct Ha as (_ & Ho & _)).
      destruct (not_in_K o Ho) as [HoΠ HoK].
      split; [by apply f_act_bind|]. exists S0. split_and!; [by rewrite lookup_union_l'|done|].
      rewrite delete_union_l, (delete_union_l o φ1) by done. rewrite map_fmap_union.
      apply (Hcont (LSess (SClose o)) n); [lia| | | |exact H3].
      + by rewrite dom_fmap_L, !dom_delete_L, HdΠ1.
      + rewrite dom_fmap_L, dom_delete_L. set_solver.
      + intros _. by destruct Ha as (_ & _ & _ & ?).
    - intros (Ha & S0 & S1 & S2 & H1 & H2 & H3).
      assert (Ho : o ∈ dom φ1) by (by destruct Ha as (_ & Ho & _)).
      destruct (not_in_K o Ho) as [HoΠ HoK].
      split; [by apply f_act_bind|]. exists S0, S1, S2. split_and!; [by rewrite lookup_union_l'|done|].
      rewrite insert_union_l, refill_union by done.
      apply (Hcont (LSess (SSel o i)) n); [lia| | | |exact H3].
      + rewrite dom_insert_L, dom_refill, HdΠ1. done.
      + rewrite dom_refill. set_solver.
      + intros _. by destruct Ha as (_ & _ & _ & ?).
    - intros (Ha & S0 & S1 & S2 & H1 & H2 & H3).
      assert (Ho : o ∈ dom φ1) by (by destruct Ha as (_ & Ho & _)).
      destruct (not_in_K o Ho) as [HoΠ HoK].
      split; [by apply f_act_bind|]. exists S0, S1, S2. split_and!; [by rewrite lookup_union_l'|done|].
      rewrite insert_union_l, refill_union by done.
      apply (Hcont (LSess (SBra o i)) n); [lia| | | |exact H3].
      + rewrite dom_insert_L, dom_refill, HdΠ1. done.
      + rewrite dom_refill. set_solver.
      + intros _. by destruct Ha as (_ & _ & _ & ?).
    - intros (Hpl & Hos & Htk & H3). assert (HoK : os ## dom φK) by set_solver.
      split_and!; [|rewrite dom_union_L; set_solver|done|].
      { destruct Hpl as (o1 & o2 & S1 & S2 & -> & Hne & H1 & H2 & Hdu).
        exists o1, o2, S1, S2. split_and!; [done|done|by apply lookup_union_Some_l|
          by apply lookup_union_Some_l|done]. }
      rewrite mrem_union_l, (mrem_union_l _ φ1) by (rewrite ?HdΠK; done).
      apply (Hcont (LSess (SLink os)) n); [lia| | |intros H; exfalso; by apply H|exact H3].
      + by rewrite !dom_mrem, HdΠ1.
      + rewrite dom_mrem. set_solver.
  Qed.
End obl_bind.

Lemma kemap_id K : kemap id K = K.
Proof. induction K as [|f K IH]; simpl; [done|]. rewrite IH. f_equal. destruct f; simpl; by rewrite ?emap_id. Qed.

(** F1. A hole whose result, after any number i ≤ c1 of its actions,
    the context continues, runs in the context. *)
Lemma FuelE_bind n : ∀ N σ1 r1 σ r Π1 φ1 ΠK φK tk c1 d K e,
  ectx_ok K → dom Π1 = dom φ1 → dom ΠK = dom φK → dom φ1 ## dom φK →
  fabove c1 ΠK φK → fle c1 d →
  fkont n N σ1 r1 σ r c1 d ΠK φK K →
  e ∈ F^N _ n⟦σ1 ▷ c1 ; r1⟧(Π1, φ1, tk) →
  efill K e ∈ F^N _ n⟦σ ▷ d ; r⟧(Π1 ∪ ΠK, φ1 ∪ φK, tk).
Proof.
  induction n as [n IH] using lt_wf_ind.
  intros N σ1 r1 σ r Π1 φ1 ΠK φK tk c1 d K e HK HdΠ1 HdΠK Hd Hab Hcd Hkont HF.
  destruct n as [|n]; [apply FuelE_0|].
  apply FuelE_S. intros N' g Π' φ' HN Hk1 Hk2 HΠ Hφ.
  assert (HdisΠ : Π1 ##ₘ ΠK) by (apply map_disjoint_dom; by rewrite HdΠ1, HdΠK).
  assert (Hdisφ : φ1 ##ₘ φK) by (by apply map_disjoint_dom).
  destruct (renk_union_split g Π1 ΠK Π' Hk1 HdisΠ HΠ) as (Π1' & ΠK' & -> & RΠ1 & RΠK & HdΠ').
  destruct (renk_union_split g φ1 φK φ' Hk2 Hdisφ Hφ) as (φ1' & φK' & -> & Rφ1 & RφK & Hdφ').
  assert (Hk1Π : kinj g Π1) by (apply (kinj_dom g (Π1 ∪ ΠK)); [rewrite dom_union_L; set_solver|done]).
  assert (HkKΠ : kinj g ΠK) by (apply (kinj_dom g (Π1 ∪ ΠK)); [rewrite dom_union_L; set_solver|done]).
  assert (Hk1φ : kinj g φ1) by (apply (kinj_dom g (φ1 ∪ φK)); [rewrite dom_union_L; set_solver|done]).
  assert (HkKφ : kinj g φK) by (apply (kinj_dom g (φ1 ∪ φK)); [rewrite dom_union_L; set_solver|done]).
  assert (HdΠ1' : dom Π1' = dom φ1') by (by rewrite (renk_dom _ _ _ RΠ1), (renk_dom _ _ _ Rφ1), HdΠ1).
  assert (HdΠK' : dom ΠK' = dom φK') by (by rewrite (renk_dom _ _ _ RΠK), (renk_dom _ _ _ RφK), HdΠK).
  assert (Hd' : dom φ1' ## dom φK') by (by apply map_disjoint_dom).
  assert (Hab' : fabove c1 ΠK' φK') by (by eapply fabove_rename).
  assert (Hkont' : fkont (S n) N' σ1 r1 σ r c1 d ΠK' φK' (kemap g K)) by (by eapply fkont_rename).
  assert (HK' : ectx_ok (kemap g K)) by (by apply ectx_ok_emap).
  apply FuelE_S in HF. destruct (HF N' g Π1' φ1' HN Hk1Π Hk1φ RΠ1 Rφ1) as [Hv1 Hs1].
  rewrite emap_efill.
  assert (Hdec : is_val (emap g e) ∨ ¬ is_val (emap g e)) by (destruct (is_val (emap g e)); simpl; auto).
  destruct Hdec as [Hve|Hve'].
  - (* the hole returned: the continuation after no action *)
    destruct (Hv1 Hve) as [Hr1 HV1].
    pose proof (Hkont' N' id ΠK' φK' 0 (S n) (emap g e) Π1' φ1' tk (rle_refl N')
      (kinj_id _) (kinj_id _) (renk_id _) (renk_id _) ltac:(by destruct c1; simpl; lia) ltac:(lia)
      Hve Hr1 HdΠ' Hdφ' ltac:(by apply Vfuel_eq)) as HC.
    rewrite kemap_id, fminus_0_map, fsub_0 in HC.
    apply FuelE_S in HC.
    pose proof (HC N' id _ _ (rle_refl N') (kinj_id _) (kinj_id _) (renk_id _) (renk_id _)) as HC'.
    by rewrite emap_id in HC'.
  - split.
    + intros Hv. exfalso. exact (efill_not_val _ _ Hve' Hv).
    + intros α e2 Hst. destruct (tstep_efill_inv _ _ _ _ HK' Hve' Hst) as (e3 & Hst3 & ->).
      apply (Fobl_bind n N' σ1 σ r1 r Π1' ΠK' φ1' φK' tk c1 d (kemap g K)); try done.
      * intros α' j tk' Πh φh e4 Hj Hdh Hdh' H1 Hh.
        apply (IH j ltac:(lia) N' σ1 r1 σ r Πh φh ΠK' (kupd α' φK') tk' (dupd c1 α') (dupd d α')
          (kemap g K) e4); try done.
        -- by rewrite dom_kupd.
        -- by rewrite dom_kupd.
        -- by apply fabove_kupd.
        -- by apply fle_dupd.
        -- apply (fkont_down j (S n)); [lia|]. by apply fkont_upd.
      * by apply Hs1.
Qed.

(** ** Link loops exhaust the tickets

    A thread that links in every state of a family Q, and stays in Q
    after the link, has no fuel at tk tickets and index tk + 1. A link
    loop with chatter (C3, Appendix B #5) is of this shape between its
    chatter steps, so no ticket count gives it fuel at every index. *)
Lemma link_tickets_fall N σ d r (Q : penv → cenv → expr → Prop) :
  (∀ Π φ e, Q Π φ e → ∃ os e', tstep e (LSess (SLink os)) e' ∧ Q (mrem os Π) (mrem os φ) e') →
  ∀ tk Π φ e, Q Π φ e → ¬ e ∈ F^N _ (S tk)⟦σ ▷ d ; r⟧(Π, φ, tk).
Proof.
  intros HQ tk. induction tk as [|tk IH]; intros Π φ e Hq HF;
    destruct (HQ Π φ e Hq) as (os & e' & Hst & Hq');
    pose proof (fuel_obl _ _ _ _ _ _ HF _ _ Hst) as (_ & _ & H1 & H2); [simpl in H1; lia|].
  simpl in H2. rewrite Nat.sub_0_r in H2. exact (IH _ _ _ Hq' H2).
Qed.
