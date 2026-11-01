(** * Point substitution (spec §9, sharp edges 56, 57, 65)

    Substituting points for point variables in types, constraints,
    environments, hypotheses and frames, and the transport of every
    fact of the static system along a substitution. *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export static.FactTheory.

Set Default Proof Using "All".

(** ** Point substitution (sharp edges 56, 57)

    The body of a box is typed once, with the box's ιs as the point
    variables 0, …, m-1 and every outer point variable shifted past
    them. [typed_sem_rules] substitutes points for the variables. A
    payload ∃ιs.T is scoped: its points are constants or among its m
    binders, so substitution commutes with [payload_at]. *)

Definition pshift (m : nat) : nat → point := λ a, pvar (a + m).

Lemma pt_shift_0 x : pt_shift 0 x = x.
Proof. destruct x as [p o]. unfold pt_shift. simpl. f_equal. lia. Qed.

Lemma pt_inst_pvar_at σ a : pt_inst σ (pvar a) = σ a.
Proof. unfold pt_inst, pvar. simpl. apply pt_shift_0. Qed.

Lemma pt_inst_shift σ n x : pt_inst σ (pt_shift n x) = pt_shift n (pt_inst σ x).
Proof.
  destruct x as [p o]. unfold pt_inst, pt_shift. simpl.
  destruct (pn_inst σ p). simpl. f_equal. lia.
Qed.

Lemma pt_inst_slot σ x i : pt_inst σ (pt_slot x i) = pt_slot (pt_inst σ x) i.
Proof. destruct x as [p o]. unfold pt_inst, pt_slot, pt_shift. simpl. done. Qed.

Lemma pn_inst_comp τ σ p : pt_inst τ (pn_inst σ p) = pn_inst (pt_inst τ ∘ σ) p.
Proof.
  induction p as [a|a|p IH b i]; simpl; [done|done|].
  by rewrite pt_inst_slot, pt_inst_shift, IH.
Qed.

Lemma pt_inst_comp τ σ x : pt_inst τ (pt_inst σ x) = pt_inst (pt_inst τ ∘ σ) x.
Proof. unfold pt_inst at 2 3. by rewrite pt_inst_shift, pn_inst_comp. Qed.

Lemma pn_inst_ext_root σ τ p :
  (∀ a, pn_root p = NVar a → σ a = τ a) → pn_inst σ p = pn_inst τ p.
Proof. induction p as [a|a|p IH b i]; simpl; intros H; [done|by apply H|by rewrite IH]. Qed.

Lemma pt_inst_ext_root σ τ x :
  (∀ a, pt_root x = NVar a → σ a = τ a) → pt_inst σ x = pt_inst τ x.
Proof. intros H. unfold pt_inst. f_equal. by apply pn_inst_ext_root. Qed.

Lemma pt_inst_ext σ τ x : (∀ a, σ a = τ a) → pt_inst σ x = pt_inst τ x.
Proof. intros H. apply pt_inst_ext_root. auto. Qed.

Lemma pn_inst_pvar p : pn_inst pvar p = Pt p 0.
Proof. induction p as [a|a|p IH b i]; simpl; [done|done|]. by rewrite IH. Qed.

Lemma pt_inst_pvar x : pt_inst pvar x = x.
Proof. destruct x as [p o]. unfold pt_inst. simpl. by rewrite pn_inst_pvar. Qed.

Lemma pn_inst_const σ p a : pn_root p = NConst a → pn_inst σ p = Pt p 0.
Proof.
  induction p as [a'|a'|p IH b i]; simpl; intros H; [done|done|].
  by rewrite (IH H).
Qed.

Lemma pt_inst_const σ x a : pt_root x = NConst a → pt_inst σ x = x.
Proof. destruct x as [p o]. intros H. unfold pt_inst. simpl. by rewrite (pn_inst_const σ p a H). Qed.

(** Lifting composes, and the identity lifts to itself. *)
Lemma pup_ext n σ τ a : (∀ b, σ b = τ b) → pup n σ a = pup n τ a.
Proof. intros H. unfold pup. by rewrite H. Qed.

Lemma pup_pvar n a : pup n pvar a = pvar a.
Proof.
  unfold pup. destruct (decide (a < n)); [done|].
  rewrite pt_inst_pvar_at. unfold pvar. f_equal. f_equal. lia.
Qed.

Lemma pup_comp τ σ n a : pt_inst (pup n τ) (pup n σ a) = pup n (pt_inst τ ∘ σ) a.
Proof.
  unfold pup at 2 3. destruct (decide (a < n)).
  - rewrite pt_inst_pvar_at. unfold pup. by rewrite decide_True.
  - change ((pt_inst τ ∘ σ) (a - n)) with (pt_inst τ (σ (a - n))).
    rewrite !pt_inst_comp. apply pt_inst_ext. intros b. simpl.
    rewrite pt_inst_pvar_at. unfold pup. rewrite decide_False by lia.
    by replace (b + n - n) with b by lia.
Qed.

Lemma bcs_comp τ σ C : bcs_inst τ (bcs_inst σ C) = bcs_inst (pt_inst τ ∘ σ) C.
Proof.
  destruct C as [env P]. unfold bcs_inst. simpl. f_equal.
  rewrite <-list_fmap_compose. apply list_fmap_ext. intros _ x _. apply pt_inst_comp.
Qed.

Lemma bcs_pvar C : bcs_inst pvar C = C.
Proof.
  destruct C as [env P]. unfold bcs_inst. simpl. f_equal.
  rewrite <-(list_fmap_id env) at 2. apply list_fmap_ext. intros _ x _. apply pt_inst_pvar.
Qed.

Lemma pinst_ty_ext T : ∀ σ τ, (∀ a, σ a = τ a) → pinst_ty σ T = pinst_ty τ T.
Proof. apply tinst_ext. Qed.

Lemma pinst_ty_comp T : ∀ τ σ, pinst_ty τ (pinst_ty σ T) = pinst_ty (pt_inst τ ∘ σ) T.
Proof. apply tinst_comp. Qed.

Lemma pinst_ty_pvar T : pinst_ty pvar T = T.
Proof. apply tinst_pvar. Qed.

(** Instantiating a list after lifting past it. *)
Lemma plist_shift xs m b : length xs = m → plist xs (b + m) = pvar b.
Proof.
  intros Hxs. unfold plist. rewrite lookup_ge_None_2 by lia.
  unfold pvar. f_equal. f_equal. lia.
Qed.

Lemma plist_pup_shift xs m σ a :
  length xs = m → pt_inst (pt_inst (plist xs) ∘ pup m σ) (pshift m a) = σ a.
Proof.
  intros Hxs. unfold pshift. rewrite pt_inst_pvar_at. simpl.
  unfold pup. rewrite decide_False by lia. replace (a + m - m) with a by lia.
  rewrite pt_inst_comp. transitivity (pt_inst pvar (σ a)); [|apply pt_inst_pvar].
  apply pt_inst_ext. intros b. simpl. rewrite pt_inst_pvar_at. by apply plist_shift.
Qed.

Lemma plist_pup_comm xs n σ a :
  length xs = n →
  pt_inst (plist (pt_inst σ <$> xs)) (pup n σ a) = pt_inst σ (plist xs a).
Proof.
  intros Hxs. unfold pup. destruct (decide (a < n)).
  - rewrite pt_inst_pvar_at. unfold plist.
    destruct (lookup_lt_is_Some_2 xs a) as [x Hx]; [lia|].
    by rewrite list_lookup_fmap, Hx.
  - assert (plist xs a = pvar (a - n)) as ->.
    { unfold plist. rewrite lookup_ge_None_2 by lia. by rewrite Hxs. }
    rewrite pt_inst_pvar_at, pt_inst_comp.
    transitivity (pt_inst pvar (σ (a - n))); [|apply pt_inst_pvar].
    apply pt_inst_ext. intros b. simpl. rewrite pt_inst_pvar_at.
    apply plist_shift. by rewrite length_fmap.
Qed.

(** ** Constraints under substitution (sharp edges 65)

    C[σ] at xs[σ] holds when C at xs does: the facts of the one are the
    facts of the other, substituted ([bcs_open_inst]). *)

Lemma plist_pup_inst xs σ z :
  pt_inst (plist (pt_inst σ <$> xs)) (pt_inst (pup (length xs) σ) z)
  = pt_inst σ (pt_inst (plist xs) z).
Proof.
  rewrite !pt_inst_comp. apply pt_inst_ext. intros a. unfold compose.
  by apply plist_pup_comm.
Qed.

Lemma bcs_hold_inst (eq eq' lt lt' : point → point → Prop) σ C xs :
  (∀ x y, eq x y → eq' (pt_inst σ x) (pt_inst σ y)) →
  (∀ x y, lt x y → lt' (pt_inst σ x) (pt_inst σ y)) →
  bcs_hold eq lt C xs → bcs_hold eq' lt' (bcs_inst σ C) (pt_inst σ <$> xs).
Proof.
  intros He Hl H g Hg. rewrite length_fmap in Hg.
  apply bcs_open_inst in Hg as (g0 & Hg0 & ->). specialize (H g0 Hg0).
  destruct g0; simpl in *; rewrite !plist_pup_inst; auto.
Qed.

(** A constraint without outer points: its open facts are its scoped
    facts. *)
Lemma bcs_open_nil n P g : bcs_open n (BCs [] P) g ↔ P g ∧ fact_scoped n g.
Proof.
  unfold bcs_open. simpl. rewrite Nat.add_0_r.
  assert (∀ f, fact_map (pt_inst (pup n (plist []))) f = f) as E.
  { intros f. transitivity (fact_map id f); [|by destruct f].
    apply fact_map_ext. intros x. unfold id. rewrite <-(pt_inst_pvar x) at 2.
    apply pt_inst_ext. intros a. unfold pup. destruct (decide (a < n)); [done|].
    unfold plist. simpl. rewrite pt_inst_pvar_at. unfold pvar. f_equal. f_equal. lia. }
  split.
  - intros (f & Hf & Hs & ->). by rewrite E.
  - intros [Hg Hs]. exists g. by rewrite E.
Qed.

Lemma bcs_hold_intro (eq lt : point → point → Prop) P xs :
  (∀ g, P g → fact_scoped (length xs) g → fact_holds eq lt (fact_map (pt_inst (plist xs)) g)) →
  bcs_hold eq lt (BCs [] P) xs.
Proof. intros H g Hg. apply bcs_open_nil in Hg as [? ?]. auto. Qed.

(** A recursive call. The force at ys gets C[ys/ιs] from the body's
    own hypothesis (C, xs) when every fact of the instance is a fact of
    the hypothesis, C[ys/ιs] ⊆ C[xs/ιs] (sharp edges 65). No rule of
    its own is needed. *)
Lemma bcs_hold_sub W Ψ C xs ys :
  (C, xs) ∈ Ψ →
  (∀ g, bcs_open (length ys) C g → ∃ g', bcs_open (length xs) C g' ∧
     fact_map (pt_inst (plist ys)) g = fact_map (pt_inst (plist xs)) g') →
  bcs_hold (seqs W Ψ) (slt W Ψ) C ys.
Proof.
  intros Hg H g Hg0. destruct (H g Hg0) as (g' & Hg' & ->).
  exact (hyp_in_fact W Ψ C xs Hg g' Hg').
Qed.

Lemma pn_vb_root k p a : pn_vb k p → pn_root p = NVar a → a < k.
Proof. induction p as [b|b|q IH b i]; simpl; [done|congruence|exact IH]. Qed.

Lemma pt_inst_ids k x : pn_vb k (pt_name x) → pt_inst (plist (ids k)) x = x.
Proof.
  intros Hx. rewrite <-(pt_inst_pvar x) at 2. apply pt_inst_ext_root. intros a Ha.
  pose proof (pn_vb_root _ _ _ Hx Ha) as Hlt. unfold plist, ids.
  by rewrite list_lookup_fmap, lookup_seq_lt by done.
Qed.

Lemma pn_vb_inst k ys p :
  Forall (λ y, pn_vb k (pt_name y)) ys → pn_vb (length ys) p →
  pn_vb k (pt_name (pn_inst (plist ys) p)).
Proof.
  intros Hys. induction p as [b|b|q IH b i]; simpl; [done| |exact IH].
  intros Hb. unfold plist. destruct (lookup_lt_is_Some_2 ys b) as [y Hy]; [done|].
  rewrite Hy. rewrite Forall_lookup in Hys. exact (Hys b y Hy).
Qed.

Lemma fact_scoped_inst k ys g :
  Forall (λ y, pn_vb k (pt_name y)) ys → fact_scoped (length ys) g →
  fact_scoped k (fact_map (pt_inst (plist ys)) g).
Proof.
  intros Hys. destruct g as [x y|x y]; simpl; intros [Hx Hy];
    unfold pt_inst; simpl; split; by apply pn_vb_inst.
Qed.

(** The recursive call for a constraint without outer points, whose
    body hypothesis is C at its own ιs: C[ys/ιs] ⊆ C. *)
Lemma bcs_hold_self W Ψ P ys :
  (BCs [] P, ids (length ys)) ∈ Ψ → Forall (λ y, pn_vb (length ys) (pt_name y)) ys →
  (∀ g, P g → fact_scoped (length ys) g → P (fact_map (pt_inst (plist ys)) g)) →
  bcs_hold (seqs W Ψ) (slt W Ψ) (BCs [] P) ys.
Proof.
  intros Hg Hys H. apply (bcs_hold_sub W Ψ _ (ids (length ys))); [done|].
  intros g Hg0. apply bcs_open_nil in Hg0 as [HP Hs].
  exists (fact_map (pt_inst (plist ys)) g).
  pose proof (fact_scoped_inst _ _ _ Hys Hs) as Hs'. split.
  - unfold ids. rewrite length_fmap, length_seq. apply bcs_open_nil. split; [by apply H|done].
  - destruct (fact_map (pt_inst (plist ys)) g) as [x y|x y]; simpl in *;
      destruct Hs' as [Hx Hy]; by rewrite !pt_inst_ids.
Qed.

Lemma hyps_comp τ σ Ψ : hyps_inst τ (hyps_inst σ Ψ) = hyps_inst (pt_inst τ ∘ σ) Ψ.
Proof.
  unfold hyps_inst. rewrite <-list_fmap_compose. apply list_fmap_ext. intros _ [C xs] _. simpl.
  rewrite bcs_comp. f_equal.
  rewrite <-list_fmap_compose. apply list_fmap_ext. intros _ x _. apply pt_inst_comp.
Qed.

Lemma hyps_inst_ext σ τ Ψ : (∀ a, σ a = τ a) → hyps_inst σ Ψ = hyps_inst τ Ψ.
Proof.
  intros H. unfold hyps_inst. apply list_fmap_ext. intros _ [C xs] _. simpl. f_equal.
  - by apply bcs_inst_ext.
  - apply list_fmap_ext. intros _ x _. by apply pt_inst_ext.
Qed.

Lemma ids_pup m σ : pt_inst (pup m σ) <$> ids m = ids m.
Proof.
  unfold ids. rewrite <-list_fmap_compose. apply list_fmap_ext. intros i x Hx. simpl.
  rewrite pt_inst_pvar_at. unfold pup. apply lookup_seq in Hx as [-> ?].
  by rewrite decide_True by lia.
Qed.

Lemma ids_plist xs τ : pt_inst (pt_inst (plist xs) ∘ pup (length xs) τ) <$> ids (length xs) = xs.
Proof.
  unfold ids. rewrite <-list_fmap_compose. apply list_eq. intros i. rewrite list_lookup_fmap.
  destruct (decide (i < length xs)).
  - rewrite lookup_seq_lt by done. simpl. rewrite pt_inst_pvar_at.
    change (Some (pt_inst (plist xs) (pup (length xs) τ i)) = xs !! i). unfold pup.
    rewrite decide_True by done. rewrite pt_inst_pvar_at. unfold plist.
    destruct (lookup_lt_is_Some_2 xs i) as [x Hx]; [done|]. by rewrite Hx.
  - rewrite lookup_seq_ge by lia. simpl. by rewrite lookup_ge_None_2 by lia.
Qed.

Lemma pn_root_inst σ p :
  pt_root (pn_inst σ p) = match pn_root p with NVar a => pt_root (σ a) | q => q end.
Proof. induction p as [a|a|p IH b i]; simpl; [done|done|]. exact IH. Qed.

Lemma pt_root_inst σ x :
  pt_root (pt_inst σ x) = match pt_root x with NVar a => pt_root (σ a) | q => q end.
Proof. destruct x as [p o]. exact (pn_root_inst σ p). Qed.

(** A hypothesis fact, substituted, is a fact of the substituted hypothesis. *)
Lemma hyp_fact_inst (eq lt : point → point → Prop) (pk : point → Prop) σ Ψ g :
  hyps_hold eq lt pk (hyps_inst σ Ψ) → hyp_fact Ψ g → fact_holds eq lt (fact_map (pt_inst σ) g).
Proof.
  intros H (C & xs & Hg & g0 & Hg0 & ->).
  assert ((bcs_inst σ C, pt_inst σ <$> xs) ∈ hyps_inst σ Ψ) as Hg'.
  { unfold hyps_inst. apply list_elem_of_fmap. by exists (C, xs). }
  destruct (H _ _ Hg') as [HC _].
  assert (bcs_open (length (pt_inst σ <$> xs)) (bcs_inst σ C)
            (fact_map (pt_inst (pup (length xs) σ)) g0)) as Ho.
  { rewrite length_fmap. apply bcs_open_inst. by exists g0. }
  specialize (HC _ Ho). destruct g0; simpl in *; by rewrite <-!plist_pup_inst.
Qed.

Lemma hyps_hold_inst (eq eq' lt lt' : point → point → Prop) (pk pk' : point → Prop) σ Ψ :
  (∀ x y, eq x y → eq' (pt_inst σ x) (pt_inst σ y)) →
  (∀ x y, lt x y → lt' (pt_inst σ x) (pt_inst σ y)) → (∀ x, pk x → pk' (pt_inst σ x)) →
  hyps_hold eq lt pk Ψ → hyps_hold eq' lt' pk' (hyps_inst σ Ψ).
Proof.
  intros He Hl Hk H C xs Hg. unfold hyps_inst in Hg.
  apply list_elem_of_fmap in Hg as ([C0 xs0] & Eg & Hg). injection Eg as -> ->.
  destruct (H C0 xs0 Hg) as [H1 H2]. split; [by eapply bcs_hold_inst|].
  apply Forall_fmap. eapply Forall_impl; [exact H2|]. intros x Hx. by apply Hk.
Qed.

Lemma skn_pinst W (pk : point → Prop) σ Ψ x :
  world_wf W → (∀ x y, pt_root x = pt_root y → pk x → pk y) → (∀ x, pt_known W x → pk x) →
  (∀ C xs, (C, xs) ∈ hyps_inst σ Ψ → Forall pk xs) → skn W Ψ x → pk (pt_inst σ x).
Proof.
  intros HW Hr Hk H [Hx|(C & xs & y & Hg & Hy & E)].
  - destruct (wf_names_const _ HW _ Hx) as [a Ha]. rewrite (pt_inst_const σ x a Ha). by apply Hk.
  - assert ((bcs_inst σ C, pt_inst σ <$> xs) ∈ hyps_inst σ Ψ) as Hg'
      by (unfold hyps_inst; apply list_elem_of_fmap; by exists (C, xs)).
    pose proof (H _ _ Hg') as Hf. rewrite Forall_forall in Hf.
    apply (Hr (pt_inst σ y)); [by rewrite !pt_root_inst, E|].
    apply Hf. by apply list_elem_of_fmap_2.
Qed.

(** ** Point scoping: every point variable lies below k *)

Definition pt_scoped (k : nat) (x : point) : Prop := ∀ a, pt_root x = NVar a → a < k.

Definition opt_scoped (k : nat) (o : option point) : Prop :=
  match o with Some x => pt_scoped k x | None => True end.

(** The outer points of a constraint live outside its binder. *)
Definition bcs_scoped (k : nat) (C : bcs) : Prop := Forall (pt_scoped k) (bc_env C).

Fixpoint pscoped (k : nat) (T : ty) : Prop :=
  match T with
  | TUnit => True
  | TLolli ub lb T1 U => opt_scoped k ub ∧ opt_scoped k lb ∧ pscoped k T1 ∧ pscoped k U
  | TProd T1 U | TSum T1 U => pscoped k T1 ∧ pscoped k U
  | TBox n C T1 => bcs_scoped k C ∧ pscoped (n + k) T1
  | TSess _ x => pt_scoped k x
  | TEx lb n C T1 => opt_scoped k lb ∧ bcs_scoped k C ∧ pscoped (n + k) T1
  end.

Lemma pinst_ty_ext_scoped T : ∀ k σ τ,
  pscoped k T → (∀ a, a < k → σ a = τ a) → pinst_ty σ T = pinst_ty τ T.
Proof.
  assert (∀ k σ τ x, pt_scoped k x → (∀ a, a < k → σ a = τ a) →
            pt_inst σ x = pt_inst τ x) as Hpt.
  { intros k σ τ x Hx H. apply pt_inst_ext_root. intros a Ha. by apply H, Hx. }
  assert (∀ k n σ τ, (∀ a, a < k → σ a = τ a) → ∀ a, a < n + k → pup n σ a = pup n τ a) as Hup.
  { intros k n σ τ H a Ha. unfold pup. destruct (decide (a < n)); [done|].
    rewrite H; [done|lia]. }
  induction T as [| ub lb T1 IH1 U IH2 | T1 IH1 U IH2 | T1 IH1 U IH2 | n C T1 IH | s x
                 | lb n C T1 IH];
    intros k σ τ HT H; simpl in *.
  - done.
  - destruct HT as (Hub & Hlb & H1 & H2).
    f_equal; [destruct ub; simpl in *; [f_equal; eauto|done]
             |destruct lb; simpl in *; [f_equal; eauto|done]|eauto|eauto].
  - destruct HT. f_equal; eauto.
  - destruct HT. f_equal; eauto.
  - destruct HT as (HC & H1). f_equal.
    + unfold bcs_inst. f_equal. apply list_fmap_ext. intros i x Hx.
      unfold bcs_scoped in HC. rewrite Forall_forall in HC. eapply Hpt; [|exact H].
      apply HC. by eapply list_elem_of_lookup_2.
    + eapply IH; [done|]. by apply Hup.
  - f_equal. eauto.
  - destruct HT as (Hlb & HC & H1). f_equal.
    + destruct lb; simpl in *; [f_equal; eauto|done].
    + unfold bcs_inst. f_equal. apply list_fmap_ext. intros i x Hx.
      unfold bcs_scoped in HC. rewrite Forall_forall in HC. eapply Hpt; [|exact H].
      apply HC. by eapply list_elem_of_lookup_2.
    + eapply IH; [done|]. by apply Hup.
Qed.

Lemma payload_pinst σ m T x :
  pscoped m T → pinst_ty σ (payload_at m T x) = payload_at m T (pt_inst σ x).
Proof.
  intros HT. unfold payload_at, ty_inst. rewrite pinst_ty_comp.
  apply (pinst_ty_ext_scoped T m); [done|]. intros a Ha. simpl. unfold plist, slots.
  rewrite !list_lookup_fmap, !lookup_seq_lt by done. simpl. apply pt_inst_slot.
Qed.

(** E-Const asks the payload of send and recv to be scoped by its m
    binders (§4: "P ::= ∃ιs. T, all points of T bound"). *)
Definition kscoped (k : konst) (T : ty) : Prop :=
  match k, T with
  | KSend, TLolli _ _ (TProd _ (TSess (SSnd m P _) _)) _ => pscoped m P
  | KRecv, TLolli _ _ (TSess (SRcv m P _) _) _ => pscoped m P
  | _, _ => True
  end.

Lemma opt_heads_pinst σ o : opt_heads (pt_inst σ <$> o) = set_map (pt_inst σ) (opt_heads o).
Proof. destruct o; simpl; [by rewrite set_map_singleton_L|by rewrite set_map_empty]. Qed.

Lemma heads_pinst σ T : heads (pinst_ty σ T) = set_map (pt_inst σ) (heads T).
Proof.
  induction T as [| ub lb T1 IH1 U IH2 | T1 IH1 U IH2 | T1 IH1 U IH2 | n C T1 IH | s x
                 | lb n C T1 IH];
    simpl.
  - by rewrite set_map_empty.
  - apply opt_heads_pinst.
  - by rewrite IH1, IH2, set_map_union_L.
  - by rewrite IH1, IH2, set_map_union_L.
  - by rewrite set_map_empty.
  - by rewrite set_map_singleton_L.
  - apply opt_heads_pinst.
Qed.

(** ** Facts survive substitution

    A world knows constants only (wf_names_const). A fact about a point
    with a variable root is reflexivity or program order, and both hold
    of any instance. *)

Definition node_inst (σ : nat → point) (a : node) : node :=
  match a with NP x => NP (pt_inst σ x) | NV φ => NV φ end.

Definition ends_pinst (σ : nat → point) (o : ends) : ends :=
  match o with
  | One e => One (e.1, pt_inst σ e.2)
  | Both e1 e2 => Both (e1.1, pt_inst σ e1.2) (e2.1, pt_inst σ e2.2)
  end.

Definition tenv_pinst (σ : nat → point) (Θ : tenv) : tenv := ends_pinst σ <$> Θ.

Lemma tenv_comp_pinst (R R' : point → point → Prop) σ Θ Θ1 Θ2 :
  (∀ x y, R x y → R' (pt_inst σ x) (pt_inst σ y)) → tenv_comp R Θ Θ1 Θ2 →
  tenv_comp R' (tenv_pinst σ Θ) (tenv_pinst σ Θ1) (tenv_pinst σ Θ2).
Proof.
  intros HR [Hj Hd]. split.
  - intros c. unfold tenv_pinst. rewrite !lookup_fmap. pose proof (Hj c) as Hc.
    destruct (Θ1 !! c), (Θ2 !! c), (Θ !! c); inversion Hc; subst; simpl; constructor.
  - intros c e1 e2 H1 H2. unfold tenv_pinst in H1, H2. rewrite lookup_fmap in H1, H2.
    destruct (Θ1 !! c) as [[e1'|]|] eqn:E1; simplify_eq/=.
    destruct (Θ2 !! c) as [[e2'|]|] eqn:E2; simplify_eq/=.
    destruct (Hd c e1' e2' E1 E2) as [He Hs]. split; [|done]. by apply HR.
Qed.

(** ** General constraints of E-NewFresh (sharp edges 93)

    A constraint C of one variable ι (the variable 0) whose every fact
    relates a point of the fresh channel to an outer point. A point of
    the fresh channel has the root ι, so it is ι+k, (ι+b).i+k and so on.
    [fresh_lo C u p] is the fact u ≺ p with p on the fresh channel,
    [fresh_hi C q v] the fact q ≺ v. [fresh_outer C u] reads an outer
    point in the context of the rule. C may be infinite. *)

(** [fresh_lo], [fresh_hi], [fresh_ok] and [fresh_outer] live in
    types/Types.v, because the existential signature of new reads them. *)

Lemma fresh_lo_inst σ C u p : fresh_lo (bcs_inst σ C) u p ↔ fresh_lo C u p.
Proof. unfold fresh_lo. simpl. by rewrite length_fmap. Qed.

Lemma fresh_hi_inst σ C q v : fresh_hi (bcs_inst σ C) q v ↔ fresh_hi C q v.
Proof. unfold fresh_hi. simpl. by rewrite length_fmap. Qed.

Lemma fresh_ok_inst σ C : fresh_ok C → fresh_ok (bcs_inst σ C).
Proof.
  intros H f Hf Hs. simpl in Hf, Hs. rewrite length_fmap in Hs.
  destruct (H f Hf Hs) as [(u & p & -> & Hu)|(q & v & -> & Hv)].
  - left. exists u, p. split; [done|]. by apply fresh_lo_inst.
  - right. exists q, v. split; [done|]. by apply fresh_hi_inst.
Qed.

Lemma pn_vb_var k p : pn_vb k p → ∃ b, pn_root p = NVar b ∧ b < k.
Proof. induction p as [c|b|q IH b' i]; simpl; [done|by exists b|exact IH]. Qed.

Lemma pt_inst_outer σ d d' env u :
  pn_vb (S (length env)) (pt_name u) → pt_root u ≠ NVar 0 →
  pt_inst (plist (d :: (pt_inst σ <$> env))) u = pt_inst σ (pt_inst (plist (d' :: env)) u).
Proof.
  intros Hs Hr. rewrite pt_inst_comp. apply pt_inst_ext_root. intros b Hb.
  pose proof (pn_vb_root _ _ _ Hs Hb) as Hlt.
  destruct b as [|j]; [done|]. unfold compose, plist. simpl. rewrite list_lookup_fmap.
  destruct (lookup_lt_is_Some_2 env j) as [y Hy]; [lia|]. by rewrite Hy.
Qed.

Lemma fresh_outer_inst σ C u :
  pn_vb (S (length (bc_env C))) (pt_name u) → pt_root u ≠ NVar 0 →
  fresh_outer (bcs_inst σ C) u = pt_inst σ (fresh_outer C u).
Proof. intros Hs Hr. unfold fresh_outer. simpl. by apply pt_inst_outer. Qed.

Section transfer.
  Context (W W1 : world) (σ : nat → point).
  Context (HW : world_wf W) (HW1 : wext W W1).

  Lemma pinst_eq x y : w_eq W x y → w_eq W1 (pt_inst σ x) (pt_inst σ y).
  Proof.
    intros Hxy. pose proof (wext_wf _ _ HW1) as Hwf.
    destruct (wf_eq_supp _ HW x y Hxy) as [->|[Hx Hy]]; [apply (wf_eq_refl _ Hwf)|].
    destruct (wf_names_const _ HW _ Hx) as [a Ha]. destruct (wf_names_const _ HW _ Hy) as [b Hb].
    rewrite (pt_inst_const σ x a Ha), (pt_inst_const σ y b Hb).
    destruct HW1 as (_ & He & Hl & _). auto.
  Qed.

  Lemma pinst_lt x y : w_lt W x y → w_lt W1 (pt_inst σ x) (pt_inst σ y).
  Proof.
    intros Hxy. pose proof (wext_wf _ _ HW1) as Hwf.
    destruct (wf_lt_supp _ HW x y Hxy) as [[Hn Ho]|[Hx Hy]].
    - destruct x as [p o], y as [p' o']. simpl in *. subst p'.
      replace (pt_inst σ (Pt p o')) with (pt_shift (S (o' - o - 1)) (pt_inst σ (Pt p o))).
      + by apply wf_lt_po_n.
      + unfold pt_inst, pt_shift. simpl. f_equal. lia.
    - destruct (wf_names_const _ HW _ Hx) as [a Ha]. destruct (wf_names_const _ HW _ Hy) as [b Hb].
      rewrite (pt_inst_const σ x a Ha), (pt_inst_const σ y b Hb).
    destruct HW1 as (_ & He & Hl & _). auto.
  Qed.

  Lemma konst_ty_pinst (peq peq' plt plt' : point → point → Prop) (pk pk' : point → Prop) k T :
    (∀ x y, peq x y → peq' (pt_inst σ x) (pt_inst σ y)) →
    (∀ x y, plt x y → plt' (pt_inst σ x) (pt_inst σ y)) →
    (∀ x, pk x → pk' (pt_inst σ x)) →
    kscoped k T → konst_ty peq plt pk k T →
    konst_ty peq' plt' pk' k (pinst_ty σ T).
  Proof.
    intros Heq Hlt Hpk Hk.
    destruct 1 as [S x Hx|ub lb|m P S x Hh|m P S x|x|S x x' Hxx'|n C ub P xs Hxs HC HK
                  |S C u H H0 H1 H2];
      simpl in *.
    - constructor. by apply Hpk.
    - constructor.
    - rewrite payload_pinst, pt_inst_shift by done. constructor.
      intros h Hh'. rewrite <-payload_pinst, heads_pinst in Hh' by done.
      apply elem_of_map in Hh' as (h0 & -> & Hh0). by apply Hlt, Hh.
    - rewrite payload_pinst, pt_inst_shift by done. constructor.
    - constructor.
    - constructor. by apply Heq.
    - assert (∀ a, pt_inst (plist (pt_inst σ <$> xs)) (pup n σ a) = pt_inst σ (plist xs a))
        as Hc by (intros a; by apply plist_pup_comm).
      assert (pt_inst (plist (pt_inst σ <$> xs)) <$> (pt_inst (pup n σ) <$> ub) =
              pt_inst σ <$> (pt_inst (plist xs) <$> ub)) as E1.
      { destruct ub; simpl; [|done]. f_equal. rewrite !pt_inst_comp.
        apply pt_inst_ext. intros a. apply Hc. }
      assert (ty_inst (pt_inst σ <$> xs) (pinst_ty (pup n σ) P) = pinst_ty σ (ty_inst xs P)) as E2.
      { unfold ty_inst. rewrite !pinst_ty_comp. apply pinst_ty_ext. intros a. apply Hc. }
      rewrite <-E1, <-E2. constructor; [by rewrite length_fmap| |].
      + by apply (bcs_hold_inst peq _ plt).
      + apply Forall_fmap. eapply Forall_impl; [exact HK|]. intros x Hx. by apply Hpk.
    - pose proof H2 as (_ & [Hs _] & _ & Hr).
      assert (pt_inst (pup 1 σ) (pvar 0) = pvar 0) as ->
        by (rewrite pt_inst_pvar_at; unfold pup; by rewrite decide_True by lia).
      rewrite <-fresh_outer_inst by done. constructor.
      + by apply fresh_ok_inst.
      + simpl. apply Forall_fmap. eapply Forall_impl; [exact H0|]. intros x Hx. by apply Hpk.
      + intros u' p q v Hu Hv Hpq. apply (proj1 (fresh_lo_inst σ C u' p)) in Hu.
        apply (proj1 (fresh_hi_inst σ C q v)) in Hv.
        pose proof Hu as (_ & [Hs1 _] & _ & Hr1). pose proof Hv as (_ & [_ Hs2] & _ & Hr2).
        rewrite (fresh_outer_inst σ C u'), (fresh_outer_inst σ C v) by done.
        apply Hlt. by apply (H1 u' p q v).
      + by apply (proj2 (fresh_lo_inst σ C u (pvar 0))).
  Qed.

  Lemma skn_pinst_known Ψ x :
    hyps_hold (w_eq W1) (w_lt W1) (pt_known W1) (hyps_inst σ Ψ) → skn W Ψ x → pt_known W1 (pt_inst σ x).
  Proof.
    intros HΨ. apply (skn_pinst W (pt_known W1) σ Ψ x HW).
    - intros y z E. unfold pt_known. by rewrite E.
    - intros y Hy. destruct HW1 as [HN _]. unfold pt_known in *. clear -HN Hy. set_solver.
    - intros C xs Hg. by destruct (HΨ C xs Hg).
  Qed.

  Lemma skn_pinst_s Ψ Ψ' x :
    hyps_hold (seqs W1 Ψ') (slt W1 Ψ') (skn W1 Ψ') (hyps_inst σ Ψ) → skn W Ψ x → skn W1 Ψ' (pt_inst σ x).
  Proof.
    intros HΨ. apply (skn_pinst W (skn W1 Ψ') σ Ψ x HW).
    - intros y z E. by apply skn_root.
    - intros y Hy. left. destruct HW1 as [HN _]. unfold pt_known in *. clear -HN Hy. set_solver.
    - intros C xs Hg. by destruct (HΨ C xs Hg).
  Qed.

  (** Facts derived from W and the hypotheses Ψ survive into W₁ when
      the hypotheses hold there (sharp edges 58). One lemma maps a
      derivation of the fact theory along σ (sharp edges 64, 65). *)

  Lemma fl_pinst Ψ Ψ' Φ Φ' :
    hyps_hold (seqs W1 Ψ') (slt W1 Ψ') (skn W1 Ψ') (hyps_inst σ Ψ) →
    (∀ φ u, Φ !! φ = Some (Some u) → fl (FCtx W1 Ψ' Φ') (NP (pt_inst σ u)) (NV φ)) →
    (∀ x y, seqs W Ψ x y → seqs W1 Ψ' (pt_inst σ x) (pt_inst σ y)) ∧
    (∀ a b, fl (FCtx W Ψ Φ) a b → fl (FCtx W1 Ψ' Φ') (node_inst σ a) (node_inst σ b)).
  Proof.
    intros HΨ HΦ. apply (fl_map (FCtx W Ψ Φ) (seqs W1 Ψ') _ (pt_inst σ) (node_inst σ)); simpl.
    - intros x y H. apply se_w. by apply pinst_eq.
    - intros x y H. exact (hyp_fact_inst _ _ _ σ Ψ (FEq x y) HΨ H).
    - intros x. apply se_refl.
    - intros x y. apply se_sym.
    - intros x y z. apply se_trans.
    - intros x y H. rewrite !pt_inst_shift. by apply se_shift.
    - intros x y i H. rewrite !pt_inst_slot. by apply se_slot.
    - intros x y H. apply (fl_w (FCtx W1 Ψ' Φ')). by apply pinst_lt.
    - intros x y Hxy. apply fl_points. exact (hyp_fact_inst _ _ _ σ Ψ (FLt x y) HΨ Hxy).
    - exact HΦ.
    - intros x x' b Hx H. exact (fl_eql (FCtx W1 Ψ' Φ') _ _ _ Hx H).
    - intros a y y' H Hy. exact (fl_eqr (FCtx W1 Ψ' Φ') _ _ _ H Hy).
    - intros a y b. exact (fl_trans (FCtx W1 Ψ' Φ') _ _ _).
  Qed.

  Lemma seqs_pinst_s Ψ Ψ' x y :
    hyps_hold (seqs W1 Ψ') (slt W1 Ψ') (skn W1 Ψ') (hyps_inst σ Ψ) →
    seqs W Ψ x y → seqs W1 Ψ' (pt_inst σ x) (pt_inst σ y).
  Proof.
    intros HΨ. exact (proj1 (fl_pinst Ψ Ψ' ∅ ∅ HΨ (λ φ u Hu, ltac:(by rewrite lookup_empty in Hu))) x y).
  Qed.

  Lemma slt_pinst_s Ψ Ψ' x y :
    hyps_hold (seqs W1 Ψ') (slt W1 Ψ') (skn W1 Ψ') (hyps_inst σ Ψ) → slt W Ψ x y → slt W1 Ψ' (pt_inst σ x) (pt_inst σ y).
  Proof.
    intros HΨ H. exact (proj2 (fl_pinst Ψ Ψ' ∅ ∅ HΨ (λ φ u Hu, ltac:(by rewrite lookup_empty in Hu))) _ _ H).
  Qed.

  (** The ground case: the target is the world W₁ itself. *)
  Lemma hyps_hold_ground Ψ :
    hyps_hold (w_eq W1) (w_lt W1) (pt_known W1) (hyps_inst σ Ψ) →
    hyps_hold (seqs W1 []) (slt W1 []) (skn W1 []) (hyps_inst σ Ψ).
  Proof.
    apply hyps_hold_mono; [intros ? ? ?; by apply se_w|intros ? ? ?; by apply sl_w|intros ? ?; by left].
  Qed.

  Lemma seqs_pinst Ψ x y :
    hyps_hold (w_eq W1) (w_lt W1) (pt_known W1) (hyps_inst σ Ψ) → seqs W Ψ x y → w_eq W1 (pt_inst σ x) (pt_inst σ y).
  Proof.
    intros HΨ H. apply (seqs_nil _ _ _ (wext_wf _ _ HW1)). apply (seqs_pinst_s Ψ); [|done].
    by apply hyps_hold_ground.
  Qed.

  Lemma slt_pinst Ψ x y :
    hyps_hold (w_eq W1) (w_lt W1) (pt_known W1) (hyps_inst σ Ψ) → slt W Ψ x y → w_lt W1 (pt_inst σ x) (pt_inst σ y).
  Proof.
    intros HΨ H. apply (slt_nil _ _ _ (wext_wf _ _ HW1)). apply (slt_pinst_s Ψ); [|done].
    by apply hyps_hold_ground.
  Qed.

  Lemma sle_pinst Ψ x y :
    hyps_hold (w_eq W1) (w_lt W1) (pt_known W1) (hyps_inst σ Ψ) → sle W Ψ x y → w_le W1 (pt_inst σ x) (pt_inst σ y).
  Proof. intros HΨ [H|H]; [left; by apply (seqs_pinst Ψ)|right; by apply (slt_pinst Ψ)]. Qed.

  Lemma sle_pinst_s Ψ Ψ' x y :
    hyps_hold (seqs W1 Ψ') (slt W1 Ψ') (skn W1 Ψ') (hyps_inst σ Ψ) → sle W Ψ x y → sle W1 Ψ' (pt_inst σ x) (pt_inst σ y).
  Proof. intros HΨ [H|H]; [left; by apply (seqs_pinst_s Ψ)|right; by apply (slt_pinst_s Ψ)]. Qed.

  Lemma lb_below_h_pinst Ψ lb H :
    hyps_hold (w_eq W1) (w_lt W1) (pt_known W1) (hyps_inst σ Ψ) →
    lb_below_h W Ψ lb H → lb_below W1 (pt_inst σ <$> lb) (set_map (pt_inst σ) H).
  Proof.
    intros HΨ. destruct lb as [x|]; simpl.
    - intros Hl y Hy. apply elem_of_map in Hy as (y0 & -> & Hy0). by apply (sle_pinst Ψ), Hl.
    - intros ->. apply set_map_empty.
  Qed.

  Lemma lb_below_h_pinst_s Ψ Ψ' lb H :
    hyps_hold (seqs W1 Ψ') (slt W1 Ψ') (skn W1 Ψ') (hyps_inst σ Ψ) →
    lb_below_h W Ψ lb H → lb_below_h W1 Ψ' (pt_inst σ <$> lb) (set_map (pt_inst σ) H).
  Proof.
    intros HΨ. destruct lb as [x|]; simpl.
    - intros Hl y Hy. apply elem_of_map in Hy as (y0 & -> & Hy0). by apply (sle_pinst_s Ψ), Hl.
    - intros ->. apply set_map_empty.
  Qed.

  (** Composition of environments reads Γ ⊢ ≡ (sharp edges 65). *)
  Lemma tenv_comp_pinst_g Ψ Θ Θ1 Θ2 :
    hyps_hold (w_eq W1) (w_lt W1) (pt_known W1) (hyps_inst σ Ψ) → tenv_comp (seqs W Ψ) Θ Θ1 Θ2 →
    tenv_comp (w_eq W1) (tenv_pinst σ Θ) (tenv_pinst σ Θ1) (tenv_pinst σ Θ2).
  Proof. intros HΨ. apply tenv_comp_pinst. intros x y. by apply (seqs_pinst Ψ). Qed.

  Lemma tenv_comp_pinst_s Ψ Ψ' Θ Θ1 Θ2 :
    hyps_hold (seqs W1 Ψ') (slt W1 Ψ') (skn W1 Ψ') (hyps_inst σ Ψ) → tenv_comp (seqs W Ψ) Θ Θ1 Θ2 →
    tenv_comp (seqs W1 Ψ') (tenv_pinst σ Θ) (tenv_pinst σ Θ1) (tenv_pinst σ Θ2).
  Proof. intros HΨ. apply tenv_comp_pinst. intros x y. by apply (seqs_pinst_s Ψ). Qed.

  (** E-Conv up to Γ ⊢ ≡ survives substitution (sharp edges 67). *)
  Lemma steq_pinst_s Ψ Ψ' T : ∀ U,
    hyps_hold (seqs W1 Ψ') (slt W1 Ψ') (skn W1 Ψ') (hyps_inst σ Ψ) →
    steq W Ψ T U → steq W1 Ψ' (pinst_ty σ T) (pinst_ty σ U).
  Proof.
    intros U HΨ. revert U. induction T; intros [] H; simpl in *; try done.
    - destruct H as (Hu & Hl & ? & ?). split_and!; auto.
      + destruct ub, ub0; simpl in *; try done. by apply (seqs_pinst_s Ψ).
      + destruct lb, lb0; simpl in *; try done. by apply (seqs_pinst_s Ψ).
    - destruct H. split; auto.
    - destruct H. split; auto.
    - destruct H as (<- & <- & ?). split_and!; [done|done|by apply eqT_pinst].
    - destruct H as [? ?]. split; [by apply (seqs_pinst_s Ψ)|done].
    - destruct H as (<- & <- & <- & ?). split_and!; [done|done|done|by apply eqT_pinst].
  Qed.

  Lemma steq_teqW Ψ T : ∀ U,
    hyps_hold (w_eq W1) (w_lt W1) (pt_known W1) (hyps_inst σ Ψ) →
    steq W Ψ T U → teqW W1 (pinst_ty σ T) (pinst_ty σ U).
  Proof.
    pose proof (wext_wf _ _ HW1) as HW1'.
    intros U HΨ. revert U. induction T; intros [] H; simpl in *; try done.
    - destruct H as (Hu & Hl & ? & ?). split_and!; auto.
      + destruct ub, ub0; simpl in *; try done.
        apply (w_eq_pteqW _ HW1'). by apply (seqs_pinst Ψ).
      + destruct lb, lb0; simpl in *; try done.
        apply (w_eq_pteqW _ HW1'). by apply (seqs_pinst Ψ).
    - destruct H. split; auto.
    - destruct H. split; auto.
    - destruct H as (<- & <- & ?). split_and!; [done|apply bcs_rel_refl|].
      apply teq_teqW. by apply eqT_pinst.
    - destruct H as [? ?]. split; [|done].
      apply (w_eq_pteqW _ HW1'). by apply (seqs_pinst Ψ).
    - destruct H as (<- & <- & <- & ?). split_and!; [|done|apply bcs_rel_refl|].
      + destruct lb; simpl; [by left|done].
      + apply teq_teqW. by apply eqT_pinst.
  Qed.
End transfer.

(** ** Substitution in environments, hypotheses and frames *)

Definition lenv_pinst (σ : nat → point) (Δ : lenv) : lenv := fmap (M:=option) (pinst_ty σ) <$> Δ.

Definition fhyps_pinst (σ : nat → point) (Φ : fhyps) : fhyps := fmap (M:=option) (pt_inst σ) <$> Φ.

Definition sf_pinst (σ : nat → point) (F : sframe) : sframe := (set_map (pt_inst σ) F.1, F.2).

Lemma unlimited_pinst σ U : unlimited U → unlimited (pinst_ty σ U).
Proof. by destruct U. Qed.

Lemma lenv_heads_pinst σ Δ : lenv_heads (lenv_pinst σ Δ) = set_map (pt_inst σ) (lenv_heads Δ).
Proof.
  induction Δ as [|[T|] Δ IH]; simpl.
  - by rewrite set_map_empty.
  - by rewrite IH, heads_pinst, set_map_union_L.
  - done.
Qed.

Lemma lenv_empty_pinst σ Δ : lenv_empty Δ → lenv_empty (lenv_pinst σ Δ).
Proof.
  intros HΔ o Ho. apply list_elem_of_fmap in Ho as (o' & -> & Ho'). by rewrite (HΔ o' Ho').
Qed.

Lemma lenv_unl_pinst σ Δ : lenv_unl Δ → lenv_unl (lenv_pinst σ Δ).
Proof.
  intros HΔ o Ho. apply list_elem_of_fmap in Ho as (o' & -> & Ho').
  destruct (HΔ o' Ho') as [->|(U & -> & HU)]; [by left|right].
  exists (pinst_ty σ U). split; [done|by apply unlimited_pinst].
Qed.

Lemma lenv_pinst_lookup σ Δ x : lenv_pinst σ Δ !! x = fmap (pinst_ty σ) <$> Δ !! x.
Proof. unfold lenv_pinst. apply list_lookup_fmap. Qed.

Lemma lenv_only_pinst σ Δ x T : lenv_only Δ x T → lenv_only (lenv_pinst σ Δ) x (pinst_ty σ T).
Proof.
  intros [Hx Hu]. split.
  - by rewrite lenv_pinst_lookup, Hx.
  - intros y T' Hy. rewrite lenv_pinst_lookup in Hy.
    destruct (Δ !! y) as [[T0|]|] eqn:E; simplify_eq/=.
    destruct (Hu y T0 E) as [-> ->]. done.
Qed.

Lemma lenv_split_pinst σ Δ Δ1 Δ2 :
  lenv_split Δ Δ1 Δ2 → lenv_split (lenv_pinst σ Δ) (lenv_pinst σ Δ1) (lenv_pinst σ Δ2).
Proof. induction 1; simpl; constructor; auto using unlimited_pinst. Qed.

Lemma lenv_wk_pinst σ Δ' Δ : lenv_wk Δ' Δ → lenv_wk (lenv_pinst σ Δ') (lenv_pinst σ Δ).
Proof. induction 1; simpl; constructor; auto using unlimited_pinst. Qed.

Lemma lenv_pinst_ext σ τ Δ : (∀ a, σ a = τ a) → lenv_pinst σ Δ = lenv_pinst τ Δ.
Proof.
  intros H. unfold lenv_pinst. apply list_fmap_ext. intros i [T|] _; simpl; [|done].
  f_equal. by apply pinst_ty_ext.
Qed.

Lemma lenv_pinst_comp τ σ Δ : lenv_pinst τ (lenv_pinst σ Δ) = lenv_pinst (pt_inst τ ∘ σ) Δ.
Proof.
  unfold lenv_pinst. rewrite <-list_fmap_compose. apply list_fmap_ext.
  intros i [T|] _; simpl; [|done]. f_equal. apply pinst_ty_comp.
Qed.

Lemma lenv_pinst_pvar Δ : lenv_pinst pvar Δ = Δ.
Proof.
  induction Δ as [|[T|] Δ IH]; simpl; [done| |]; rewrite IH; [|done].
  by rewrite pinst_ty_pvar.
Qed.

Lemma ends_heads_pinst σ c o :
  ends_heads c (ends_pinst σ o) = set_map (pt_inst σ) (ends_heads c o).
Proof. destruct o; simpl; set_solver. Qed.

Lemma tenv_heads_pinst σ Θ : tenv_heads (tenv_pinst σ Θ) = set_map (pt_inst σ) (tenv_heads Θ).
Proof.
  apply set_eq. intros x. rewrite elem_of_map, elem_of_tenv_heads. split.
  - intros (c & o & Hc & Hx). unfold tenv_pinst in Hc. rewrite lookup_fmap in Hc.
    destruct (Θ !! c) as [o0|] eqn:Ho; [|done]. injection Hc as <-.
    rewrite ends_heads_pinst in Hx.
    apply elem_of_map in Hx as (x0 & -> & Hx0). exists x0. split; [done|].
    apply elem_of_tenv_heads. eauto.
  - intros (x0 & -> & Hx0). apply elem_of_tenv_heads in Hx0 as (c & o & Hc & Hx).
    exists c, (ends_pinst σ o). split.
    + unfold tenv_pinst. by rewrite lookup_fmap, Hc.
    + rewrite ends_heads_pinst. by apply elem_of_map_2.
Qed.

Lemma tenv_pinst_pvar Θ : tenv_pinst pvar Θ = Θ.
Proof.
  apply map_eq. intros c. unfold tenv_pinst. rewrite lookup_fmap.
  destruct (Θ !! c) as [[[s x]|[s1 x1] [s2 x2]]|]; simpl; rewrite ?pt_inst_pvar; done.
Qed.

Lemma sf_pinst_union σ F X : sf_pinst σ (sf_union F X) = sf_union (sf_pinst σ F) (set_map (pt_inst σ) X).
Proof. unfold sf_pinst, sf_union. simpl. by rewrite set_map_union_L. Qed.

Lemma sf_pinst_pvar F : sf_pinst pvar F = F.
Proof.
  destruct F as [P o]. unfold sf_pinst. simpl. f_equal.
  apply set_eq. intros x. rewrite elem_of_map. split.
  - intros (y & -> & Hy). by rewrite pt_inst_pvar.
  - intros Hx. exists x. by rewrite pt_inst_pvar.
Qed.

Lemma ub_below_s_pinst W W1 σ Ψ Ψ' Φ ub F :
  world_wf W → wext W W1 → hyps_hold (seqs W1 Ψ') (slt W1 Ψ') (skn W1 Ψ') (hyps_inst σ Ψ) → ub_below_s W Ψ Φ ub F →
  ub_below_s W1 Ψ' (fhyps_pinst σ Φ) (pt_inst σ <$> ub) (sf_pinst σ F).
Proof.
  intros HW HW1 HΨ. destruct ub as [x|]; [|done]. intros [HP Hφ].
  assert (∀ a b, fl (FCtx W Ψ Φ) a b →
            fl (FCtx W1 Ψ' (fhyps_pinst σ Φ)) (node_inst σ a) (node_inst σ b)) as Hm.
  { refine (proj2 (fl_pinst W W1 σ HW HW1 Ψ Ψ' Φ _ HΨ _)). intros φ u Hu.
    apply (fl_v (FCtx W1 Ψ' (fhyps_pinst σ Φ))). simpl.
    unfold fhyps_pinst. by rewrite lookup_fmap, Hu. }
  split.
  - intros y Hy. destruct F as [P o]. simpl in *.
    apply elem_of_map in Hy as (y0 & -> & Hy0). exact (Hm _ _ (HP y0 Hy0)).
  - intros φ Hφ'. destruct F as [P o]. simpl in *. exact (Hm _ _ (Hφ φ Hφ')).
Qed.

Lemma eqT_pinst ρ T : ∀ U σ, eqT ρ T U → eqT ρ (pinst_ty σ T) (pinst_ty σ U).
Proof.
  induction T as [| ub lb T1 IH1 U IH2 | T1 IH1 U IH2 | T1 IH1 U IH2 | n C T1 IH | s x
                 | lb n C T1 IH];
    intros [| ub' lb' U1 U2 | U1 U2 | U1 U2 | n' C' U1 | r y | lb' n' C' U1] σ; simpl; try done.
  - intros (-> & -> & H1 & H2). split_and!; auto.
  - intros [H1 H2]. split_and!; auto.
  - intros [H1 H2]. split_and!; auto.
  - intros (-> & -> & H1). split_and!; auto.
  - intros (-> & H). split_and!; auto.
  - intros (-> & -> & -> & H1). split_and!; auto.
Qed.

Lemma tenv_pinst_empty σ : tenv_pinst σ ∅ = ∅.
Proof. apply fmap_empty. Qed.

Lemma sf_pinst_fresh σ φ : sf_pinst σ (∅, Some φ) = (∅, Some φ).
Proof. unfold sf_pinst. simpl. by rewrite set_map_empty. Qed.

(** ** Composition and extensionality for environments and frames *)

Lemma tenv_pinst_comp τ σ Θ : tenv_pinst τ (tenv_pinst σ Θ) = tenv_pinst (pt_inst τ ∘ σ) Θ.
Proof.
  apply map_eq. intros c. unfold tenv_pinst. rewrite !lookup_fmap.
  destruct (Θ !! c) as [[[s x]|[s1 x1] [s2 x2]]|]; simpl; rewrite ?pt_inst_comp; done.
Qed.

Lemma tenv_pinst_ext σ τ Θ : (∀ a, σ a = τ a) → tenv_pinst σ Θ = tenv_pinst τ Θ.
Proof.
  intros H. apply map_eq. intros c. unfold tenv_pinst. rewrite !lookup_fmap.
  destruct (Θ !! c) as [[[s x]|[s1 x1] [s2 x2]]|]; simpl;
    rewrite ?(pt_inst_ext σ τ); done.
Qed.

Lemma sf_pinst_comp τ σ F : sf_pinst τ (sf_pinst σ F) = sf_pinst (pt_inst τ ∘ σ) F.
Proof.
  destruct F as [P o]. unfold sf_pinst. simpl. f_equal.
  apply set_eq. intros x. rewrite !elem_of_map. split.
  - intros (y & -> & Hy). apply elem_of_map in Hy as (z & -> & Hz).
    exists z. by rewrite pt_inst_comp.
  - intros (z & -> & Hz). exists (pt_inst σ z). rewrite pt_inst_comp.
    split; [done|]. by apply elem_of_map_2.
Qed.

Lemma sf_pinst_ext σ τ F : (∀ a, σ a = τ a) → sf_pinst σ F = sf_pinst τ F.
Proof.
  intros H. destruct F as [P o]. unfold sf_pinst. simpl. f_equal.
  apply set_eq. intros x. rewrite !elem_of_map.
  split; intros (y & -> & Hy); exists y; by rewrite (pt_inst_ext σ τ).
Qed.

(** ** The hypothesis of E-NewFresh (sharp edges 90)

    [fresh_bcs L H] is the constraint of one point variable ι (the
    variable 0 under the binder) with the facts l ≺ ι for l ∈ L and
    ι ≺ h for h ∈ H. The points of L and H are its outer points. *)

Definition fresh_facts (nL nH : nat) (f : fact) : Prop :=
  (∃ i, i < nL ∧ f = FLt (pvar (S i)) (pvar 0)) ∨
  (∃ j, j < nH ∧ f = FLt (pvar 0) (pvar (S (nL + j)))).

Definition fresh_bcs (L H : list point) : bcs :=
  BCs (L ++ H) (fresh_facts (length L) (length H)).

Lemma bcs_inst_fresh σ L H :
  bcs_inst σ (fresh_bcs L H) = fresh_bcs (pt_inst σ <$> L) (pt_inst σ <$> H).
Proof. unfold bcs_inst, fresh_bcs. simpl. by rewrite fmap_app, !length_fmap. Qed.

(** An outer point, opened under one binder and instantiated by [x],
    is itself. *)
Lemma pt_inst_open1 x env i y :
  env !! i = Some y →
  pt_inst (plist [x]) (pt_inst (pup 1 (plist env)) (pvar (S i))) = y.
Proof.
  intros Hy. rewrite pt_inst_pvar_at. unfold pup. rewrite decide_False by lia.
  replace (S i - 1) with i by lia. unfold plist at 2. rewrite Hy.
  rewrite pt_inst_comp. rewrite <-(pt_inst_pvar y) at 2. apply pt_inst_ext.
  intros b. simpl. rewrite pt_inst_pvar_at. unfold plist. simpl.
  replace (b + 1) with (S b) by lia. simpl.
  unfold pvar. f_equal. f_equal. lia.
Qed.

Lemma pt_inst_open1_0 x env :
  pt_inst (plist [x]) (pt_inst (pup 1 (plist env)) (pvar 0)) = x.
Proof.
  rewrite pt_inst_pvar_at. unfold pup. rewrite decide_True by lia.
  rewrite pt_inst_pvar_at. done.
Qed.

(** The facts of [fresh_bcs L H] at the instance [x] are L ≺ x ≺ H. *)
Lemma fresh_open x L H g :
  (∃ g0, bcs_open 1 (fresh_bcs L H) g0 ∧ g = fact_map (pt_inst (plist [x])) g0) ↔
  (∃ l, l ∈ L ∧ g = FLt l x) ∨ (∃ h, h ∈ H ∧ g = FLt x h).
Proof.
  split.
  - intros (g0 & (f & Hf & Hs & ->) & ->).
    destruct Hf as [(i & Hi & ->)|(j & Hj & ->)]; simpl.
    + left. destruct (lookup_lt_is_Some_2 L i Hi) as [l Hl]. exists l.
      split; [by eapply list_elem_of_lookup_2|].
      rewrite (pt_inst_open1 x (L ++ H) i l) by (by apply lookup_app_l_Some).
      by rewrite pt_inst_open1_0.
    + right. destruct (lookup_lt_is_Some_2 H j Hj) as [h Hh]. exists h.
      split; [by eapply list_elem_of_lookup_2|].
      rewrite (pt_inst_open1 x (L ++ H) (length L + j) h).
      * by rewrite pt_inst_open1_0.
      * rewrite lookup_app_r by lia. by replace (length L + j - length L) with j by lia.
  - intros [(l & Hl & ->)|(h & Hh & ->)].
    + apply list_elem_of_lookup_1 in Hl as [i Hi].
      exists (FLt (pt_inst (pup 1 (plist (L ++ H))) (pvar (S i)))
                  (pt_inst (pup 1 (plist (L ++ H))) (pvar 0))). split.
      * exists (FLt (pvar (S i)) (pvar 0)). split_and!; [|simpl|done].
        -- left. exists i. split; [by eapply lookup_lt_Some|done].
        -- pose proof (lookup_lt_Some _ _ _ Hi). rewrite length_app. lia.
      * simpl. rewrite pt_inst_open1_0. rewrite (pt_inst_open1 x (L ++ H) i l); [done|].
        by apply lookup_app_l_Some.
    + apply list_elem_of_lookup_1 in Hh as [j Hj].
      exists (FLt (pt_inst (pup 1 (plist (L ++ H))) (pvar 0))
                  (pt_inst (pup 1 (plist (L ++ H))) (pvar (S (length L + j))))). split.
      * exists (FLt (pvar 0) (pvar (S (length L + j)))). split_and!; [|simpl|done].
        -- right. exists j. split; [by eapply lookup_lt_Some|done].
        -- pose proof (lookup_lt_Some _ _ _ Hj). rewrite length_app. lia.
      * simpl. rewrite pt_inst_open1_0. rewrite (pt_inst_open1 x (L ++ H) (length L + j) h); [done|].
        rewrite lookup_app_r by lia. by replace (length L + j - length L) with j by lia.
Qed.

Lemma fresh_hold (eq lt : point → point → Prop) x L H :
  Forall (λ l, lt l x) L → Forall (λ h, lt x h) H → bcs_hold eq lt (fresh_bcs L H) [x].
Proof.
  intros HL HH g Hg.
  destruct (proj1 (fresh_open x L H (fact_map (pt_inst (plist [x])) g)) (ex_intro _ g (conj Hg eq_refl)))
    as [(l & Hl & E)|(h & Hh & E)]; rewrite E; simpl.
  - rewrite Forall_forall in HL. by apply HL.
  - rewrite Forall_forall in HH. by apply HH.
Qed.

Lemma fresh_outer_skn W Ψ C u :
  Forall (skn W Ψ) (bc_env C) → pn_vb (S (length (bc_env C))) (pt_name u) → pt_root u ≠ NVar 0 →
  skn W Ψ (fresh_outer C u).
Proof.
  intros HK Hs Hr. destruct (pn_vb_var _ _ Hs) as ([|j] & Hb & Hlt); [done|].
  destruct (lookup_lt_is_Some_2 (bc_env C) j) as [y Hy]; [lia|].
  apply (skn_root W Ψ y); [|rewrite Forall_lookup in HK; by apply (HK j)].
  unfold fresh_outer. rewrite pt_root_inst. unfold pt_root at 2. rewrite Hb.
  unfold plist. simpl. by rewrite Hy.
Qed.

Lemma fresh_lo_skn W Ψ C u p : Forall (skn W Ψ) (bc_env C) → fresh_lo C u p → skn W Ψ (fresh_outer C u).
Proof. intros HK (_ & [Hs _] & _ & Hr). by apply fresh_outer_skn. Qed.

Lemma fresh_hi_skn W Ψ C q v : Forall (skn W Ψ) (bc_env C) → fresh_hi C q v → skn W Ψ (fresh_outer C v).
Proof. intros HK (_ & [_ Hs] & _ & Hr). by apply fresh_outer_skn. Qed.

Lemma pt_inst_unshift x z : pt_inst (plist [x]) (pt_inst (λ a', pvar (a' + 1)) z) = z.
Proof.
  rewrite pt_inst_comp. rewrite <-(pt_inst_pvar z) at 2. apply pt_inst_ext.
  intros b. simpl. rewrite pt_inst_pvar_at. unfold plist. simpl.
  replace (b + 1) with (S b) by lia. simpl. unfold pvar. f_equal. f_equal. lia.
Qed.

Lemma open1_comp x env f :
  fact_map (pt_inst (plist [x])) (fact_map (pt_inst (pup 1 (plist env))) f)
  = fact_map (pt_inst (plist (x :: env))) f.
Proof.
  assert (∀ z, pt_inst (plist [x]) (pt_inst (pup 1 (plist env)) z) = pt_inst (plist (x :: env)) z)
    as E.
  { intros z. rewrite pt_inst_comp. apply pt_inst_ext. intros b. unfold compose, pup.
    destruct (decide (b < 1)).
    - assert (b = 0) as -> by lia. by rewrite pt_inst_pvar_at.
    - rewrite pt_inst_unshift. destruct b as [|b]; [lia|]. replace (S b - 1) with b by lia.
      unfold plist. simpl. destruct (env !! b); [done|]. unfold pvar. repeat f_equal. }
  destruct f; simpl; by rewrite !E.
Qed.

Lemma bcs_hold_fresh_intro (eq lt : point → point → Prop) C x :
  (∀ f, bc_facts C f → fact_scoped (S (length (bc_env C))) f →
     fact_holds eq lt (fact_map (pt_inst (plist (x :: bc_env C))) f)) →
  bcs_hold eq lt C [x].
Proof. intros H g (f & Hf & Hs & ->). rewrite open1_comp. by apply H. Qed.

(** A fact of a hypothesis (C, [x]) read off its raw fact. *)
Lemma slt_hyp_fresh W Ψ C x u v :
  (C, [x]) ∈ Ψ → bc_facts C (FLt u v) → fact_scoped (S (length (bc_env C))) (FLt u v) →
  slt W Ψ (pt_inst (plist (x :: bc_env C)) u) (pt_inst (plist (x :: bc_env C)) v).
Proof.
  intros Hg Hf Hs. apply sl_h. exists C, [x]. split; [done|].
  exists (fact_map (pt_inst (pup 1 (plist (bc_env C)))) (FLt u v)). split.
  - exists (FLt u v). split_and!; [done|done|done].
  - by rewrite open1_comp.
Qed.
