(** * The examples of ORDERS-SPEC.md §13 in the static system

    Each typable example is a closed program: the channels come from
    [new] and the threads from [spawn], so the process is (∅, {t}) and
    P-Term types it with Σ = Θ_B = ∅. Every example is typed for every
    world that has the facts it needs ([*_typed]), then instantiated at
    an explicit strict world, and [soundness] gives deadlock freedom
    ([*_deadlock_free]).

    Strict worlds come from [wgen_strict]: a rank into ℕ that rises along
    program order and along every generating fact, read through a
    canonical representative that identifies the generating aliases.

    The examples that do not type carry the failing rule and fact in a
    comment, see SHARP-EDGES.md 59 and 60. *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export Static.

Set Default Proof Using "All".

(** ** Strict worlds from a rank *)

Lemma geq_cn (E : prel) (cn : point → point) x y :
  (∀ x, cn (pt_shift 1 x) = pt_shift 1 (cn x)) →
  (∀ x i, cn (pt_slot x i) = pt_slot (cn x) i) →
  (∀ x y, E x y → cn x = cn y) →
  geq E x y → cn x = cn y.
Proof.
  intros Hs Hl HE. induction 1; try congruence; auto.
Qed.

Lemma wgen_strict N E L (cn : point → point) (r : point → nat) :
  (∀ p, p ∈ N → ∃ a, p = NConst a) →
  (∀ x y, E x y → eq_or_supp N x y) →
  (∀ x y, L x y → po_or_supp N x y) →
  (∀ x, cn (pt_shift 1 x) = pt_shift 1 (cn x)) →
  (∀ x i, cn (pt_slot x i) = pt_slot (cn x) i) →
  (∀ x y, E x y → cn x = cn y) →
  (∀ x, r x < r (pt_shift 1 x)) →
  (∀ x y, L x y → r (cn x) < r (cn y)) →
  strict (wgen N E L).
Proof.
  intros HN HE HL Hs Hl Hc Hr HLr. split; [by apply wgen_wf|].
  assert (∀ x y, glt E L x y → r (cn x) < r (cn y)) as Hlt.
  { induction 1 as [x y H|x|x x' y y' Hx _ IH Hy|x y z _ IH1 _ IH2].
    - by apply HLr.
    - rewrite Hs. apply Hr.
    - apply (geq_cn E cn) in Hx, Hy; [|done..]. by rewrite Hx, <-Hy.
    - lia. }
  intros x H. apply Hlt in H. lia.
Qed.

(** The rank of a point: a weight per root constant, slots weighted
    by their base, and a step per name times the offset. *)
Fixpoint pn_rank (g : nat → nat) (h : nat → nat → nat → nat) (p : pname) : nat :=
  match p with
  | NConst a => g a
  | NVar _ => 0
  | NSlot q b i => h (pn_rank g h q) b i
  end.

Definition prank (k : pname → nat) (g : nat → nat) (h : nat → nat → nat → nat) (x : point) : nat :=
  pn_rank g h (pt_name x) + k (pt_name x) * S (pt_off x).

Lemma prank_shift k g h x : (∀ p, 0 < k p) → prank k g h x < prank k g h (pt_shift 1 x).
Proof. intros Hk. specialize (Hk (pt_name x)). unfold prank, pt_shift. simpl. nia. Qed.

(** ** Splitting linear environments by occurrence

    The derivations below never name Δ₁ and Δ₂. [lp e x Δ] keeps the
    unlimited bindings of Δ and the linear ones that occur in e, with
    x the index of Δ's head inside e. [sok] checks that every linear
    binding goes to exactly one side. *)

Fixpoint occ (x : nat) (e : expr) : bool :=
  match e with
  | Var y => Nat.eqb x y
  | EUnit | Konst _ | Chan _ => false
  | Lam e | EBox e => occ (S x) e
  | App e1 e2 | Pair e1 e2 | LetU e1 e2 => occ x e1 || occ x e2
  | LetP e1 e2 => occ x e1 || occ (S (S x)) e2
  | Inj1 e | Inj2 e => occ x e
  | Case e e1 e2 => occ x e || occ (S x) e1 || occ (S x) e2
  end.

Definition unlb (T : ty) : bool := match T with TBox _ _ _ _ => true | _ => false end.

Lemma unlb_unl T : unlb T = true → unlimited T.
Proof. by destruct T. Qed.

Fixpoint lp (e : expr) (x : nat) (Δ : lenv) : lenv :=
  match Δ with
  | [] => []
  | None :: Δ' => None :: lp e (S x) Δ'
  | Some T :: Δ' => (if unlb T || occ x e then Some T else None) :: lp e (S x) Δ'
  end.

Fixpoint sok (e1 : expr) (x1 : nat) (e2 : expr) (x2 : nat) (Δ : lenv) : bool :=
  match Δ with
  | [] => true
  | None :: Δ' => sok e1 (S x1) e2 (S x2) Δ'
  | Some T :: Δ' => (unlb T || xorb (occ x1 e1) (occ x2 e2)) && sok e1 (S x1) e2 (S x2) Δ'
  end.

Lemma lp_split e1 x1 e2 x2 Δ :
  sok e1 x1 e2 x2 Δ = true → lenv_split Δ (lp e1 x1 Δ) (lp e2 x2 Δ).
Proof.
  revert x1 x2. induction Δ as [|[T|] Δ IH]; intros x1 x2 H; simpl in *; [constructor| |].
  - apply andb_true_iff in H as [H1 H2].
    destruct (unlb T) eqn:Hu; simpl.
    + apply lsplit_unl; [by apply unlb_unl|by apply IH].
    + destruct (occ x1 e1), (occ x2 e2); simpl in *; try done;
        [apply lsplit_l|apply lsplit_r]; by apply IH.
  - apply lsplit_none. by apply IH.
Qed.

Fixpoint allunl (Δ : lenv) : bool :=
  match Δ with
  | [] => true
  | None :: Δ' => allunl Δ'
  | Some T :: Δ' => unlb T && allunl Δ'
  end.

Fixpoint lonly (x : nat) (Δ : lenv) : lenv :=
  match Δ, x with
  | [], _ => []
  | o :: Δ', 0 => o :: lenv_nones Δ'
  | _ :: Δ', S x' => None :: lonly x' Δ'
  end.

Fixpoint oku (x : nat) (Δ : lenv) : bool :=
  match Δ, x with
  | [], _ => true
  | _ :: Δ', 0 => allunl Δ'
  | o :: Δ', S x' => match o with Some T => unlb T | None => true end && oku x' Δ'
  end.

Lemma nones_wk Δ : allunl Δ = true → lenv_wk (lenv_nones Δ) Δ.
Proof.
  induction Δ as [|[T|] Δ IH]; simpl; intros H; [constructor| |].
  - apply andb_true_iff in H as [H1 H2]. apply lwk_drop; [by apply unlb_unl|by apply IH].
  - apply lwk_cons. by apply IH.
Qed.

Lemma lonly_wk x Δ : oku x Δ = true → lenv_wk (lonly x Δ) Δ.
Proof.
  revert x. induction Δ as [|o Δ IH]; intros [|x] H; simpl in *; [constructor|constructor| |].
  - apply lwk_cons. by apply nones_wk.
  - apply andb_true_iff in H as [H1 H2]. destruct o as [T|].
    + apply lwk_drop; [by apply unlb_unl|by apply IH].
    + apply lwk_cons. by apply IH.
Qed.

Lemma lonly_only x Δ T : Δ !! x = Some (Some T) → lenv_only (lonly x Δ) x T.
Proof.
  revert x. induction Δ as [|o Δ IH]; intros [|x] H; simpl in *; [done|done| |].
  - simplify_eq. split; [done|]. intros [|y] T' Hy; simpl in Hy; [by simplify_eq|].
    exfalso. apply list_elem_of_lookup_2 in Hy. apply lenv_empty_nones in Hy. done.
  - destruct (IH x H) as [H1 H2]. split; [done|]. intros [|y] T' Hy; simpl in Hy; [done|].
    destruct (H2 y T' Hy). split; [lia|done].
Qed.

Lemma allunl_unl Δ : allunl Δ = true → lenv_unl Δ.
Proof.
  induction Δ as [|[T|] Δ IH]; simpl; intros H o Ho; [by apply elem_of_nil in Ho| |].
  - apply andb_true_iff in H as [H1 H2]. apply elem_of_cons in Ho as [->|Ho].
    + right. exists T. split; [done|by apply unlb_unl].
    + by apply IH.
  - apply elem_of_cons in Ho as [->|Ho]; [by left|by apply IH].
Qed.

(** ** Derived rules for Θ = ∅ *)

Section rules.
  Context (W : world) (HW : world_wf W).

  Lemma comp0 : tenv_comp (w_eq W) ∅ ∅ ∅.
  Proof. apply tenv_comp_empty_l. intros ? ?. apply (wf_eq_sym _ HW). Qed.

  Lemma tenv_heads0 : tenv_heads ∅ = ∅.
  Proof. unfold tenv_heads. by rewrite map_fold_empty. Qed.

  Lemma tv_var Φ Ψ Δ F x T :
    Δ !! x = Some (Some T) → oku x Δ = true → typed W Φ Ψ ∅ Δ F (Var x) T.
  Proof. intros H1 H2. eapply t_wk; [by apply lonly_wk|]. apply t_var. by apply lonly_only. Qed.

  Lemma tv_unit Φ Ψ Δ F : allunl Δ = true → typed W Φ Ψ ∅ Δ F EUnit TUnit.
  Proof. intros H. eapply t_wk; [by apply nones_wk|]. apply t_unit, lenv_empty_nones. Qed.

  Lemma tv_app Φ Ψ Δ F e1 e2 ub lb T U :
    sok e1 0 e2 0 Δ = true →
    typed W Φ Ψ ∅ (lp e1 0 Δ) (sf_union F (lenv_heads (lp e2 0 Δ))) e1 (TLolli ub lb T U) →
    typed W Φ Ψ ∅ (lp e2 0 Δ) (sf_union F (opt_heads lb)) e2 T →
    ub_below_s W Ψ Φ ub F →
    typed W Φ Ψ ∅ Δ F (App e1 e2) U.
  Proof.
    intros Hs H1 H2 Hu. eapply t_app; [apply comp0|by apply lp_split|exact Hu| |exact H2].
    by rewrite tenv_heads0, union_empty_l_L.
  Qed.

  (** A constant applied: its type is given by [konst_ty], the
      argument comes first so that its type is known. *)
  Lemma tv_appk Φ Ψ Δ F k e2 ub T U :
    typed W Φ Ψ ∅ Δ F e2 T →
    konst_ty (w_eq W) (slt W Ψ) (pt_known W) k (TLolli ub None T U) →
    kscoped k (TLolli ub None T U) →
    ub_below_s W Ψ Φ ub F →
    typed W Φ Ψ ∅ Δ F (App (Konst k) e2) U.
  Proof.
    intros H2 Hk Hks Hu. eapply (t_app W Φ Ψ ∅ ∅ ∅ Δ (lenv_nones Δ) Δ F _ _ ub None).
    - apply comp0.
    - apply lenv_split_nones_l.
    - exact Hu.
    - apply t_konst; [apply lenv_empty_nones|done|done].
    - destruct F as [P o]. unfold sf_union. simpl. by rewrite union_empty_r_L.
  Qed.

  Lemma tv_pair Φ Ψ Δ F e1 e2 T U :
    sok e1 0 e2 0 Δ = true →
    typed W Φ Ψ ∅ (lp e2 0 Δ) (sf_union F (heads T)) e2 U →
    typed W Φ Ψ ∅ (lp e1 0 Δ) (sf_union F (lenv_heads (lp e2 0 Δ))) e1 T →
    typed W Φ Ψ ∅ Δ F (Pair e1 e2) (TProd T U).
  Proof.
    intros Hs H2 H1. eapply t_pair; [apply comp0|by apply lp_split| |exact H2].
    by rewrite tenv_heads0, union_empty_l_L.
  Qed.

  Lemma tv_letu Φ Ψ Δ F e1 e2 T :
    sok e1 0 e2 0 Δ = true →
    typed W Φ Ψ ∅ (lp e1 0 Δ) (sf_union F (lenv_heads (lp e2 0 Δ))) e1 TUnit →
    typed W Φ Ψ ∅ (lp e2 0 Δ) F e2 T →
    typed W Φ Ψ ∅ Δ F (LetU e1 e2) T.
  Proof.
    intros Hs H1 H2. eapply t_letu; [apply comp0|by apply lp_split| |exact H2].
    by rewrite tenv_heads0, union_empty_l_L.
  Qed.

  Lemma tv_letp Φ Ψ Δ F e1 e2 T1 T2 T :
    sok e1 0 e2 2 Δ = true →
    typed W Φ Ψ ∅ (lp e1 0 Δ) (sf_union F (lenv_heads (lp e2 2 Δ))) e1 (TProd T1 T2) →
    typed W Φ Ψ ∅ (Some T2 :: Some T1 :: lp e2 2 Δ) F e2 T →
    typed W Φ Ψ ∅ Δ F (LetP e1 e2) T.
  Proof.
    intros Hs H1 H2. eapply t_letp; [apply comp0|by apply lp_split| |exact H2].
    by rewrite tenv_heads0, union_empty_l_L.
  Qed.

  Lemma tv_lam Φ Ψ Δ F e T U ub lb φ :
    φ ∉ dom Φ →
    lb_below_h W Ψ lb (lenv_heads Δ) →
    typed W (<[φ := ub]> Φ) Ψ ∅ (Some T :: Δ) (∅, Some φ) e U →
    typed W Φ Ψ ∅ Δ F (Lam e) (TLolli ub lb T U).
  Proof. intros Hφ Hl H. eapply t_lam; [exact Hφ| |exact H]. by rewrite tenv_heads0, union_empty_l_L. Qed.

End rules.

(** {u} ≺ F, split into the points of F and the frame variable. *)
Section frames.
  Context (W : world).

  Lemma ubs_intro Ψ Φ x P o :
    (∀ y, y ∈ P → slt W Ψ x y) →
    match o with Some φ => ∃ u, Φ !! φ = Some (Some u) ∧ sle W Ψ x u | None => True end →
    ub_below_s W Ψ Φ (Some x) (P, o).
  Proof. intros H1 H2. split; [exact H1|by destruct o]. Qed.

  Lemma ubs_none Ψ Φ F : ub_below_s W Ψ Φ None F.
  Proof. destruct F as [? []]; split; done. Qed.

  Lemma sle_refl Ψ x : world_wf W → sle W Ψ x x.
  Proof. intros HW. left. apply (wf_eq_refl _ HW). Qed.

  Lemma slt_po Ψ x : world_wf W → slt W Ψ x (pt_shift 1 x).
  Proof. intros HW. apply sl_w, (wf_lt_po _ HW). Qed.
End frames.

(** A closed thread is a closed process. *)
Lemma ptyped_closed W t T :
  prim T → typed W ∅ [] ∅ [] (∅, None) t T → ptyped W ∅ (∅, {[+ t +]}) T.
Proof.
  intros HT Ht. apply (pt_term W ∅ ∅ ∅ t T HT); [done|set_solver| | |].
  { intros c o Ho. by rewrite lookup_empty in Ho. }
  { intros c e1 e2 He. by rewrite lookup_empty in He. }
  unfold tenv_of. rewrite fmap_empty, (left_id_L ∅ (∪)). exact Ht.
Qed.

(** Membership in a concrete frame: one goal per point. *)
Ltac mem_cases H :=
  cbn in H; rewrite ?elem_of_union, ?elem_of_singleton in H;
  repeat match type of H with _ ∨ _ => destruct H as [H|H] end;
  try (by apply not_elem_of_empty in H); subst.

(** One typing step, by the head of the term. *)
Ltac tstep :=
  match goal with
  | |- typed _ _ _ _ _ _ (Var _) _ => apply tv_var; [assumption|done|reflexivity]
  | |- typed _ _ _ _ _ _ EUnit _ => apply tv_unit; [assumption|reflexivity]
  | |- typed _ _ _ _ _ _ (LetU _ _) _ => apply tv_letu; [assumption|reflexivity| |]
  | |- typed _ _ _ _ _ _ (LetP _ _) _ => eapply tv_letp; [assumption|reflexivity| |]
  | |- typed _ _ _ _ _ _ (Pair _ _) _ => eapply tv_pair; [assumption|reflexivity| |]
  | |- typed _ _ _ _ _ _ (App (Konst _) _) _ => eapply tv_appk; [assumption| | | |]
  end.

Abbreviation pc a k := (Pt (NConst a) k).

(** ** sync: typable

    sync = let (c, d) = new ∗ in
           let () = spawn (λu. let () = u in close (send ⟨∗, c⟩)) in
           let (x, d) = recv d in let () = x in close d

    c : !∗.Close@(a,0) and d : ?∗.Close@(a,0). Each thread holds one end
    only, so no fact beyond program order is needed. The thunk blocks
    at (a,0) and (a,1), its upper point is (a,1), its lower point (a,0). *)

Definition Ssync : sty := SSnd 0 TUnit SEnd.

Definition sync_thunk : expr :=
  Lam (LetU (Var 0) (App EClos (App ESend (Pair EUnit (Var 2))))).

Definition sync_main : expr :=
  LetP (App ENew EUnit)
    (LetU (App ESpawn sync_thunk)
      (LetP (App ERecv (Var 0)) (LetU (Var 1) (App EClos (Var 0))))).

Lemma sync_typed W : world_wf W → pt_known W (pc 0 0) →
  typed W ∅ [] ∅ [] (∅, None) sync_main TUnit.
Proof.
  intros HW Ha. unfold sync_main.
  tstep.
  { tstep; [tstep|apply (KTNew _ _ _ Ssync (pc 0 0) Ha)|done|apply ubs_none]. }
  cbn. tstep.
  { cbn. tstep.
    - eapply (tv_lam W HW _ _ _ _ _ TUnit TUnit (Some (pc 0 1)) (Some (pc 0 0)) 0); [set_solver| |].
      { intros y Hy. mem_cases Hy. apply sle_refl, HW. }
      cbn. tstep; [tstep|]. cbn.
      tstep.
      + tstep; [|apply (KTSend _ _ _ 0 TUnit SEnd (pc 0 0)); cbn; set_solver|done|].
        * tstep; tstep.
        * apply ubs_intro; [intros y Hy; mem_cases Hy|].
          exists (pc 0 1). split; [done|]. right. apply (slt_po W _ (pc 0 0) HW).
      + apply KTClos.
      + done.
      + apply ubs_intro; [intros y Hy; mem_cases Hy|].
        exists (pc 0 1). split; [done|]. apply sle_refl, HW.
    - apply KTSpawn.
    - done.
    - apply ubs_none. }
  cbn. tstep.
  { tstep; [tstep|apply KTRecv|done|]. apply ubs_intro; [intros y Hy; mem_cases Hy|done]. }
  cbn. tstep; [tstep|]. cbn. tstep; [tstep|apply KTClos|done|].
  apply ubs_intro; [intros y Hy; mem_cases Hy|done].
Qed.

(** The world with program order only, on the constants [as]. *)
Definition Wpo (cs : list nat) : world :=
  wgen (list_to_set (NConst <$> cs)) (λ _ _, False) (λ _ _, False).

Lemma Wpo_strict cs : strict (Wpo cs).
Proof.
  apply (wgen_strict _ _ _ id (prank (λ _, 1) (λ _, 0) (λ _ _ _, 0))); try done.
  - intros p Hp. apply elem_of_list_to_set, list_elem_of_fmap in Hp as (a & -> & _). by exists a.
  - intros x. apply prank_shift. lia.
Qed.

Lemma sync_deadlock_free : deadlock_free (∅, {[+ sync_main +]}).
Proof.
  apply (soundness (Wpo [0]) _ TUnit (Wpo_strict _)).
  apply ptyped_closed; [constructor|]. apply sync_typed; [apply Wpo_strict|].
  unfold pt_known, Wpo. simpl. set_solver.
Qed.

(** The world with program order and the facts [L] on the constants [cs]. *)
Definition Wfacts (cs : list nat) (L : list (point * point)) : world :=
  wgen (list_to_set (NConst <$> cs)) (λ _ _, False) (λ x y, (x, y) ∈ L).

Lemma Wfacts_strict cs L k g h :
  (∀ p, 0 < k p) →
  Forall (λ p, pt_root p.1 ∈ NConst <$> cs ∧ pt_root p.2 ∈ NConst <$> cs) L →
  Forall (λ p, prank k g h p.1 < prank k g h p.2) L →
  strict (Wfacts cs L).
Proof.
  intros Hk HL Hr. apply (wgen_strict _ _ _ id (prank k g h)); try done.
  - intros p Hp. apply elem_of_list_to_set, list_elem_of_fmap in Hp as (a & -> & _). by exists a.
  - intros x y Hxy. right. rewrite Forall_forall in HL. destruct (HL _ Hxy) as [H1 H2].
    rewrite !elem_of_list_to_set. by split.
  - intros x. by apply prank_shift.
  - intros x y Hxy. rewrite Forall_forall in Hr. apply (Hr _ Hxy).
Qed.

Lemma Wfacts_lt cs L x y : (x, y) ∈ L → w_lt (Wfacts cs L) x y.
Proof. intros H. by apply glt_base. Qed.

Lemma Wfacts_known cs L a : a ∈ cs → pt_known (Wfacts cs L) (pc a 0).
Proof. intros H. unfold pt_known. simpl. apply elem_of_list_to_set, list_elem_of_fmap. eauto. Qed.

(** ** cycle: typable

    cycle = let (c, c′) = new ∗ in let (d, d′) = new ∗ in
            let () = spawn (λu. let () = u in let () = close c′ in close d′) in
            let () = close c in close d

    c, c′ : Close@(a,0) and d, d′ : Close@(b,0). Both threads close c
    while they hold d, so both need (a,0) ≺ (b,0), and the world has it.
    The paper's P-Connect over {c, d} is here the closed program that
    creates both channels. *)

Definition cycle_thunk : expr :=
  Lam (LetU (Var 0) (LetU (App EClos (Var 3)) (App EClos (Var 1)))).

Definition cycle_main : expr :=
  LetP (App ENew EUnit) (LetP (App ENew EUnit)
    (LetU (App ESpawn cycle_thunk) (LetU (App EClos (Var 3)) (App EClos (Var 1))))).

Lemma cycle_typed W : world_wf W → pt_known W (pc 0 0) → pt_known W (pc 1 0) →
  w_lt W (pc 0 0) (pc 1 0) →
  typed W ∅ [] ∅ [] (∅, None) cycle_main TUnit.
Proof.
  intros HW Ha Hb Hab. unfold cycle_main.
  tstep.
  { tstep; [tstep|apply (KTNew _ _ _ SEnd (pc 0 0) Ha)|done|apply ubs_none]. }
  cbn. tstep.
  { tstep; [tstep|apply (KTNew _ _ _ SEnd (pc 1 0) Hb)|done|apply ubs_none]. }
  cbn. tstep.
  { tstep.
    - eapply (tv_lam W HW _ _ _ _ _ TUnit TUnit (Some (pc 1 0)) (Some (pc 0 0)) 0); [set_solver| |].
      { intros y Hy. mem_cases Hy; first [apply sle_refl, HW|right; by apply sl_w]. }
      cbn. tstep; [tstep|]. cbn. tstep.
      + tstep; [tstep|apply KTClos|done|].
        apply ubs_intro; [intros y Hy; mem_cases Hy; by apply sl_w|].
        exists (pc 1 0). split; [done|]. right. by apply sl_w.
      + tstep; [tstep|apply KTClos|done|].
        apply ubs_intro; [intros y Hy; mem_cases Hy|].
        exists (pc 1 0). split; [done|]. apply sle_refl, HW.
    - apply KTSpawn.
    - done.
    - apply ubs_none. }
  cbn. tstep.
  { tstep; [tstep|apply KTClos|done|]. apply ubs_intro; [|done].
    intros y Hy. mem_cases Hy. by apply sl_w. }
  tstep; [tstep|apply KTClos|done|]. apply ubs_intro; [intros y Hy; mem_cases Hy|done].
Qed.

Definition Wcycle : world := Wfacts [0; 1] [(pc 0 0, pc 1 0)].

Lemma Wcycle_strict : strict Wcycle.
Proof.
  apply (Wfacts_strict _ _ (λ _, 1) (λ a, 10 * a) (λ _ _ _, 0)); [lia| |].
  - apply Forall_singleton. cbn. set_solver.
  - apply Forall_singleton. cbn. lia.
Qed.

Lemma cycle_deadlock_free : deadlock_free (∅, {[+ cycle_main +]}).
Proof.
  apply (soundness Wcycle _ TUnit Wcycle_strict).
  apply ptyped_closed; [constructor|]. apply cycle_typed; [apply Wcycle_strict| | |].
  - apply Wfacts_known. set_solver.
  - apply Wfacts_known. set_solver.
  - apply Wfacts_lt. set_solver.
Qed.

Lemma Wfacts_known_root cs L x a : pt_root x = NConst a → a ∈ cs → pt_known (Wfacts cs L) x.
Proof. intros Hx H. unfold pt_known. rewrite Hx. simpl. apply elem_of_list_to_set, list_elem_of_fmap. eauto. Qed.

(** E-Const at send and recv: the payload is scoped by its binders. *)
Ltac kscope := cbn; repeat split; try done; intros ? Hv; injection Hv; lia.

(** ** delegation: typable

    delegation = let (c, c′) = new ∗ in let (d, d′) = new ∗ in
                 let () = spawn (λu. let () = u in let (e, c′) = recv c′ in
                                     let () = close (send ⟨∗, e⟩) in close c′) in
                 let (c, u) = ⟨send ⟨d, c⟩, ∗⟩ in let () = u in
                 let (x, d′) = recv d′ in let () = x in let () = close d′ in close c

    c : !(∃ι. (!∗.Close)@ι).Close@(a,0). The receiver gets d at the slot
    (a,0)[0], written s below, and acts on it while it holds c′ at
    (a,1), so it needs (s,0) ≺ (a,1) and (s,1) ≺ (a,1): this is the
    spec's c[k][1] ≺ (c,k+1), slots counted from 0 here. The sender
    creates d at s itself, so the alias of the spec is the choice of
    the point of [new]. send asks (a,0) ≺ (s,0) (KTSend, {ι} ≺ heads of
    the payload), which the sender also needs because it holds d′ at s.
    ⟨send ⟨d, c⟩, ∗⟩ stands for a let of one variable. *)

Definition Sd : sty := SSnd 0 TUnit SEnd.
Definition Sdel : sty := SSnd 1 (TSess Sd (pvar 0)) SEnd.
Abbreviation ps k := (Pt (NSlot (NConst 0) 0 0) k).

Definition deleg_thunk : expr :=
  Lam (LetU (Var 0) (LetP (App ERecv (Var 3))
    (LetU (App EClos (App ESend (Pair EUnit (Var 1)))) (App EClos (Var 0))))).

Definition deleg_main : expr :=
  LetP (App ENew EUnit) (LetP (App ENew EUnit)
    (LetU (App ESpawn deleg_thunk)
      (LetP (Pair (App ESend (Pair (Var 1) (Var 3))) EUnit)
        (LetU (Var 0)
          (LetP (App ERecv (Var 2))
            (LetU (Var 1) (LetU (App EClos (Var 0)) (App EClos (Var 3))))))))).

Lemma deleg_typed W : world_wf W → pt_known W (pc 0 0) →
  w_lt W (pc 0 0) (ps 0) → w_lt W (ps 1) (pc 0 1) →
  typed W ∅ [] ∅ [] (∅, None) deleg_main TUnit.
Proof.
  intros HW Ha H1 H2.
  assert (w_lt W (ps 0) (pc 0 1)) as H3.
  { eapply (wf_lt_trans _ HW); [apply (wf_lt_po _ HW (ps 0))|exact H2]. }
  assert (pt_known W (ps 0)) as Hs by exact Ha.
  unfold deleg_main.
  tstep.
  { tstep; [tstep|apply (KTNew _ _ _ Sdel (pc 0 0) Ha)|done|apply ubs_none]. }
  cbn. tstep.
  { tstep; [tstep|apply (KTNew _ _ _ Sd (ps 0) Hs)|done|apply ubs_none]. }
  cbn. tstep.
  { tstep.
    - eapply (tv_lam W HW _ _ _ _ _ TUnit TUnit (Some (pc 0 1)) (Some (pc 0 0)) 0); [set_solver| |].
      { intros y Hy. mem_cases Hy. apply sle_refl, HW. }
      cbn. tstep; [tstep|]. cbn. tstep.
      + tstep; [tstep|apply (KTRecv _ _ _ 1 (TSess Sd (pvar 0)) SEnd (pc 0 0))|kscope|].
        apply ubs_intro; [intros y Hy; mem_cases Hy|].
        exists (pc 0 1). split; [done|]. right. apply (slt_po W _ (pc 0 0) HW).
      + cbn. tstep.
        * tstep.
          -- tstep; [|apply (KTSend _ _ _ 0 TUnit SEnd (ps 0)); cbn; set_solver|done|].
             ++ tstep; tstep.
             ++ apply ubs_intro; [intros y Hy; mem_cases Hy; by apply sl_w|].
                exists (pc 0 1). split; [done|]. right. by apply sl_w.
          -- apply KTClos.
          -- done.
          -- apply ubs_intro; [intros y Hy; mem_cases Hy; by apply sl_w|].
             exists (pc 0 1). split; [done|]. right. by apply sl_w.
        * tstep; [tstep|apply KTClos|done|].
          apply ubs_intro; [intros y Hy; mem_cases Hy|].
          exists (pc 0 1). split; [done|]. apply sle_refl, HW.
    - apply KTSpawn.
    - done.
    - apply ubs_none. }
  cbn. tstep.
  { tstep; [tstep|].
    tstep; [|apply (KTSend _ _ _ 1 (TSess Sd (pvar 0)) SEnd (pc 0 0))| |].
    - tstep; tstep.
    - cbn. intros h Hh. mem_cases Hh. by apply sl_w.
    - kscope.
    - apply ubs_intro; [|done]. intros y Hy. mem_cases Hy. by apply sl_w. }
  cbn. tstep; [tstep|]. cbn. tstep.
  { tstep; [tstep|apply KTRecv|kscope|].
    apply ubs_intro; [|done]. intros y Hy. mem_cases Hy. by apply sl_w. }
  cbn. tstep; [tstep|]. cbn. tstep.
  { tstep; [tstep|apply KTClos|done|].
    apply ubs_intro; [|done]. intros y Hy. mem_cases Hy. by apply sl_w. }
  tstep; [tstep|apply KTClos|done|]. apply ubs_intro; [intros y Hy; mem_cases Hy|done].
Qed.

Definition Wdeleg : world := Wfacts [0] [(pc 0 0, ps 0); (ps 1, pc 0 1)].

Definition kdel (p : pname) : nat := match p with NConst _ => 10 | _ => 1 end.

Lemma Wdeleg_strict : strict Wdeleg.
Proof.
  apply (Wfacts_strict _ _ kdel (λ _, 0) (λ _ _ _, 15)); [intros []; cbn; lia| |].
  - repeat apply Forall_cons_2; try apply Forall_nil_2; cbn; set_solver.
  - repeat apply Forall_cons_2; try apply Forall_nil_2; cbn; lia.
Qed.

Lemma deleg_deadlock_free : deadlock_free (∅, {[+ deleg_main +]}).
Proof.
  apply (soundness Wdeleg _ TUnit Wdeleg_strict).
  apply ptyped_closed; [constructor|]. apply deleg_typed; [apply Wdeleg_strict| | |].
  - apply Wfacts_known. set_solver.
  - apply Wfacts_lt. set_solver.
  - apply Wfacts_lt. set_solver.
Qed.

(** ** scheduler: typable

    Milner's scheduler with three agents on a ring r₀, r₁, r₂ (the paper
    era's Scheduler.v), as a closed program:

      ag₀ = let () = close (send ⟨∗, r₀⟩) in recvclose r₂          (main)
      ag₁ = link ⟨r₁, r₀⟩                                          (spawned)
      ag₂ = let () = recvclose r₁ in close (send ⟨∗, r₂⟩)          (spawned)
      recvclose r = let (x, r) = recv r in let () = x in close r

    r₀ lives at (a,0), r₂ at (b,0) and r₁ at (c,0). link asks
    (c,0) ≡ (a,0) (KTLink), the spec's (r₁,0) ≡ (r₀,0). ag₀ holds r₂ while
    it sends and closes r₀, so it needs (a,1) ≺ (b,0). ag₂ holds r₂ while
    it receives on and closes r₁, so it needs (c,0) ≺ (b,0) and
    (c,1) ≺ (b,0), which follow through the alias and successor
    congruence. The world has the alias and (a,1) ≺ (b,0).

    Reversed ag₀ = let () = recvclose r₂ in close (send ⟨∗, r₀⟩) is
    rejected: it receives on r₂ at (b,0) while it holds r₀ at (a,0), so
    E-Let* and E-App ask (b,0) ≺ (a,0), while ag₂ asks (c,0) ≺ (b,0), and
    (c,0) ≡ (a,0) closes the cycle (a,0) ≺ (b,0) ≺ (a,0). No strict world
    has all three, and link needs the alias whatever points [new] picks
    for r₀ and r₁. *)

Definition sendclose (v : expr) : expr := App EClos (App ESend (Pair EUnit v)).
Definition recvclose (v : expr) : expr := LetP (App ERecv v) (LetU (Var 1) (App EClos (Var 0))).

Definition ag1_thunk : expr := Lam (LetU (Var 0) (App ELink (Pair (Var 4) (Var 5)))).
Definition ag2_thunk : expr := Lam (LetU (Var 0) (LetU (recvclose (Var 3)) (sendclose (Var 2)))).
Definition ag0 : expr := LetU (sendclose (Var 5)) (recvclose (Var 0)).

Definition sched_main : expr :=
  LetP (App ENew EUnit) (LetP (App ENew EUnit) (LetP (App ENew EUnit)
    (LetU (App ESpawn ag1_thunk) (LetU (App ESpawn ag2_thunk) ag0)))).

Lemma sched_typed W : world_wf W →
  pt_known W (pc 0 0) → pt_known W (pc 1 0) → pt_known W (pc 2 0) →
  w_eq W (pc 2 0) (pc 0 0) → w_lt W (pc 0 1) (pc 1 0) →
  typed W ∅ [] ∅ [] (∅, None) sched_main TUnit.
Proof.
  intros HW Ha Hb Hc Hca Hab.
  assert (w_lt W (pc 0 0) (pc 1 0)) as Ha0b.
  { eapply (wf_lt_trans _ HW); [apply (wf_lt_po _ HW (pc 0 0))|exact Hab]. }
  assert (w_lt W (pc 2 0) (pc 1 0)) as Hc0b.
  { eapply (wf_lt_eq _ HW); [exact Hca|exact Ha0b|apply (wf_eq_refl _ HW)]. }
  assert (w_lt W (pc 2 1) (pc 1 0)) as Hc1b.
  { eapply (wf_lt_eq _ HW); [apply (wf_eq_shift _ HW _ _ Hca)|exact Hab|apply (wf_eq_refl _ HW)]. }
  assert (w_lt W (pc 1 0) (pc 1 1)) as Hbb by apply (wf_lt_po _ HW (pc 1 0)).
  unfold sched_main.
  tstep.
  { tstep; [tstep|apply (KTNew _ _ _ Sd (pc 0 0) Ha)|done|apply ubs_none]. }
  cbn. tstep.
  { tstep; [tstep|apply (KTNew _ _ _ Sd (pc 2 0) Hc)|done|apply ubs_none]. }
  cbn. tstep.
  { tstep; [tstep|apply (KTNew _ _ _ Sd (pc 1 0) Hb)|done|apply ubs_none]. }
  cbn. tstep.
  { (* ag₁ = link ⟨r₁, r₀⟩ *)
    tstep.
    - eapply (tv_lam W HW _ _ _ _ _ TUnit TUnit (Some (pc 2 0)) (Some (pc 0 0)) 0); [set_solver| |].
      { intros y Hy. mem_cases Hy; first [apply sle_refl, HW|left; by apply (wf_eq_sym _ HW)]. }
      cbn. tstep; [tstep|]. cbn.
      tstep; [tstep; tstep|apply (KTLink _ _ _ Sd (pc 2 0) (pc 0 0) Hca)|done|].
      apply ubs_intro; [intros y Hy; mem_cases Hy|].
      exists (pc 2 0). split; [done|]. apply sle_refl, HW.
    - apply KTSpawn.
    - done.
    - apply ubs_none. }
  cbn. tstep.
  { (* ag₂ = let () = recvclose r₁ in close (send ⟨∗, r₂⟩) *)
    tstep.
    - eapply (tv_lam W HW _ _ _ _ _ TUnit TUnit (Some (pc 1 1)) (Some (pc 2 0)) 0); [set_solver| |].
      { intros y Hy. mem_cases Hy; first [apply sle_refl, HW|right; by apply sl_w]. }
      cbn. tstep; [tstep|]. cbn. tstep.
      + unfold recvclose. tstep.
        * tstep; [tstep|apply KTRecv|kscope|].
          apply ubs_intro; [intros y Hy; mem_cases Hy; by apply sl_w|].
          exists (pc 1 1). split; [done|]. right. apply sl_w. by eapply (wf_lt_trans _ HW).
        * cbn. tstep; [tstep|]. cbn. tstep; [tstep|apply KTClos|done|].
          apply ubs_intro; [intros y Hy; mem_cases Hy; by apply sl_w|].
          exists (pc 1 1). split; [done|]. right. apply sl_w. by eapply (wf_lt_trans _ HW).
      + unfold sendclose. tstep.
        * tstep; [tstep; tstep|apply (KTSend _ _ _ 0 TUnit SEnd (pc 1 0)); cbn; set_solver|done|].
          apply ubs_intro; [intros y Hy; mem_cases Hy|].
          exists (pc 1 1). split; [done|]. right. by apply sl_w.
        * apply KTClos.
        * done.
        * apply ubs_intro; [intros y Hy; mem_cases Hy|].
          exists (pc 1 1). split; [done|]. apply sle_refl, HW.
    - apply KTSpawn.
    - done.
    - apply ubs_none. }
  (* ag₀ *)
  cbn. unfold ag0, sendclose, recvclose. tstep.
  { tstep.
    - tstep; [tstep; tstep|apply (KTSend _ _ _ 0 TUnit SEnd (pc 0 0)); cbn; set_solver|done|].
      apply ubs_intro; [|done]. intros y Hy. mem_cases Hy. by apply sl_w.
    - apply KTClos.
    - done.
    - apply ubs_intro; [|done]. intros y Hy. mem_cases Hy. by apply sl_w. }
  cbn. tstep.
  { tstep; [tstep|apply KTRecv|kscope|]. apply ubs_intro; [intros y Hy; mem_cases Hy|done]. }
  cbn. tstep; [tstep|]. cbn. tstep; [tstep|apply KTClos|done|].
  apply ubs_intro; [intros y Hy; mem_cases Hy|done].
Qed.

(** The world: (c,0) ≡ (a,0) and (a,1) ≺ (b,0). The rank reads c as a. *)
Fixpoint ren20 (p : pname) : pname :=
  match p with
  | NConst a => if decide (a = 2) then NConst 0 else NConst a
  | NVar a => NVar a
  | NSlot q b i => NSlot (ren20 q) b i
  end.

Definition cn20 (x : point) : point := Pt (ren20 (pt_name x)) (pt_off x).

Definition Wsched : world :=
  wgen (list_to_set (NConst <$> [0; 1; 2]))
    (λ x y, x = pc 2 0 ∧ y = pc 0 0) (λ x y, x = pc 0 1 ∧ y = pc 1 0).

Lemma Wsched_strict : strict Wsched.
Proof.
  apply (wgen_strict _ _ _ cn20 (prank (λ _, 1) (λ a, 10 * a) (λ _ _ _, 0))).
  - intros p Hp. apply elem_of_list_to_set, list_elem_of_fmap in Hp as (a & -> & _). by exists a.
  - intros x y [-> ->]. right. unfold pt_root. simpl. set_solver.
  - intros x y [-> ->]. right. unfold pt_root. simpl. set_solver.
  - done.
  - done.
  - intros x y [-> ->]. done.
  - intros x. apply prank_shift. lia.
  - intros x y [-> ->]. vm_compute. lia.
Qed.

Lemma sched_deadlock_free : deadlock_free (∅, {[+ sched_main +]}).
Proof.
  apply (soundness Wsched _ TUnit Wsched_strict).
  apply ptyped_closed; [constructor|].
  apply sched_typed; [apply Wsched_strict|..].
  1-3: unfold pt_known; simpl; set_solver.
  - by apply geq_base.
  - by apply glt_base.
Qed.

(** ** factory: typable at one constant point, not under □∀ι

    The spec's factory is a box □(∀ι.^⊥ ∗ ⊸ S@ι) whose body runs new and
    spawns the worker, so that every request yields a session at a
    point the caller picks. That box does not type (SHARP-EDGES 59).
    Its body must create the channel at the point variable ι, and KTNew
    asks pt_known W ι, the premise of sharp edges 49. A well-formed world
    knows constants only (wf_names_const), so no world knows a point
    variable ([pvar_unknown]). A value of type S@ι cannot come from
    elsewhere either: E-Conv compares points by equality (eqT), E-Ch
    needs a channel of Θ, which a box body (E-Exp, Θ = ∅) lacks, and a
    payload received at x lives at the slots of x, not at ι.

    What types is the factory at one constant point:

      fac  = !(f = λu. let () = u in let (c, c′) = new ∗ in
                       let () = spawn (λv. let () = v in close (send ⟨∗, c⟩)) in c′)
           : □(∗ ⊸^⊥_⊤ (?∗.Close)@(a,0))
      main = let (f, u) = ⟨fac, ∗⟩ in let () = u in
             let () = recvclose ((force f) ∗) in recvclose ((force f) ∗)

    f is used twice (contraction at □). Both sessions live at (a,0), so
    the client must finish one before it requests the next: holding
    both while it blocks on one would ask (a,0) ≺ (a,0). *)

Lemma pvar_unknown W a : world_wf W → ¬ pt_known W (pvar a).
Proof. intros HW Hk. destruct (wf_names_const _ HW _ Hk) as [b Hb]. done. Qed.

Definition Tfac_body : ty := TLolli None None TUnit (TSess (SRcv 0 TUnit SEnd) (pc 0 0)).
Definition Tfac : ty := TBox 0 [] None Tfac_body.

Definition fac : expr :=
  EBox (Lam (LetU (Var 0) (LetP (App ENew EUnit)
    (LetU (App ESpawn (Lam (LetU (Var 0) (sendclose (Var 2))))) (Var 0))))).

Definition request : expr := recvclose (App (App EForce (Var 1)) EUnit).

Definition fac_main : expr :=
  LetP (Pair fac EUnit) (LetU (Var 0) (LetU request request)).

Lemma fac_typed W : world_wf W → pt_known W (pc 0 0) →
  typed W ∅ [] ∅ [] (∅, None) fac_main TUnit.
Proof.
  intros HW Ha. unfold fac_main.
  tstep.
  { tstep; [tstep|].
    apply (t_box W _ _ _ _ _ 0 [] None Tfac_body 0); [by apply allunl_unl|set_solver|].
    cbn. eapply (tv_lam W HW _ _ _ _ _ TUnit _ None None 1); [set_solver|cbn; set_solver|].
    cbn. tstep; [tstep|]. cbn. tstep.
    { tstep; [tstep|apply (KTNew _ _ _ Sd (pc 0 0) Ha)|done|apply ubs_none]. }
    cbn. tstep; [|tstep].
    tstep; [|apply KTSpawn|done|apply ubs_none].
    eapply (tv_lam W HW _ _ _ _ _ TUnit TUnit (Some (pc 0 1)) (Some (pc 0 0)) 2); [set_solver| |].
    { intros y Hy. mem_cases Hy. apply sle_refl, HW. }
    cbn. tstep; [tstep|]. cbn. unfold sendclose. tstep.
    - tstep; [tstep; tstep|apply (KTSend _ _ _ 0 TUnit SEnd (pc 0 0)); cbn; set_solver|done|].
      apply ubs_intro; [intros y Hy; mem_cases Hy|].
      exists (pc 0 1). split; [done|]. right. apply (slt_po W _ (pc 0 0) HW).
    - apply KTClos.
    - done.
    - apply ubs_intro; [intros y Hy; mem_cases Hy|].
      exists (pc 0 1). split; [done|]. apply sle_refl, HW. }
  cbn. tstep; [tstep|]. cbn.
  assert (∀ P, (∀ y, y ∈ P → False) →
    typed W ∅ [] ∅ [None; Some Tfac] (P, None) request TUnit) as Hreq.
  { intros P HP. unfold request, recvclose. tstep.
    - tstep; [| | |].
      + eapply tv_app; [exact HW|reflexivity| |tstep|apply ubs_none].
        cbn. apply (typed_force W _ _ _ _ _ _ 0 [] None Tfac_body []); [done|done| |apply ubs_none|tstep].
        intros q Hq. by apply elem_of_nil in Hq.
      + apply KTRecv.
      + kscope.
      + apply ubs_intro; [|done]. intros y Hy. cbn in Hy.
        rewrite elem_of_union in Hy. destruct Hy as [Hy|Hy]; [by destruct (HP y)|set_solver].
    - cbn. tstep; [tstep|]. cbn. tstep; [tstep|apply KTClos|done|].
      apply ubs_intro; [|done]. intros y Hy. by destruct (HP y). }
  tstep; apply Hreq; cbn; set_solver.
Qed.

Lemma fac_deadlock_free : deadlock_free (∅, {[+ fac_main +]}).
Proof.
  apply (soundness (Wpo [0]) _ TUnit (Wpo_strict _)).
  apply ptyped_closed; [constructor|]. apply fac_typed; [apply Wpo_strict|].
  unfold pt_known, Wpo. simpl. set_solver.
Qed.
