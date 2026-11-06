(** * The guard with a mark per variable (liveness.md §10)

    [ok f x e] of Guard.v checks one later variable x with the flag f.
    The fundamental theorem of the guarded fragment passes E-Contract,
    which renames two variables to one, and nested boxes, inside which
    the self of the enclosing box stays later. So it reads the guard
    with a mark per variable: [L y = Some f] says y is later and may be
    forced and applied when f holds ([okM]). [ok] and [okv] are its
    instances with one mark ([ok_okM], [okv_okR]), and [okM] is
    invariant under renaming ([okM_rename]). *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export liveness.Guard.

Set Default Proof Using "All".

Definition lmark : Type := nat → option bool.

(** No variable is later. *)
Definition noL : lmark := λ _, None.

Definition is_lam (e : expr) : bool := match e with Lam _ => true | _ => false end.

Definition marked (L : lmark) (y : nat) : bool := match L y with Some _ => true | None => false end.

Definition force_var (e : expr) : option nat :=
  match e with App (Konst KForce) (Var y) => Some y | _ => None end.

Fixpoint occursM (L : lmark) (e : expr) : bool :=
  match e with
  | Var y => marked L y
  | EUnit | Konst _ | Chan _ => false
  | Lam e | EBox e => occursM (None .: L) e
  | App e1 e2 | Pair e1 e2 | LetU e1 e2 => occursM L e1 || occursM L e2
  | LetP e1 e2 => occursM L e1 || occursM (None .: None .: L) e2
  | Inj1 e | Inj2 e => occursM L e
  | Case e e1 e2 => occursM L e || occursM (None .: L) e1 || occursM (None .: L) e2
  end.

Fixpoint okM (L : lmark) (e : expr) : bool :=
  match e with
  | Var y => negb (marked L y)
  | EUnit | Konst _ | Chan _ => true
  | Lam b | EBox b => negb (occursM (None .: L) b)
  | App e1 e2 =>
      match force_var e1 with
      | Some y => match L y with Some f => f && gd e2 && okM L e2 | None => okM L e2 end
      | None =>
          match e1 with
          | Lam b => okM L e2 && (gd e2 || okM (None .: L) b)
          | _ => okM L e1 && (gd e1 || okM L e2)
          end
      end
  | Pair e1 e2 | LetU e1 e2 => okM L e1 && (gd e1 || okM L e2)
  | LetP e1 e2 => okM L e1 && (gd e1 || okM (None .: None .: L) e2)
  | Inj1 e | Inj2 e => okM L e
  | Case e e1 e2 => okM L e && (gd e || (okM (None .: L) e1 && okM (None .: L) e2))
  end.

(** Under the λs of a term the guard may hold of the body only. *)
Fixpoint okR (L : lmark) (e : expr) : bool :=
  okM L e || match e with Lam b => okR (None .: L) b | _ => false end.

(** Every box is guarded, its self marked with whether its body is a λ. *)
Fixpoint gallM (e : expr) : bool :=
  match e with
  | Var _ | EUnit | Konst _ | Chan _ => true
  | EBox b => okR (Some (is_lam b) .: noL) b && gallM b
  | Lam e | Inj1 e | Inj2 e => gallM e
  | App e1 e2 | Pair e1 e2 | LetU e1 e2 | LetP e1 e2 => gallM e1 && gallM e2
  | Case e e1 e2 => gallM e && gallM e1 && gallM e2
  end.

Ltac orstep :=
  match goal with
  | H : ?a || _ = true |- ?a || _ = true => apply orb_true_iff in H as [H|H]; apply orb_true_iff; [by left|right]
  end.

Ltac bool_simpl :=
  repeat match goal with
  | H : _ && _ = true |- _ => apply andb_true_iff in H as [? ?]
  | H : negb _ = true |- _ => apply negb_true_iff in H
  | |- _ && _ = true => apply andb_true_iff; split
  end.

(** ** Renaming *)

Lemma up_ren (L L' : lmark) ρ : (∀ i, L' i = L (ρ i)) → ∀ i, (None .: L') i = (None .: L) (upren ρ i).
Proof. intros H [|i]; simpl; [done|apply H]. Qed.

Lemma occursM_rename e : ∀ ρ L L', (∀ i, L' i = L (ρ i)) → occursM L (rename ρ e) = occursM L' e.
Proof.
  induction e as [x| |k|c|e IH|e1 IH1 e2 IH2|e1 IH1 e2 IH2|e1 IH1 e2 IH2|e1 IH1 e2 IH2
                 |e IH|e IH|e IH e1 IH1 e2 IH2|e IH]; intros ρ L L' HL; simpl; try done.
  - unfold marked. by rewrite HL.
  - by apply IH, up_ren.
  - by rewrite (IH1 _ _ L'), (IH2 _ _ L').
  - by rewrite (IH1 _ _ L'), (IH2 _ _ L').
  - by rewrite (IH1 _ _ L'), (IH2 _ _ L').
  - rewrite (IH1 _ _ L'), (IH2 (upren (upren ρ)) (None .: None .: L) (None .: None .: L')); [done|by do 2 apply up_ren|done].
  - by apply IH.
  - by apply IH.
  - rewrite (IH _ _ L'), (IH1 (upren ρ) (None .: L) (None .: L')), (IH2 (upren ρ) (None .: L) (None .: L'));
      [done|by apply up_ren..|done].
  - by apply IH, up_ren.
Qed.

Lemma gd_rename_aux e : ∀ ρ, gd (rename ρ e) = gd e ∧
  (match e with Lam b => ∀ ρ, gd (rename ρ b) = gd b | _ => True end).
Proof.
  induction e as [x| |k|c|e IH|e1 IH1 e2 IH2|e1 IH1 e2 IH2|e1 IH1 e2 IH2|e1 IH1 e2 IH2
                 |e IH|e IH|e IH e1 IH1 e2 IH2|e IH]; intros ρ; simpl; try done.
  - split; [done|]. intros ρ'. apply IH.
  - split; [|done]. destruct (IH1 ρ) as [H1 H1']. rewrite (proj1 (IH2 ρ)).
    destruct e1; simpl in *; first [done|by rewrite H1|by rewrite H1'|idtac].
  - by rewrite (proj1 (IH1 ρ)), (proj1 (IH2 ρ)).
  - by rewrite (proj1 (IH1 ρ)), (proj1 (IH2 ρ)).
  - by rewrite (proj1 (IH1 ρ)), (proj1 (IH2 _)).
  - by rewrite (proj1 (IH ρ)).
  - by rewrite (proj1 (IH ρ)).
  - by rewrite (proj1 (IH ρ)), (proj1 (IH1 _)), (proj1 (IH2 _)).
Qed.

Lemma gd_rename e ρ : gd (rename ρ e) = gd e.
Proof. apply gd_rename_aux. Qed.

Lemma force_var_some e y : force_var e = Some y → e = App EForce (Var y).
Proof.
  destruct e as [| | | | |e1 e2| | | | | | |]; try done.
  destruct e1 as [| |k| | | | | | | | | |]; try done. destruct k; try done.
  destruct e2; try done. simpl. by intros [= ->].
Qed.

Lemma force_var_rename ρ e : force_var (rename ρ e) = option_map ρ (force_var e).
Proof.
  destruct e as [| | | | |e1 e2| | | | | | |]; try done.
  destruct e1 as [| |k| | | | | | | | | |]; try done. destruct k; try done.
  destruct e2; done.
Qed.

Lemma is_lam_rename ρ e : is_lam (rename ρ e) = is_lam e.
Proof. by destruct e. Qed.

Lemma okM_app_gen L e1 e2 : force_var e1 = None → is_lam e1 = false →
  okM L (App e1 e2) = okM L e1 && (gd e1 || okM L e2).
Proof.
  intros Hf Hl. destruct e1 as [| | | | |e11 e12| | | | | | |]; try done.
  cbn -[force_var gd]. by rewrite Hf.
Qed.

Lemma okM_rename_aux e : ∀ ρ L L', (∀ i, L' i = L (ρ i)) → okM L (rename ρ e) = okM L' e ∧
  (match e with Lam b => ∀ ρ L L', (∀ i, L' i = L (ρ i)) →
     okM (None .: L) (rename (upren ρ) b) = okM (None .: L') b | _ => True end).
Proof.
  induction e as [x| |k|c|e IH|e1 IH1 e2 IH2|e1 IH1 e2 IH2|e1 IH1 e2 IH2|e1 IH1 e2 IH2
                 |e IH|e IH|e IH e1 IH1 e2 IH2|e IH]; intros ρ L L' HL; simpl; try done.
  - unfold marked. by rewrite HL.
  - split; [by erewrite occursM_rename; [|apply up_ren]|].
    intros ρ' L1 L1' HL1. by apply IH, up_ren.
  - enough (okM L (App (rename ρ e1) (rename ρ e2)) = okM L' (App e1 e2) ∧ True) as Hen by exact Hen.
    split; [|done]. destruct (IH1 ρ L L' HL) as [H1 H1'].
    destruct (force_var e1) as [y|] eqn:Hf.
    + apply force_var_some in Hf as ->. simpl. by rewrite HL, gd_rename, (proj1 (IH2 ρ L L' HL)).
    + destruct (is_lam e1) eqn:Hl.
      * destruct e1 as [| | | |b| | | | | | | |]; try done. simpl.
        by rewrite (H1' ρ L L' HL), gd_rename, (proj1 (IH2 ρ L L' HL)).
      * rewrite !okM_app_gen; [|done|done|by rewrite force_var_rename, Hf|by rewrite is_lam_rename].
        by rewrite H1, gd_rename, (proj1 (IH2 ρ L L' HL)).
  - by rewrite (proj1 (IH1 ρ L L' HL)), (proj1 (IH2 ρ L L' HL)), gd_rename.
  - by rewrite (proj1 (IH1 ρ L L' HL)), (proj1 (IH2 ρ L L' HL)), gd_rename.
  - by rewrite (proj1 (IH1 ρ L L' HL)), (proj1 (IH2 (upren (upren ρ)) (None .: None .: L) (None .: None .: L')
      ltac:(by do 2 apply up_ren))), gd_rename.
  - split; [by apply IH|done].
  - split; [by apply IH|done].
  - by rewrite (proj1 (IH ρ L L' HL)), (proj1 (IH1 (upren ρ) (None .: L) (None .: L') ltac:(by apply up_ren))),
      (proj1 (IH2 (upren ρ) (None .: L) (None .: L') ltac:(by apply up_ren))), gd_rename.
  - by erewrite occursM_rename; [|apply up_ren].
Qed.

Lemma okM_rename e ρ L L' : (∀ i, L' i = L (ρ i)) → okM L (rename ρ e) = okM L' e.
Proof. intros H. by apply okM_rename_aux. Qed.

Definition okRl (L : lmark) (e : expr) : bool :=
  match e with Lam b => okR (None .: L) b | _ => false end.

Lemma okR_eq L e : okR L e = okM L e || okRl L e.
Proof. by destruct e. Qed.

Lemma okR_rename e : ∀ ρ L L', (∀ i, L' i = L (ρ i)) → okR L (rename ρ e) = okR L' e.
Proof.
  induction e; intros ρ L L' HL; rewrite (okR_eq L), (okR_eq L'), (okM_rename _ ρ L L' HL); try done.
  simpl. by rewrite (IHe _ _ (None .: L')); [|apply up_ren].
Qed.

Lemma gallM_rename e : ∀ ρ, gallM (rename ρ e) = gallM e.
Proof.
  induction e; intros ρ; simpl; rewrite ?IHe, ?IHe1, ?IHe2, ?IHe3; try done.
  rewrite is_lam_rename, (okR_rename _ _ _ (Some (is_lam e) .: noL)); [done|]. by intros [|i].
Qed.

(** ** No mark *)

Definition nooc_P (e : expr) : Prop := ∀ L, occursM L e = false → okM L e = true.

Lemma occursM_false_okM_aux e : nooc_P e ∧ match e with Lam b => nooc_P b | _ => True end.
Proof.
  induction e as [x| |k|c|e IH|e1 IH1 e2 IH2|e1 IH1 e2 IH2|e1 IH1 e2 IH2|e1 IH1 e2 IH2
                 |e IH|e IH|e IH e1 IH1 e2 IH2|e IH];
    (split; [intros L H|try done]).
  - simpl in *. by rewrite H.
  - done.
  - done.
  - done.
  - simpl in *. by rewrite H.
  - exact (proj1 IH).
  - simpl in H. apply orb_false_iff in H as [H1 H2].
    destruct (force_var e1) as [y|] eqn:Hf.
    + apply force_var_some in Hf as ->. simpl in *. unfold marked in H1.
      destruct (L y); [done|]. by apply (proj1 IH2).
    + destruct (is_lam e1) eqn:Hl.
      * destruct e1 as [| | | |b| | | | | | | |]; try done. simpl in *.
        by rewrite (proj1 IH2 L H2), (proj2 IH1 _ H1), orb_true_r.
      * rewrite okM_app_gen; [|done|done]. by rewrite (proj1 IH1 L H1), (proj1 IH2 L H2), orb_true_r.
  - simpl in *. apply orb_false_iff in H as [H1 H2]. by rewrite (proj1 IH1 L H1), (proj1 IH2 L H2), orb_true_r.
  - simpl in *. apply orb_false_iff in H as [H1 H2]. by rewrite (proj1 IH1 L H1), (proj1 IH2 L H2), orb_true_r.
  - simpl in *. apply orb_false_iff in H as [H1 H2]. by rewrite (proj1 IH1 L H1), (proj1 IH2 _ H2), orb_true_r.
  - simpl in *. by apply (proj1 IH).
  - simpl in *. by apply (proj1 IH).
  - simpl in *. apply orb_false_iff in H as [H H2]. apply orb_false_iff in H as [H0 H1].
    by rewrite (proj1 IH L H0), (proj1 IH1 _ H1), (proj1 IH2 _ H2), orb_true_r.
  - simpl in *. by rewrite H.
Qed.

Lemma occursM_false_okM e L : occursM L e = false → okM L e = true.
Proof. apply occursM_false_okM_aux. Qed.

Lemma occursM_noL e : ∀ L, (∀ i, L i = None) → occursM L e = false.
Proof.
  induction e; intros L HL; simpl; rewrite ?IHe, ?IHe1, ?IHe2, ?IHe3; try done;
    try (intros [|[|i]]; simpl; done).
  unfold marked. by rewrite HL.
Qed.

Lemma okM_okR L e : okM L e = true → okR L e = true.
Proof. intros H. by rewrite okR_eq, H. Qed.

Lemma okR_noL e : okR noL e = true.
Proof. apply okM_okR, occursM_false_okM, occursM_noL. done. Qed.

(** ** One mark: [ok] and [okv] *)

Definition only_mark (L : lmark) (x : nat) (f : bool) : Prop :=
  L x = Some f ∧ ∀ y, y ≠ x → L y = None.

Lemma only_mark_up L x f : only_mark L x f → only_mark (None .: L) (S x) f.
Proof.
  intros [Hx Hy]. split; [done|]. intros [|y] Hne; simpl; [done|]. apply Hy. lia.
Qed.

Lemma occursM_single e : ∀ L x f, only_mark L x f → occursM L e = occurs x e.
Proof.
  induction e as [y| |k|c|e IH|e1 IH1 e2 IH2|e1 IH1 e2 IH2|e1 IH1 e2 IH2|e1 IH1 e2 IH2
                 |e IH|e IH|e IH e1 IH1 e2 IH2|e IH]; intros L x f HL; simpl; try done.
  - destruct HL as [Hx Hy]. unfold marked. destruct (Nat.eq_dec x y) as [->|Hne].
    + by rewrite Hx, Nat.eqb_refl.
    + rewrite Hy; [|done]. symmetry. by apply Nat.eqb_neq.
  - apply (IH _ _ f), only_mark_up, HL.
  - by rewrite (IH1 L x f HL), (IH2 L x f HL).
  - by rewrite (IH1 L x f HL), (IH2 L x f HL).
  - by rewrite (IH1 L x f HL), (IH2 L x f HL).
  - by rewrite (IH1 L x f HL), (IH2 _ (S (S x)) f (only_mark_up _ _ _ (only_mark_up _ _ _ HL))).
  - apply (IH L x f HL).
  - apply (IH L x f HL).
  - by rewrite (IH L x f HL), (IH1 _ (S x) f (only_mark_up _ _ _ HL)), (IH2 _ (S x) f (only_mark_up _ _ _ HL)).
  - apply (IH _ _ f), only_mark_up, HL.
Qed.

Lemma ok_app_gen f x e1 e2 : force_var e1 = None → is_lam e1 = false →
  ok f x (App e1 e2) = ok f x e1 && (gd e1 || ok f x e2).
Proof.
  intros Hf Hl. destruct e1 as [| | | | |e11 e12| | | | | | |]; try done.
  destruct e11 as [| |k| | | | | | | | | |]; try done. destruct k; try done.
  destruct e12; done.
Qed.

Definition ok_okM_P (e : expr) : Prop := ∀ L x f, only_mark L x f → ok f x e = true → okM L e = true.

Lemma ok_okM_aux e : ok_okM_P e ∧ match e with Lam b => ok_okM_P b | _ => True end.
Proof.
  induction e as [y| |k|c|e IH|e1 IH1 e2 IH2|e1 IH1 e2 IH2|e1 IH1 e2 IH2|e1 IH1 e2 IH2
                 |e IH|e IH|e IH e1 IH1 e2 IH2|e IH];
    (split; [intros L x f HL H|try done]).
  - simpl in *. destruct HL as [Hx Hy]. unfold marked. destruct (Nat.eq_dec x y) as [->|Hne].
    + by rewrite Nat.eqb_refl in H.
    + by rewrite Hy.
  - done.
  - done.
  - done.
  - simpl in *. by erewrite occursM_single; [|apply only_mark_up; exact HL].
  - exact (proj1 IH).
  - destruct (force_var e1) as [y|] eqn:Hf.
    + apply force_var_some in Hf as ->. simpl in H |- *. destruct HL as [Hx Hy].
      destruct (Nat.eq_dec x y) as [->|Hne].
      * rewrite Nat.eqb_refl in H. rewrite Hx. bool_simpl; [done|done|].
        by apply (proj1 IH2 L y f).
      * rewrite (proj2 (Nat.eqb_neq x y) Hne) in H. rewrite Hy; [|done].
        by apply (proj1 IH2 L x f).
    + destruct (is_lam e1) eqn:Hl.
      * destruct e1 as [| | | |b| | | | | | | |]; try done. simpl in H |- *. bool_simpl.
        { by apply (proj1 IH2 L x f). }
        orstep.
        apply (proj2 IH1 (None .: L) (S x) f); [by apply only_mark_up|done].
      * rewrite okM_app_gen; [|done|done]. rewrite ok_app_gen in H; [|done|done]. bool_simpl.
        { by apply (proj1 IH1 L x f). }
        orstep; (by apply (proj1 IH2 L x f)).
  - simpl in *. bool_simpl; [by apply (proj1 IH1 L x f)|].
    orstep; (by apply (proj1 IH2 L x f)).
  - simpl in *. bool_simpl; [by apply (proj1 IH1 L x f)|].
    orstep; (by apply (proj1 IH2 L x f)).
  - simpl in *. bool_simpl; [by apply (proj1 IH1 L x f)|].
    orstep.
    apply (proj1 IH2 _ (S (S x)) f); [by do 2 apply only_mark_up|done].
  - simpl in *. by apply (proj1 IH L x f).
  - simpl in *. by apply (proj1 IH L x f).
  - simpl in *. bool_simpl; [by apply (proj1 IH L x f)|].
    orstep. bool_simpl.
    + apply (proj1 IH1 _ (S x) f); [by apply only_mark_up|done].
    + apply (proj1 IH2 _ (S x) f); [by apply only_mark_up|done].
  - simpl in *. by erewrite occursM_single; [|apply only_mark_up; exact HL].
Qed.

Lemma ok_okM e L x f : only_mark L x f → ok f x e = true → okM L e = true.
Proof. apply ok_okM_aux. Qed.

Lemma okv_okR e : ∀ L x f, only_mark L x (f || is_lam e) → okv f x e = true → okR L e = true.
Proof.
  induction e as [y| |k|c|b IH|e1 e2|e1 e2|e1 e2|e1 e2|e0|e0|e0 e1 e2|e0]; intros L x f HL H;
    try (apply okM_okR; eapply ok_okM; [|exact H]; simpl in HL; by rewrite orb_false_r in HL).
  rewrite okR_eq. apply orb_true_iff. right. apply (IH _ (S x) true); [|done].
  simpl in HL. rewrite orb_true_r in HL. by apply only_mark_up.
Qed.

Lemma gall_gallM e : gall e = true → gallM e = true.
Proof.
  induction e as [y| |k|c|e IH|e1 IH1 e2 IH2|e1 IH1 e2 IH2|e1 IH1 e2 IH2|e1 IH1 e2 IH2
                 |e IH|e IH|e IH e1 IH1 e2 IH2|e IH]; intros H; cbn [gall gallM] in *; bool_simpl; auto.
  apply (okv_okR _ _ 0 false); [|done]. split; [done|]. intros [|y] Hne; [lia|done].
Qed.

(** ** Adding marks that do not occur *)

Definition mark_union (L1 L2 : lmark) : lmark :=
  λ i, match L1 i with Some f => Some f | None => L2 i end.

Lemma mark_union_up L1 L2 L : (∀ i, L i = mark_union L1 L2 i) →
  ∀ i, (None .: L) i = mark_union (None .: L1) (None .: L2) i.
Proof. intros H [|i]; simpl; [done|apply H]. Qed.

Lemma occursM_union e : ∀ L1 L2 L, (∀ i, L i = mark_union L1 L2 i) →
  occursM L e = occursM L1 e || occursM L2 e.
Proof.
  induction e as [y| |k|c|e IH|e1 IH1 e2 IH2|e1 IH1 e2 IH2|e1 IH1 e2 IH2|e1 IH1 e2 IH2
                 |e IH|e IH|e IH e1 IH1 e2 IH2|e IH]; intros L1 L2 L HL; simpl; try done.
  - unfold marked, mark_union in *. rewrite HL. by destruct (L1 y), (L2 y).
  - by erewrite IH; [|apply mark_union_up].
  - erewrite IH1, IH2; [|done|done]. by destruct (occursM L1 e1), (occursM L2 e1), (occursM L1 e2), (occursM L2 e2).
  - erewrite IH1, IH2; [|done|done]. by destruct (occursM L1 e1), (occursM L2 e1), (occursM L1 e2), (occursM L2 e2).
  - erewrite IH1, IH2; [|done|done]. by destruct (occursM L1 e1), (occursM L2 e1), (occursM L1 e2), (occursM L2 e2).
  - erewrite IH1, IH2; [|by do 2 apply mark_union_up|done].
    by destruct (occursM L1 e1), (occursM L2 e1), (occursM _ e2), (occursM (None .: None .: L2) e2).
  - by apply IH.
  - by apply IH.
  - erewrite IH, IH1, IH2; [|by apply mark_union_up..|done].
    by destruct (occursM L1 e), (occursM L2 e), (occursM (None .: L1) e1), (occursM (None .: L2) e1),
      (occursM (None .: L1) e2), (occursM (None .: L2) e2).
  - by erewrite IH; [|apply mark_union_up].
Qed.

Definition okM_union_P (e : expr) : Prop := ∀ L1 L2 L, (∀ i, L i = mark_union L1 L2 i) →
  okM L1 e = true → occursM L2 e = false → okM L e = true.

Lemma okM_union_aux e : okM_union_P e ∧ match e with Lam b => okM_union_P b | _ => True end.
Proof.
  induction e as [y| |k|c|e IH|e1 IH1 e2 IH2|e1 IH1 e2 IH2|e1 IH1 e2 IH2|e1 IH1 e2 IH2
                 |e IH|e IH|e IH e1 IH1 e2 IH2|e IH];
    (split; [intros L1 L2 L HL H1 H2; simpl in *; rewrite ?orb_false_iff in H2|try done]).
  - unfold marked, mark_union in *. rewrite HL. by destruct (L1 y), (L2 y).
  - done.
  - done.
  - done.
  - erewrite occursM_union; [|apply mark_union_up; exact HL]. bool_simpl. by rewrite H1, H2.
  - exact (proj1 IH).
  - destruct H2 as [H21 H22].
    change (okM L (App e1 e2) = true). change (okM L1 (App e1 e2) = true) in H1.
    destruct (force_var e1) as [y|] eqn:Hf.
    + apply force_var_some in Hf as ->. simpl in H1, H21 |- *.
      unfold marked, mark_union in *. rewrite HL.
      destruct (L1 y) as [f|]; bool_simpl; try done.
      * by apply (proj1 IH2 L1 L2).
      * destruct (L2 y); [done|]. by apply (proj1 IH2 L1 L2).
    + destruct (is_lam e1) eqn:Hl.
      * destruct e1 as [| | | |b| | | | | | | |]; try done. simpl in H1, H21 |- *. bool_simpl.
        { by apply (proj1 IH2 L1 L2). }
        orstep. apply (proj2 IH1 (None .: L1) (None .: L2)); [by apply mark_union_up|done|done].
      * rewrite okM_app_gen; [|done|done]. rewrite okM_app_gen in H1; [|done|done]. bool_simpl.
        { by apply (proj1 IH1 L1 L2). }
        orstep. by apply (proj1 IH2 L1 L2).
  - destruct H2 as [H21 H22]. bool_simpl; [by apply (proj1 IH1 L1 L2)|].
    orstep; (by apply (proj1 IH2 L1 L2)).
  - destruct H2 as [H21 H22]. bool_simpl; [by apply (proj1 IH1 L1 L2)|].
    orstep; (by apply (proj1 IH2 L1 L2)).
  - destruct H2 as [H21 H22]. bool_simpl; [by apply (proj1 IH1 L1 L2)|].
    orstep.
    apply (proj1 IH2 (None .: None .: L1) (None .: None .: L2)); [by do 2 apply mark_union_up|done|done].
  - by apply (proj1 IH L1 L2).
  - by apply (proj1 IH L1 L2).
  - destruct H2 as [[H20 H21] H22]. bool_simpl; [by apply (proj1 IH L1 L2)|].
    orstep. bool_simpl.
    + apply (proj1 IH1 (None .: L1) (None .: L2)); [by apply mark_union_up|done|done].
    + apply (proj1 IH2 (None .: L1) (None .: L2)); [by apply mark_union_up|done|done].
  - erewrite occursM_union; [|apply mark_union_up; exact HL]. bool_simpl. by rewrite H1, H2.
Qed.

Lemma okM_union e L1 L2 L : (∀ i, L i = mark_union L1 L2 i) →
  okM L1 e = true → occursM L2 e = false → okM L e = true.
Proof. apply okM_union_aux. Qed.

Lemma okR_union e : ∀ L1 L2 L, (∀ i, L i = mark_union L1 L2 i) →
  okR L1 e = true → occursM L2 e = false → okR L e = true.
Proof.
  induction e as [y| |k|c|b IH|e1 e2|e1 e2|e1 e2|e1 e2|e0|e0|e0 e1 e2|e0]; intros L1 L2 L HL H1 H2;
    rewrite okR_eq in H1 |- *; apply orb_true_iff in H1 as [H1|H1]; apply orb_true_iff;
    try (left; by eapply okM_union); try done.
  right. simpl in *. eapply IH; [by apply mark_union_up|done|done].
Qed.
