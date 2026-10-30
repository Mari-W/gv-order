(** * Examples of PGV, deadlock free through the translation

    Each program is typed in the fragment of repaired PGV
    ([pgv_frag]), and [pgv_deadlock_free_applied] gives deadlock
    freedom of the program itself.

    - [ex21]: Example 2.1 of Kokke and Dardha (pdf p. 4). Two threads
      share two channels. PGV types it and GV does not.
    - [deleg]: the main thread sends one end of a channel over another
      channel, and the child uses it.
    - [lnk]: a child links two channels and two other threads talk
      through the link.

    Both counterexamples of docs/extensions/adequacy/pgv-counterexamples.txt
    fail at the step the repairs name ([cx1_rejected], [cx2_rejected]). *)

From stdpp Require Import base list.
From LRGV Require Export pgv.PGVTranslate.

Set Default Proof Using "All".

(** ** Splitting PGV environments by occurrence (as in ExampleTools.v) *)

Fixpoint plp (e : expr) (x : nat) (Γ : penv) : penv :=
  match Γ with
  | [] => []
  | None :: Γ' => None :: plp e (S x) Γ'
  | Some T :: Γ' => (if occ x e then Some T else None) :: plp e (S x) Γ'
  end.

Fixpoint psok (e1 : expr) (x1 : nat) (e2 : expr) (x2 : nat) (Γ : penv) : bool :=
  match Γ with
  | [] => true
  | None :: Γ' => psok e1 (S x1) e2 (S x2) Γ'
  | Some _ :: Γ' => xorb (occ x1 e1) (occ x2 e2) && psok e1 (S x1) e2 (S x2) Γ'
  end.

Lemma plp_split e1 x1 e2 x2 Γ :
  psok e1 x1 e2 x2 Γ = true → psplit Γ (plp e1 x1 Γ) (plp e2 x2 Γ).
Proof.
  revert x1 x2. induction Γ as [|[T|] Γ IH]; intros x1 x2 H; simpl in *; [constructor| |].
  - apply andb_true_iff in H as [H1 H2].
    destruct (occ x1 e1), (occ x2 e2); simpl in *; try done; constructor; by apply IH.
  - constructor. by apply IH.
Qed.

Definition pnone (Γ : penv) : bool := forallb (λ o, match o with None => true | _ => false end) Γ.

Fixpoint ponly (x : nat) (Γ : penv) : bool :=
  match Γ, x with
  | [], _ => false
  | Some _ :: Γ', 0 => pnone Γ'
  | None :: _, 0 => false
  | o :: Γ', S x' => match o with None => ponly x' Γ' | Some _ => false end
  end.

Lemma pnone_empty Γ : pnone Γ = true → penv_empty Γ.
Proof.
  induction Γ as [|o Γ IH]; simpl; intros H o' Ho'; [by apply elem_of_nil in Ho'|].
  destruct o; [done|]. apply elem_of_cons in Ho' as [->|Ho']; [done|by apply IH].
Qed.

Lemma ponly_only x Γ T : Γ !! x = Some (Some T) → ponly x Γ = true → penv_only Γ x T.
Proof.
  revert x. induction Γ as [|o Γ IH]; intros [|x] Hx H; simpl in *; try done.
  - simplify_eq. split; [done|]. intros [|y] T' Hy; simpl in Hy; [by simplify_eq|].
    apply list_elem_of_lookup_2, pnone_empty in Hy; [done|done].
  - destruct o; [done|]. destruct (IH x Hx H) as [H1 H2]. split; [done|].
    intros [|y] T' Hy; simpl in Hy; [done|]. destruct (H2 y T' Hy). split; [lia|done].
Qed.

(** ** Derived rules *)

Section rules.
  Context (ok : psty → Prop).

  Lemma pv_var Γ x T : Γ !! x = Some (Some T) → ponly x Γ = true → pgv_typed ok Γ PBot (Var x) T.
  Proof. intros. by apply pt_var, ponly_only. Qed.

  Lemma pv_unit Γ : pnone Γ = true → pgv_typed ok Γ PBot EUnit PUnit.
  Proof. intros. by apply pt_unit, pnone_empty. Qed.

  Lemma pv_konst Γ k T : pnone Γ = true → pgv_konst ok k T → pgv_typed ok Γ PBot (Konst k) T.
  Proof. intros. by apply pt_const; [apply pnone_empty|]. Qed.

  (** The argument comes first, so that its type is known. *)
  Lemma pv_app Γ M N T U p q p' q' :
    psok M 0 N 0 Γ = true →
    pgv_typed ok (plp N 0 Γ) q N T →
    pgv_typed ok (plp M 0 Γ) p M (PLolli p' q' T U) →
    prio_lt p (pr_env (plp N 0 Γ)) → prio_lt q p' →
    pgv_typed ok Γ (prio_max (prio_max p q) q') (App M N) U.
  Proof. intros Hs HN HM Hp Hq. eapply pt_app; [by apply plp_split|done..]. Qed.

  Lemma pv_letu Γ M N T p q :
    psok M 0 N 0 Γ = true →
    pgv_typed ok (plp M 0 Γ) p M PUnit →
    pgv_typed ok (plp N 0 Γ) q N T →
    prio_lt p (pr_env (plp N 0 Γ)) →
    pgv_typed ok Γ (prio_max p q) (LetU M N) T.
  Proof. intros Hs HM HN Hp. eapply pt_letu; [by apply plp_split|done..]. Qed.

  Lemma pv_pair Γ M N T U p q :
    psok M 0 N 0 Γ = true →
    pgv_typed ok (plp M 0 Γ) p M T →
    pgv_typed ok (plp N 0 Γ) q N U →
    prio_lt p (pr_env (plp N 0 Γ)) → prio_lt q (pr T) →
    pgv_typed ok Γ (prio_max p q) (Pair M N) (PProd T U).
  Proof. intros Hs HM HN Hp Hq. eapply pt_pair; [by apply plp_split|done..]. Qed.

  Lemma pv_letp Γ M N T T' U p q :
    psok M 0 N 2 Γ = true →
    pgv_typed ok (plp M 0 Γ) p M (PProd T T') →
    pgv_typed ok (Some T' :: Some T :: plp N 2 Γ) q N U →
    prio_lt p (pr_env (Some T' :: Some T :: plp N 2 Γ)) →
    pgv_typed ok Γ (prio_max p q) (LetP M N) U.
  Proof. intros Hs HM HN Hp. eapply pt_letp; [by apply plp_split|done..]. Qed.

  (** new at the session type S. *)
  Lemma pv_new Γ S :
    pnone Γ = true →
    pgv_typed ok Γ PBot (App (Konst KNew) EUnit) (PProd (PSess S) (PSess (pdual S))).
  Proof.
    intros H. change PBot with (prio_max (prio_max PBot PBot) PBot).
    eapply pt_app; [|apply pv_konst; [exact H|apply pk_new]|apply pv_unit; exact H|..].
    - clear -H. induction Γ as [|[] Γ IH]; simpl in *; [constructor|done|constructor; by apply IH].
    - clear -H. induction Γ as [|[] Γ IH]; simpl in *; [done|done|by apply IH].
    - done.
  Qed.
End rules.

Ltac side := cbn; first [exact I | reflexivity | lia | (repeat split; lia)].

Ltac pstep :=
  match goal with
  | |- pgv_typed _ _ _ (Var _) _ => apply pv_var; reflexivity
  | |- pgv_typed _ _ _ EUnit _ => apply pv_unit; reflexivity
  | |- pgv_typed _ _ _ (Konst _) _ => apply pv_konst; [reflexivity|econstructor; side]
  | |- pgv_typed _ _ _ (Lam _) _ => apply pt_lam
  | |- pgv_typed _ _ _ (App _ _) _ => eapply pv_app; [reflexivity| | | |]
  | |- pgv_typed _ _ _ (LetU _ _) _ => eapply pv_letu; [reflexivity| | |]
  | |- pgv_typed _ _ _ (Pair _ _) _ => eapply pv_pair; [reflexivity| | | |]
  | |- pgv_typed _ _ _ (LetP _ _) _ => eapply pv_letp; [reflexivity| | |]
  | |- prio_lt _ _ => side
  | |- _ = _ => side
  end.

(** new at S, then the body. *)
Ltac pnew S := eapply pv_letp; [reflexivity|apply (pv_new _ _ S); reflexivity| |side]; cbn [pdual].

(** ** Example 2.1 (p. 4)

    let (x, x′) = new () in let (y, y′) = new () in
    spawn (λ(). let ((), x′) = recv x′ in let y = send ((), y) in wait x′; close y);
    let x = send ((), x) in let ((), y′) = recv y′ in close x; wait y′

    x : !⁰1.end²_!  and  y : !¹1.end³_!. *)

Definition ex21_child : expr :=
  Lam (LetU (Var 0) (LetP (App (Konst KRecv) (Var 3))
    (LetU (Var 1) (plet (App (Konst KSend) (Pair EUnit (Var 4)))
      (LetU (App (Konst KClos) (Var 1)) (App (Konst KClos) (Var 0))))))).

Definition ex21_main : expr :=
  plet (App (Konst KSend) (Pair EUnit (Var 3)))
    (LetP (App (Konst KRecv) (Var 1))
      (LetU (Var 1) (LetU (App (Konst KClos) (Var 2)) (App (Konst KClos) (Var 0))))).

Definition ex21 : expr :=
  LetP (App (Konst KNew) EUnit) (LetP (App (Konst KNew) EUnit)
    (LetU (App (Konst KSpawn) ex21_child) ex21_main)).

Lemma ex21_typed : ∃ p, pgv_frag [] p ex21 PUnit.
Proof.
  eexists. unfold ex21, ex21_child, ex21_main, plet.
  pnew (PSnd 0 PUnit (PEndS 2)). pnew (PSnd 1 PUnit (PEndS 3)).
  repeat pstep.
Qed.

Theorem pgv_ex21_deadlock_free : deadlock_free (∅, {[+ ex21 +]}).
Proof. destruct ex21_typed as [p H]. by apply (pgv_deadlock_free_applied _ p). Qed.

(** ** Delegation

    let (x, x′) = new () in let (y, y′) = new () in
    spawn (λ(). let (z, y′) = recv y′ in let z = send ((), z) in close z; wait y′);
    let y = send (x, y) in let ((), x′) = recv x′ in wait x′; close y

    x : !²1.end³_!  and  y : !¹(!²1.end³_!).end⁴_!. The payload of y has
    priority 2 above the action at 1, as R1 asks. *)

Definition deleg_child : expr :=
  Lam (LetU (Var 0) (LetP (App (Konst KRecv) (Var 1))
    (plet (App (Konst KSend) (Pair EUnit (Var 1)))
      (LetU (App (Konst KClos) (Var 0)) (App (Konst KClos) (Var 1)))))).

Definition deleg_main : expr :=
  plet (App (Konst KSend) (Pair (Var 3) (Var 1)))
    (LetP (App (Konst KRecv) (Var 3))
      (LetU (Var 1) (LetU (App (Konst KClos) (Var 0)) (App (Konst KClos) (Var 2))))).

Definition deleg : expr :=
  LetP (App (Konst KNew) EUnit) (LetP (App (Konst KNew) EUnit)
    (LetU (App (Konst KSpawn) deleg_child) deleg_main)).

Lemma deleg_typed : ∃ p, pgv_frag [] p deleg PUnit.
Proof.
  eexists. unfold deleg, deleg_child, deleg_main, plet.
  pnew (PSnd 2 PUnit (PEndS 3)). pnew (PSnd 1 (PSess (PSnd 2 PUnit (PEndS 3))) (PEndS 4)).
  repeat pstep.
Qed.

Theorem pgv_deleg_deadlock_free : deadlock_free (∅, {[+ deleg +]}).
Proof. destruct deleg_typed as [p H]. by apply (pgv_deadlock_free_applied _ p). Qed.

(** ** Link

    let (x, x′) = new () in let (y, y′) = new () in
    spawn (λ(). link (x′, y));
    spawn (λ(). let x = send ((), x) in close x);
    let ((), y′) = recv y′ in wait y′

    x, y : !⁰1.end¹_!. The child links x′ to y, so the send on x reaches
    the receive on y′. *)

Definition lnk : expr :=
  LetP (App (Konst KNew) EUnit) (LetP (App (Konst KNew) EUnit)
    (LetU (App (Konst KSpawn) (Lam (LetU (Var 0) (App (Konst KLink) (Pair (Var 3) (Var 2))))))
      (LetU (App (Konst KSpawn) (Lam (LetU (Var 0)
              (plet (App (Konst KSend) (Pair EUnit (Var 4))) (App (Konst KClos) (Var 0))))))
        (LetP (App (Konst KRecv) (Var 0)) (LetU (Var 1) (App (Konst KClos) (Var 0))))))).

Lemma lnk_typed : ∃ p, pgv_frag [] p lnk PUnit.
Proof.
  eexists. unfold lnk, plet.
  pnew (PSnd 0 PUnit (PEndS 1)). pnew (PSnd 0 PUnit (PEndS 1)).
  repeat pstep.
Qed.

Theorem pgv_link_deadlock_free : deadlock_free (∅, {[+ lnk +]}).
Proof. destruct lnk_typed as [p H]. by apply (pgv_deadlock_free_applied _ p). Qed.

(** ** The counterexamples fail where the repairs say

    Program 2 of pgv-counterexamples.txt sends c′ : !¹1.end⁴_! over
    d : !³(!¹1.end⁴_!).end⁵_!. R1 rejects that send, whatever bound and
    type are asked for. Program 1 pairs c : !¹1.end⁷_! with a send on
    w : !⁵1.end⁹_!. R2 rejects that pair. *)

Lemma psplit_lookup_l Γ Γ1 Γ2 x T : psplit Γ Γ1 Γ2 → Γ1 !! x = Some (Some T) → Γ !! x = Some (Some T).
Proof. intros Hs. revert x. induction Hs; intros [|x] Hx; simpl in *; simplify_eq; auto. Qed.

Lemma psplit_lookup_r Γ Γ1 Γ2 x T : psplit Γ Γ1 Γ2 → Γ2 !! x = Some (Some T) → Γ !! x = Some (Some T).
Proof. intros Hs. revert x. induction Hs; intros [|x] Hx; simpl in *; simplify_eq; auto. Qed.

Lemma pgv_var_inv ok Γ p x T : pgv_typed ok Γ p (Var x) T → Γ !! x = Some (Some T).
Proof. inversion 1 as [? ? ? [Hx _]| | | | | | | | | |]; subst. done. Qed.

Ltac inv_var :=
  repeat match goal with H : pgv_typed _ _ _ (Var _) _ |- _ => apply pgv_var_inv in H end;
  repeat match goal with
    | Hs : psplit _ ?G1 _, H : ?G1 !! _ = Some (Some _) |- _ => eapply psplit_lookup_l in H; [|exact Hs]
    | Hs : psplit _ _ ?G2, H : ?G2 !! _ = Some (Some _) |- _ => eapply psplit_lookup_r in H; [|exact Hs]
    end;
  simpl in *; simplify_eq; simpl in *.

Ltac inv_konst :=
  match goal with H : pgv_typed _ _ _ (Konst _) _ |- _ =>
    let Hk := fresh "Hk" in apply pgv_konst_inv in H as (_ & _ & Hk); inversion Hk; subst end.

Definition cx_c' : pty := PSess (PSnd 1 PUnit (PEndS 4)).
Definition cx_d : pty := PSess (PSnd 3 cx_c' (PEndS 5)).

Lemma cx2_rejected ok p T :
  ¬ pgv_typed ok [Some cx_c'; Some cx_d] p (App (Konst KSend) (Pair (Var 0) (Var 1))) T.
Proof.
  inversion 1; subst. inv_konst.
  match goal with H : pgv_typed _ _ _ (Pair _ _) _ |- _ => inversion H; subst end.
  unfold cx_c', cx_d in *. inv_var. lia.
Qed.

Definition cx_c : pty := PSess (PSnd 1 PUnit (PEndS 7)).
Definition cx_w : pty := PSess (PSnd 5 PUnit (PEndS 9)).

Lemma cx1_rejected ok p T :
  ¬ pgv_typed ok [Some cx_c; Some cx_w] p
      (Pair (Var 0) (App (Konst KSend) (Pair EUnit (Var 1)))) T.
Proof.
  inversion 1; subst.
  match goal with H : pgv_typed _ _ _ (App _ _) _ |- _ => inversion H; subst end.
  inv_konst.
  match goal with H : pgv_typed _ _ _ (Pair _ _) _ |- _ => inversion H; subst end.
  unfold cx_c, cx_w in *. inv_var.
  match goal with H : prio_lt (prio_max (prio_max ?a ?b) _) _ |- _ =>
    destruct (prio_max a b); simpl in H; lia end.
Qed.
