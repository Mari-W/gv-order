(** * Programs the static system rejects

    Each section names the rule and the fact that fail. The one-round
    request/reply call is proved underivable ([rr_call_underivable]).
    The others carry the argument in a comment. *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export examples.ExampleTools.

Set Default Proof Using "All".

(** ** request/reply with one round only: the call does not type (SHARP-EDGES 60, 65)

    The server answers every request on a with a reply on b, forever:

      Sa = μX. ?∗.X      Sb = μX. !∗.X
      srv = !(f = λp. let (a, b) = p in let (x, a) = recv a in let () = x in
                     spawn (λv. let () = v in (force f) ⟨a, send ⟨∗, b⟩⟩))

    recv a blocks at ι while the body holds b at ι′ and asks ι ≺ ι′.
    send b blocks at ι′ while it holds a at ι+1 and asks ι′ ≺ ι+1. With
    the one-round constraint {ι ≺ ι′, ι′ ≺ ι+1} the recursive force at
    (ι+1, ι′+1) asks ι+1 ≺ ι′+1, and the fact theory does not derive it.
    Its ≡ relates points with a variable root by equality only, its ≺
    closes the hypotheses under ≡ and transitivity, and a world_wf W
    relates points with a variable root by program order only. The rank
    10(k+1) for (ι,k) and 15+k for (ι′,k) meets the hypotheses and
    program order but puts ι′+1 below ι+1 ([rr_call_underivable]). C is
    the invariant of the recursion, so it has to state every round at
    once, which the typed version below does. *)

Definition isvar (x : point) : bool := match pt_root x with NVar _ => true | _ => false end.

Definition rr_rank (x : point) : nat :=
  match pt_name x with
  | NVar 0 => 10 * S (pt_off x)
  | NVar 1 => 15 + pt_off x
  | _ => pt_off x
  end.

Definition rr_R (x y : point) : Prop :=
  if isvar x && isvar y then rr_rank x < rr_rank y else isvar x = false ∧ isvar y = false.

Definition rr_C1 (g : fact) : Prop :=
  g = FLt (pvar 0) (pvar 1) ∨ g = FLt (pvar 1) (pt_shift 1 (pvar 0)).

Lemma isvar_const W x : world_wf W → pt_root x ∈ w_names W → isvar x = false.
Proof. intros HW Hx. unfold isvar. by destruct (wf_names_const _ HW _ Hx) as [a ->]. Qed.

(** Program order lies in [rr_R]: the rank grows with the offset. *)
Lemma rr_R_po x : rr_R x (pt_shift 1 x).
Proof.
  unfold rr_R, isvar, pt_shift, pt_root, rr_rank. destruct x as [p o]. simpl.
  destruct (pn_root p); simpl; try (split; reflexivity).
  destruct p as [a0|[|[|k]]|q b i]; simpl; lia.
Qed.

Lemma rr_call_underivable W : world_wf W →
  ¬ slt W [(BCs [] rr_C1, ids 2)] (pt_shift 1 (pvar 0)) (pt_shift 1 (pvar 1)).
Proof.
  intros HW H.
  assert (∀ x y, slt W [(BCs [] rr_C1, ids 2)] x y → rr_R x y) as HR.
  { intros x y Hxy. change (match NP x, NP y with NP x, NP y => rr_R x y | _, _ => True end).
    refine (proj2 (fl_map (FCtx W [(BCs [] rr_C1, ids 2)] ∅)
      (λ x y, x = y ∨ (isvar x = false ∧ isvar y = false))
      (λ a b, match a, b with NP x, NP y => rr_R x y | _, _ => True end) id id
      _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ Hxy); clear Hxy H; unfold id; simpl.
    - intros x0 y0 H0. destruct (wf_eq_supp _ HW _ _ H0) as [->|[Hx Hy]]; [by left|right].
      split; by apply (isvar_const W).
    - intros x0 y0 (C & xs & Hg & g0 & Hg0 & E). apply list_elem_of_singleton in Hg.
      injection Hg as -> ->. apply bcs_open_nil in Hg0 as [[->| ->] _]; discriminate.
    - by left.
    - intros x0 y0 [->|[? ?]]; [by left|by right].
    - intros x0 y0 z0 [->|[? ?]] [->|[? ?]]; [by left|by right|by right|by right].
    - intros x0 y0 [->|[Hx Hy]]; [by left|right; split; [exact Hx|exact Hy]].
    - intros x0 y0 i [->|[Hx Hy]]; [by left|right; split; [exact Hx|exact Hy]].
    - intros x0 y0 Hxy. unfold rr_R. destruct (wf_lt_supp _ HW _ _ Hxy) as [[Hn Ho]|[Hx Hy]].
      + destruct x0 as [p o], y0 as [q o']. simpl in *. subst q. unfold isvar, rr_rank, pt_root. simpl.
        destruct (pn_root p) eqn:Hr; simpl; [done| |done].
        destruct p as [|[|[|]]|]; simpl in *; try lia; simplify_eq.
      + rewrite (isvar_const W x0), (isvar_const W y0); done.
    - intros x0 y0 (C & xs & Hg & g0 & Hg0 & E). apply list_elem_of_singleton in Hg.
      injection Hg as -> ->. apply bcs_open_nil in Hg0 as [[->| ->] _];
        cbn in E; injection E as -> ->; vm_compute; lia.
    - intros φ u Hu. by rewrite lookup_empty in Hu.
    - intros x0 x' [y0|] HQ H0; [|done]. destruct HQ as [->|[Hx Hx']]; [done|].
      revert H0. unfold rr_R. rewrite Hx, Hx'. cbn. tauto.
    - intros [x0|] y0 y' H0 HQ; [|done]. destruct HQ as [<-|[Hy' Hy]]; [done|].
      revert H0. unfold rr_R. rewrite Hy, Hy', !andb_false_r. cbn. tauto.
    - intros [x0|] y0 [z0|]; try done. unfold rr_R.
      destruct (isvar x0), (isvar y0), (isvar z0); simpl; intuition (try lia; try discriminate).
    - intros x0. apply rr_R_po. }
  apply HR in H. vm_compute in H. lia.
Qed.

(** ** relay with a one-round constraint: the call does not type (SHARP-EDGES 60)

      S = μX. ?(∃ι. D@ι).X     D = ?∗.Close
      r = !(f = λp. let (c, d) = p in let (e, c) = recv c in
                   let (v, e) = recv e in let () = v in
                   let () = close d in (force f) ⟨c, e⟩)
        : □(∀ι ι′. C.^⊥ S@ι ⊗ Close@ι′ ⊸ ∗)

    The body blocks at ι holding d at ι′, at ι[0] holding c at ι+1 and
    d at ι′, and at ι′ holding c at ι+1 and e at ι[0]+1. So C needs
    ι ≺ ι′, ι[0] ≺ ι+1, ι[0] ≺ ι′, ι′ ≺ ι+1 and ι′ ≺ ι[0]+1 (slots
    counted from 0). The call instantiates (ι, ι′) by (ι+1, ι[0]+1) and
    asks C there, among others ι+1 ≺ ι[0]+1. C relates ι+1 and ι[0]+1
    only through ι′, which lies below both. The rank of
    [rr_call_underivable] adapts: put ι[0]+1 below ι+1. Shift-invariant
    facts do not help here, because the step ι′ ↦ ι[0]+1 is no shift.
    Relay.v types the relay with a constraint for every round.

    ** blocked: rejected

      blocked = let (c, c′) = new ∗ in let (d, d′) = new ∗ in
                let () = spawn (λu. let () = u in let () = close d′ in close c′) in
                let () = close c in close d

    Say new puts c at x and d at y. With the one signature of new, x
    and y are the points E-Open binds, aliased or not to known points
    by the constraint of new (sharp edges 104). The main thread closes c while it
    holds d, so E-Let* puts y into the frame of close c and E-App asks
    x ≺ y (ub_below_s). The thunk closes d′ while it holds c′, so its
    body asks y ≺ x. E-Conv keeps points (eqT compares them by
    equality) and E-Weak drops only unlimited bindings, so every
    derivation asks both facts, and x ≺ y ≺ x contradicts strictness.
    This holds for every choice of x and y, x = y included.

    ** bad link: rejected

      badlink = let (c₁, c₂) = new ∗ in let (d₁, d₃) = new ∗ in let (e₂, e₃) = new ∗ in
                let () = spawn (λu. let () = u in link ⟨c₁, d₁⟩) in
                let () = spawn (λu. let () = u in let () = close e₃ in close d₃) in
                let () = close c₂ in close e₂

    With c at x, d at y and e at z: link asks x ≡ y (KTLink), the main
    thread closes c₂ while it holds e₂ and asks x ≺ z, the second
    thunk closes e₃ while it holds d₃ and asks z ≺ y. Then
    x ≺ z ≺ y ≡ x, and wf_lt_eq gives x ≺ x. This is the spec's
    (c,0) ≺ (e,0) ≺ (d,0) ≡ (c,0). The program deadlocks: after the
    link the main thread waits on c₂ for d₃, and the second thread
    waits on e₃ for e₂. The argument reads only the alias of KTLink.
    link has upper point ⊥ (sharp edges 68), so the link thunk asks
    no fact, and the program stays rejected. *)

Definition blocked_main : expr :=
  let_new_pair (let_new_pair
    (LetU (App ESpawn (Lam (LetU (Var 0) (LetU (App EClos (Var 1)) (App EClos (Var 3))))))
      (LetU (App EClos (Var 3)) (App EClos (Var 1))))).

Definition badlink_main : expr :=
  let_new_pair (let_new_pair (let_new_pair
    (LetU (App ESpawn (Lam (LetU (Var 0) (App ELink (Pair (Var 6) (Var 4))))))
      (LetU (App ESpawn (Lam (LetU (Var 0) (LetU (App EClos (Var 1)) (App EClos (Var 3))))))
        (LetU (App EClos (Var 4)) (App EClos (Var 1))))))).
