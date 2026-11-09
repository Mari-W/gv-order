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

    recv a blocks at ι while the body holds b at ι′ and asks ι ≺ ι̅′,
    against the partner point of b. send b blocks at ι′ while it holds
    a at ι+1 and asks ι′ ≺ (ι+1)‾ (end points). With the one-round
    constraint {ι ≺ ι̅′, ι′ ≺ (ι+1)‾} the recursive force at (ι+1, ι′+1)
    asks ι+1 ≺ (ι′+1)‾, and the fact theory does not derive it.
    Its ≡ relates points with a variable root by equality only, its ≺
    closes the hypotheses under ≡ and transitivity, and a world_wf W
    relates points with a variable root by program order only, now
    x ≺ x+1 and x ≺ x̄+1. The rank 10(k+1) for (ι,k) and 15+k for
    (ι′,k), at either polarity, meets the hypotheses and program order
    but puts (ι′+1)‾ below ι+1 ([rr_call_underivable]). C is
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
  g = FLt (pvar 0) (pt_dual (pvar 1)) ∨ g = FLt (pvar 1) (pt_dual (pt_shift 1 (pvar 0))).

Lemma isvar_const W x : world_wf W → pt_root x ∈ w_names W → isvar x = false.
Proof. intros HW Hx. unfold isvar. by destruct (wf_names_const _ HW _ Hx) as [a ->]. Qed.

(** Program order lies in [rr_R]: the rank grows with the offset. *)
Lemma rr_R_po x : rr_R x (pt_shift 1 x).
Proof.
  unfold rr_R, isvar, pt_shift, pt_root, rr_rank. destruct x as [p pb o]. simpl.
  destruct (pn_root p); simpl; try (split; reflexivity).
  destruct p as [a0|[|[|k]]|q b i]; simpl; lia.
Qed.

Lemma rr_R_dpo x : rr_R x (pt_shift 1 (pt_dual x)).
Proof.
  unfold rr_R, isvar, pt_shift, pt_dual, pt_root, rr_rank. destruct x as [p pb o]. simpl.
  destruct (pn_root p); simpl; try (split; reflexivity).
  destruct p as [a0|[|[|k]]|q b i]; simpl; lia.
Qed.

Lemma rr_call_underivable W : world_wf W →
  ¬ slt W [(BCs [] rr_C1, ids 2)] (pt_shift 1 (pvar 0)) (pt_dual (pt_shift 1 (pvar 1))).
Proof.
  intros HW H.
  assert (∀ x y, slt W [(BCs [] rr_C1, ids 2)] x y → rr_R x y) as HR.
  { intros x y Hxy. change (match NP x, NP y with NP x, NP y => rr_R x y | _, _ => True end).
    refine (proj2 (fl_map (FCtx W [(BCs [] rr_C1, ids 2)] ∅)
      (λ x y, x = y ∨ (isvar x = false ∧ isvar y = false))
      (λ a b, match a, b with NP x, NP y => rr_R x y | _, _ => True end) id id
      _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ Hxy); clear Hxy H; unfold id; simpl.
    - intros x0 y0 H0. destruct (wf_eq_supp _ HW _ _ H0) as [->|[Hx Hy]]; [by left|right].
      split; by apply (isvar_const W).
    - by left.
    - intros x0 y0 [->|[? ?]]; [by left|by right].
    - intros x0 y0 z0 [->|[? ?]] [->|[? ?]]; [by left|by right|by right|by right].
    - intros x0 y0 [->|[Hx Hy]]; [by left|right; split; [exact Hx|exact Hy]].
    - intros x0 y0 i [->|[Hx Hy]]; [by left|right; split; [exact Hx|exact Hy]].
    - intros x0 y0 Hxy. unfold rr_R. destruct (wf_lt_supp _ HW _ _ Hxy) as [[Hn Ho]%ppo_pofs|[Hx Hy]].
      + destruct x0 as [p pb o], y0 as [q pb' o']. simpl in *. subst q. unfold isvar, rr_rank, pt_root. simpl.
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
    - intros x0. apply rr_R_po.
    - intros x0 y0 [->|[Hx Hy]]; [by left|right]. unfold isvar, pt_root in *. by simpl.
    - intros x0. apply rr_R_dpo. }
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
    ι ≺ ι′, ι[0] ≺ ι+1, ι[0] ≺ ι′, ι′ ≺ ι+1 and ι′ ≺ ι[0]+1 (positions
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
    by the constraint of new (sharp edges 104). With end points c′ and
    d′ sit at x̄ and ȳ. The main thread closes c while it holds d, so
    E-Let* puts the partner point ȳ into the future of close c and
    E-App asks x ≺ ȳ (ub_below_s). The thunk closes d′ at ȳ while it
    holds c′, whose partner point is x, so its body asks ȳ ≺ x. E-Conv keeps points (eqT compares them by
    equality) and E-Weak drops only unlimited bindings, so every
    derivation asks both facts, and x ≺ ȳ ≺ x contradicts strictness.
    This holds for every choice of x and y, x = y included.

    ** bad link: rejected

      badlink = let (c₁, c₂) = new ∗ in let (d₁, d₃) = new ∗ in let (e₂, e₃) = new ∗ in
                let () = spawn (λu. let () = u in link ⟨c₁, d₁⟩) in
                let () = spawn (λu. let () = u in let () = close e₃ in close d₃) in
                let () = close c₂ in close e₂

    With c₁, c₂ at x, x̄, d₁, d₃ at y, ȳ and e₂, e₃ at z, z̄ (end
    points): link types only with d₁ at x̄ (KTLink, branch no-eq), so
    y = x̄ and d₃ sits at x. On main the link asked the alias x ≡ ȳ. The
    main thread closes c₂ at x̄ while it holds e₂ and asks x̄ ≺ z̄, the
    second thunk closes e₃ at z̄ while it holds d₃ and asks z̄ ≺ x̄. This
    is the spec's (c,0) ≺ (e,0) ≺ (c,0). The program deadlocks: after
    the link the main thread waits on c₂ for d₃, and the second thread
    waits on e₃ for e₂. The argument reads only the points KTLink
    fixes.
    link has upper point ⊥ (sharp edges 68), so the link thunk asks
    no fact, and the program stays rejected. *)

(** Under syntactic points (sharp edges 173) the news name their points:
    c at the constant 0 and d at 1 in [blocked_main], and c at x = 0, d
    at x̄ and e at z = 1 in [badlink_main]. *)
Definition blocked_main : expr :=
  let_new_pair_at (EPt (pconst 0)) (let_new_pair_at (EPt (pconst 1))
    (LetU (App ESpawn (Lam (LetU (Var 0) (LetU (App EClos (Var 1)) (App EClos (Var 3))))))
      (LetU (App EClos (Var 3)) (App EClos (Var 1))))).

Definition badlink_main : expr :=
  let_new_pair_at (EPt (pconst 0)) (let_new_pair_at (EPt (pt_dual (pconst 0))) (let_new_pair_at (EPt (pconst 1))
    (LetU (App ESpawn (Lam (LetU (Var 0) (App ELink (Pair (Var 6) (Var 4))))))
      (LetU (App ESpawn (Lam (LetU (Var 0) (LetU (App EClos (Var 1)) (App EClos (Var 3))))))
        (LetU (App EClos (Var 4)) (App EClos (Var 1))))))).

(** ** The three rejections above as theorems

    Each argument above names the facts a derivation of the program
    would have to supply. The lemmas below show that those facts do not
    hold together.

    Two of them close a cycle, so they are stated for any Γ whose ≺ has
    no cycle. Every Γ that a derivation of a closed typable program
    meets is of that kind. [soundness] takes a strict world, and every
    creation constraint is acyclic relative to the context it is read in
    ([cc_acyclic], types/Types.v), so a cycle in Γ + C is already a
    cycle in Γ, and by induction in the world. [slt_acyclic_nil]
    discharges the hypothesis for Γ = W. The step from "the program has
    no derivation" to "these facts fail" is the one the comments make by
    hand, and making it a theorem means inverting derivations, which the
    development avoids. *)

Lemma slt_acyclic_nil W : strict W → ∀ p, ¬ slt W [] p p.
Proof. intros [HW Hs] p H. apply (Hs p). by apply slt_nil. Qed.

(** The reversed agent of examples/Scheduler.v. ag₀ receives on r₂ at y
    while it holds r₀ at x, so it asks y ≺ x. ag₂ receives on r₁ at z
    while it holds r₂ at y, so it asks z ≺ y. link ⟨r₁, r₀⟩ types only
    when the two ends sit at dual points, so z is x (branch no-eq: no
    alias, the points are equal). The two give x ≺ x. *)
Lemma sched_rev_underivable W Ψ x y :
  (∀ p, ¬ slt W Ψ p p) → ¬ (slt W Ψ y x ∧ slt W Ψ x y).
Proof.
  intros Hacy (Hyx & Hxy). apply (Hacy x). by eapply sl_trans.
Qed.

(** The reversed agent of examples/MilnerSched.v. With r_i the point of
    the ring channel between A_i and A_{i+1}, a reversed A_0 receives on
    d_0 at r_2 while it holds c_0 at r_0 and asks r_2 ≺ r_0. A_1 asks
    r_0 ≺ r_1 and A_2 asks r_1 ≺ r_2. The three give r_0 ≺ r_0. *)
Lemma ms_rev_underivable W Ψ r0 r1 r2 :
  (∀ p, ¬ slt W Ψ p p) → ¬ (slt W Ψ r2 r0 ∧ slt W Ψ r0 r1 ∧ slt W Ψ r1 r2).
Proof.
  intros Hacy (H20 & H01 & H12). apply (Hacy r0).
  eapply sl_trans; [exact H01|]. by eapply sl_trans.
Qed.

(** The bad link of [badlink_main]. With end points read x, z below
    as x̄, z̄ of the comment above. link ⟨c₁, d₁⟩ types only when d₁
    sits at the partner point of c₁, so d₃ sits at x̄ (branch no-eq: d
    is created by new@x̄, no alias). The main thread closes c₂ at x̄
    while it holds e₂ and asks x̄ ≺ z̄, and the second thunk closes e₃ at
    z̄ while it holds d₃ and asks z̄ ≺ x̄. The two give x̄ ≺ x̄. *)
Lemma badlink_underivable W Ψ x z :
  (∀ p, ¬ slt W Ψ p p) → ¬ (slt W Ψ x z ∧ slt W Ψ z x).
Proof.
  intros Hacy (Hxz & Hzx). apply (Hacy x). by eapply sl_trans.
Qed.

(** ** [ordered] without its constraint: the body does not type

      ordered = !(f = λp. let (c, d) = p in let () = close c in close d)
              : □(∀ι ι′. {}. ∗ ⊸ Close@ι ⊗ Close@ι′ ⊸^{ι′} ∗)

    close c blocks at ι while the body still holds d at ι′, so E-App
    asks ι ≺ ι′ (examples/Ordered.v). With the empty constraint the
    fact theory derives no fact between two points with distinct
    variable roots. The model below sends ≺ to program order on one
    name between points with a variable root, and to the full relation
    between points with a constant root. ≡ goes to equality, or to the
    pair of constant roots. A well-formed world relates points with a
    variable root by program order only ([wf_lt_supp]) and identifies
    them only when they are equal ([wf_eq_supp]), the one hypothesis has
    no fact, and ι and ι′ have the names NVar 0 and NVar 1, so no
    derived fact puts ι below ι′. *)

Definition ord0_C : bcs := BCs [] (λ _, False).

Definition ord_R (x y : point) : Prop :=
  if isvar x && isvar y then pt_name x = pt_name y ∧ pt_off x < pt_off y
  else isvar x = false ∧ isvar y = false.

Lemma isvar_name x y : pt_name x = pt_name y → isvar x = isvar y.
Proof. intros E. unfold isvar, pt_root. by rewrite E. Qed.

(** Program order lies in [ord_R]: the offset grows and the root stays. *)
Lemma ord_R_po x : ord_R x (pt_shift 1 x).
Proof.
  unfold ord_R, isvar, pt_shift, pt_root. destruct x as [p pb o]. simpl.
  destruct (pn_root p); simpl; split; (reflexivity || lia).
Qed.

Lemma ord_R_dpo x : ord_R x (pt_shift 1 (pt_dual x)).
Proof.
  unfold ord_R, isvar, pt_shift, pt_dual, pt_root. destruct x as [p pb o]. simpl.
  destruct (pn_root p); simpl; split; (reflexivity || lia).
Qed.

Lemma ord_no_constraint W : world_wf W → ¬ slt W [(ord0_C, ids 2)] (pvar 0) (pvar 1).
Proof.
  intros HW H.
  assert (∀ x y, slt W [(ord0_C, ids 2)] x y → ord_R x y) as HR.
  { intros x0 y0 Hxy. change (match NP x0, NP y0 with NP x, NP y => ord_R x y | _, _ => True end).
    refine (proj2 (fl_map (FCtx W [(ord0_C, ids 2)] ∅)
      (λ x y, x = y ∨ (isvar x = false ∧ isvar y = false))
      (λ a b, match a, b with NP x, NP y => ord_R x y | _, _ => True end) id id
      _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ Hxy); clear Hxy H; unfold id; simpl.
    - intros x1 y1 H0. destruct (wf_eq_supp _ HW _ _ H0) as [->|[Hx Hy]]; [by left|right].
      split; by apply (isvar_const W).
    - by left.
    - intros x1 y1 [->|[? ?]]; [by left|by right].
    - intros x1 y1 z1 [->|[? ?]] [->|[? ?]]; [by left|by right|by right|by right].
    - intros x1 y1 [->|[Hx Hy]]; [by left|right; split; [exact Hx|exact Hy]].
    - intros x1 y1 i [->|[Hx Hy]]; [by left|right; split; [exact Hx|exact Hy]].
    - intros x1 y1 Hxy. unfold ord_R. destruct (wf_lt_supp _ HW _ _ Hxy) as [[Hn Ho]%ppo_pofs|[Hx Hy]].
      + rewrite (isvar_name x1 y1 Hn). destruct (isvar y1); simpl; [by split|done].
      + rewrite (isvar_const W x1), (isvar_const W y1); done.
    - intros x1 y1 (C & xs & Hg & g0 & Hg0 & E). apply list_elem_of_singleton in Hg.
      injection Hg as -> ->. by apply bcs_open_nil in Hg0 as [[] _].
    - intros φ u Hu. by rewrite lookup_empty in Hu.
    - intros x1 x' [y1|] HQ H0; [|done]. destruct HQ as [->|[Hx Hx']]; [done|].
      revert H0. unfold ord_R. rewrite Hx, Hx'. cbn. tauto.
    - intros [x1|] y1 y' H0 HQ; [|done]. destruct HQ as [<-|[Hy' Hy]]; [done|].
      revert H0. unfold ord_R. rewrite Hy, Hy', !andb_false_r. cbn. tauto.
    - intros [x1|] y1 [z1|]; try done. unfold ord_R.
      destruct (isvar x1), (isvar y1), (isvar z1); simpl;
        intuition (try discriminate; try lia); try congruence.
    - intros x1. apply ord_R_po.
    - intros x1 y1 [->|[Hx Hy]]; [by left|right]. unfold isvar, pt_root in *. by simpl.
    - intros x1. apply ord_R_dpo. }
  apply HR in H. unfold ord_R in H. cbn in H. destruct H as [Hn _]. discriminate.
Qed.
