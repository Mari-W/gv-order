(** * Programs the static system rejects

    Each section names the rule and the fact that fail. The one-round
    request/reply call is proved underivable ([rr_call_underivable]).
    The others carry the argument in a comment. *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export examples.ExampleTools.

Set Default Proof Using "All".

(** ** request/reply with one round only: the call does not type (SHARP-EDGES 60, 65)

    The server answers every request on a with a reply on b, forever.

      Sa  = µα. ?∗.α        Sb = µα. !∗.α
      C   = {ι ≺ ι′, ι′ ≺ ι+1}                   one round only

      srv = ! f ∀ι ι′ { C }. λ^{ι′}_⊤ p.
                let (a : Sa@ι, b : Sb@ι′) = p in
                let (x : ∗, a₁ : Sa@(ι+1)) = recv a in
                x;
                spawn (λ^{ι′+1}_{ι′} ∗. (force f [ι+1, ι′+1]) ⟨a₁, send ⟨∗, b⟩⟩)

    recv a blocks at ι while the body holds b at ι′ and asks ι ≺ ι′.
    send b blocks at ι′ while it holds a at ι+1 and asks ι′ ≺ ι+1. With
    the one-round constraint C the recursive force at [ι+1, ι′+1] asks
    ι+1 ≺ ι′+1, and the fact theory does not derive it. Its ≡ relates
    points with a variable root by equality only, its ≺ closes the
    hypotheses under ≡ and transitivity, and a world_wf W relates points
    with a variable root by program order only. The rank 10(k+1) for ι+k
    and 15+k for ι′+k meets the hypotheses and program order but puts
    ι′+1 below ι+1 ([rr_call_underivable]). C is the invariant of the
    recursion, so it has to state every round at once, which the typed
    version below does. *)

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

(** Program order lies in [rr_R], where the rank grows with the
    offset. *)
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

      Srl = µα. ?(Dr@self.0).α        Dr = ?∗.Close

      r : □(∀ι ι′. C. ∗ ⊸^⊥_⊤ (Srl@ι ⊗ Close@ι′ ⊸^{ι′}_⊤ ∗))
      r = ! f ∀ι ι′ { C }. λ^{ι′}_⊤ p.
              let (c : Srl@ι, d : Close@ι′) = p in
              let (e : Dr@ι.0, c₁ : Srl@(ι+1)) = recv c in
              let (v : ∗, e₁ : Close@(ι.0+1)) = recv e in
              v;
              close d;
              (force f [ι+1, ι.0+1]) ⟨c₁, e₁⟩

    The body blocks at ι holding d at ι′, at ι.0 holding c at ι+1 and
    d at ι′, and at ι′ holding c at ι+1 and e at ι.0+1. So C needs
    ι ≺ ι′, ι.0 ≺ ι+1, ι.0 ≺ ι′, ι′ ≺ ι+1 and ι′ ≺ ι.0+1. The call
    instantiates ι, ι′ by ι+1, ι.0+1 and asks C there, among others
    ι+1 ≺ ι.0+1. C relates ι+1 and ι.0+1 only through ι′, which lies
    below both. The rank of [rr_call_underivable] adapts by putting
    ι.0+1 below ι+1. Shift-invariant facts do not help here, because the
    step ι′ ↦ ι.0+1 is no shift. Relay.v types the relay with a
    constraint for every round.

    ** blocked: rejected

      blocked = let (c : Close@x, c′ : Close@x) = new ι { … } ∗ in
                let (d : Close@y, d′ : Close@y) = new κ { … } ∗ in
                spawn (λ^y_x ∗. close d′; close c′);
                close c;
                close d

    Say new puts c at x and d at y. With the one signature of new, x
    and y are the points E-Open binds, aliased or not to known points
    by the constraint of new (sharp edges 104). The main thread closes c
    while it holds d, so E-Let∗ puts y into the frame of close c and
    E-App asks x ≺ y (ub_below_s). The thunk closes d′ while it holds
    c′, so its body asks y ≺ x. E-Conv keeps points (eqT compares them
    by equality) and E-Weak drops only unlimited bindings, so every
    derivation asks both facts, and x ≺ y ≺ x contradicts strictness.
    This holds for every choice of x and y, x = y included.

    ** bad link: rejected

      badlink = let (c₁ : Close@x, c₂ : Close@x) = new ι { … } ∗ in
                let (d₁ : Close@y, d₃ : Close@y) = new κ { … } ∗ in
                let (e₂ : Close@z, e₃ : Close@z) = new ν { … } ∗ in
                spawn (λ^⊥_x ∗. link ⟨c₁, d₁⟩);
                spawn (λ^{y+1}_z ∗. close e₃; close d₃);
                close c₂;
                close e₂

    With c at x, d at y and e at z, link asks x ≡ y (KTLink), the main
    thread closes c₂ while it holds e₂ and asks x ≺ z, and the second
    thunk closes e₃ while it holds d₃ and asks z ≺ y. Then
    x ≺ z ≺ y ≡ x, and wf_lt_eq gives x ≺ x. This is the spec's
    c ≺ e ≺ d ≡ c. The program deadlocks. After the link the main thread
    waits on c₂ for d₃, and the second thread waits on e₃ for e₂. The
    argument reads only the alias of KTLink. link has upper point ⊥
    (sharp edges 68), so the link thunk asks no fact, and the program
    stays rejected. *)

Definition blocked_main : expr :=
  let_new_pair (let_new_pair
    (LetU (App ESpawn (Lam (LetU (Var 0) (LetU (App EClos (Var 1)) (App EClos (Var 3))))))
      (LetU (App EClos (Var 3)) (App EClos (Var 1))))).

Definition badlink_main : expr :=
  let_new_pair (let_new_pair (let_new_pair
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
    while it holds r₂ at y, so it asks z ≺ y. link ⟨r₁, r₀⟩ asks
    z ≡ x. The three give z ≺ z. *)
Lemma sched_rev_underivable W Ψ x y z :
  (∀ p, ¬ slt W Ψ p p) → ¬ (slt W Ψ y x ∧ slt W Ψ z y ∧ seqs W Ψ z x).
Proof.
  intros Hacy (Hyx & Hzy & Hzx). apply (Hacy z).
  eapply sl_trans; [exact Hzy|]. eapply sl_eqr; [exact Hyx|by apply se_sym].
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

(** The bad link of [badlink_main]. link ⟨c₁, d₁⟩ asks x ≡ y, the main
    thread closes c₂ at x while it holds e₂ at z and asks x ≺ z, and the
    second thunk closes e₃ at z while it holds d₃ at y and asks z ≺ y.
    The three give x ≺ x. *)
Lemma badlink_underivable W Ψ x y z :
  (∀ p, ¬ slt W Ψ p p) → ¬ (seqs W Ψ x y ∧ slt W Ψ x z ∧ slt W Ψ z y).
Proof.
  intros Hacy (Hxy & Hxz & Hzy). apply (Hacy x).
  eapply sl_eqr; [|by apply se_sym]. by eapply sl_trans.
Qed.

(** ** [ordered] without its constraint: the body does not type

      ordered : □(∀ι ι′. { }. ∗ ⊸^⊥_⊤ (Close@ι ⊗ Close@ι′ ⊸^{ι′}_⊤ ∗))
      ordered = ! f ∀ι ι′ { }. λ^{ι′}_⊤ p.
                    let (c : Close@ι, d : Close@ι′) = p in
                    close c;
                    close d

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

(** Program order lies in [ord_R], where the offset grows and the root
    stays. *)
Lemma ord_R_po x : ord_R x (pt_shift 1 x).
Proof.
  unfold ord_R, isvar, pt_shift, pt_root. destruct x as [p o]. simpl.
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
      _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ Hxy); clear Hxy H; unfold id; simpl.
    - intros x1 y1 H0. destruct (wf_eq_supp _ HW _ _ H0) as [->|[Hx Hy]]; [by left|right].
      split; by apply (isvar_const W).
    - intros x1 y1 (C & xs & Hg & g0 & Hg0 & E). apply list_elem_of_singleton in Hg.
      injection Hg as -> ->. by apply bcs_open_nil in Hg0 as [[] _].
    - by left.
    - intros x1 y1 [->|[? ?]]; [by left|by right].
    - intros x1 y1 z1 [->|[? ?]] [->|[? ?]]; [by left|by right|by right|by right].
    - intros x1 y1 [->|[Hx Hy]]; [by left|right; split; [exact Hx|exact Hy]].
    - intros x1 y1 i [->|[Hx Hy]]; [by left|right; split; [exact Hx|exact Hy]].
    - intros x1 y1 Hxy. unfold ord_R. destruct (wf_lt_supp _ HW _ _ Hxy) as [[Hn Ho]|[Hx Hy]].
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
    - intros x1. apply ord_R_po. }
  apply HR in H. unfold ord_R in H. cbn in H. destruct H as [Hn _]. discriminate.
Qed.
