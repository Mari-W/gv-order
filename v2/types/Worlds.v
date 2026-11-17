(** * Worlds (stage S2, proposal §2.4)

    W = (A, ≺_A, L, (Λ_ℓ)_{ℓ ∈ L})
      A      a finite set of constants
      ≺_A    facts between points with constant roots in A
      L      a finite set of family labels
      Λ_ℓ    the laws of family ℓ, facts between points whose root is
             the one variable ι₀

    ≺_W is the transitive closure of ≺_A, of the laws Λ_ℓ at every
    generated root g of every family ℓ ∈ L, of x ≺ x⁺ and of x ≺ x‾⁺.
    Every generated root is known up front and obeys the laws of its
    family, so W is constant along a run although the run creates roots.
    A world carries no budget, no payload cost type and no alias.

    The join W1 ⊔ W2 unions constants, facts, families and laws. Two
    components meet in a join only after their families are renamed
    apart ([wfrename], [w_lt_frename]), so P-Connect and P-Join ask
    [w_fams W1 ## w_fams W2]. [strict_join_iff] is cleanup item R7. The
    join is strict iff both worlds are and the two orders restricted to
    the shared constants are acyclic together. *)

From GV Require Export types.Points.

Record world := World {
  w_consts : gset nat;
  w_facts : fact → Prop;
  w_fams : gset family;
  w_laws : family → fact → Prop
}.

(** The law x of family ℓ read at the generated root g. *)
Definition law_inst (ℓ : family) (g : nat) (x : point) : point :=
  pt_inst (λ _, pgen ℓ g) x.

(** One generating step of ≺_W. *)
Inductive wstep (W : world) : point → point → Prop :=
  | ws_fact x y : w_facts W (FLt x y) → wstep W x y
  | ws_law ℓ g x y :
      ℓ ∈ w_fams W → w_laws W ℓ (FLt x y) → wstep W (law_inst ℓ g x) (law_inst ℓ g y)
  | ws_po x : wstep W x x⁺
  | ws_dpo x : wstep W x x‾⁺.

Definition w_lt (W : world) : point → point → Prop := tc (wstep W).

Notation "W ⊢ x ≺ y" := (w_lt W x y)
  (at level 74, x at level 60, y at level 60, format "W  ⊢  x  ≺  y").

Definition w_le (W : world) (x y : point) : Prop := x = y ∨ W ⊢ x ≺ y.

(** A constant root in a set. *)
Definition croot_in (S : gset nat) (x : point) : Prop :=
  ∃ a, pt_root x = NConst a ∧ a ∈ S.

Global Instance croot_in_dec S x : Decision (croot_in S x).
Proof.
  unfold croot_in. destruct (pt_root x) as [a|ℓ g|a|p b κ];
    [destruct (decide (a ∈ S))|..]; first [left; naive_solver|right; naive_solver].
Defined.

Record world_wf (W : world) : Prop := {
  wf_facts x y : w_facts W (FLt x y) → croot_in (w_consts W) x ∧ croot_in (w_consts W) y;
  wf_laws ℓ x y : ℓ ∈ w_fams W → w_laws W ℓ (FLt x y) →
    pt_root x = NVar 0 ∧ pt_root y = NVar 0
}.

Definition strict (W : world) : Prop := world_wf W ∧ ∀ x, ¬ W ⊢ x ≺ x.

(** The lock-free world: strict and well founded, one record. *)
Definition lfworld (W : world) : Prop := strict W ∧ well_founded (w_lt W).

Lemma w_lt_trans W x y z : W ⊢ x ≺ y → W ⊢ y ≺ z → W ⊢ x ≺ z.
Proof. apply tc_transitive. Qed.
Lemma w_lt_po W x : W ⊢ x ≺ x⁺.
Proof. apply tc_once, ws_po. Qed.
Lemma w_lt_dpo W x : W ⊢ x ≺ x‾⁺.
Proof. apply tc_once, ws_dpo. Qed.
Lemma w_lt_fact W x y : w_facts W (FLt x y) → W ⊢ x ≺ y.
Proof. intros H. by apply tc_once, ws_fact. Qed.
Lemma w_lt_law W ℓ g x y :
  ℓ ∈ w_fams W → w_laws W ℓ (FLt x y) → W ⊢ law_inst ℓ g x ≺ law_inst ℓ g y.
Proof. intros ??. by apply tc_once, ws_law. Qed.

(** ** Program order, the facts every world has *)

Definition po (x y : point) : Prop := tc (λ a b, b = a⁺ ∨ b = a‾⁺) x y.

Lemma po_lt W x y : po x y → W ⊢ x ≺ y.
Proof.
  induction 1 as [x y [->| ->]|x y z [->| ->] _ IH].
  - apply w_lt_po.
  - apply w_lt_dpo.
  - eapply w_lt_trans; [apply w_lt_po|done].
  - eapply w_lt_trans; [apply w_lt_dpo|done].
Qed.

Lemma po_root x y : po x y → pt_root x = pt_root y ∧ pt_off x < pt_off y.
Proof.
  induction 1 as [x y [->| ->]|x y z [->| ->] _ [IH1 IH2]]; unfold pt_root in *;
    cbn [pt_shift pt_dual pt_name pt_off] in *; split; try done; lia.
Qed.

Lemma po_irrefl x : ¬ po x x.
Proof. intros H. apply po_root in H. lia. Qed.

(** ** Extension, join, restriction *)

Record wext (W W' : world) : Prop := {
  wext_consts : w_consts W ⊆ w_consts W';
  wext_facts g : w_facts W g → w_facts W' g;
  wext_fams : w_fams W ⊆ w_fams W';
  wext_laws ℓ g : ℓ ∈ w_fams W → w_laws W ℓ g → w_laws W' ℓ g
}.

Notation "W ⊑ W'" := (wext W W') (at level 70).

Lemma wext_refl W : W ⊑ W.
Proof. split; auto. Qed.

Lemma wext_trans W1 W2 W3 : W1 ⊑ W2 → W2 ⊑ W3 → W1 ⊑ W3.
Proof.
  intros [] []. split; [set_solver|auto|set_solver|]. intros ℓ g Hℓ Hg.
  apply wext_laws1; [set_solver|auto].
Qed.

Lemma wstep_mono W W' x y : W ⊑ W' → wstep W x y → wstep W' x y.
Proof.
  intros HW. destruct 1.
  - apply ws_fact. by apply (wext_facts _ _ HW).
  - apply ws_law; [by apply (wext_fams _ _ HW)|by apply (wext_laws _ _ HW)].
  - apply ws_po.
  - apply ws_dpo.
Qed.

Lemma w_lt_mono W W' x y : W ⊑ W' → W ⊢ x ≺ y → W' ⊢ x ≺ y.
Proof. intros HW. apply tc_congruence with (f := id). intros. by eapply wstep_mono. Qed.

Lemma strict_mono W W' : world_wf W → W ⊑ W' → strict W' → strict W.
Proof. intros Hwf HW [_ HS]. split; [done|]. intros x Hx. apply (HS x). by eapply w_lt_mono. Qed.

Definition wjoin (W1 W2 : world) : world :=
  World (w_consts W1 ∪ w_consts W2)
    (λ g, w_facts W1 g ∨ w_facts W2 g)
    (w_fams W1 ∪ w_fams W2)
    (λ ℓ g, (ℓ ∈ w_fams W1 ∧ w_laws W1 ℓ g) ∨ (ℓ ∈ w_fams W2 ∧ w_laws W2 ℓ g)).

Notation "W1 ⊔ W2" := (wjoin W1 W2) (at level 50).

Lemma wext_join_l W1 W2 : W1 ⊑ W1 ⊔ W2.
Proof. split; simpl; [set_solver|auto|set_solver|auto]. Qed.

Lemma wext_join_r W1 W2 : W2 ⊑ W1 ⊔ W2.
Proof. split; simpl; [set_solver|auto|set_solver|auto]. Qed.

Lemma wjoin_wf W1 W2 : world_wf W1 → world_wf W2 → world_wf (W1 ⊔ W2).
Proof.
  intros H1 H2. split; simpl.
  - intros x y [Hf|Hf]; [destruct (wf_facts _ H1 x y Hf) as [[a [??]] [b [??]]]
                         |destruct (wf_facts _ H2 x y Hf) as [[a [??]] [b [??]]]];
      split; eexists; split; eauto; set_solver.
  - intros ℓ x y _ [[Hℓ Hl]|[Hℓ Hl]]; [by apply (wf_laws _ H1 ℓ)|by apply (wf_laws _ H2 ℓ)].
Qed.

(** W restricted to the constants S: the facts of ≺_W between points
    with constant roots in S, no families. *)
Definition wrestrict (W : world) (S : gset nat) : world :=
  World (w_consts W ∩ S)
    (λ g, match g with FLt x y => W ⊢ x ≺ y ∧ croot_in (w_consts W ∩ S) x ∧ croot_in (w_consts W ∩ S) y end)
    ∅ (λ _ _, False).

Lemma wrestrict_wf W S : world_wf (wrestrict W S).
Proof. split; simpl; [by intros x y (_ & ? & ?)|set_solver]. Qed.

(** The restriction says nothing W does not. *)
Lemma wrestrict_lt W S x y : wrestrict W S ⊢ x ≺ y → W ⊢ x ≺ y.
Proof.
  induction 1 as [x y Hs|x y z Hs _ IH].
  - destruct Hs as [x y (H & _ & _)|ℓ g x y Hℓ _|x|x]; [done|set_solver|apply w_lt_po|apply w_lt_dpo].
  - eapply w_lt_trans; [|done].
    destruct Hs as [x y (H & _ & _)|ℓ g x y Hℓ _|x|x]; [done|set_solver|apply w_lt_po|apply w_lt_dpo].
Qed.

(** The shared constants of two worlds. *)
Definition wshared (W1 W2 : world) : gset nat := w_consts W1 ∩ w_consts W2.

(** A step of a join is a step of one side. *)
Lemma wstep_join_inv A B x y : wstep (A ⊔ B) x y → wstep A x y ∨ wstep B x y.
Proof.
  destruct 1 as [x y [Hf|Hf]|ℓ g x y Hℓ [[Hℓ' Hl]|[Hℓ' Hl]]|x|x].
  - left. by apply ws_fact.
  - right. by apply ws_fact.
  - left. by apply ws_law.
  - right. by apply ws_law.
  - left. apply ws_po.
  - left. apply ws_dpo.
Qed.

(** ** Cleanup item R7: strictness of a join at the interface *)

Section join.
  Context (W1 W2 : world).
  Context (H1 : world_wf W1) (H2 : world_wf W2) (HL : w_fams W1 ## w_fams W2).

  Local Abbreviation J := (W1 ⊔ W2).
  Local Abbreviation S := (wshared W1 W2).

  (** The zone of a world: points whose root it owns. *)
  Definition zone (W : world) (x : point) : Prop :=
    (∃ a, pt_root x = NConst a ∧ a ∈ w_consts W) ∨
    (∃ ℓ g, pt_root x = NGen ℓ g ∧ ℓ ∈ w_fams W).

  Global Instance zone_dec W x : Decision (zone W x).
  Proof.
    unfold zone. destruct (pt_root x) as [a|ℓ g|a|p b κ];
      [destruct (decide (a ∈ w_consts W))|destruct (decide (ℓ ∈ w_fams W))|..];
      first [left; naive_solver|right; naive_solver].
  Defined.

  Local Definition shared (x : point) : Prop := croot_in S x.

  Lemma law_inst_root ℓ g x : pt_root x = NVar 0 → pt_root (law_inst ℓ g x) = NGen ℓ g.
  Proof.
    intros Hx. unfold law_inst. rewrite pt_root_inst_var, Hx. done.
  Qed.

  (** A chain of one world either is program order or stays in its zone. *)
  Lemma lt_zone (W : world) x y : world_wf W → W ⊢ x ≺ y → po x y ∨ (zone W x ∧ zone W y).
  Proof.
    intros Hwf. induction 1 as [x y Hs|x y z Hs _ IH].
    - destruct Hs as [x y Hf|ℓ g x y Hℓ Hl|x|x].
      + right. destruct (wf_facts _ Hwf x y Hf) as [[a [??]] [b [??]]].
        split; left; eauto.
      + right. destruct (wf_laws _ Hwf ℓ x y Hℓ Hl) as [Hx Hy].
        split; right; exists ℓ, g; split; auto using law_inst_root.
      + left. apply tc_once. by left.
      + left. apply tc_once. by right.
    - assert (po x y ∨ (zone W x ∧ zone W y)) as Hxy.
      { destruct Hs as [x y Hf|ℓ g x y Hℓ Hl|x|x].
        + right. destruct (wf_facts _ Hwf x y Hf) as [[a [??]] [b [??]]].
          split; left; eauto.
        + right. destruct (wf_laws _ Hwf ℓ x y Hℓ Hl) as [Hx Hy].
          split; right; exists ℓ, g; split; auto using law_inst_root.
        + left. apply tc_once. by left.
        + left. apply tc_once. by right. }
      destruct Hxy as [Hp|[Zx Zy]], IH as [Hp'|[Zy' Zz]].
      + left. by eapply tc_transitive.
      + right. split; [|done]. apply po_root in Hp as [Hr _]. unfold zone in *. by rewrite Hr.
      + right. split; [done|]. apply po_root in Hp' as [Hr _]. unfold zone in *. by rewrite <-Hr.
      + by right.
  Qed.

  (** A step of the join is a step of W1 or of W2. *)
  Lemma jstep_inv x y : wstep J x y → wstep W1 x y ∨ wstep W2 x y.
  Proof.
    destruct 1 as [x y [Hf|Hf]|ℓ g x y Hℓ [[Hℓ' Hl]|[Hℓ' Hl]]|x|x].
    - left. by apply ws_fact.
    - right. by apply ws_fact.
    - left. by apply ws_law.
    - right. by apply ws_law.
    - left. apply ws_po.
    - left. apply ws_dpo.
  Qed.

  Lemma zone_shared x : zone W1 x → zone W2 x → shared x.
  Proof.
    intros [(a & Ha & Ha1)|(ℓ & g & Hg & Hℓ1)] [(b & Hb & Hb2)|(ℓ' & g' & Hg' & Hℓ2)];
      try congruence.
    - exists a. split; [done|]. rewrite Ha in Hb. injection Hb as <-. unfold wshared. set_solver.
    - exfalso. rewrite Hg in Hg'. injection Hg' as <- <-. set_solver.
  Qed.

  (** The amalgam: the two orders between shared points. *)
  Definition amalgam (x y : point) : Prop :=
    shared x ∧ shared y ∧ (W1 ⊢ x ≺ y ∨ W2 ⊢ x ≺ y).

  Local Lemma wstep_lt W x y : wstep W x y → W ⊢ x ≺ y.
  Proof. apply tc_once. Qed.

  (** The core of R7. A chain of the join from a shared point, entered by
      a chain of one world from a shared point, ends in the amalgam. *)
  Lemma join_amalgam z y :
    J ⊢ z ≺ y → shared y →
    (∀ x, shared x → (W1 ⊢ x ≺ z ∨ W2 ⊢ x ≺ z) → tc amalgam x y) ∧
    (shared z → tc amalgam z y).
  Proof.
    induction 1 as [z y Hs|z w y Hs _ IH]; intros Hy.
    - apply jstep_inv in Hs.
      split.
      + intros x Hx [Hxz|Hxz]; destruct Hs as [Hs|Hs].
        * apply tc_once. split_and!; [done|done|left]. eapply w_lt_trans; [done|by apply wstep_lt].
        * destruct (lt_zone W1 x z H1 Hxz) as [Hp|[_ Zz]].
          -- apply tc_once. split_and!; [done|done|right].
             eapply w_lt_trans; [by apply po_lt|by apply wstep_lt].
          -- assert (zone W2 z) as Zz2.
             { destruct (lt_zone W2 z y H2 (wstep_lt _ _ _ Hs)) as [Hp|[Z _]]; [|done].
               apply po_root in Hp as [Hr _]. destruct Hy as (a & Ha & HaS).
               left. exists a. split; [congruence|unfold wshared in HaS; set_solver]. }
             pose proof (zone_shared z Zz Zz2) as Hz.
             eapply tc_l; [split_and!; [done|done|by left]|].
             apply tc_once. split_and!; [done|done|right]. by apply wstep_lt.
        * destruct (lt_zone W2 x z H2 Hxz) as [Hp|[_ Zz]].
          -- apply tc_once. split_and!; [done|done|left].
             eapply w_lt_trans; [by apply po_lt|by apply wstep_lt].
          -- assert (zone W1 z) as Zz1.
             { destruct (lt_zone W1 z y H1 (wstep_lt _ _ _ Hs)) as [Hp|[Z _]]; [|done].
               apply po_root in Hp as [Hr _]. destruct Hy as (a & Ha & HaS).
               left. exists a. split; [congruence|unfold wshared in HaS; set_solver]. }
             pose proof (zone_shared z Zz1 Zz) as Hz.
             eapply tc_l; [split_and!; [done|done|by right]|].
             apply tc_once. split_and!; [done|done|left]. by apply wstep_lt.
        * apply tc_once. split_and!; [done|done|right]. eapply w_lt_trans; [done|by apply wstep_lt].
      + intros Hz. apply tc_once. split_and!; [done|done|].
        destruct Hs; [left|right]; by apply wstep_lt.
    - destruct (IH Hy) as [IH1 IH2]. apply jstep_inv in Hs. split.
      + intros x Hx [Hxz|Hxz]; destruct Hs as [Hs|Hs].
        * apply IH1; [done|left]. eapply w_lt_trans; [done|by apply wstep_lt].
        * destruct (lt_zone W1 x z H1 Hxz) as [Hp|[_ Zz]].
          -- apply IH1; [done|right]. eapply w_lt_trans; [by apply po_lt|by apply wstep_lt].
          -- destruct (lt_zone W2 z w H2 (wstep_lt _ _ _ Hs)) as [Hp|[Zz2 _]].
             ++ assert (W1 ⊢ x ≺ w) by (eapply w_lt_trans; [done|by apply po_lt]).
                apply IH1; [done|by left].
             ++ pose proof (zone_shared z Zz Zz2) as Hz.
                eapply tc_l; [split_and!; [done|done|by left]|].
                apply IH1; [done|right]. by apply wstep_lt.
        * destruct (lt_zone W2 x z H2 Hxz) as [Hp|[_ Zz]].
          -- apply IH1; [done|left]. eapply w_lt_trans; [by apply po_lt|by apply wstep_lt].
          -- destruct (lt_zone W1 z w H1 (wstep_lt _ _ _ Hs)) as [Hp|[Zz1 _]].
             ++ assert (W2 ⊢ x ≺ w) by (eapply w_lt_trans; [done|by apply po_lt]).
                apply IH1; [done|by right].
             ++ pose proof (zone_shared z Zz1 Zz) as Hz.
                eapply tc_l; [split_and!; [done|done|by right]|].
                apply IH1; [done|left]. by apply wstep_lt.
        * apply IH1; [done|right]. eapply w_lt_trans; [done|by apply wstep_lt].
      + intros Hz. apply IH1; [done|]. destruct Hs; [left|right]; by apply wstep_lt.
  Qed.

  Lemma join_shared x y : shared x → shared y → J ⊢ x ≺ y → tc amalgam x y.
  Proof. intros Hx Hy H. by apply (join_amalgam x y H Hy). Qed.

  Lemma zone_po W x y : po x y → zone W x ↔ zone W y.
  Proof. intros Hp. apply po_root in Hp as [Hr _]. unfold zone. by rewrite Hr. Qed.

  (** A step of a world from outside its zone is program order. *)
  Lemma step_out (Wa Wb : world) x y : world_wf Wb → wstep Wb x y → ¬ zone Wb x → wstep Wa x y.
  Proof.
    intros Hwf Hs Hx. destruct Hs as [x y Hf|ℓ g x y Hℓ Hl|x|x].
    - destruct (wf_facts _ Hwf x y Hf) as [[a [??]] _]. destruct Hx. left. eauto.
    - destruct (wf_laws _ Hwf ℓ x y Hℓ Hl) as [Hr _]. destruct Hx. right. exists ℓ, g.
      split; [by apply law_inst_root|done].
    - apply ws_po.
    - apply ws_dpo.
  Qed.

  (** A chain of the join from outside the zone of Wb stays in Wa until
      it reaches a shared point. *)
  Lemma join_exit (Wa Wb : world) :
    world_wf Wa → world_wf Wb →
    (∀ x y, wstep J x y → wstep Wa x y ∨ wstep Wb x y) →
    (∀ x y, Wa ⊢ x ≺ y → J ⊢ x ≺ y) →
    (∀ x, zone Wa x → zone Wb x → shared x) →
    ∀ x y, ¬ zone Wb x → J ⊢ x ≺ y →
      Wa ⊢ x ≺ y ∨ ∃ u, shared u ∧ Wa ⊢ x ≺ u ∧ (u = y ∨ J ⊢ u ≺ y).
  Proof.
    intros Ha Hb Hinv Hmono Hsh x y Hx H. revert Hx.
    induction H as [x y Hs|x z y Hs Hzy0 IH]; intros Hx.
    - left. apply wstep_lt. destruct (Hinv x y Hs) as [?|Hs']; [done|].
      by apply (step_out Wa Wb).
    - assert (wstep Wa x z) as Hs'.
      { destruct (Hinv x z Hs) as [?|Hs']; [done|]. by apply (step_out Wa Wb). }
      destruct (decide (zone Wb z)) as [Zz|Zz]; [|]; cycle 1.
      + destruct (IH Zz) as [Hzy|(u & Hu & Hzu & Huy)].
        * left. eapply w_lt_trans; [by apply wstep_lt|done].
        * right. exists u. split_and!; [done| |done]. eapply w_lt_trans; [by apply wstep_lt|done].
      + destruct (lt_zone Wa x z Ha (wstep_lt _ _ _ Hs')) as [Hp|[_ Za]].
        * exfalso. apply Hx. by apply (zone_po Wb x z Hp).
        * right. exists z. split_and!; [by apply Hsh|by apply wstep_lt|right; exact Hzy0].
  Qed.

  Lemma rjoin_lt x y :
    wrestrict W1 S ⊔ wrestrict W2 S ⊢ x ≺ y → J ⊢ x ≺ y.
  Proof.
    assert (∀ x y, wstep (wrestrict W1 S ⊔ wrestrict W2 S) x y → J ⊢ x ≺ y) as Hs.
    { intros a b Hs. apply wstep_join_inv in Hs as [Hs|Hs]; apply tc_once in Hs;
        apply wrestrict_lt in Hs; [eapply w_lt_mono; [apply wext_join_l|exact Hs]
                                  |eapply w_lt_mono; [apply wext_join_r|exact Hs]]. }
    induction 1 as [x y H|x z y H _ IH].
    - by apply Hs.
    - eapply w_lt_trans; [by apply Hs|done].
  Qed.

  Lemma amalgam_lt x y : tc amalgam x y → wrestrict W1 S ⊔ wrestrict W2 S ⊢ x ≺ y.
  Proof.
    assert (∀ x y, amalgam x y → wrestrict W1 S ⊔ wrestrict W2 S ⊢ x ≺ y) as Ha.
    { intros a b (Ha & Hb & [H|H]); apply w_lt_fact; simpl; [left|right]; split_and!; try done.
      all: destruct Ha as (c & Hc & HcS), Hb as (d & Hd & HdS); unfold wshared in *.
      all: first [exists c; split; [done|set_solver] | exists d; split; [done|set_solver]]. }
    induction 1 as [x y H|x z y H _ IH]; [by apply Ha|]. eapply w_lt_trans; [by apply Ha|done].
  Qed.

  (** Cleanup item R7. *)
  Theorem strict_join_iff :
    strict (W1 ⊔ W2) ↔ strict W1 ∧ strict W2 ∧ strict (wrestrict W1 S ⊔ wrestrict W2 S).
  Proof.
    split.
    - intros HJ. split_and!.
      + by apply (strict_mono W1 J H1 (wext_join_l _ _)).
      + by apply (strict_mono W2 J H2 (wext_join_r _ _)).
      + split; [apply wjoin_wf; apply wrestrict_wf|]. intros x Hx.
        apply (proj2 HJ x). by apply rjoin_lt.
    - intros (HS1 & HS2 & HSR). split; [by apply wjoin_wf|].
      assert (∀ u, shared u → ¬ J ⊢ u ≺ u) as Hsh.
      { intros u Hu Huu. apply (proj2 HSR u). apply amalgam_lt. by apply join_shared. }
      intros x Hx. destruct (decide (shared x)) as [Hs|Hs]; [by apply (Hsh x)|].
      assert (∀ x y, W1 ⊢ x ≺ y → J ⊢ x ≺ y) as Hm1 by (intros; eapply w_lt_mono; [apply wext_join_l|done]).
      assert (∀ x y, W2 ⊢ x ≺ y → J ⊢ x ≺ y) as Hm2 by (intros; eapply w_lt_mono; [apply wext_join_r|done]).
      destruct (decide (zone W2 x)) as [Z2|Z2].
      + assert (¬ zone W1 x) as Z1 by (intros Z1; by apply Hs, zone_shared).
        destruct (join_exit W2 W1 H2 H1 ltac:(intros a b Hab; apply jstep_inv in Hab; tauto) Hm2
                    ltac:(intros a Za Zb; by apply zone_shared) x x Z1 Hx)
          as [Hxx|(u & Hu & Hxu & [<-|Hux])]; [by apply (proj2 HS2 x)|done|].
        apply (Hsh u Hu). eapply w_lt_trans; [done|by apply Hm2].
      + destruct (join_exit W1 W2 H1 H2 ltac:(intros a b Hab; by apply jstep_inv) Hm1 zone_shared
                    x x Z2 Hx)
          as [Hxx|(u & Hu & Hxu & [<-|Hux])]; [by apply (proj2 HS1 x)|done|].
        apply (Hsh u Hu). eapply w_lt_trans; [done|by apply Hm1].
  Qed.

End join.

(** ** Renaming families apart

    [wfrename f W] renames the families of W by an injective f. The
    order is the same up to the renaming of generated roots, so a
    component can always be relabelled before a join. *)
Definition wfrename (f : family → family) (W : world) : world :=
  World (w_consts W) (w_facts W) (set_map f (w_fams W))
    (λ ℓ g, ∃ ℓ0, ℓ = f ℓ0 ∧ ℓ0 ∈ w_fams W ∧ w_laws W ℓ0 g).

(** A point of a law or a constant fact has no generated root. *)
Definition no_gen (x : point) : Prop := ∀ ℓ g, pt_root x ≠ NGen ℓ g.

Lemma pn_gmap_nogen r p : (∀ ℓ g, pn_root p ≠ NGen ℓ g) → pn_gmap r p = p.
Proof. induction p; simpl; intros H; rewrite ?IHp; auto. by destruct (H ℓ g). Qed.

Lemma pt_gmap_nogen r x : no_gen x → pt_gmap r x = x.
Proof. intros H. destruct x. unfold pt_gmap. simpl. by rewrite pn_gmap_nogen. Qed.

Lemma law_inst_gmap r ℓ g x :
  pt_root x = NVar 0 → pt_gmap r (law_inst ℓ g x) = law_inst (r (ℓ, g)).1 (r (ℓ, g)).2 x.
Proof.
  intros Hx. unfold law_inst. rewrite pt_gmap_inst.
  rewrite (pt_gmap_nogen r x) by (intros ??; rewrite Hx; done).
  apply pt_inst_ext. intros a. done.
Qed.

(** A renaming of generated roots that respects families maps the order
    into the order. Families renamed by f, roots within a family by
    anything. *)
Lemma w_lt_gmap W r f x y :
  world_wf W → (∀ ℓ g, (r (ℓ, g)).1 = f ℓ) →
  W ⊢ x ≺ y → wfrename f W ⊢ pt_gmap r x ≺ pt_gmap r y.
Proof.
  intros Hwf Hr. apply tc_congruence. intros a b Hs.
  destruct Hs as [a b Hf|ℓ g a b Hℓ Hl|a|a].
  - destruct (wf_facts _ Hwf a b Hf) as [[c [Hc _]] [d [Hd _]]].
    rewrite !pt_gmap_nogen by (intros ??; congruence). by apply ws_fact.
  - destruct (wf_laws _ Hwf ℓ a b Hℓ Hl) as [Ha Hb].
    rewrite !law_inst_gmap by done. rewrite Hr. apply ws_law; [set_solver|].
    exists ℓ. split_and!; done.
  - apply ws_po.
  - apply ws_dpo.
Qed.

Lemma wfrename_wf f W : world_wf W → world_wf (wfrename f W).
Proof.
  intros Hwf. split; simpl.
  - apply (wf_facts _ Hwf).
  - intros ℓ x y _ (ℓ0 & -> & Hℓ0 & Hl). by apply (wf_laws _ Hwf ℓ0).
Qed.

(** A family renaming with a left inverse loses nothing. Renaming the
    families back lands inside W. *)
Lemma wfrename_back f f' W : (∀ ℓ, f' (f ℓ) = ℓ) → wfrename f' (wfrename f W) ⊑ W.
Proof.
  intros Hf. split; simpl; [done|done| |].
  - intros ℓ Hℓ. apply elem_of_map in Hℓ as (ℓ1 & -> & H1).
    apply elem_of_map in H1 as (ℓ0 & -> & H0). by rewrite Hf.
  - intros ℓ g _ (ℓ1 & -> & _ & ℓ0 & -> & Hℓ0 & Hl). by rewrite Hf.
Qed.

Lemma w_lt_frename_back W f f' x y :
  world_wf W → (∀ ℓ, f' (f ℓ) = ℓ) →
  wfrename f W ⊢ x ≺ y → W ⊢ pt_gmap (frename f') x ≺ pt_gmap (frename f') y.
Proof.
  intros Hwf Hf H. eapply w_lt_mono; [by apply wfrename_back|].
  apply (w_lt_gmap _ _ f'); [by apply wfrename_wf|done|done].
Qed.

Lemma strict_wfrename f f' W : (∀ ℓ, f' (f ℓ) = ℓ) → strict W → strict (wfrename f W).
Proof.
  intros Hf [Hwf HS]. split; [by apply wfrename_wf|]. intros x Hx.
  apply (HS (pt_gmap (frename f') x)). by eapply w_lt_frename_back.
Qed.

Lemma lfworld_wfrename f f' W : (∀ ℓ, f' (f ℓ) = ℓ) → lfworld W → lfworld (wfrename f W).
Proof.
  intros Hf [HS Hwf]. split; [by apply (strict_wfrename f f')|].
  apply (wf_projected (w_lt W) (pt_gmap (frename f'))); [|done].
  intros x y H. by apply (w_lt_frename_back W f f'); [apply HS|done|].
Qed.

(** Renaming the generated roots of one family is invisible to W: the
    order between renamed points is the order between the points. *)
Lemma w_lt_grename W r x y :
  world_wf W → (∀ ℓ g, (r (ℓ, g)).1 = ℓ) →
  W ⊢ x ≺ y → W ⊢ pt_gmap r x ≺ pt_gmap r y.
Proof.
  intros Hwf Hr H. eapply w_lt_mono; [|apply (w_lt_gmap W r id); done].
  split; simpl; [done|done| |].
  - intros ℓ Hℓ. apply elem_of_map in Hℓ as (ℓ0 & -> & ?). done.
  - by intros ℓ g _ (ℓ0 & -> & _ & ?).
Qed.
