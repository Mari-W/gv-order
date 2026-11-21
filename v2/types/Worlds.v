(** * Static worlds (stage 3, layers)

    W = (A, ≺_A)
      A      a finite set of constants
      ≺_A    facts between points with constant roots in A

    ≺_W is the transitive closure of ≺_A, of x ≺ x⁺ and of x ≺ x‾⁺. A
    static world is the world of a typing derivation. The relation reads
    ranked worlds instead (relation/Ranks.v), and a ranked world models
    a static one when it ranks every fact of it.

    The join W1 ⊔ W2 unions constants and facts. P-Term asks W
    well-founded ([swf]), and P-Connect asks the restrictions of the two
    worlds to their shared constants S = A_{W1} ∩ A_{W2} well-founded
    together. [wf_join_iff] shows that this makes the join well-founded,
    constructively, by nested accessibility on the amalgam at S and on
    each side. *)

From GV Require Export types.Points.

Record sworld := SWorld {
  sw_consts : gset nat;
  sw_facts : fact → Prop
}.

(** One generating step of ≺_W. *)
Inductive swstep (W : sworld) : point → point → Prop :=
  | ws_fact x y : sw_facts W (FLt x y) → swstep W x y
  | ws_po x : swstep W x x⁺
  | ws_dpo x : swstep W x x‾⁺.

Definition sw_lt (W : sworld) : point → point → Prop := tc (swstep W).

Notation "W ⊢ₛ x ≺ y" := (sw_lt W x y)
  (at level 74, x at level 60, y at level 60, format "W  ⊢ₛ  x  ≺  y").

(** A constant root in a set. *)
Definition croot_in (S : gset nat) (x : point) : Prop :=
  ∃ a, pt_root x = NConst a ∧ a ∈ S.

Global Instance croot_in_dec S x : Decision (croot_in S x).
Proof.
  unfold croot_in. destruct (pt_root x) as [a|a|p b κ];
    [destruct (decide (a ∈ S))|..]; first [left; naive_solver|right; naive_solver].
Defined.

(** The facts of W relate points with constant roots of W. *)
Record sworld_wf (W : sworld) : Prop := {
  wf_facts x y : sw_facts W (FLt x y) → croot_in (sw_consts W) x ∧ croot_in (sw_consts W) y
}.

(** W is well-founded: ≺_W has no infinite descending chain. P-Term asks
    it, and [wf_join_iff] reduces it at a join to the shared roots. *)
Definition swf (W : sworld) : Prop := well_founded (sw_lt W).

Lemma sw_lt_trans W x y z : W ⊢ₛ x ≺ y → W ⊢ₛ y ≺ z → W ⊢ₛ x ≺ z.
Proof. apply tc_transitive. Qed.
Lemma sw_lt_po W x : W ⊢ₛ x ≺ x⁺.
Proof. apply tc_once, ws_po. Qed.
Lemma sw_lt_dpo W x : W ⊢ₛ x ≺ x‾⁺.
Proof. apply tc_once, ws_dpo. Qed.
Lemma sw_lt_fact W x y : sw_facts W (FLt x y) → W ⊢ₛ x ≺ y.
Proof. intros H. by apply tc_once, ws_fact. Qed.

(** ** Program order, the facts every world has *)

Definition po (x y : point) : Prop := tc (λ a b, b = a⁺ ∨ b = a‾⁺) x y.

Lemma po_slt W x y : po x y → W ⊢ₛ x ≺ y.
Proof.
  induction 1 as [x y [->| ->]|x y z [->| ->] _ IH].
  - apply sw_lt_po.
  - apply sw_lt_dpo.
  - eapply sw_lt_trans; [apply sw_lt_po|done].
  - eapply sw_lt_trans; [apply sw_lt_dpo|done].
Qed.

Lemma po_root x y : po x y → pt_root x = pt_root y ∧ pt_off x < pt_off y.
Proof.
  induction 1 as [x y [->| ->]|x y z [->| ->] _ [IH1 IH2]]; unfold pt_root in *;
    cbn [pt_shift pt_dual pt_name pt_off] in *; split; try done; lia.
Qed.

Lemma po_trans x y z : po x y → po y z → po x z.
Proof. apply tc_transitive. Qed.

Lemma po_irrefl x : ¬ po x x.
Proof. intros H. apply po_root in H as [_ H]. lia. Qed.

(** Program order is well-founded, because it raises the offset. *)
Lemma po_wf : well_founded po.
Proof.
  intros x. remember (pt_off x) as k eqn:Hk. revert x Hk.
  induction k as [k IH] using (well_founded_induction lt_wf). intros x ->.
  constructor. intros y Hy. apply (IH (pt_off y)); [|done]. by apply po_root in Hy as [_ ?].
Qed.

(** A world without facts orders only by program order. *)
Lemma sw_lt_bare W x y : (∀ g, ¬ sw_facts W g) → W ⊢ₛ x ≺ y → po x y.
Proof.
  intros Hf. induction 1 as [x y Hs|x y z Hs _ IH].
  - destruct Hs as [x y Hxy|x|x]; [by destruct (Hf _ Hxy)|by apply tc_once; left|by apply tc_once; right].
  - eapply tc_transitive; [|exact IH].
    destruct Hs as [x y Hxy|x|x]; [by destruct (Hf _ Hxy)|by apply tc_once; left|by apply tc_once; right].
Qed.

Lemma swf_bare W : (∀ g, ¬ sw_facts W g) → swf W.
Proof.
  intros Hf x. induction (po_wf x) as [x _ IH]. constructor. intros y Hy.
  apply IH. by apply (sw_lt_bare W).
Qed.

Lemma sworld_wf_bare W : (∀ g, ¬ sw_facts W g) → sworld_wf W.
Proof. intros Hf. split. intros x y H. by destruct (Hf _ H). Qed.

(** A relation contained in a well-founded one is well-founded. *)
Lemma wf_sub {A} (R R' : A → A → Prop) : (∀ x y, R' x y → R x y) → well_founded R → well_founded R'.
Proof.
  intros H HR x. induction (HR x) as [x _ IH]. constructor. intros y Hy. by apply IH, H.
Qed.

(** Accessibility for the steps gives accessibility for their closure. *)
Lemma acc_tc {A} (R : A → A → Prop) x : Acc R x → Acc (λ a b, tc (λ c d, R c d) a b) x.
Proof.
  induction 1 as [x _ IH]. constructor. intros y Hy.
  cut (∀ z, tc (λ c d, R c d) z x → Acc (λ a b, tc (λ c d, R c d) a b) z); [eauto|].
  clear y Hy. intros z Hz. induction Hz as [z x Hzx|z w x Hzw Hwx IHw].
  - by apply IH.
  - destruct (IHw IH) as [Hacc]. apply Hacc. by apply tc_once.
Qed.

(** ** Extension, join, restriction *)

Record swext (W W' : sworld) : Prop := {
  swext_consts : sw_consts W ⊆ sw_consts W';
  swext_facts g : sw_facts W g → sw_facts W' g
}.

Notation "W ⊑ₛ W'" := (swext W W') (at level 70).

Lemma swext_refl W : W ⊑ₛ W.
Proof. split; auto. Qed.

Lemma swext_trans W1 W2 W3 : W1 ⊑ₛ W2 → W2 ⊑ₛ W3 → W1 ⊑ₛ W3.
Proof. intros [] []. split; [set_solver|auto]. Qed.

Lemma swstep_mono W W' x y : W ⊑ₛ W' → swstep W x y → swstep W' x y.
Proof.
  intros HW. destruct 1.
  - apply ws_fact. by apply (swext_facts _ _ HW).
  - apply ws_po.
  - apply ws_dpo.
Qed.

Lemma sw_lt_mono W W' x y : W ⊑ₛ W' → W ⊢ₛ x ≺ y → W' ⊢ₛ x ≺ y.
Proof. intros HW. apply tc_congruence with (f := id). intros. by eapply swstep_mono. Qed.

Lemma swf_mono W W' : W ⊑ₛ W' → swf W' → swf W.
Proof. intros HW. apply wf_sub. intros x y. by apply sw_lt_mono. Qed.

Definition swjoin (W1 W2 : sworld) : sworld :=
  SWorld (sw_consts W1 ∪ sw_consts W2) (λ g, sw_facts W1 g ∨ sw_facts W2 g).

Notation "W1 ⊔ W2" := (swjoin W1 W2) (at level 50).

Lemma swext_join_l W1 W2 : W1 ⊑ₛ W1 ⊔ W2.
Proof. split; simpl; [set_solver|auto]. Qed.

Lemma swext_join_r W1 W2 : W2 ⊑ₛ W1 ⊔ W2.
Proof. split; simpl; [set_solver|auto]. Qed.

Lemma swjoin_wf W1 W2 : sworld_wf W1 → sworld_wf W2 → sworld_wf (W1 ⊔ W2).
Proof.
  intros H1 H2. split; simpl.
  intros x y [Hf|Hf]; [destruct (wf_facts _ H1 x y Hf) as [[a [??]] [b [??]]]
                      |destruct (wf_facts _ H2 x y Hf) as [[a [??]] [b [??]]]];
    split; eexists; split; eauto; set_solver.
Qed.

(** W restricted to the constants S: the facts of ≺_W between points
    with constant roots in S. *)
Definition swrestrict (W : sworld) (S : gset nat) : sworld :=
  SWorld (sw_consts W ∩ S)
    (λ g, match g with FLt x y => W ⊢ₛ x ≺ y ∧ croot_in (sw_consts W ∩ S) x ∧ croot_in (sw_consts W ∩ S) y end).

Lemma swrestrict_wf W S : sworld_wf (swrestrict W S).
Proof. split; simpl. by intros x y (_ & ? & ?). Qed.

(** The restriction says nothing W does not. *)
Lemma swrestrict_lt W S x y : swrestrict W S ⊢ₛ x ≺ y → W ⊢ₛ x ≺ y.
Proof.
  induction 1 as [x y Hs|x y z Hs _ IH].
  - destruct Hs as [x y (H & _ & _)|x|x]; [done|apply sw_lt_po|apply sw_lt_dpo].
  - eapply sw_lt_trans; [|done].
    destruct Hs as [x y (H & _ & _)|x|x]; [done|apply sw_lt_po|apply sw_lt_dpo].
Qed.

(** The shared constants of two worlds. *)
Definition swshared (W1 W2 : sworld) : gset nat := sw_consts W1 ∩ sw_consts W2.

(** A step of a join is a step of one side. *)
Lemma swstep_join_inv A B x y : swstep (A ⊔ B) x y → swstep A x y ∨ swstep B x y.
Proof.
  destruct 1 as [x y [Hf|Hf]|x|x].
  - left. by apply ws_fact.
  - right. by apply ws_fact.
  - left. apply ws_po.
  - left. apply ws_dpo.
Qed.

(** ** Well-foundedness of a join at the interface *)

Section join.
  Context (W1 W2 : sworld).
  Context (H1 : sworld_wf W1) (H2 : sworld_wf W2).

  Local Abbreviation J := (W1 ⊔ W2).
  Local Abbreviation S := (swshared W1 W2).

  (** The zone of a world: points whose root it owns. *)
  Definition zone (W : sworld) (x : point) : Prop := croot_in (sw_consts W) x.

  Global Instance zone_dec W x : Decision (zone W x).
  Proof. unfold zone. apply _. Defined.

  Local Definition shared (x : point) : Prop := croot_in S x.

  Lemma zone_po W x y : po x y → zone W x ↔ zone W y.
  Proof. intros Hp. apply po_root in Hp as [Hr _]. unfold zone, croot_in. by rewrite Hr. Qed.

  (** A chain of one world either is program order or stays in its zone. *)
  Lemma lt_zone (W : sworld) x y : sworld_wf W → W ⊢ₛ x ≺ y → po x y ∨ (zone W x ∧ zone W y).
  Proof.
    intros Hwf. induction 1 as [x y Hs|x y z Hs _ IH].
    - destruct Hs as [x y Hf|x|x].
      + right. exact (wf_facts _ Hwf x y Hf).
      + left. apply tc_once. by left.
      + left. apply tc_once. by right.
    - assert (po x y ∨ (zone W x ∧ zone W y)) as Hxy.
      { destruct Hs as [x y Hf|x|x].
        + right. exact (wf_facts _ Hwf x y Hf).
        + left. apply tc_once. by left.
        + left. apply tc_once. by right. }
      destruct Hxy as [Hp|[Zx Zy]], IH as [Hp'|[Zy' Zz]].
      + left. by eapply tc_transitive.
      + right. split; [|done]. by apply (zone_po W x y Hp).
      + right. split; [done|]. by apply (zone_po W y z Hp').
      + by right.
  Qed.

  Lemma zone_shared x : zone W1 x → zone W2 x → shared x.
  Proof.
    intros (a & Ha & Ha1) (b & Hb & Hb2). exists a. split; [done|].
    rewrite Ha in Hb. injection Hb as <-. unfold swshared. set_solver.
  Qed.

  (** The amalgam: the two orders between shared points. *)
  Definition amalgam (x y : point) : Prop :=
    shared x ∧ shared y ∧ (W1 ⊢ₛ x ≺ y ∨ W2 ⊢ₛ x ≺ y).

  Local Lemma swstep_lt W x y : swstep W x y → W ⊢ₛ x ≺ y.
  Proof. apply tc_once. Qed.

  Local Lemma jstep_inv x y : swstep J x y → swstep W1 x y ∨ swstep W2 x y.
  Proof. apply swstep_join_inv. Qed.

  (** A chain of the join from a shared point, entered by a chain of one
      world from a shared point, ends in the amalgam. *)
  Lemma join_amalgam z y :
    J ⊢ₛ z ≺ y → shared y →
    (∀ x, shared x → (W1 ⊢ₛ x ≺ z ∨ W2 ⊢ₛ x ≺ z) → tc amalgam x y) ∧
    (shared z → tc amalgam z y).
  Proof.
    induction 1 as [z y Hs|z w y Hs _ IH]; intros Hy.
    - apply jstep_inv in Hs.
      split.
      + intros x Hx [Hxz|Hxz]; destruct Hs as [Hs|Hs].
        * apply tc_once. split_and!; [done|done|left]. eapply sw_lt_trans; [done|by apply swstep_lt].
        * destruct (lt_zone W1 x z H1 Hxz) as [Hp|[_ Zz]].
          -- apply tc_once. split_and!; [done|done|right].
             eapply sw_lt_trans; [by apply po_slt|by apply swstep_lt].
          -- assert (zone W2 z) as Zz2.
             { destruct (lt_zone W2 z y H2 (swstep_lt _ _ _ Hs)) as [Hp|[Z _]]; [|done].
               apply po_root in Hp as [Hr _]. destruct Hy as (a & Ha & HaS).
               exists a. split; [congruence|unfold swshared in HaS; set_solver]. }
             pose proof (zone_shared z Zz Zz2) as Hz.
             eapply tc_l; [split_and!; [done|done|by left]|].
             apply tc_once. split_and!; [done|done|right]. by apply swstep_lt.
        * destruct (lt_zone W2 x z H2 Hxz) as [Hp|[_ Zz]].
          -- apply tc_once. split_and!; [done|done|left].
             eapply sw_lt_trans; [by apply po_slt|by apply swstep_lt].
          -- assert (zone W1 z) as Zz1.
             { destruct (lt_zone W1 z y H1 (swstep_lt _ _ _ Hs)) as [Hp|[Z _]]; [|done].
               apply po_root in Hp as [Hr _]. destruct Hy as (a & Ha & HaS).
               exists a. split; [congruence|unfold swshared in HaS; set_solver]. }
             pose proof (zone_shared z Zz1 Zz) as Hz.
             eapply tc_l; [split_and!; [done|done|by right]|].
             apply tc_once. split_and!; [done|done|left]. by apply swstep_lt.
        * apply tc_once. split_and!; [done|done|right]. eapply sw_lt_trans; [done|by apply swstep_lt].
      + intros Hz. apply tc_once. split_and!; [done|done|].
        destruct Hs; [left|right]; by apply swstep_lt.
    - destruct (IH Hy) as [IH1 IH2]. apply jstep_inv in Hs. split.
      + intros x Hx [Hxz|Hxz]; destruct Hs as [Hs|Hs].
        * apply IH1; [done|left]. eapply sw_lt_trans; [done|by apply swstep_lt].
        * destruct (lt_zone W1 x z H1 Hxz) as [Hp|[_ Zz]].
          -- apply IH1; [done|right]. eapply sw_lt_trans; [by apply po_slt|by apply swstep_lt].
          -- destruct (lt_zone W2 z w H2 (swstep_lt _ _ _ Hs)) as [Hp|[Zz2 _]].
             ++ assert (W1 ⊢ₛ x ≺ w) by (eapply sw_lt_trans; [done|by apply po_slt]).
                apply IH1; [done|by left].
             ++ pose proof (zone_shared z Zz Zz2) as Hz.
                eapply tc_l; [split_and!; [done|done|by left]|].
                apply IH1; [done|right]. by apply swstep_lt.
        * destruct (lt_zone W2 x z H2 Hxz) as [Hp|[_ Zz]].
          -- apply IH1; [done|left]. eapply sw_lt_trans; [by apply po_slt|by apply swstep_lt].
          -- destruct (lt_zone W1 z w H1 (swstep_lt _ _ _ Hs)) as [Hp|[Zz1 _]].
             ++ assert (W2 ⊢ₛ x ≺ w) by (eapply sw_lt_trans; [done|by apply po_slt]).
                apply IH1; [done|by right].
             ++ pose proof (zone_shared z Zz1 Zz) as Hz.
                eapply tc_l; [split_and!; [done|done|by right]|].
                apply IH1; [done|left]. by apply swstep_lt.
        * apply IH1; [done|right]. eapply sw_lt_trans; [done|by apply swstep_lt].
      + intros Hz. apply IH1; [done|]. destruct Hs; [left|right]; by apply swstep_lt.
  Qed.

  Lemma join_shared x y : shared x → shared y → J ⊢ₛ x ≺ y → tc amalgam x y.
  Proof. intros Hx Hy H. by apply (join_amalgam x y H Hy). Qed.

  Lemma rjoin_lt x y :
    swrestrict W1 S ⊔ swrestrict W2 S ⊢ₛ x ≺ y → J ⊢ₛ x ≺ y.
  Proof.
    assert (∀ x y, swstep (swrestrict W1 S ⊔ swrestrict W2 S) x y → J ⊢ₛ x ≺ y) as Hs.
    { intros a b Hs. apply swstep_join_inv in Hs as [Hs|Hs]; apply tc_once in Hs;
        apply swrestrict_lt in Hs; [eapply sw_lt_mono; [apply swext_join_l|exact Hs]
                                   |eapply sw_lt_mono; [apply swext_join_r|exact Hs]]. }
    induction 1 as [x y H|x z y H _ IH].
    - by apply Hs.
    - eapply sw_lt_trans; [by apply Hs|done].
  Qed.

  Lemma amalgam_lt x y : tc amalgam x y → swrestrict W1 S ⊔ swrestrict W2 S ⊢ₛ x ≺ y.
  Proof.
    assert (∀ x y, amalgam x y → swrestrict W1 S ⊔ swrestrict W2 S ⊢ₛ x ≺ y) as Ha.
    { intros a b (Ha & Hb & [H|H]); apply sw_lt_fact; simpl; [left|right]; split_and!; try done.
      all: destruct Ha as (c & Hc & HcS), Hb as (d & Hd & HdS); unfold swshared in *.
      all: first [exists c; split; [done|set_solver] | exists d; split; [done|set_solver]]. }
    induction 1 as [x y H|x z y H _ IH]; [by apply Ha|]. eapply sw_lt_trans; [by apply Ha|done].
  Qed.

  (** A step of the join into a point outside the zone of Wb is a step of Wa. *)
  Local Lemma step_into (Wa Wb : sworld) z x :
    sworld_wf Wb → (swstep J z x → swstep Wa z x ∨ swstep Wb z x) →
    swstep J z x → ¬ zone Wb x → swstep Wa z x.
  Proof.
    intros Hwf Hinv Hs Hx. destruct (Hinv Hs) as [?|Hs']; [done|].
    destruct Hs' as [z x Hf|z|z].
    - destruct (wf_facts _ Hwf z x Hf) as [_ ?]. by destruct Hx.
    - apply ws_po.
    - apply ws_dpo.
  Qed.

  (** Below a point outside the zone of Wb, the steps of the join are
      accessible as soon as every shared point Wa puts below it is. *)
  Local Lemma acc_side (Wa Wb : sworld) :
    sworld_wf Wa → sworld_wf Wb → swf Wa →
    (∀ z x, swstep J z x → swstep Wa z x ∨ swstep Wb z x) →
    (∀ x, zone Wa x → zone Wb x → shared x) →
    ∀ x, ¬ zone Wb x → (∀ v, shared v → Wa ⊢ₛ v ≺ x → Acc (swstep J) v) → Acc (swstep J) x.
  Proof.
    intros Ha Hb Hwfa Hinv Hsh x. induction (Hwfa x) as [x _ IH]. intros Hx Hv.
    constructor. intros z Hz.
    pose proof (step_into Wa Wb z x Hb (Hinv z x) Hz Hx) as Hza.
    destruct (decide (zone Wb z)) as [Zb|Zb].
    - apply Hv; [|by apply swstep_lt]. apply Hsh; [|done].
      inversion Hza as [z' x' Hf| |]; subst.
      + exact (proj1 (wf_facts _ Ha z x Hf)).
      + exfalso. apply Hx. apply (zone_po Wb z z⁺); [apply tc_once; by left|done].
      + exfalso. apply Hx. apply (zone_po Wb z z‾⁺); [apply tc_once; by right|done].
    - apply IH; [by apply swstep_lt|done|]. intros v Hvs Hvz. apply Hv; [done|].
      eapply sw_lt_trans; [done|by apply swstep_lt].
  Qed.

  (** The join is well-founded iff both worlds are and the two orders
      restricted to the shared constants are together. Constructive, by
      nested accessibility on the amalgam and on each side. *)
  Theorem wf_join_iff :
    swf (W1 ⊔ W2) ↔ swf W1 ∧ swf W2 ∧ swf (swrestrict W1 S ⊔ swrestrict W2 S).
  Proof.
    split.
    - intros HJ. split_and!.
      + exact (swf_mono W1 J (swext_join_l _ _) HJ).
      + exact (swf_mono W2 J (swext_join_r _ _) HJ).
      + apply (wf_sub _ _ rjoin_lt HJ).
    - intros (HS1 & HS2 & HSR).
      assert (well_founded (tc amalgam)) as Ham by (apply (wf_sub _ _ amalgam_lt HSR)).
      assert (∀ z x, swstep J z x → swstep W1 z x ∨ swstep W2 z x) as Hi1 by apply jstep_inv.
      assert (∀ z x, swstep J z x → swstep W2 z x ∨ swstep W1 z x) as Hi2
        by (intros z x Hs; destruct (jstep_inv z x Hs); tauto).
      assert (∀ u, shared u → Acc (swstep J) u) as Hsh.
      { intros u. induction (Ham u) as [u _ IH]. intros Hu.
        constructor. intros z Hz.
        assert (∀ v, shared v → (W1 ⊢ₛ v ≺ z ∨ W2 ⊢ₛ v ≺ z) → Acc (swstep J) v) as Hbelow.
        { intros v Hv Hvz. apply IH; [|done].
          apply join_shared; [done|done|]. eapply sw_lt_trans; [|by apply tc_once].
          destruct Hvz; [eapply sw_lt_mono; [apply swext_join_l|done]
                        |eapply sw_lt_mono; [apply swext_join_r|done]]. }
        destruct (decide (shared z)) as [Zs|Zs].
        - apply IH; [|done]. apply join_shared; [done|done|by apply tc_once].
        - destruct (decide (zone W2 z)) as [Z2|Z2].
          + assert (¬ zone W1 z) as Z1 by (intros Z1; by apply Zs, zone_shared).
            apply (acc_side W2 W1 H2 H1 HS2 Hi2 (λ x a b, zone_shared x b a) z Z1).
            intros v Hv Hvz. apply Hbelow; [done|by right].
          + apply (acc_side W1 W2 H1 H2 HS1 Hi1 zone_shared z Z2).
            intros v Hv Hvz. apply Hbelow; [done|by left]. }
      assert (∀ x, Acc (swstep J) x) as Hall.
      { intros x. destruct (decide (zone W2 x)) as [Z2|Z2].
        - destruct (decide (zone W1 x)) as [Z1|Z1]; [by apply Hsh, zone_shared|].
          apply (acc_side W2 W1 H2 H1 HS2 Hi2 (λ x a b, zone_shared x b a) x Z1).
          intros v Hv _. by apply Hsh.
        - apply (acc_side W1 W2 H1 H2 HS1 Hi1 zone_shared x Z2).
          intros v Hv _. by apply Hsh. }
      intros x. exact (acc_tc _ x (Hall x)).
  Qed.

End join.
