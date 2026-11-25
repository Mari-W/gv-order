(** * Static worlds (stage 3, layers)

    W = (A, ≺_A)
      A      a finite set of constants
      ≺_A    facts between points with constant bases in A

    ≺_W is the transitive closure of ≺_A, of x ≺ x⁺ and of x ≺ x‾⁺. A
    static world is the world of a typing derivation. The relation reads
    ranked worlds instead (relation/Ranks.v), and a ranked world models
    a static one when it ranks every fact of it.

    The join W1 ⊔ W2 unions constants and facts. At N = ∞ P-Term asks W
    acyclic ([sacyc]), at a finite N well-founded ([swf]), and P-Connect
    asks the restrictions of the two worlds to their shared constants
    S = A_{W1} ∩ A_{W2} acyclic, or well-founded, together.
    [acyc_join_iff] and [wf_join_iff] show that this makes the join
    acyclic, or well-founded, constructively. *)

From GV Require Export relation.Ranks.

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

(** A constant base in a set. *)
Definition croot_in (S : gset nat) (x : point) : Prop :=
  ∃ a, pt_root x = NConst a ∧ a ∈ S.

Global Instance croot_in_dec S x : Decision (croot_in S x).
Proof.
  unfold croot_in. destruct (pt_root x) as [a|a|p b κ];
    [destruct (decide (a ∈ S))|..]; first [left; naive_solver|right; naive_solver].
Defined.

(** The facts of W relate points with constant bases of W. *)
Record sworld_wf (W : sworld) : Prop := {
  wf_facts x y : sw_facts W (FLt x y) → croot_in (sw_consts W) x ∧ croot_in (sw_consts W) y
}.

(** W is well-founded: ≺_W has a rank function (relation/Ranks.v), so
    no infinite descending chain. P-Term asks it, and [wf_join_iff]
    reduces it at a join to the shared bases. *)
Definition swf (W : sworld) : Prop := wf (sw_lt W).

Lemma swf_iff W : swf W ↔ well_founded (sw_lt W).
Proof. apply wf_iff_wellfounded. Qed.

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
  intros Hf. apply swf_iff. intros x. induction (po_wf x) as [x _ IH]. constructor. intros y Hy.
  apply IH. by apply (sw_lt_bare W).
Qed.

Lemma sworld_wf_bare W : (∀ g, ¬ sw_facts W g) → sworld_wf W.
Proof. intros Hf. split. intros x y H. by destruct (Hf _ H). Qed.

(** The static world with no constant and no fact. *)
Definition sw_empty : sworld := SWorld ∅ (λ _, False).

Lemma sw_empty_ok : sworld_wf sw_empty ∧ swf sw_empty.
Proof. split; [apply sworld_wf_bare|apply swf_bare]; intros ? []. Qed.

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
Proof. intros HW [ρ Hρ]. exists ρ. intros x y H. apply Hρ. by eapply sw_lt_mono. Qed.

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
    with constant bases in S. *)
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

(** ** Acyclic static worlds

    The deadlock-free judgment asks a world acyclic ([sacyc]): no point
    lies below itself. A well-founded world is acyclic ([swf_sacyc]), and
    the lock-free judgment keeps well-foundedness. [acyc_join_iff]
    reduces acyclicity of a join to the shared constants. *)
Definition sacyc (W : sworld) : Prop := ∀ x, ¬ W ⊢ₛ x ≺ x.

Lemma swf_sacyc W : swf W → sacyc W.
Proof. intros [ρ Hρ] x H. exact (olt_irrefl _ (Hρ x x H)). Qed.

Lemma sacyc_mono W W' : W ⊑ₛ W' → sacyc W' → sacyc W.
Proof. intros HW H x Hx. apply (H x). by eapply sw_lt_mono. Qed.

Lemma sacyc_bare W : (∀ g, ¬ sw_facts W g) → sacyc W.
Proof. intros Hf. apply swf_sacyc, swf_bare, Hf. Qed.

Lemma sw_empty_acyc : sworld_wf sw_empty ∧ sacyc sw_empty.
Proof. split; [apply sworld_wf_bare|apply sacyc_bare]; intros ? []. Qed.

Section join.
  Context (W1 W2 : sworld).
  Context (H1 : sworld_wf W1) (H2 : sworld_wf W2).

  Local Abbreviation J := (W1 ⊔ W2).
  Local Abbreviation S := (swshared W1 W2).

  (** The zone of a world: points whose base it owns. *)
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
    intros Ha Hb Hwfa Hinv Hsh x. apply swf_iff in Hwfa. induction (Hwfa x) as [x _ IH]. intros Hx Hv.
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
      + destruct HJ as [ρ Hρ]. exists ρ. intros x y H. by apply Hρ, rjoin_lt.
    - intros (HS1 & HS2 & HSR).
      assert (well_founded (tc amalgam)) as Ham by (apply (wf_sub _ _ amalgam_lt), swf_iff, HSR).
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
      apply swf_iff. intros x. exact (acc_tc _ x (Hall x)).
  Qed.


  (** A chain of the join stays in one world or meets a shared point. *)
  Lemma join_split x y : J ⊢ₛ x ≺ y →
    W1 ⊢ₛ x ≺ y ∨ W2 ⊢ₛ x ≺ y ∨ ∃ z, shared z ∧ (x = z ∨ J ⊢ₛ x ≺ z) ∧ (z = y ∨ J ⊢ₛ z ≺ y).
  Proof.
    induction 1 as [x y Hs|x w y Hs Hwy IH].
    - apply jstep_inv in Hs as [Hs|Hs]; [left|right; left]; by apply swstep_lt.
    - assert (J ⊢ₛ x ≺ w) as Hxw by by apply tc_once.
      destruct IH as [H|[H|(z & Hz & Hxz & Hzy)]].
      + apply jstep_inv in Hs as [Hs|Hs]; [left; eapply sw_lt_trans; [by apply swstep_lt|done]|].
        destruct (lt_zone W1 w y H1 H) as [Hp|[Zw _]].
        * right; left. eapply sw_lt_trans; [by apply swstep_lt|by apply po_slt].
        * destruct Hs as [x w Hf|x|x].
          -- right; right. exists w. split; [apply zone_shared; [done|exact (proj2 (wf_facts _ H2 x w Hf))]|].
             split; [by right|]. right. by eapply sw_lt_mono; [apply swext_join_l|].
          -- left. eapply sw_lt_trans; [apply sw_lt_po|done].
          -- left. eapply sw_lt_trans; [apply sw_lt_dpo|done].
      + apply jstep_inv in Hs as [Hs|Hs]; [|right; left; eapply sw_lt_trans; [by apply swstep_lt|done]].
        destruct (lt_zone W2 w y H2 H) as [Hp|[Zw _]].
        * left. eapply sw_lt_trans; [by apply swstep_lt|by apply po_slt].
        * destruct Hs as [x w Hf|x|x].
          -- right; right. exists w. split; [apply zone_shared; [exact (proj2 (wf_facts _ H1 x w Hf))|done]|].
             split; [by right|]. right. by eapply sw_lt_mono; [apply swext_join_r|].
          -- right; left. eapply sw_lt_trans; [apply sw_lt_po|done].
          -- right; left. eapply sw_lt_trans; [apply sw_lt_dpo|done].
      + right; right. exists z. split; [done|]. split; [|done]. right.
        destruct Hxz as [<-|Hxz]; [done|]. by eapply sw_lt_trans.
  Qed.

  (** The join is acyclic iff both worlds are and the two orders
      restricted to the shared constants are together. A cycle of the
      join that meets a shared point rotates to start there and is a
      cycle of the amalgam ([join_shared]). Constructive. *)
  Theorem acyc_join_iff :
    sacyc (W1 ⊔ W2) ↔ sacyc W1 ∧ sacyc W2 ∧ sacyc (swrestrict W1 S ⊔ swrestrict W2 S).
  Proof.
    split.
    - intros HJ. split_and!.
      + exact (sacyc_mono W1 J (swext_join_l _ _) HJ).
      + exact (sacyc_mono W2 J (swext_join_r _ _) HJ).
      + intros x Hx. by apply (HJ x), rjoin_lt.
    - intros (HS1 & HS2 & HSR) x Hx.
      destruct (join_split x x Hx) as [H|[H|(z & Hz & Hxz & Hzx)]]; [by apply (HS1 x)|by apply (HS2 x)|].
      assert (J ⊢ₛ z ≺ z) as Hzz.
      { destruct Hxz as [<-|Hxz], Hzx as [Hzx|Hzx]; [by subst|done|by subst|by eapply sw_lt_trans]. }
      apply (HSR z), amalgam_lt, join_shared; done.
  Qed.

End join.

(** ** Worlds of the relation

    A world is a set of bases and a strict order on the points with
    these bases, which contains program order. It has a kind. A strict
    world ([wstrict]) carries no rank and is an arbitrary strict partial
    order. The deadlock-free relation and the live relation of
    [live_soundness] read strict worlds. A ranked world ([wranked])
    carries a rank function that gives its order. The threads of the
    lock-free development read ranked worlds, because lock freedom needs
    the ranks of a run fixed once chosen ([wchain_lt_wf]).

    Extension keeps the kind and, at a ranked world, every rank. So a
    world and all its extensions have one kind, and the relation, which
    quantifies over extensions only, is the relation of that kind
    (.claude/notes/redesign/check-df-acyclic.md, section 3.2). *)

Record world := World {
  w_roots : gset pname;
  w_ord : point → point → Prop;
  w_ord_trans x y z : pt_root x ∈ w_roots → pt_root y ∈ w_roots → pt_root z ∈ w_roots →
    w_ord x y → w_ord y z → w_ord x z;
  w_ord_irrefl x : pt_root x ∈ w_roots → ¬ w_ord x x;
  w_ord_po x y : pt_root x ∈ w_roots → po x y → w_ord x y;
  w_rk : option (point → rank_ord);
  w_rk_ord ρ x y : w_rk = Some ρ → pt_root x ∈ w_roots → pt_root y ∈ w_roots →
    w_ord x y ↔ olt (ρ x) (ρ y)
}.

(** x is ranked in W: its base is a base of W. *)
Definition rin (W : world) (x : point) : Prop := pt_root x ∈ w_roots W.

Global Instance rin_dec W x : Decision (rin W x).
Proof. unfold rin. apply _. Defined.

Definition wranked (W : world) : Prop := is_Some (w_rk W).
Definition wstrict (W : world) : Prop := w_rk W = None.

Lemma wkind_dec W : {wranked W} + {wstrict W}.
Proof. unfold wranked, wstrict. destruct (w_rk W); [left; eauto|by right]. Defined.

Lemma wranked_strict W : wranked W → wstrict W → False.
Proof. unfold wranked, wstrict. intros [ρ Hρ] H. congruence. Qed.

(** The rank of a point in a ranked world. *)
Definition w_rank (W : world) (x : point) : rank_ord :=
  match w_rk W with Some ρ => ρ x | None => onat 0 end.

Lemma w_ord_rank W x y : wranked W → rin W x → rin W y → w_ord W x y ↔ olt (w_rank W x) (w_rank W y).
Proof.
  intros [ρ Hρ] Hx Hy. unfold w_rank. rewrite Hρ. by apply (w_rk_ord W ρ).
Qed.

Definition w_lt (W : world) (x y : point) : Prop :=
  po x y ∨ (rin W x ∧ rin W y ∧ w_ord W x y).

Notation "W ⊢ x ≺ y" := (w_lt W x y)
  (at level 74, x at level 60, y at level 60, format "W  ⊢  x  ≺  y").

Definition w_le (W : world) (x y : point) : Prop := x = y ∨ W ⊢ x ≺ y.

Lemma rin_po W x y : po x y → rin W x ↔ rin W y.
Proof. intros Hp. apply po_root in Hp as [Hr _]. unfold rin. by rewrite Hr. Qed.

Lemma rank_po W x y : wranked W → rin W x → po x y → olt (w_rank W x) (w_rank W y).
Proof.
  intros HW Hx Hp. apply w_ord_rank; [done|done|by apply (rin_po _ x y)|]. by apply w_ord_po.
Qed.

Lemma w_lt_trans W x y z : W ⊢ x ≺ y → W ⊢ y ≺ z → W ⊢ x ≺ z.
Proof.
  intros [Hxy|(Hx & Hy & Hxy)] [Hyz|(Hy' & Hz & Hyz)].
  - left. by eapply po_trans.
  - assert (rin W x) as Hx by by apply (rin_po _ x y).
    right. split_and!; [done|done|]. apply (w_ord_trans W x y z); [done|done|done| |done]. by apply w_ord_po.
  - assert (rin W z) as Hz by by apply (rin_po _ y z).
    right. split_and!; [done|done|]. apply (w_ord_trans W x y z); [done|done|done|done|]. by apply w_ord_po.
  - right. split_and!; [done|done|]. by apply (w_ord_trans W x y z).
Qed.

Lemma po_lt W x y : po x y → W ⊢ x ≺ y.
Proof. by left. Qed.
Lemma w_lt_po W x : W ⊢ x ≺ x⁺.
Proof. left. apply tc_once. by left. Qed.
Lemma w_lt_dpo W x : W ⊢ x ≺ x‾⁺.
Proof. left. apply tc_once. by right. Qed.

Lemma w_lt_irrefl W x : ¬ W ⊢ x ≺ x.
Proof. intros [H|(Hx & _ & H)]; [by apply po_irrefl in H|by apply (w_ord_irrefl W x Hx)]. Qed.

(** Every ranked world is well-founded. A descending chain that meets a
    ranked point stays ranked and lowers the rank, and one that does not
    is program order and lowers the offset. A strict world need not be. *)
Lemma w_lt_wf W : wranked W → well_founded (w_lt W).
Proof.
  intros HW.
  assert (∀ x, rin W x → Acc (w_lt W) x) as Hin.
  { intros x. remember (w_rank W x) as a eqn:Ha. revert x Ha.
    induction a as [a IH] using oind. intros x -> Hx. constructor.
    intros y [Hy|(Hy & _ & Hyx)].
    - apply (IH (w_rank W y)); [by apply rank_po; [|apply (rin_po _ y x)|]|done|].
      by apply (rin_po _ y x).
    - apply (IH (w_rank W y)); [|done|done]. by apply w_ord_rank. }
  intros x. induction (po_wf x) as [x _ IH]. constructor. intros y [Hy|(Hy & _ & _)].
  - by apply IH.
  - by apply Hin.
Qed.

(** ** Extension *)

Definition wk_ext (W : world) (r r' : option (point → rank_ord)) : Prop :=
  match r, r' with
  | Some ρ, Some ρ' => ∀ x, rin W x → ρ' x = ρ x
  | None, None => True
  | _, _ => False
  end.

Record wext (W W' : world) : Prop := {
  wext_roots : w_roots W ⊆ w_roots W';
  wext_ord x y : rin W x → rin W y → w_ord W x y → w_ord W' x y;
  wext_kind : wk_ext W (w_rk W) (w_rk W')
}.

Notation "W ⊑ W'" := (wext W W') (at level 70).

Lemma wext_refl W : W ⊑ W.
Proof. split; [done|auto|]. unfold wk_ext. by destruct (w_rk W). Qed.

Lemma rin_mono W W' x : W ⊑ W' → rin W x → rin W' x.
Proof. intros HW. unfold rin. apply HW. Qed.

Lemma wext_trans W1 W2 W3 : W1 ⊑ W2 → W2 ⊑ W3 → W1 ⊑ W3.
Proof.
  intros [R12 O12 K12] [R23 O23 K23]. split.
  - by etrans.
  - intros x y Hx Hy H. apply O23; [by apply R12|by apply R12|]. by apply O12.
  - unfold wk_ext in *. destruct (w_rk W1), (w_rk W2), (w_rk W3); try done.
    intros x Hx. rewrite K23; [by apply K12|]. by apply R12.
Qed.

Lemma wext_ranked W W' : W ⊑ W' → wranked W ↔ wranked W'.
Proof.
  intros [_ _ K]. unfold wranked, wk_ext in *. destruct (w_rk W), (w_rk W'); try done.
  all: split; intros [? ?]; discriminate.
Qed.

Lemma wext_strict W W' : W ⊑ W' → wstrict W ↔ wstrict W'.
Proof.
  intros [_ _ K]. unfold wstrict, wk_ext in *. destruct (w_rk W), (w_rk W'); try done.
Qed.

Lemma wext_rank W W' x : W ⊑ W' → wranked W → rin W x → w_rank W' x = w_rank W x.
Proof.
  intros [_ _ K] [ρ Hρ] Hx. unfold w_rank, wk_ext in *. rewrite Hρ in K |- *.
  destruct (w_rk W'); [by apply K|done].
Qed.

Lemma w_lt_mono W W' x y : W ⊑ W' → W ⊢ x ≺ y → W' ⊢ x ≺ y.
Proof.
  intros HW [H|(Hx & Hy & H)]; [by left|right].
  split_and!; [by eapply rin_mono|by eapply rin_mono|]. by apply (wext_ord _ _ HW).
Qed.

Lemma w_le_mono W W' x y : W ⊑ W' → w_le W x y → w_le W' x y.
Proof. intros HW [->|H]; [by left|right; by eapply w_lt_mono]. Qed.

(** ** Worlds that model a static world *)

Definition wmodels (R : world) (W : sworld) : Prop :=
  (∀ a, a ∈ sw_consts W → NConst a ∈ w_roots R) ∧ ∀ x y, sw_facts W (FLt x y) → R ⊢ x ≺ y.

Lemma wmodels_lt R W x y : wmodels R W → W ⊢ₛ x ≺ y → R ⊢ x ≺ y.
Proof.
  intros [_ HR]. induction 1 as [x y Hs|x y z Hs _ IH].
  - destruct Hs as [x y Hf|x|x]; [by apply HR|apply w_lt_po|apply w_lt_dpo].
  - eapply w_lt_trans; [|exact IH].
    destruct Hs as [x y Hf|x|x]; [by apply HR|apply w_lt_po|apply w_lt_dpo].
Qed.

Lemma wmodels_mono R R' W : R ⊑ R' → wmodels R W → wmodels R' W.
Proof.
  intros HR [Hc Hf]. split; [intros a Ha; apply HR; by apply Hc|]. intros x y H. by eapply w_lt_mono, Hf.
Qed.

Lemma wmodels_ext R W W' : W ⊑ₛ W' → wmodels R W' → wmodels R W.
Proof.
  intros HW [Hc Hf]. split; [intros a Ha; apply Hc; by apply HW|]. intros x y H. by apply Hf, (swext_facts _ _ HW).
Qed.

(** ** Ranked worlds

    [wranked_of B ρ] has the bases B and orders them by the ranks ρ,
    which rise along program order. *)

Definition ranks_po (B : gset pname) (ρ : point → rank_ord) : Prop :=
  ∀ x, pt_root x ∈ B → olt (ρ x) (ρ x⁺) ∧ olt (ρ x) (ρ x‾⁺).

Lemma ranks_po_lt B ρ x y : ranks_po B ρ → pt_root x ∈ B → po x y → olt (ρ x) (ρ y).
Proof.
  intros Hρ Hx Hp. induction Hp as [x y Hxy|x y z Hxy Hp IH].
  - destruct Hxy as [->| ->]; apply (Hρ x Hx).
  - assert (olt (ρ x) (ρ y)) as H1 by (destruct Hxy as [->| ->]; apply (Hρ x Hx)).
    eapply olt_trans; [exact H1|]. apply IH. destruct Hxy as [->| ->]; exact Hx.
Qed.

Definition wranked_of (B : gset pname) (ρ : point → rank_ord) (Hρ : ranks_po B ρ) : world.
Proof.
  refine (World B (λ x y, olt (ρ x) (ρ y)) _ _ _ (Some ρ) _).
  - intros x y z _ _ _. apply olt_trans.
  - intros x _. apply olt_irrefl.
  - intros x y Hx Hp. by apply (ranks_po_lt B).
  - intros ρ' x y [= <-] _ _. reflexivity.
Defined.

Lemma wranked_of_ranked B ρ Hρ : wranked (wranked_of B ρ Hρ).
Proof. by eexists. Qed.

Lemma wranked_of_rank B ρ Hρ x : w_rank (wranked_of B ρ Hρ) x = ρ x.
Proof. done. Qed.

(** A rank function of a static world gives a ranked world that models it. *)
Definition wrank (W : sworld) (ρ : point → rank_ord) (Hρ : ranked (sw_lt W) ρ) : world.
Proof.
  refine (wranked_of (set_map NConst (sw_consts W)) ρ _).
  intros x _. split; apply Hρ; [apply sw_lt_po|apply sw_lt_dpo].
Defined.

Lemma wrank_models W ρ Hρ : sworld_wf W → wmodels (wrank W ρ Hρ) W.
Proof.
  intros Hwf. split; [intros a Ha; simpl; set_solver|]. intros x y Hf. right.
  destruct (wf_facts _ Hwf x y Hf) as [(a & Ha & Ha') (b & Hb & Hb')].
  split_and!; [unfold rin; simpl; rewrite Ha; set_solver|unfold rin; simpl; rewrite Hb; set_solver|].
  apply Hρ, sw_lt_fact, Hf.
Qed.

(** A well-founded static world has a ranked model. *)
Lemma wmodels_exists W : sworld_wf W → swf W → ∃ R, wranked R ∧ wmodels R W.
Proof.
  intros Hwf [ρ Hρ]. exists (wrank W ρ Hρ). split; [apply wranked_of_ranked|by apply wrank_models].
Qed.

(** ** Strict worlds

    An acyclic static world is a strict world itself: its constants are
    the bases and its order is the order. No rank is needed. *)

Definition wstrict_of (W : sworld) (Hac : sacyc W) : world.
Proof.
  refine (World (set_map NConst (sw_consts W)) (sw_lt W) _ _ _ None _).
  - intros x y z _ _ _. apply sw_lt_trans.
  - intros x _. apply Hac.
  - intros x y _. apply po_slt.
  - intros ρ x y [=].
Defined.

Lemma wstrict_of_strict W Hac : wstrict (wstrict_of W Hac).
Proof. done. Qed.

Lemma wstrict_of_models W Hac : sworld_wf W → wmodels (wstrict_of W Hac) W.
Proof.
  intros Hwf. split; [intros a Ha; simpl; set_solver|]. intros x y Hf. right.
  destruct (wf_facts _ Hwf x y Hf) as [(a & Ha & Ha') (b & Hb & Hb')].
  split_and!; [unfold rin; simpl; rewrite Ha; set_solver|unfold rin; simpl; rewrite Hb; set_solver|].
  apply sw_lt_fact, Hf.
Qed.

(** An acyclic static world has a strict model, constructively. *)
Lemma dmodels_exists W : sworld_wf W → sacyc W → ∃ R, wstrict R ∧ wmodels R W.
Proof. intros Hwf Hac. exists (wstrict_of W Hac). split; [done|by apply wstrict_of_models]. Qed.

(** ** Growing a ranked world by bases

    [wgrow W B ρ] ranks the points of the bases in B that W does not rank
    by ρ, and keeps every rank of W. The lock-free creation grows the
    world this way. *)

Definition wgrow_rank (W : world) (ρ : point → rank_ord) (x : point) : rank_ord :=
  if decide (rin W x) then w_rank W x else ρ x.

Definition wgrow (W : world) (HW : wranked W) (B : gset pname) (ρ : point → rank_ord) (Hρ : ranks_po B ρ) : world.
Proof.
  refine (wranked_of (B ∪ w_roots W) (wgrow_rank W ρ) _).
  intros x Hx. unfold wgrow_rank.
  assert (rin W x ↔ rin W x⁺) as E1 by (unfold rin, pt_root; done).
  assert (rin W x ↔ rin W x‾⁺) as E2 by (unfold rin, pt_root; done).
  destruct (decide (rin W x)) as [Ha|Ha].
  - rewrite !decide_True by tauto. split; apply rank_po; try done; apply tc_once; [by left|by right].
  - rewrite !decide_False by tauto. apply Hρ. apply elem_of_union in Hx as [?|?]; [done|by destruct Ha].
Defined.

Lemma wgrow_ext W HW B ρ Hρ : W ⊑ wgrow W HW B ρ Hρ.
Proof.
  split; [simpl; set_solver| |].
  - intros x y Hx Hy H. simpl. unfold wgrow_rank. rewrite !decide_True by done. by apply w_ord_rank.
  - unfold wk_ext. change (w_rk (wgrow W HW B ρ Hρ)) with (Some (wgrow_rank W ρ)).
    destruct HW as [ρW HρW]. rewrite HρW. intros x Hx. unfold wgrow_rank.
    rewrite decide_True by done. unfold w_rank. by rewrite HρW.
Qed.

Lemma wgrow_rank_new W HW B ρ Hρ x : ¬ rin W x → w_rank (wgrow W HW B ρ Hρ) x = ρ x.
Proof. intros H. change (w_rank (wgrow W HW B ρ Hρ) x) with (wgrow_rank W ρ x). unfold wgrow_rank. by rewrite decide_False. Qed.

Lemma wgrow_rin W HW B ρ Hρ x : pt_root x ∈ B → rin (wgrow W HW B ρ Hρ) x.
Proof. intros H. unfold rin. simpl. set_solver. Qed.

Lemma wgrow_ranked W HW B ρ Hρ : wranked (wgrow W HW B ρ Hρ).
Proof. apply wranked_of_ranked. Qed.

(** ** A chain of ranked worlds

    The worlds of a run only grow. The order of a chain of ranked
    worlds, x ≺ y in some world of it, is well-founded: every rank stays
    fixed once chosen. *)
Section chain.
  Context (Wc : nat → world) (Hc : ∀ k, Wc k ⊑ Wc (S k)) (H0 : wranked (Wc 0)).

  Lemma wchain_le k j : k ≤ j → Wc k ⊑ Wc j.
  Proof.
    induction 1 as [|j _ IH]; [apply wext_refl|]. eapply wext_trans; [exact IH|apply Hc].
  Qed.

  Lemma wchain_ranked k : wranked (Wc k).
  Proof. apply (wext_ranked (Wc 0)); [apply wchain_le; lia|done]. Qed.

  Definition wchain_lt (x y : point) : Prop := ∃ k, Wc k ⊢ x ≺ y.

  Lemma wchain_lt_wf : well_founded wchain_lt.
  Proof.
    assert (∀ a k x, rin (Wc k) x → w_rank (Wc k) x = a → Acc wchain_lt x) as Hin.
    { intros a. induction a as [a IH] using oind. intros k x Hx <-. constructor.
      intros y [j Hy]. set (m := k `max` j).
      assert (Wc k ⊑ Wc m) as Hk by (apply wchain_le; lia).
      assert (Wc j ⊑ Wc m) as Hj by (apply wchain_le; lia).
      pose proof (w_lt_mono _ _ _ _ Hj Hy) as Hym.
      assert (rin (Wc m) x) as Hxm by exact (rin_mono _ _ _ Hk Hx).
      destruct Hym as [Hp|(Hy' & _ & Hlt)].
      - assert (rin (Wc m) y) as Hym by exact (proj2 (rin_po _ y x Hp) Hxm).
        apply (IH (w_rank (Wc m) y) ltac:(rewrite <-(wext_rank _ _ x Hk (wchain_ranked k) Hx);
                                          by apply rank_po; [apply wchain_ranked| |]) m y Hym eq_refl).
      - apply (w_ord_rank _ _ _ (wchain_ranked m) Hy' Hxm) in Hlt.
        apply (IH (w_rank (Wc m) y) ltac:(by rewrite <-(wext_rank _ _ x Hk (wchain_ranked k) Hx)) m y Hy' eq_refl). }
    intros x. induction (po_wf x) as [x _ IH]. constructor. intros y [j [Hy|(Hy & _ & _)]].
    - by apply IH.
    - by apply (Hin _ j y Hy eq_refl).
  Qed.
End chain.

Lemma swf_irrefl W x : swf W → ¬ W ⊢ₛ x ≺ x.
Proof. intros HW. by apply swf_sacyc. Qed.
