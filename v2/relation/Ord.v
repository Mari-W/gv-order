(** * Brouwer-tree ordinals and the transfinite fixpoint (stage 2, groundwork)

    [ord@{u}] is the type of Brouwer trees whose limits range over
    families indexed by a type of universe u. The type is universe
    polymorphic and cumulative, so it is used at two levels, the level
    of the step index and a level above the space of creation choices
    (docs/redesign/check-transfinite.md, section 1).

    - [ole] and [olt] are the order of Brouwer trees, defined by
      structural recursion, so no proof inverts a limit and no
      dependent-equality axiom enters.
    - [olt_wf]: the strict order is well-founded.
    - [oadd β c] is the c-fold successor β + c. [oadd_lt]: a step of
      positive cost c with β + c ≤ α leaves β strictly below α.
    - [osfix F] is the family defined by well-founded recursion on the
      index, where [F below α] reads [below] only strictly below α.
      [osfix_unfold] is the unfolding up to pointwise ↔, so no proof
      needs functional extensionality.

    The relation and fuel still use the natural-number fixpoint of
    relation/Sfix.v. The port is open (docs/redesign/pending.md). *)

From stdpp Require Import base tactics.

#[local] Set Universe Polymorphism.

#[universes(polymorphic, cumulative)]
Inductive ord@{u} : Type@{u+1} :=
  | ozero : ord
  | osucc : ord → ord
  | olim (X : Type@{u}) : (X → ord) → ord.

Arguments olim {_} _.

Section order.

  (** a ≤ b by recursion on a. At a successor the inner recursion on b
      states a < b: below a successor b′ it is a ≤ b′, below a limit it
      is a < f x for some x. *)
  Fixpoint ole (a : ord) : ord → Prop :=
    match a with
    | ozero => λ _, True
    | osucc a' =>
        fix lt (b : ord) : Prop :=
          match b with
          | ozero => False
          | osucc b' => ole a' b'
          | olim g => ∃ x, lt (g x)
          end
    | olim f => λ b, ∀ x, ole (f x) b
    end.

  Definition olt (a b : ord) : Prop := ole (osucc a) b.

  Lemma ole_succ_succ a b : ole (osucc a) (osucc b) ↔ ole a b.
  Proof. done. Qed.

  Lemma ole_succ_lim a {X} (g : X → ord) : ole (osucc a) (olim g) ↔ ∃ x, ole (osucc a) (g x).
  Proof. done. Qed.

  Lemma ole_lim_l {X} (f : X → ord) b : ole (olim f) b ↔ ∀ x, ole (f x) b.
  Proof. done. Qed.

  Lemma ole_succ_zero a : ¬ ole (osucc a) ozero.
  Proof. intros H. exact H. Qed.

  (** a ≤ b implies a ≤ b + 1, and a ≤ g x implies a ≤ lim g. *)
  Lemma ole_lim_r a {X} (g : X → ord) x : ole a (g x) → ole a (olim g).
  Proof.
    revert x. induction a as [|a IH|Y f IH]; intros x H; [done| |].
    - exists x. exact H.
    - intros y. apply (IH y x). apply H.
  Qed.

  Lemma ole_succ_r a : ∀ b, ole a b → ole a (osucc b).
  Proof.
    induction a as [|a IH|X f IH]; intros b H; [done| |].
    - simpl. induction b as [|b IHb|Y g IHb]; [done| |].
      + apply IH. exact H.
      + destruct H as [y Hy]. specialize (IHb y Hy). exact (ole_lim_r a g y IHb).
    - intros x. apply IH. apply H.
  Qed.


  Lemma ole_refl a : ole a a.
  Proof.
    induction a as [|a IH|X f IH]; [done|exact IH|].
    intros x. apply (ole_lim_r _ f x). apply IH.
  Qed.

  (** a + 1 ≤ b implies a ≤ b. *)
  Lemma ole_succ_l a : ∀ b, ole (osucc a) b → ole a b.
  Proof.
    induction b as [|b IH|X g IH]; intros H; [done| |].
    - by apply ole_succ_r.
    - destruct H as [x Hx]. apply (ole_lim_r _ g x). by apply IH.
  Qed.

  Lemma ole_trans a : ∀ b c, ole a b → ole b c → ole a c.
  Proof.
    induction a as [|a IH|X f IH]; intros b c Hab Hbc; [done| |].
    - revert c Hbc. induction b as [|b IHb|Y g IHb]; intros c Hbc; [done| |].
      + induction c as [|c IHc|Z h IHc]; [done| |].
        * exact (IH _ _ Hab Hbc).
        * destruct Hbc as [z Hz]. exists z. by apply IHc.
      + destruct Hab as [y Hy]. apply (IHb y Hy). apply Hbc.
    - intros x. apply (IH x b c); [apply Hab|exact Hbc].
  Qed.

  Lemma olt_ole a b : olt a b → ole a b.
  Proof. apply ole_succ_l. Qed.

  Lemma olt_trans_le a b c : olt a b → ole b c → olt a c.
  Proof. apply ole_trans. Qed.

  Lemma ole_trans_lt a b c : ole a b → olt b c → olt a c.
  Proof. intros H1 H2. apply (ole_trans _ (osucc b)); [exact H1|exact H2]. Qed.

  Lemma olt_succ a : olt a (osucc a).
  Proof. apply ole_refl. Qed.

  Lemma olt_lim {X} (g : X → ord) x : ole (g x) (olim g).
  Proof. apply (ole_lim_r _ g x), ole_refl. Qed.

  (** The strict order is well-founded. *)
  Lemma olt_acc_below b : ∀ a, olt a b → Acc olt a.
  Proof.
    induction b as [|b IH|X g IH]; intros a H; [done| |].
    - constructor. intros a' Ha'. apply IH. exact (olt_trans_le _ _ _ Ha' H).
    - destruct H as [x Hx]. exact (IH x a Hx).
  Qed.

  Lemma olt_wf : well_founded olt.
  Proof. intros a. apply (olt_acc_below (osucc a)), olt_succ. Qed.

  Lemma olt_irrefl a : ¬ olt a a.
  Proof.
    intros H. induction (olt_wf a) as [a _ IH]. exact (IH a H H).
  Qed.

  (** β + c, the c-fold successor. *)
  Fixpoint oadd (b : ord) (c : nat) : ord :=
    match c with 0 => b | S c' => osucc (oadd b c') end.

  Lemma ole_oadd b c : ole b (oadd b c).
  Proof. induction c as [|c IH]; simpl; [apply ole_refl|by apply ole_succ_r]. Qed.

  (** A step of positive cost c with β + c ≤ α leaves β below α. *)
  Lemma oadd_lt b c a : c ≠ 0 → ole (oadd b c) a → olt b a.
  Proof.
    destruct c as [|c]; [done|]. intros _ H. simpl in H.
    apply (ole_trans_lt _ (oadd b c)); [apply ole_oadd|exact H].
  Qed.
End order.

(** ** The transfinite fixpoint *)

(** Dependent elimination of accessibility into Prop. *)
Scheme Acc_ind_dep := Induction for Acc Sort Prop.

Section osfix.
  Context {T : Type} (F : (ord → T → Prop) → ord → T → Prop).

  (** [F below α] reads [below] only strictly below α, up to ↔. *)
  Context (F_ext : ∀ α (R R' : ord → T → Prop),
    (∀ β, olt β α → ∀ t, R β t ↔ R' β t) → ∀ t, F R α t ↔ F R' α t).

  Definition osfix_step (α : ord) (rec : ∀ β, olt β α → T → Prop) : T → Prop :=
    F (λ β t, ∃ H : olt β α, rec β H t) α.

  Definition osfix (α : ord) : T → Prop :=
    Fix olt_wf (λ _, T → Prop) osfix_step α.

  Lemma osfix_F_irr α (a1 : Acc olt α) : ∀ (a2 : Acc olt α) t,
    Fix_F (λ _, T → Prop) osfix_step a1 t ↔ Fix_F (λ _, T → Prop) osfix_step a2 t.
  Proof.
    induction a1 as [α h1 IH] using Acc_ind_dep. intros [h2] t. simpl.
    apply F_ext. intros β Hβ t'. split.
    - intros [H Hf]. exists Hβ. apply (IH β H (h2 β Hβ) t'). exact Hf.
    - intros [H Hf]. exists Hβ. apply (IH β Hβ (h2 β H) t'). exact Hf.
  Qed.

  Lemma osfix_unfold α t : osfix α t ↔ F osfix α t.
  Proof.
    unfold osfix at 1, Fix. destruct (olt_wf α) as [h]. simpl.
    apply F_ext. intros β Hβ t'. unfold osfix, Fix. split.
    - intros [H Hf]. by apply (osfix_F_irr β (h β H)).
    - intros Hf. exists Hβ. by apply (osfix_F_irr β (olt_wf β)).
  Qed.
End osfix.
