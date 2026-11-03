(** * Creation constraints: closure, transfer and the world of new
    (static-system.md §5, sharp edges 105)

    [cc_ok] (types/Types.v) asks that Γ + C be acyclic and conservative
    over Γ. This file proves the three things the rest of the
    development needs from it.

    - [interp]: let a theory K over the points of the body contain the
      facts of C, agree with a theory T on the outer points through a
      map g, and have no cycle that T lacks. Then T plus the image of C
      adds nothing between outer points and no cycle. The proof is a
      closed form [V] of the order of T + C, in which a path visits the
      points of the fresh name at most twice.
    - [cc_ok_transfer]: [cc_ok] moves along a map of the generators, so
      it survives world extension, renaming and substitution of the
      outer points (an instance of [interp]).
    - [wext_cc]: in a strict world W, [cc_ok] gives the fresh extension
      W ⊑ₒ W′ by the facts of C at a fresh name a (an instance of
      [interp] with T = W).

    [cc_model] proves [cc_ok] for a concrete C from a model, a closed
    form of Γ + C built from a map φ that identifies points of ι with
    outer points, an order R inside ι and the facts Lo, Hi that enter
    and leave ι. The special cases of static/ and the examples use it. *)

From stdpp Require Import base gmap relations.
From LRGV Require Export relation.Worlds.

Set Default Proof Using "All".

(** ** Theories *)

Record theory (E L : prel) : Prop := {
  th_refl x : E x x;
  th_sym x y : E x y → E y x;
  th_trans x y z : E x y → E y z → E x z;
  th_shift x y : E x y → E (pt_shift 1 x) (pt_shift 1 y);
  th_slot x y i : E x y → E (pt_slot x i) (pt_slot y i);
  th_lt_trans x y z : L x y → L y z → L x z;
  th_lt_eq x x' y y' : E x x' → L x' y' → E y' y → L x y;
  th_po x : L x (pt_shift 1 x)
}.

Lemma theory_gen E L : theory (geq E) (glt E L).
Proof. split; eauto using geq, glt. Qed.

Lemma theory_world W : world_wf W → theory (w_eq W) (w_lt W).
Proof.
  intros HW. split.
  - apply (wf_eq_refl _ HW).
  - apply (wf_eq_sym _ HW).
  - apply (wf_eq_trans _ HW).
  - apply (wf_eq_shift _ HW).
  - apply (wf_eq_slot _ HW).
  - apply (wf_lt_trans _ HW).
  - apply (wf_lt_eq _ HW).
  - apply (wf_lt_po _ HW).
Qed.

(** Same name, strictly later offset: program order. *)
Definition pofs (x y : point) : Prop := pt_name x = pt_name y ∧ pt_off x < pt_off y.

Lemma pofs_trans x y z : pofs x y → pofs y z → pofs x z.
Proof. unfold pofs. intros [??] [??]. split; [congruence|lia]. Qed.

Lemma pofs_irrefl x : ¬ pofs x x.
Proof. unfold pofs. lia. Qed.

Lemma pofs_shift x : pofs x (pt_shift 1 x).
Proof. unfold pofs, pt_shift. simpl. split; [done|lia]. Qed.

Lemma pofs_root x y : pofs x y → pt_root x = pt_root y.
Proof. unfold pofs, pt_root. intros [-> _]. done. Qed.

Lemma pt_shift_S k x : pt_shift 1 (pt_shift k x) = pt_shift (S k) x.
Proof. unfold pt_shift. simpl. f_equal. lia. Qed.

Lemma pofs_is_shift x y : pofs x y → ∃ k, y = pt_shift (S k) x.
Proof.
  destruct x as [p o], y as [q o']. unfold pofs, pt_shift. simpl. intros [-> Ho].
  exists (o' - o - 1). f_equal. lia.
Qed.

Lemma th_po_n E L k x : theory E L → L x (pt_shift (S k) x).
Proof.
  intros HT. induction k as [|k IH].
  - replace (pt_shift 1 x) with (pt_shift 1 x) by done. apply (th_po _ _ HT).
  - rewrite <-pt_shift_S. eapply (th_lt_trans _ _ HT); [exact IH|apply (th_po _ _ HT)].
Qed.

Lemma th_pofs E L x y : theory E L → pofs x y → L x y.
Proof. intros HT H. destruct (pofs_is_shift x y H) as [k ->]. by apply (th_po_n E L). Qed.

Lemma map_shift_n (f : point → point) :
  (∀ x, f (pt_shift 1 x) = pt_shift 1 (f x)) → ∀ k x, f (pt_shift k x) = pt_shift k (f x).
Proof.
  intros Hs k. assert (∀ y, pt_shift 0 y = y) as H0.
  { intros [p o]. unfold pt_shift. simpl. f_equal. lia. }
  induction k as [|k IH]; intros x.
  - by rewrite !H0.
  - rewrite <-(pt_shift_S k x), <-(pt_shift_S k (f x)). by rewrite Hs, IH.
Qed.

(** A map that commutes with successor and carried roots carries the closure of
    generators into every theory that holds their images. *)
Lemma gen_map E L E' L' (f : point → point) :
  theory E' L' →
  (∀ x, f (pt_shift 1 x) = pt_shift 1 (f x)) →
  (∀ x i, f (pt_slot x i) = pt_slot (f x) i) →
  (∀ x y, E x y → E' (f x) (f y)) → (∀ x y, L x y → L' (f x) (f y)) →
  (∀ x y, geq E x y → E' (f x) (f y)) ∧ (∀ x y, glt E L x y → L' (f x) (f y)).
Proof.
  intros HT Hs Hl HE HL.
  assert (∀ x y, geq E x y → E' (f x) (f y)) as Hq.
  { induction 1 as [x y H|x|x y _ IH|x y z _ IH1 _ IH2|x y _ IH|x y i _ IH].
    - auto.
    - apply (th_refl _ _ HT).
    - by apply (th_sym _ _ HT).
    - by eapply (th_trans _ _ HT).
    - rewrite !Hs. by apply (th_shift _ _ HT).
    - rewrite !Hl. by apply (th_slot _ _ HT). }
  split; [done|].
  induction 1 as [x y H|x|x x' y y' Hx _ IH Hy|x y z _ IH1 _ IH2].
  - auto.
  - rewrite Hs. apply (th_po _ _ HT).
  - eapply (th_lt_eq _ _ HT); [by apply Hq|exact IH|by apply Hq].
  - by eapply (th_lt_trans _ _ HT).
Qed.

Lemma gen_mono E L E' L' :
  (∀ x y, E x y → E' x y) → (∀ x y, L x y → L' x y) →
  (∀ x y, geq E x y → geq E' x y) ∧ (∀ x y, glt E L x y → glt E' L' x y).
Proof.
  intros HE HL.
  destruct (gen_map E L (geq E') (glt E' L') id (theory_gen E' L')) as [H1 H2];
    [done|done|intros; apply geq_base; auto|intros; apply glt_base; auto|].
  split; intros x y H; [exact (H1 _ _ H)|exact (H2 _ _ H)].
Qed.

(** Generators that avoid the root rn leave its points unrelated, except
    by reflexivity and program order. *)
Lemma gen_triv (rn : pname) E L :
  (∀ x y, E x y → pt_root x ≠ rn ∧ pt_root y ≠ rn) →
  (∀ x y, L x y → pt_root x ≠ rn ∧ pt_root y ≠ rn) →
  (∀ x y, geq E x y → x = y ∨ (pt_root x ≠ rn ∧ pt_root y ≠ rn)) ∧
  (∀ x y, glt E L x y → pofs x y ∨ (pt_root x ≠ rn ∧ pt_root y ≠ rn)).
Proof.
  intros HE HL.
  assert (∀ x y, geq E x y → x = y ∨ (pt_root x ≠ rn ∧ pt_root y ≠ rn)) as Hq.
  { induction 1 as [x y H|x|x y _ IH|x y z _ IH1 _ IH2|x y _ IH|x y i _ IH].
    - right. auto.
    - by left.
    - naive_solver.
    - destruct IH1 as [->|[??]], IH2 as [->|[??]]; [by left|right..]; done.
    - destruct IH as [->|[??]]; [by left|right; done].
    - destruct IH as [->|[??]]; [by left|right; done]. }
  split; [done|].
  induction 1 as [x y H|x|x x' y y' Hx _ IH Hy|x y z _ IH1 _ IH2].
  - right. auto.
  - left. apply pofs_shift.
  - apply Hq in Hx, Hy. unfold pofs, pt_root in *.
    destruct Hx as [->|[??]], Hy as [<-|[??]], IH as [[??]|[??]];
      first [left; split; [congruence|lia]|right; split; congruence].
  - unfold pofs, pt_root in *.
    destruct IH1 as [[??]|[??]], IH2 as [[??]|[??]];
      first [left; split; [congruence|lia]|right; split; congruence].
Qed.

(** The relation of a flag: ≡ at [false], ≺ at [true]. *)
Definition rb (E L : prel) (b : bool) : prel := if b then L else E.

Lemma rb_trans E L b1 b2 x y z :
  theory E L → rb E L b1 x y → rb E L b2 y z → rb E L (b1 || b2) x z.
Proof.
  intros HT. destruct b1, b2; simpl; intros H1 H2.
  - by eapply (th_lt_trans _ _ HT).
  - eapply (th_lt_eq _ _ HT); [apply (th_refl _ _ HT)|exact H1|exact H2].
  - eapply (th_lt_eq _ _ HT); [exact H1|exact H2|apply (th_refl _ _ HT)].
  - by eapply (th_trans _ _ HT).
Qed.

Ltac bools := repeat match goal with b : bool |- _ => destruct b end; simpl in *; try done.

(** ** The closed form of T + C *)

Section interp.
  Context (E L : prel) (HT : theory E L) (rt : pname).
  Context (HEn : ∀ x y, E x y → pt_root x = rt ∨ pt_root y = rt → x = y).
  Context (HLn : ∀ x y, L x y → pt_root x = rt ∨ pt_root y = rt → pofs x y).
  Context (KE KL : prel) (HK : theory KE KL).
  Context (g : point → point).
  Context (Hgs : ∀ x, g (pt_shift 1 x) = pt_shift 1 (g x)).
  Context (Hgl : ∀ x i, g (pt_slot x i) = pt_slot (g x) i).
  Context (Hg1 : ∀ p, pt_root p = NVar 0 → pt_root (g p) = rt).
  Context (Hg2 : ∀ x, pt_root x ≠ NVar 0 → pt_root (g x) ≠ rt).
  Context (Hg3 : ∀ p q, pt_root p = NVar 0 → pt_root q = NVar 0 → g p = g q → p = q).
  Context (Hg4 : ∀ y, pt_root y = rt → ∃ p, pt_root p = NVar 0 ∧ g p = y).
  Context (HKe : ∀ x y, pt_root x ≠ NVar 0 → pt_root y ≠ NVar 0 → KE x y → E (g x) (g y)).
  Context (HKl : ∀ x y, pt_root x ≠ NVar 0 → pt_root y ≠ NVar 0 → KL x y → L (g x) (g y)).
  Context (HKc : ∀ p, KL p p → ∃ y, L y y).
  Context (De Dl : prel).
  Context (HDe : ∀ x y, De x y → ∃ x0 y0, KE x0 y0 ∧ x = g x0 ∧ y = g y0).
  Context (HDl : ∀ x y, Dl x y → ∃ x0 y0, KL x0 y0 ∧ x = g x0 ∧ y = g y0).

  Local Notation Nt x := (pt_root x = rt).
  Local Notation Ns x := (pt_root x = NVar 0).
  Local Notation TR := (rb E L).
  Local Notation KR := (rb KE KL).

  Local Lemma HKr b x y : ¬ Ns x → ¬ Ns y → KR b x y → TR b (g x) (g y).
  Proof. destruct b; simpl; auto. Qed.

  Definition V (b : bool) (x y : point) : Prop :=
    (¬ Nt x ∧ ¬ Nt y ∧ TR b x y)
    ∨ (∃ p w b1 b2, Ns p ∧ x = g p ∧ ¬ Ns w ∧ ¬ Nt y ∧ KR b1 p w ∧ TR b2 (g w) y ∧ b = b1 || b2)
    ∨ (∃ q w b1 b2, Ns q ∧ y = g q ∧ ¬ Ns w ∧ ¬ Nt x ∧ TR b1 x (g w) ∧ KR b2 w q ∧ b = b1 || b2)
    ∨ (∃ p q, Ns p ∧ Ns q ∧ x = g p ∧ y = g q ∧
         (KR b p q ∨ ∃ w w' b1 b2 b3, ¬ Ns w ∧ ¬ Ns w' ∧ KR b1 p w ∧ TR b2 (g w) (g w') ∧
                                      KR b3 w' q ∧ b = b1 || b2 || b3)).

  Local Lemma rbT b1 b2 x y z : TR b1 x y → TR b2 y z → TR (b1 || b2) x z.
  Proof. by apply rb_trans. Qed.
  Local Lemma rbK b1 b2 x y z : KR b1 x y → KR b2 y z → KR (b1 || b2) x z.
  Proof. by apply rb_trans. Qed.

  Local Lemma rb_eq {A B : prel} b b' x y : b = b' → rb A B b x y → rb A B b' x y.
  Proof. by intros ->. Qed.

  Lemma V_trans b1 b2 x y z : V b1 x y → V b2 y z → V (b1 || b2) x z.
  Proof.
    intros [H1|[H1|[H1|H1]]] [H2|[H2|[H2|H2]]].
    - destruct H1 as (Hx & Hy & H1), H2 as (_ & Hz & H2). left. split_and!; [done|done|by eapply rbT].
    - exfalso. destruct H1 as (_ & Hy & _), H2 as (p & w & c1 & c2 & Hp & -> & _). by apply Hy, Hg1.
    - destruct H1 as (Hx & Hy & H1), H2 as (q & w & c1 & c2 & Hq & -> & Hw & _ & H2 & H3 & ->).
      right; right; left. exists q, w, (b1 || c1), c2. split_and!; try done; [by eapply rbT|by bools].
    - exfalso. destruct H1 as (_ & Hy & _), H2 as (p & q & Hp & _ & -> & _). by apply Hy, Hg1.
    - destruct H1 as (p & w & c1 & c2 & Hp & -> & Hw & Hy & H1 & H3 & ->), H2 as (_ & Hz & H2).
      right; left. exists p, w, c1, (c2 || b2). split_and!; try done; [by eapply rbT|by bools].
    - exfalso. destruct H1 as (p & w & c1 & c2 & _ & _ & _ & Hy & _), H2 as (p' & w' & d1 & d2 & Hp & -> & _).
      by apply Hy, Hg1.
    - destruct H1 as (p & w & c1 & c2 & Hp & -> & Hw & Hy & H1 & H3 & ->),
               H2 as (q & w' & d1 & d2 & Hq & -> & Hw' & _ & H4 & H5 & ->).
      right; right; right. exists p, q. split_and!; try done. right.
      exists w, w', c1, (c2 || d1), d2. split_and!; try done; [by eapply rbT|by bools].
    - exfalso. destruct H1 as (p & w & c1 & c2 & _ & _ & _ & Hy & _), H2 as (p' & q & Hp & _ & -> & _).
      by apply Hy, Hg1.
    - exfalso. destruct H1 as (q & w & c1 & c2 & Hq & -> & _), H2 as (Hy & _ & _). by apply Hy, Hg1.
    - destruct H1 as (q & w & c1 & c2 & Hq & -> & Hw & Hx & H1 & H3 & ->),
               H2 as (p & w' & d1 & d2 & Hp & Ep & Hw' & Hz & H4 & H5 & ->).
      apply Hg3 in Ep as <-; [|done|done].
      left. split_and!; [done|done|].
      eapply rb_eq; [|eapply rbT; [exact H1|eapply rbT; [(apply HKr; [done| |eapply rbK; [exact H3|exact H4]]; done)|exact H5]]].
      by bools.
    - exfalso. destruct H1 as (q & w & c1 & c2 & Hq & -> & _), H2 as (q' & w' & d1 & d2 & _ & _ & _ & Hy & _).
      by apply Hy, Hg1.
    - destruct H1 as (q & w & c1 & c2 & Hq & -> & Hw & Hx & H1 & H3 & ->),
               H2 as (p & q' & Hp & Hq' & Ep & -> & [H4|(w1 & w1' & d1 & d2 & d3 & Hw1 & Hw1' & H4 & H5 & H6 & ->)]);
        apply Hg3 in Ep as <-; try done.
      + right; right; left. exists q', w, c1, (c2 || b2). split_and!; try done; [by eapply rbK|by bools].
      + right; right; left. exists q', w1', (c1 || ((c2 || d1) || d2)), d3. split_and!; try done; [|by bools].
        eapply rbT; [exact H1|]. eapply rbT; [(apply HKr; [done| |eapply rbK; [exact H3|exact H4]]; done)|exact H5].
    - exfalso. destruct H1 as (p & q & _ & Hq & _ & -> & _), H2 as (Hy & _ & _). by apply Hy, Hg1.
    - destruct H1 as (p & q & Hp & Hq & -> & -> & [H1|(w1 & w1' & c1 & c2 & c3 & Hw1 & Hw1' & H1 & H3 & H4 & ->)]),
               H2 as (q' & w & d1 & d2 & Hq' & Ep & Hw & Hz & H5 & H6 & ->);
        apply Hg3 in Ep as <-; try done.
      + right; left. exists p, w, (b1 || d1), d2. split_and!; try done; [by eapply rbK|by bools].
      + right; left. exists p, w1, c1, (c2 || ((c3 || d1) || d2)). split_and!; try done; [|by bools].
        eapply rbT; [exact H3|]. eapply rbT; [(apply HKr; [done| |eapply rbK; [exact H4|exact H5]]; done)|exact H6].
    - exfalso. destruct H1 as (p & q & _ & Hq & _ & -> & _), H2 as (q' & w & d1 & d2 & _ & _ & _ & Hy & _).
      by apply Hy, Hg1.
    - destruct H1 as (p & q & Hp & Hq & -> & -> & H1), H2 as (p' & q' & Hp' & Hq' & Ep & -> & H2).
      apply Hg3 in Ep as <-; [|done|done].
      right; right; right. exists p, q'. split_and!; try done.
      destruct H1 as [H1|(w1 & w1' & c1 & c2 & c3 & Hw1 & Hw1' & H1 & H3 & H4 & ->)],
               H2 as [H2|(w2 & w2' & d1 & d2 & d3 & Hw2 & Hw2' & H2 & H5 & H6 & ->)].
      + left. by eapply rbK.
      + right. exists w2, w2', (b1 || d1), d2, d3. split_and!; try done; [by eapply rbK|by bools].
      + right. exists w1, w1', c1, c2, (c3 || b2). split_and!; try done; [by eapply rbK|by bools].
      + right. exists w1, w2', c1, (c2 || ((c3 || d1) || d2)), d3. split_and!; try done; [|by bools].
        eapply rbT; [exact H3|]. eapply rbT; [(apply HKr; [done| |eapply rbK; [exact H4|exact H2]]; done)|exact H5].
  Qed.

  Lemma V_refl x : V false x x.
  Proof.
    destruct (decide (Nt x)) as [Hx|Hx].
    - destruct (Hg4 x Hx) as (p & Hp & <-). right; right; right. exists p, p. split_and!; try done.
      left. apply (th_refl _ _ HK).
    - left. split_and!; [done|done|apply (th_refl _ _ HT)].
  Qed.

  Lemma V_sym x y : V false x y → V false y x.
  Proof.
    intros [(Hx & Hy & H)|[(p & w & b1 & b2 & Hp & -> & Hw & Hy & H1 & H2 & Hb)
           |[(q & w & b1 & b2 & Hq & -> & Hw & Hx & H1 & H2 & Hb)|(p & q & Hp & Hq & -> & -> & H)]]].
    - left. split_and!; [done|done|by apply (th_sym _ _ HT)].
    - destruct b1, b2; try done. right; right; left. exists p, w, false, false.
      split_and!; try done; simpl in *; [by apply (th_sym _ _ HT)|by apply (th_sym _ _ HK)].
    - destruct b1, b2; try done. right; left. exists q, w, false, false.
      split_and!; try done; simpl in *; [by apply (th_sym _ _ HK)|by apply (th_sym _ _ HT)].
    - right; right; right. exists q, p. split_and!; try done.
      destruct H as [H|(w & w' & b1 & b2 & b3 & Hw & Hw' & H1 & H2 & H3 & Hb)].
      + left. simpl in *. by apply (th_sym _ _ HK).
      + destruct b1, b2, b3; try done. right. exists w', w, false, false, false.
        split_and!; try done; simpl in *; first [by apply (th_sym _ _ HK)|by apply (th_sym _ _ HT)].
  Qed.

  Lemma V_shift x y : V false x y → V false (pt_shift 1 x) (pt_shift 1 y).
  Proof.
    intros [(Hx & Hy & H)|[(p & w & b1 & b2 & Hp & -> & Hw & Hy & H1 & H2 & Hb)
           |[(q & w & b1 & b2 & Hq & -> & Hw & Hx & H1 & H2 & Hb)|(p & q & Hp & Hq & -> & -> & H)]]].
    - left. split_and!; [done|done|by apply (th_shift _ _ HT)].
    - destruct b1, b2; try done. right; left. exists (pt_shift 1 p), (pt_shift 1 w), false, false.
      rewrite Hgs. split_and!; try done; simpl in *;
        [by apply (th_shift _ _ HK)|rewrite Hgs; by apply (th_shift _ _ HT)].
    - destruct b1, b2; try done. right; right; left. exists (pt_shift 1 q), (pt_shift 1 w), false, false.
      rewrite Hgs. split_and!; try done; simpl in *;
        [rewrite Hgs; by apply (th_shift _ _ HT)|by apply (th_shift _ _ HK)].
    - right; right; right. exists (pt_shift 1 p), (pt_shift 1 q). rewrite !Hgs. split_and!; try done.
      destruct H as [H|(w & w' & b1 & b2 & b3 & Hw & Hw' & H1 & H2 & H3 & Hb)].
      + left. simpl in *. by apply (th_shift _ _ HK).
      + destruct b1, b2, b3; try done. right. exists (pt_shift 1 w), (pt_shift 1 w'), false, false, false.
        rewrite !Hgs. split_and!; try done; simpl in *;
          first [by apply (th_shift _ _ HK)|by apply (th_shift _ _ HT)].
  Qed.

  Lemma V_slot x y i : V false x y → V false (pt_slot x i) (pt_slot y i).
  Proof.
    intros [(Hx & Hy & H)|[(p & w & b1 & b2 & Hp & -> & Hw & Hy & H1 & H2 & Hb)
           |[(q & w & b1 & b2 & Hq & -> & Hw & Hx & H1 & H2 & Hb)|(p & q & Hp & Hq & -> & -> & H)]]].
    - left. split_and!; [done|done|by apply (th_slot _ _ HT)].
    - destruct b1, b2; try done. right; left. exists (pt_slot p i), (pt_slot w i), false, false.
      rewrite Hgl. split_and!; try done; simpl in *;
        [by apply (th_slot _ _ HK)|rewrite Hgl; by apply (th_slot _ _ HT)].
    - destruct b1, b2; try done. right; right; left. exists (pt_slot q i), (pt_slot w i), false, false.
      rewrite Hgl. split_and!; try done; simpl in *;
        [rewrite Hgl; by apply (th_slot _ _ HT)|by apply (th_slot _ _ HK)].
    - right; right; right. exists (pt_slot p i), (pt_slot q i). rewrite !Hgl. split_and!; try done.
      destruct H as [H|(w & w' & b1 & b2 & b3 & Hw & Hw' & H1 & H2 & H3 & Hb)].
      + left. simpl in *. by apply (th_slot _ _ HK).
      + destruct b1, b2, b3; try done. right. exists (pt_slot w i), (pt_slot w' i), false, false, false.
        rewrite !Hgl. split_and!; try done; simpl in *;
          first [by apply (th_slot _ _ HK)|by apply (th_slot _ _ HT)].
  Qed.

  Lemma V_pofs x y : pofs x y → Nt x → V true x y.
  Proof.
    intros Hxy Hx. destruct (pofs_is_shift x y Hxy) as [k ->].
    destruct (Hg4 x Hx) as (p & Hp & <-). right; right; right.
    exists p, (pt_shift (S k) p). split_and!; try done; [by rewrite (map_shift_n g Hgs)|].
    left. simpl. by apply (th_po_n KE KL).
  Qed.

  Lemma V_po x : V true x (pt_shift 1 x).
  Proof.
    destruct (decide (Nt x)) as [Hx|Hx].
    - apply V_pofs; [apply pofs_shift|done].
    - left. split_and!; [done|done|apply (th_po _ _ HT)].
  Qed.

  Lemma V_base b x y : rb KE KL b x y → V b (g x) (g y).
  Proof.
    intros H. destruct (decide (Ns x)) as [Hx|Hx], (decide (Ns y)) as [Hy|Hy].
    - right; right; right. exists x, y. split_and!; try done. by left.
    - right; left. exists x, y, b, false. split_and!; try done; [by apply Hg2|apply (th_refl _ _ HT)|by bools].
    - right; right; left. exists y, x, false, b. split_and!; try done; [by apply Hg2|apply (th_refl _ _ HT)].
    - left. split_and!; [by apply Hg2|by apply Hg2|by apply HKr].
  Qed.

  Lemma V_gen :
    (∀ x y, geq (λ x y, E x y ∨ De x y) x y → V false x y) ∧
    (∀ x y, glt (λ x y, E x y ∨ De x y) (λ x y, L x y ∨ Dl x y) x y → V true x y).
  Proof.
    assert (∀ x y, geq (λ x y, E x y ∨ De x y) x y → V false x y) as Hq.
    { induction 1 as [x y [H|H]|x|x y _ IH|x y z _ IH1 _ IH2|x y _ IH|x y i _ IH].
      - destruct (decide (Nt x)) as [Hx|Hx]; [rewrite (HEn x y H) by auto; apply V_refl|].
        destruct (decide (Nt y)) as [Hy|Hy]; [rewrite (HEn x y H) by auto; apply V_refl|].
        left. by split_and!.
      - destruct (HDe x y H) as (x0 & y0 & H0 & -> & ->). by apply (V_base false).
      - apply V_refl.
      - by apply V_sym.
      - exact (V_trans false false _ _ _ IH1 IH2).
      - by apply V_shift.
      - by apply V_slot. }
    split; [done|].
    induction 1 as [x y [H|H]|x|x x' y y' Hx _ IH Hy|x y z _ IH1 _ IH2].
    - destruct (decide (Nt x)) as [Hx|Hx]; [apply V_pofs; auto|].
      destruct (decide (Nt y)) as [Hy|Hy].
      + pose proof (HLn x y H (or_intror Hy)) as Hp. exfalso. apply Hx. by rewrite (pofs_root x y Hp).
      + left. by split_and!.
    - destruct (HDl x y H) as (x0 & y0 & H0 & -> & ->). by apply (V_base true).
    - apply V_po.
    - apply Hq in Hx, Hy. exact (V_trans true false _ _ _ (V_trans false true _ _ _ Hx IH) Hy).
    - exact (V_trans true true _ _ _ IH1 IH2).
  Qed.

  Theorem interp :
    (∀ x y, ¬ Nt x → ¬ Nt y → geq (λ x y, E x y ∨ De x y) x y → E x y) ∧
    (∀ x y, ¬ Nt x → ¬ Nt y → glt (λ x y, E x y ∨ De x y) (λ x y, L x y ∨ Dl x y) x y → L x y) ∧
    (∀ x, glt (λ x y, E x y ∨ De x y) (λ x y, L x y ∨ Dl x y) x x → ∃ y, L y y).
  Proof.
    destruct V_gen as [Hq Hl].
    assert (∀ b x y, ¬ Nt x → ¬ Nt y → V b x y → TR b x y) as Hold.
    { intros b x y Hx Hy [(_ & _ & H)|[(p & _ & _ & _ & Hp & -> & _)|[(q & _ & _ & _ & Hq' & -> & _)
        |(p & _ & Hp & _ & -> & _)]]]; [done|exfalso; by apply Hx, Hg1|exfalso; by apply Hy, Hg1
        |exfalso; by apply Hx, Hg1]. }
    split_and!.
    - intros x y Hx Hy H. exact (Hold false x y Hx Hy (Hq _ _ H)).
    - intros x y Hx Hy H. exact (Hold true x y Hx Hy (Hl _ _ H)).
    - intros x H. apply Hl in H.
      destruct H as [(_ & _ & H)|[(p & _ & _ & _ & Hp & -> & _ & Hy & _)|[(q & _ & _ & _ & Hq' & -> & _ & Hx & _)
        |(p & q & Hp & Hq' & Ep & E2 & H)]]].
      + by exists x.
      + exfalso. by apply Hy, Hg1.
      + exfalso. by apply Hx, Hg1.
      + rewrite Ep in E2. apply Hg3 in E2 as <-; [|done|done].
        destruct H as [H|(w & w' & b1 & b2 & b3 & Hw & Hw' & H1 & H2 & H3 & Hb)]; [exact (HKc _ H)|].
        exists (g w).
        assert (rb E L (b2 || (b3 || b1)) (g w) (g w)) as Hc.
        { eapply rbT; [exact H2|]. apply HKr; [done|done|]. eapply rbK; [exact H3|exact H1]. }
        destruct b1, b2, b3; simpl in *; try done.
  Qed.
End interp.

(** ** The model lemma for concrete constraints *)

Lemma cc_up_root R x y : cc_up R x y → pt_root x ≠ NVar 0 ∧ pt_root y ≠ NVar 0.
Proof.
  assert (∀ z, pt_root (pt_inst (λ a, pvar (a + 1)) z) ≠ NVar 0) as Hr.
  { intros [p o]. unfold pt_inst, pt_root, pt_shift. simpl.
    induction p as [c|c|q IH b i]; simpl; [done|intros [=]; lia|done]. }
  intros (x0 & y0 & _ & -> & ->). split; apply Hr.
Qed.

Lemma cc_triv peq plt :
  (∀ x y, geq (cc_up peq) x y → x = y ∨ (pt_root x ≠ NVar 0 ∧ pt_root y ≠ NVar 0)) ∧
  (∀ x y, glt (cc_up peq) (cc_up plt) x y → pofs x y ∨ (pt_root x ≠ NVar 0 ∧ pt_root y ≠ NVar 0)).
Proof. apply gen_triv; intros x y H; exact (cc_up_root _ x y H). Qed.

Lemma cc_eq_new peq x y :
  geq (cc_up peq) x y → pt_root x = NVar 0 ∨ pt_root y = NVar 0 → x = y.
Proof. intros H Hr. destruct (proj1 (cc_triv peq peq) x y H) as [->|[??]]; [done|naive_solver]. Qed.

(** The closed form of the model. [TE] and [TL] are Γ, R orders the
    points of ι, Lo u p enters ι from below and Hi q v leaves it. *)
Definition cc_rel (TE TL R Lo Hi : prel) (x y : point) : Prop :=
  (pt_root x ≠ NVar 0 ∧ pt_root y ≠ NVar 0 ∧ TL x y)
  ∨ (pt_root x ≠ NVar 0 ∧ pt_root y = NVar 0 ∧
       ∃ u p, Lo u p ∧ (TE x u ∨ TL x u) ∧ (p = y ∨ R p y))
  ∨ (pt_root x = NVar 0 ∧ pt_root y ≠ NVar 0 ∧
       ∃ q v, Hi q v ∧ (x = q ∨ R x q) ∧ (TE v y ∨ TL v y))
  ∨ (pt_root x = NVar 0 ∧ pt_root y = NVar 0 ∧
       (R x y ∨ ∃ q v u p, Hi q v ∧ (TE v u ∨ TL v u) ∧ Lo u p ∧ (x = q ∨ R x q) ∧ (p = y ∨ R p y))).

Section model.
  Context (peq plt : prel) (C : bcs).
  Local Notation TE := (geq (cc_up peq)).
  Local Notation TL := (glt (cc_up peq) (cc_up plt)).
  Context (φ : point → point) (R Lo Hi : prel).
  Context (Hφo : ∀ x, pt_root x ≠ NVar 0 → φ x = x).
  Context (Hφs : ∀ x, φ (pt_shift 1 x) = pt_shift 1 (φ x)).
  Context (Hφl : ∀ x i, pt_root (φ x) ≠ NVar 0 → φ (pt_slot x i) = pt_slot (φ x) i).
  Context (Hφr : ∀ x y i, φ x = φ y → φ (pt_slot x i) = φ (pt_slot y i)).
  Context (HRt : ∀ x y z, R x y → R y z → R x z).
  Context (HRp : ∀ p, pt_root p = NVar 0 → R p (pt_shift 1 p)).
  Context (HRi : ∀ p, ¬ R p p).
  Context (HB : ∀ u p q v, Lo u p → Hi q v → (p = q ∨ R p q) → TL u v).
  Context (HCe : ∀ a b, bcs_open 1 C (FEq a b) → TE (φ a) (φ b)).
  Context (HCl : ∀ a b, bcs_open 1 C (FLt a b) → cc_rel TE TL R Lo Hi (φ a) (φ b)).

  Local Notation N := (cc_rel TE TL R Lo Hi).
  Local Notation TLE a b := (TE a b ∨ TL a b).
  Local Notation Rle a b := (a = b ∨ R a b).

  Local Lemma HT : theory TE TL.
  Proof. apply theory_gen. Qed.

  Local Lemma TLE_trans a b c : TLE a b → TLE b c → TLE a c.
  Proof.
    intros [H1|H1] [H2|H2].
    - left. by eapply geq_trans.
    - right. eapply glt_eq; [exact H1|exact H2|apply geq_refl].
    - right. eapply glt_eq; [apply geq_refl|exact H1|exact H2].
    - right. by eapply glt_trans.
  Qed.

  Local Lemma TLE_TL a b c : TLE a b → TL b c → TL a c.
  Proof. intros [H1|H1] H2; [eapply glt_eq; [exact H1|exact H2|apply geq_refl]|by eapply glt_trans]. Qed.

  Local Lemma TL_TLE a b c : TL a b → TLE b c → TL a c.
  Proof. intros H1 [H2|H2]; [eapply glt_eq; [apply geq_refl|exact H1|exact H2]|by eapply glt_trans]. Qed.

  Local Lemma Rle_trans a b c : Rle a b → Rle b c → Rle a c.
  Proof. intros [->|H1] [->|H2]; [by left|by right|by right|right; by eapply HRt]. Qed.

  Local Lemma Rle_R a b c : Rle a b → R b c → R a c.
  Proof. intros [->|H1] H2; [done|by eapply HRt]. Qed.

  Local Lemma R_Rle a b c : R a b → Rle b c → R a c.
  Proof. intros H1 [<-|H2]; [done|by eapply HRt]. Qed.

  Lemma N_trans x y z : N x y → N y z → N x z.
  Proof.
    intros [(Hx & Hy & H1)|[(Hx & Hy & u & p & Hlo & H1 & H2)|[(Hx & Hy & q & v & Hhi & H1 & H2)
      |(Hx & Hy & [H1|(q & v & u & p & Hhi & H1 & Hlo & H2 & H3)])]]]
      [(Hy' & Hz & K1)|[(Hy' & Hz & u' & p' & Hlo' & K1 & K2)|[(Hy' & Hz & q' & v' & Hhi' & K1 & K2)
      |(Hy' & Hz & [K1|(q' & v' & u' & p' & Hhi' & K1 & Hlo' & K2 & K3)])]]];
      try contradiction.
    - left. split_and!; [done|done|by eapply glt_trans].
    - right; left. split_and!; [done|done|]. exists u', p'. split_and!; [done| |done].
      right. by eapply TL_TLE.
    - left. split_and!; [done|done|]. eapply TLE_TL; [exact H1|].
      eapply TL_TLE; [apply (HB u p q' v'); [done|done|by eapply Rle_trans]|exact K2].
    - right; left. split_and!; [done|done|]. exists u, p. split_and!; [done|done|].
      right. by eapply Rle_R.
    - right; left. split_and!; [done|done|]. exists u', p'. split_and!; [done| |].
      + right. eapply TLE_TL; [exact H1|]. eapply TL_TLE; [|exact K1].
        apply (HB u p q' v'); [done|done|by eapply Rle_trans].
      + done.
    - right; right; left. split_and!; [done|done|]. exists q, v. split_and!; [done|done|].
      right. eapply TLE_TL; [exact H2|exact K1].
    - right; right; right. split_and!; [done|done|]. right.
      exists q, v, u', p'. split_and!; try done. by eapply TLE_trans.
    - right; right; left. split_and!; [done|done|]. exists q', v'. split_and!; [done| |done].
      right. by eapply R_Rle.
    - right; right; right. split_and!; [done|done|]. left. by eapply HRt.
    - right; right; right. split_and!; [done|done|]. right.
      exists q', v', u', p'. split_and!; try done. right. by eapply R_Rle.
    - right; right; left. split_and!; [done|done|]. exists q, v. split_and!; [done|done|].
      right. eapply TLE_TL; [exact H1|]. eapply TL_TLE; [|exact K2].
      apply (HB u p q' v'); [done|done|by eapply Rle_trans].
    - right; right; right. split_and!; [done|done|]. right.
      exists q, v, u, p. split_and!; try done. right. by eapply Rle_R.
    - right; right; right. split_and!; [done|done|]. right.
      exists q, v, u', p'. split_and!; try done. right. eapply TLE_TL; [exact H1|].
      eapply TL_TLE; [|exact K1]. apply (HB u p q' v'); [done|done|by eapply Rle_trans].
  Qed.

  Lemma N_eql a a' b : TE a a' → N a' b → N a b.
  Proof.
    intros He H. destruct (decide (pt_root a = NVar 0)) as [Ha|Ha].
    { by rewrite (cc_eq_new peq a a' He (or_introl Ha)). }
    destruct (decide (pt_root a' = NVar 0)) as [Ha'|Ha'].
    { exfalso. apply Ha. by rewrite (cc_eq_new peq a a' He (or_intror Ha')). }
    destruct H as [(_ & Hb & H)|[(_ & Hb & u & p & Hlo & H1 & H2)|[(Hx & _)|(Hx & _)]]]; try contradiction.
    - left. split_and!; [done|done|]. eapply glt_eq; [exact He|exact H|apply geq_refl].
    - right; left. split_and!; [done|done|]. exists u, p. split_and!; [done| |done].
      eapply TLE_trans; [left; exact He|exact H1].
  Qed.

  Lemma N_eqr a b b' : N a b' → TE b' b → N a b.
  Proof.
    intros H He. destruct (decide (pt_root b = NVar 0)) as [Hb|Hb].
    { by rewrite <-(cc_eq_new peq b' b He (or_intror Hb)). }
    destruct (decide (pt_root b' = NVar 0)) as [Hb'|Hb'].
    { exfalso. apply Hb. by rewrite <-(cc_eq_new peq b' b He (or_introl Hb')). }
    destruct H as [(Ha & _ & H)|[(_ & Hx & _)|[(Ha & _ & q & v & Hhi & H1 & H2)|(_ & Hx & _)]]]; try contradiction.
    - left. split_and!; [done|done|]. eapply glt_eq; [apply geq_refl|exact H|exact He].
    - right; right; left. split_and!; [done|done|]. exists q, v. split_and!; [done|done|].
      eapply TLE_trans; [exact H2|left; exact He].
  Qed.

  Local Notation E1 := (cc_eq peq C).
  Local Notation L1 := (cc_lt plt C).

  Lemma model_gen :
    (∀ x y, geq E1 x y → TE (φ x) (φ y)) ∧ (∀ x y, glt E1 L1 x y → N (φ x) (φ y)).
  Proof.
    assert (∀ x y, geq E1 x y → TE (φ x) (φ y)) as Hq.
    { induction 1 as [x y [H|H]|x|x y _ IH|x y z _ IH1 _ IH2|x y _ IH|x y i _ IH].
      - destruct (cc_up_root _ _ _ H). rewrite !Hφo by done. by apply geq_base.
      - by apply HCe.
      - apply geq_refl.
      - by apply geq_sym.
      - by eapply geq_trans.
      - rewrite !Hφs. by apply geq_shift.
      - destruct (decide (pt_root (φ x) = NVar 0)) as [Hx|Hx].
        { rewrite (Hφr x y i (cc_eq_new peq _ _ IH (or_introl Hx))). apply geq_refl. }
        destruct (decide (pt_root (φ y) = NVar 0)) as [Hy|Hy].
        { rewrite (Hφr x y i (cc_eq_new peq _ _ IH (or_intror Hy))). apply geq_refl. }
        rewrite !Hφl by done. by apply geq_slot. }
    split; [done|].
    induction 1 as [x y [H|H]|x|x x' y y' Hx _ IH Hy|x y z _ IH1 _ IH2].
    - destruct (cc_up_root _ _ _ H) as [Hx Hy]. rewrite !Hφo by done.
      left. split_and!; [done|done|by apply glt_base].
    - by apply HCl.
    - rewrite Hφs. destruct (decide (pt_root (φ x) = NVar 0)) as [Hx|Hx].
      + right; right; right. split_and!; [done|done|]. left. by apply HRp.
      + left. split_and!; [done|done|apply glt_po].
    - apply Hq in Hx, Hy. eapply N_eql; [exact Hx|]. by eapply N_eqr.
    - by eapply N_trans.
  Qed.

  Theorem cc_model : cc_ok peq plt C.
  Proof.
    destruct model_gen as [Hq Hl]. split.
    - intros p H. apply Hl in H.
      destruct H as [(_ & _ & H)|[(Hx & Hy & _)|[(Hx & Hy & _)|(_ & _ & [H|(q & v & u & p' & Hhi & H1 & Hlo & H2 & H3)])]]];
        try contradiction.
      + by exists (φ p).
      + exfalso. by apply (HRi (φ p)).
      + exists u. eapply TL_TLE; [|exact H1]. apply (HB u p' q v); [done|done|by eapply Rle_trans].
    - split.
      + intros x y Hx Hy H. apply Hq in H. by rewrite !Hφo in H.
      + intros x y Hx Hy H. apply Hl in H. rewrite !Hφo in H by done.
        destruct H as [(_ & _ & H)|[(_ & Hy' & _)|[(Hx' & _)|(Hx' & _)]]]; try contradiction. done.
  Qed.
End model.

(** Facts of Γ read under the binder of ι. *)
Lemma cc_up_lt peq plt x y : plt x y →
  glt (cc_up peq) (cc_up plt) (pt_inst (λ a, pvar (a + 1)) x) (pt_inst (λ a, pvar (a + 1)) y).
Proof. intros H. apply glt_base. by exists x, y. Qed.

Lemma cc_up_eq peq x y : peq x y →
  geq (cc_up peq) (pt_inst (λ a, pvar (a + 1)) x) (pt_inst (λ a, pvar (a + 1)) y).
Proof. intros H. apply geq_base. by exists x, y. Qed.

(** ** Transfer *)

Lemma cc_ok_transfer peq plt peq' plt' C C' (f : point → point) :
  (∀ x, f (pt_shift 1 x) = pt_shift 1 (f x)) →
  (∀ x i, f (pt_slot x i) = pt_slot (f x) i) →
  (∀ p, pt_root p = NVar 0 → pt_root (f p) = NVar 0) →
  (∀ x, pt_root x ≠ NVar 0 → pt_root (f x) ≠ NVar 0) →
  (∀ p q, pt_root p = NVar 0 → pt_root q = NVar 0 → f p = f q → p = q) →
  (∀ y, pt_root y = NVar 0 → ∃ p, pt_root p = NVar 0 ∧ f p = y) →
  (∀ x y, cc_up peq x y → geq (cc_up peq') (f x) (f y)) →
  (∀ x y, cc_up plt x y → glt (cc_up peq') (cc_up plt') (f x) (f y)) →
  (∀ g, bcs_open 1 C' g → ∃ g0, bcs_open 1 C g0 ∧ g = fact_map f g0) →
  cc_ok peq plt C → cc_ok peq' plt' C'.
Proof.
  intros Hs Hl H1 H2 H3 H4 He Hlt HC [Hacy [Hce Hcl]].
  destruct (gen_map (cc_up peq) (cc_up plt) (geq (cc_up peq')) (glt (cc_up peq') (cc_up plt')) f
              (theory_gen _ _) Hs Hl He Hlt) as [Mq Ml].
  destruct (interp (geq (cc_up peq')) (glt (cc_up peq') (cc_up plt')) (theory_gen _ _) (NVar 0)
              (λ x y H Hr, cc_eq_new peq' x y H Hr)
              (λ x y H Hr, match proj2 (cc_triv peq' plt') x y H with
                           | or_introl Hp => Hp
                           | or_intror (conj Ha Hb) => match Hr with or_introl E => False_rect _ (Ha E)
                                                                   | or_intror E => False_rect _ (Hb E) end end)
              (geq (cc_eq peq C)) (glt (cc_eq peq C) (cc_lt plt C)) (theory_gen _ _) f Hs Hl H1 H2 H3 H4
              ltac:(intros x y Hx Hy H; apply Mq; by apply Hce)
              ltac:(intros x y Hx Hy H; apply Ml; by apply Hcl)
              ltac:(intros p H; destruct (Hacy p H) as [x Hx]; exists (f x); by apply Ml)
              (λ x y, bcs_open 1 C' (FEq x y)) (λ x y, bcs_open 1 C' (FLt x y)))
    as (Ie & Il & Ic).
  - intros x y H. destruct (HC _ H) as ([x0 y0|x0 y0] & H0 & E); simpl in E; simplify_eq.
    exists x0, y0. split_and!; [apply geq_base; by right|done|done].
  - intros x y H. destruct (HC _ H) as ([x0 y0|x0 y0] & H0 & E); simpl in E; simplify_eq.
    exists x0, y0. split_and!; [apply glt_base; by right|done|done].
  - destruct (gen_mono (cc_eq peq' C') (cc_lt plt' C')
                (λ x y, geq (cc_up peq') x y ∨ bcs_open 1 C' (FEq x y))
                (λ x y, glt (cc_up peq') (cc_up plt') x y ∨ bcs_open 1 C' (FLt x y))) as [Gq Gl].
    { intros x y [H|H]; [left; by apply geq_base|by right]. }
    { intros x y [H|H]; [left; by apply glt_base|by right]. }
    split.
    + intros p H. apply Gl in H. destruct (Ic p H) as [y Hy]. by exists y.
    + split.
      * intros x y Hx Hy H. apply Gq in H. by apply Ie.
      * intros x y Hx Hy H. apply Gl in H. by apply Il.
Qed.

Lemma cc_ok_mono peq plt peq' plt' C :
  (∀ x y, peq x y → peq' x y) → (∀ x y, plt x y → plt' x y) →
  cc_ok peq plt C → cc_ok peq' plt' C.
Proof.
  intros He Hl. apply (cc_ok_transfer peq plt peq' plt' C C id); try done.
  - intros p. by exists p.
  - intros x y (x0 & y0 & H & -> & ->). apply geq_base. exists x0, y0. auto.
  - intros x y (x0 & y0 & H & -> & ->). apply glt_base. exists x0, y0. auto.
  - intros g Hg. exists g. split; [done|by destruct g].
Qed.

(** ** The world of new

    At O-New the relation picks a fresh constant a. The map [ga] reads a
    point under the binder of ι at a: ι becomes a, the outer variables
    shift back, and a itself goes out of the way. The world W′ is W
    with the facts of C at a. [interp] at T = W shows that W′ adds no
    fact between points of other names and no cycle. *)

Section world.
  Context (a : nat).

  Definition ga_root (p : pname) : pname :=
    match p with
    | NVar 0 => NConst a
    | NVar (S k) => NVar k
    | NConst c => if decide (c = a) then NVar 0 else NConst c
    | NSlot _ _ _ => p
    end.

  Fixpoint ga_name (p : pname) : pname :=
    match p with NSlot q b i => NSlot (ga_name q) b i | _ => ga_root p end.

  Definition ga (x : point) : point := Pt (ga_name (pt_name x)) (pt_off x).

  Lemma ga_shift x : ga (pt_shift 1 x) = pt_shift 1 (ga x).
  Proof. done. Qed.

  Lemma ga_slot x i : ga (pt_slot x i) = pt_slot (ga x) i.
  Proof. done. Qed.

  Lemma ga_name_root p : pn_root (ga_name p) = ga_root (pn_root p).
  Proof. induction p as [c|[|c]|q IH b i]; simpl; try done. by case_decide. Qed.

  Lemma ga_root_new p : pt_root p = NVar 0 → pt_root (ga p) = NConst a.
  Proof. intros H. unfold ga, pt_root in *. simpl. by rewrite ga_name_root, H. Qed.

  Lemma ga_root_old x : pt_root x ≠ NVar 0 → pt_root (ga x) ≠ NConst a.
  Proof.
    intros H. unfold ga, pt_root in *. simpl. rewrite ga_name_root.
    destruct (pn_root (pt_name x)) as [c|[|c]|q b i] eqn:E; simpl; try done.
    case_decide; [done|congruence].
  Qed.

  Lemma ga_name_inj_new p q :
    pn_root p = NVar 0 → pn_root q = NVar 0 → ga_name p = ga_name q → p = q.
  Proof.
    revert q. induction p as [c|[|c]|p IH b i]; intros q Hp Hq E; simpl in *; try done;
      destruct q as [c'|[|c']|q b' i']; simpl in *; try done.
    - injection E as E1 -> ->. f_equal. by apply IH.
  Qed.

  Lemma ga_inj_new p q : pt_root p = NVar 0 → pt_root q = NVar 0 → ga p = ga q → p = q.
  Proof.
    destruct p as [p o], q as [q o']. unfold ga, pt_root. simpl. intros Hp Hq [=E ->].
    f_equal. by apply ga_name_inj_new.
  Qed.

  Lemma ga_surj_new y : pt_root y = NConst a → ∃ p, pt_root p = NVar 0 ∧ ga p = y.
  Proof.
    destruct y as [n o]. unfold pt_root, ga. simpl. intros Hn.
    assert (∃ p, pn_root p = NVar 0 ∧ ga_name p = n) as (p & Hp & <-).
    { induction n as [c|c|q IH b i]; simpl in *.
      - injection Hn as ->. by exists (NVar 0).
      - done.
      - destruct (IH Hn) as (p & Hp & <-). by exists (NSlot p b i). }
    by exists (Pt p o).
  Qed.

  (** On points rooted at 0 or at a constant other than a, [ga] is the
      instantiation of ι by a. *)
  Lemma ga_inst x :
    (pt_root x = NVar 0 ∨ ∃ c, pt_root x = NConst c ∧ c ≠ a) →
    ga x = pt_inst (plist [pconst a]) x.
  Proof.
    destruct x as [n o]. unfold ga, pt_inst, pt_root. simpl. intros Hr.
    assert (∀ n, (pn_root n = NVar 0 ∨ ∃ c, pn_root n = NConst c ∧ c ≠ a) →
              pn_inst (plist [pconst a]) n = Pt (ga_name n) 0) as Hn.
    { induction n0 as [c|[|c]|q IH b i]; simpl; intros H.
      - destruct H as [?|(c' & [= ->] & Hc)]; [done|]. by rewrite decide_False.
      - done.
      - destruct H as [?|(? & ? & _)]; done.
      - rewrite IH by done. done. }
    rewrite (Hn n Hr). unfold pt_shift. simpl. try (f_equal; lia).
  Qed.
End world.

Lemma pn_vb_inst_root σ k p :
  pn_vb k p → ∃ j, j < k ∧ pn_root (pt_name (pn_inst σ p)) = pt_root (σ j).
Proof.
  induction p as [c|c|q IH b i]; simpl; [done|intros H; by exists c|].
  intros H. destruct (IH H) as (j & Hj & E). exists j. split; [done|]. exact E.
Qed.

Lemma pt_inst_root_vb σ k x :
  pn_vb k (pt_name x) → ∃ j, j < k ∧ pt_root (pt_inst σ x) = pt_root (σ j).
Proof. intros H. destruct (pn_vb_inst_root σ k _ H) as (j & ? & E). exists j. split; [done|exact E]. Qed.

(** The points of the facts of C under the binder, at outer points known
    in W: their root is 0 or a name of W. *)
Lemma bcs_open1_root W C g x :
  world_wf W → Forall (pt_known W) (bc_env C) → bcs_open 1 C g →
  (match g with FLt x y | FEq x y => x end = x ∨ match g with FLt x y | FEq x y => y end = x) →
  pt_root x = NVar 0 ∨ pt_root x ∈ w_names W.
Proof.
  intros HW HK (f & _ & Hs & ->) Hx.
  assert (∀ z, pn_vb (1 + length (bc_env C)) (pt_name z) →
            pt_root (pt_inst (pup 1 (plist (bc_env C))) z) = NVar 0 ∨
            pt_root (pt_inst (pup 1 (plist (bc_env C))) z) ∈ w_names W) as Hz.
  { intros z Hz. destruct (pt_inst_root_vb (pup 1 (plist (bc_env C))) _ z Hz) as (j & Hj & ->).
    unfold pup. destruct (decide (j < 1)) as [Hj0|Hj0]; [left; by replace j with 0 by lia|right].
    unfold plist. destruct (lookup_lt_is_Some_2 (bc_env C) (j - 1)) as [e He]; [lia|]. rewrite He.
    pose proof (proj1 (Forall_lookup _ _) HK _ _ He) as Hk. unfold pt_known in Hk.
    destruct (wf_names_const _ HW _ Hk) as [c Hc].
    destruct e as [n o]. unfold pt_root in *. simpl in *.
    assert (∀ n, pn_root n = NConst c →
              pn_root (pt_name (pn_inst (λ a', pvar (a' + 1)) n)) = NConst c) as Hc'.
    { induction n0 as [c'|c'|q IH b i]; simpl; [done|done|]. intros Hq. by apply IH. }
    unfold pt_inst. simpl. rewrite Hc'; [|done]. by rewrite <-Hc. }
  destruct f as [u v|u v]; destruct Hs as [Hu Hv]; simpl in *; destruct Hx as [<-|<-]; by apply Hz.
Qed.

Lemma wext_cc W a C :
  strict W → cc_ok (w_eq W) (w_lt W) C → Forall (pt_known W) (bc_env C) →
  NConst a ∉ w_names W →
  ∃ W', wext_fresh W {[NConst a]} W' ∧ bcs_hold (w_eq W') (w_lt W') C [pconst a].
Proof.
  intros [HW Hirr] [Hacy [Hce Hcl]] HK Ha.
  set (De := λ x y, ∃ x0 y0, bcs_open 1 C (FEq x0 y0) ∧ x = ga a x0 ∧ y = ga a y0).
  set (Dl := λ x y, ∃ x0 y0, bcs_open 1 C (FLt x0 y0) ∧ x = ga a x0 ∧ y = ga a y0).
  set (W' := wgen (w_names W ∪ {[NConst a]}) (λ x y, w_eq W x y ∨ De x y) (λ x y, w_lt W x y ∨ Dl x y)).
  (* W sends Γ under the binder back to W *)
  assert (∀ x, pt_root (pt_inst (λ b, pvar (b + 1)) x) ≠ NVar 0 ∧
               (pt_root x ∈ w_names W → ga a (pt_inst (λ b, pvar (b + 1)) x) = x)) as Hup.
  { intros [n o]. unfold pt_root, pt_inst, ga. simpl.
    assert (∀ n, pn_root (pt_name (pn_inst (λ b, pvar (b + 1)) n)) ≠ NVar 0 ∧
                 (pn_root n ∈ w_names W →
                  ga_name a (pt_name (pn_inst (λ b, pvar (b + 1)) n)) = n ∧
                  pt_off (pn_inst (λ b, pvar (b + 1)) n) = 0)) as Hn.
    { induction n0 as [c|c|q IH b i]; simpl.
      - split; [done|]. intros Hc. split; [|done]. rewrite decide_False; [done|].
        intros ->. by apply Ha.
      - split; [intros [=]; lia|]. intros Hc. destruct (wf_names_const _ HW _ Hc) as [? [=]].
      - destruct IH as [IH1 IH2]. split; [done|]. intros Hq. destruct (IH2 Hq) as [E1 E2].
        split; [|done]. simpl. rewrite E1. f_equal. lia. }
    destruct (Hn n) as [H1 H2]. split; [done|]. intros Hr. destruct (H2 Hr) as [E1 E2].
    rewrite E1. simpl. f_equal. lia. }
  assert (∀ x y, cc_up (w_eq W) x y → w_eq W (ga a x) (ga a y)) as Mq.
  { intros x y (x0 & y0 & H & -> & ->).
    destruct (wf_eq_supp _ HW _ _ H) as [->|[Hx Hy]]; [apply (wf_eq_refl _ HW)|].
    rewrite (proj2 (Hup x0) Hx), (proj2 (Hup y0) Hy). done. }
  assert (∀ x y, cc_up (w_lt W) x y → w_lt W (ga a x) (ga a y)) as Ml.
  { intros x y (x0 & y0 & H & -> & ->).
    destruct (wf_lt_supp _ HW _ _ H) as [Hp|[Hx Hy]].
    - apply (th_pofs _ _ (ga a (pt_inst (λ b, pvar (b + 1)) x0)) _ (theory_world W HW)).
      destruct x0 as [p o], y0 as [q o']. destruct Hp as [Hn Ho]. simpl in *. subst q.
      unfold pofs, ga, pt_inst, pt_shift. simpl. split; [done|lia].
    - rewrite (proj2 (Hup x0) Hx), (proj2 (Hup y0) Hy). done. }
  destruct (gen_map (cc_up (w_eq W)) (cc_up (w_lt W)) (w_eq W) (w_lt W) (ga a) (theory_world W HW)
              (ga_shift a) (ga_slot a) Mq Ml) as [Gq Gl].
  destruct (interp (w_eq W) (w_lt W) (theory_world W HW) (NConst a)
              ltac:(intros x y H Hr; destruct (wf_eq_supp _ HW _ _ H) as [?|[Hx Hy]]; [done|];
                    exfalso; destruct Hr as [Hr|Hr]; rewrite <-Hr in *; by apply Ha)
              ltac:(intros x y H Hr; destruct (wf_lt_supp _ HW _ _ H) as [?|[Hx Hy]]; [done|];
                    exfalso; destruct Hr as [Hr|Hr]; rewrite <-Hr in *; by apply Ha)
              (geq (cc_eq (w_eq W) C)) (glt (cc_eq (w_eq W) C) (cc_lt (w_lt W) C)) (theory_gen _ _)
              (ga a) (ga_shift a) (ga_slot a) (ga_root_new a) (ga_root_old a) (ga_inj_new a)
              (ga_surj_new a)
              ltac:(intros x y Hx Hy H; apply Gq; by apply Hce)
              ltac:(intros x y Hx Hy H; apply Gl; by apply Hcl)
              ltac:(intros p H; destruct (Hacy p H) as [x Hx]; exists (ga a x); by apply Gl)
              De Dl) as (Ie & Il & Ic).
  - intros x y (x0 & y0 & H & -> & ->). exists x0, y0. split_and!; [apply geq_base; by right|done|done].
  - intros x y (x0 & y0 & H & -> & ->). exists x0, y0. split_and!; [apply glt_base; by right|done|done].
  - (* roots of the facts of C at a *)
    assert (∀ g x0, bcs_open 1 C g →
              (match g with FLt x y | FEq x y => x end = x0 ∨ match g with FLt x y | FEq x y => y end = x0) →
              pt_root (ga a x0) ∈ w_names W ∪ {[NConst a]} ∧ ga a x0 = pt_inst (plist [pconst a]) x0) as Hr.
    { intros g x0 Hg Hx0. destruct (bcs_open1_root W C g x0 HW HK Hg Hx0) as [H0|H0].
      - split; [rewrite (ga_root_new a x0 H0); set_solver|]. apply ga_inst. by left.
      - destruct (wf_names_const _ HW _ H0) as [c Hc].
        assert (c ≠ a) by (intros ->; by rewrite Hc in H0).
        split; [|apply ga_inst; right; by exists c].
        unfold ga, pt_root in *. simpl. rewrite ga_name_root, Hc. simpl. rewrite decide_False by done.
        rewrite <-Hc. set_solver. }
    assert (world_wf W') as HW'.
    { apply wgen_wf.
      - intros p Hp. apply elem_of_union in Hp as [Hp|Hp]; [by apply (wf_names_const _ HW)|].
        apply elem_of_singleton in Hp as ->. by exists a.
      - intros x y [H|(x0 & y0 & H & -> & ->)].
        + eapply eq_or_supp_mono; [|by apply (wf_eq_supp _ HW)]. set_solver.
        + right. split; [apply (Hr _ x0 H); by left|apply (Hr _ y0 H); by right].
      - intros x y [H|(x0 & y0 & H & -> & ->)].
        + eapply po_or_supp_mono; [|by apply (wf_lt_supp _ HW)]. set_solver.
        + right. split; [apply (Hr _ x0 H); by left|apply (Hr _ y0 H); by right]. }
    assert (strict W') as HS.
    { split; [done|]. intros x Hx. destruct (Ic x Hx) as [y Hy]. by apply (Hirr y). }
    exists W'. split.
    + split_and!.
      * split_and!; simpl; [set_solver|intros x y H; apply geq_base; by left
          |intros x y H; apply glt_base; by left|done].
      * set_solver.
      * done.
      * intros x y Hx Hy. assert (pt_root x ≠ NConst a) by set_solver.
        assert (pt_root y ≠ NConst a) by set_solver. split; intros Hxy; [by apply Ie|by apply Il].
    + intros g Hg. simpl. destruct g as [x0 y0|x0 y0]; simpl.
      * rewrite <-(proj2 (Hr _ x0 Hg (or_introl eq_refl))), <-(proj2 (Hr _ y0 Hg (or_intror eq_refl))).
        apply glt_base. right. by exists x0, y0.
      * rewrite <-(proj2 (Hr _ x0 Hg (or_introl eq_refl))), <-(proj2 (Hr _ y0 Hg (or_intror eq_refl))).
        apply geq_base. right. by exists x0, y0.
Qed.
