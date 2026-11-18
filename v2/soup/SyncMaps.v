(** * Parts of the ownership after a synchronization (stage S8)

    Pointwise equalities between the parts of the updated ownership and
    the maps the obligations of the two actors name. Each lemma lives in
    a small context, so that the case analysis stays cheap. *)

From stdpp Require Import relations.
From GV Require Export soup.OwnFacts.

Ltac own_cases :=
  repeat match goal with
  | |- context [decide ?P] => destruct (decide P)
  | H : context [decide ?P] |- _ => destruct (decide P)
  end.

(** ** A synchronization *)

Lemma lookup_ksync N K i j o y y' Mv o0 :
  ksync N i j o y y' Mv K !! o0 =
    if decide (o0 = o) then Some (Hold i y (Some N))
    else if decide (o0 = edual o) then Some (Hold j y' (Some N))
    else (λ h, if decide (o0 ∈ Mv) then Hold j h.(h_pt) (ftick h.(h_ctr))
               else if decide (h.(h_th) = i ∨ h.(h_th) = j) then htick h else h) <$> K !! o0.
Proof.
  unfold ksync, kact. destruct (decide (o0 = o)) as [->|Hne].
  { by rewrite lookup_insert_eq. }
  rewrite lookup_insert_ne by done. destruct (decide (o0 = edual o)) as [->|Hne'].
  { by rewrite lookup_insert_eq. }
  rewrite lookup_insert_ne by done. unfold khand, ktick. rewrite !lookup_kmod.
  destruct (K !! o0) as [h|]; simpl; [|done]. f_equal. own_cases; naive_solver.
Qed.

Section sync.
  #[local] Set Default Proof Using "All".
  Context (N : nat) (K : own) (i j : nat) (o : cend) (y y' : point) (Mv : gset cend).
  Context (Hij : i ≠ j) (Hoi : ∃ h, K !! o = Some h ∧ h.(h_th) = i)
    (Hoj : ∃ h, K !! edual o = Some h ∧ h.(h_th) = j)
    (HMi : ∀ o1, o1 ∈ Mv → ∃ h, K !! o1 = Some h ∧ h.(h_th) = i ∧ o1 ≠ o) (Hoo : o ≠ edual o).

  Local Abbreviation K' := (ksync N i j o y y' Mv K).

  Local Ltac base o0 :=
    destruct (decide (o0 = o)) as [->|H1]; [naive_solver|];
    destruct (decide (o0 = edual o)) as [->|H2]; [naive_solver|];
    destruct (K !! o0) as [h|] eqn:Eh; simpl; [|naive_solver];
    destruct (decide (o0 ∈ Mv)) as [Hin|Hin];
    [destruct (HMi o0 Hin) as (h' & Hh' & Ht' & _); simplify_eq; naive_solver
    |destruct (decide (h_th h = i ∨ h_th h = j)); naive_solver].

  Lemma sync_kres_i {Y : Type} (m : gmap cend Y) v v' :
    kres K' i (<[o := v]> (<[edual o := v']> m)) = <[o := v]> (mrem Mv (delete o (kres K i m))).
  Proof.
    apply map_eq_some; intros o0 v0.
    rewrite lookup_kres, lookup_ksync, !lookup_insert_Some, lookup_mrem_Some, lookup_delete_Some, lookup_kres.
    base o0.
  Qed.

  Lemma sync_kres_i' {Y : Type} (m : gmap cend Y) v v' :
    kres K' i (<[o := v]> (<[edual o := v']> m)) = <[o := v]> (mrem Mv (kres K i m)).
  Proof.
    apply map_eq_some; intros o0 v0.
    rewrite lookup_kres, lookup_ksync, !lookup_insert_Some, lookup_mrem_Some, lookup_kres.
    base o0.
  Qed.

  Lemma sync_kres_j {Y : Type} (m : gmap cend Y) v v' :
    kres K' j (<[o := v]> (<[edual o := v']> m)) =
    <[edual o := v']> (kres K j m) ∪ mres Mv (delete o (kres K i m)).
  Proof.
    apply map_eq_some; intros o0 v0.
    rewrite lookup_kres, lookup_ksync, !lookup_union_Some_raw, !lookup_insert_Some, lookup_mres_Some,
      lookup_delete_Some, !lookup_kres, lookup_insert_None, lookup_kres_None.
    base o0.
  Qed.

  Lemma sync_kres_j' {Y : Type} (m : gmap cend Y) v v' :
    kres K' j (<[o := v]> (<[edual o := v']> m)) =
    <[edual o := v']> (kres K j m) ∪ mres Mv (kres K i m).
  Proof.
    apply map_eq_some; intros o0 v0.
    rewrite lookup_kres, lookup_ksync, !lookup_union_Some_raw, !lookup_insert_Some, lookup_mres_Some,
      !lookup_kres, lookup_insert_None, lookup_kres_None.
    base o0.
  Qed.

  Lemma sync_kres_other {Y : Type} t (m : gmap cend Y) v v' :
    t ≠ i → t ≠ j → kres K' t (<[o := v]> (<[edual o := v']> m)) = kres K t m.
  Proof.
    intros Hti Htj. apply map_eq_some; intros o0 v0.
    rewrite lookup_kres, lookup_ksync, !lookup_insert_Some, lookup_kres.
    base o0.
  Qed.

  Lemma sync_ctrs_i : ctrs K' i = refill (Some N) o (mrem Mv (ctrs K i)).
  Proof.
    apply map_eq_some; intros o0 f. unfold refill.
    rewrite lookup_ctrs, lookup_ksync, lookup_insert_Some, lookup_fmap_Some.
    setoid_rewrite lookup_delete_Some. setoid_rewrite lookup_mrem_Some. setoid_rewrite lookup_ctrs.
    base o0.
  Qed.

  Lemma sync_ctrs_j : ctrs K' j = refill (Some N) (edual o) (ctrs K j) ∪ fhand Mv (ctrs K i).
  Proof.
    apply map_eq_some; intros o0 f. unfold refill, fhand.
    rewrite lookup_ctrs, lookup_ksync, lookup_union_Some_raw, lookup_insert_Some, lookup_insert_None,
      !lookup_fmap, fmap_None, !fmap_Some.
    setoid_rewrite lookup_delete_Some. setoid_rewrite lookup_delete_None.
    setoid_rewrite lookup_mres_Some. setoid_rewrite lookup_ctrs.
    setoid_rewrite lookup_ctrs_None.
    base o0.
  Qed.

  Lemma sync_ctrs_other t : t ≠ i → t ≠ j → ctrs K' t = ctrs K t.
  Proof.
    intros Hti Htj. apply map_eq_some; intros o0 f. rewrite !lookup_ctrs, lookup_ksync. base o0.
  Qed.
End sync.

Lemma mrem_empty {Y : Type} (m : gmap cend Y) : mrem ∅ m = m.
Proof. apply map_eq_some. intros o v. rewrite lookup_mrem_Some. set_solver. Qed.

Lemma mres_empty {Y : Type} (m : gmap cend Y) : mres ∅ m = ∅.
Proof. apply map_eq_some. intros o v. rewrite lookup_mres_Some, lookup_empty. set_solver. Qed.

Lemma fhand_empty (φ : cenv) : fhand ∅ φ = ∅.
Proof. unfold fhand. by rewrite mres_empty, fmap_empty. Qed.

(** ** A close *)

Section close.
  #[local] Set Default Proof Using "All".
  Context (K : own) (i j : nat) (o : cend).
  Context (Hij : i ≠ j) (Hoi : ∃ h, K !! o = Some h ∧ h.(h_th) = i)
    (Hoj : ∃ h, K !! edual o = Some h ∧ h.(h_th) = j) (Hoo : o ≠ edual o).

  Local Abbreviation K' := (ktick i j ∅ (delete o (delete (edual o) K))).

  Lemma lookup_kclose o0 :
    K' !! o0 = if decide (o0 = o ∨ o0 = edual o) then None
               else (λ h, if decide (h.(h_th) = i ∨ h.(h_th) = j) then htick h else h) <$> K !! o0.
  Proof.
    unfold ktick. rewrite lookup_kmod. case_decide as Ho.
    - destruct Ho as [->| ->]; [by rewrite lookup_delete_eq|].
      by rewrite lookup_delete_ne, lookup_delete_eq.
    - rewrite !lookup_delete_ne by naive_solver. destruct (K !! o0); simpl; [|done].
      f_equal. own_cases; naive_solver.
  Qed.

  Lemma dom_kclose o0 : o0 ∈ dom K' ↔ o0 ∈ dom K ∧ ¬ (o0 = o ∨ o0 = edual o).
  Proof. rewrite !elem_of_dom, lookup_kclose. case_decide; [naive_solver|]. rewrite fmap_is_Some. naive_solver. Qed.

  Local Ltac base o0 :=
    destruct (decide (o0 = o ∨ o0 = edual o)) as [[-> | ->]|H1]; [naive_solver|naive_solver|];
    destruct (K !! o0) as [h|] eqn:Eh; simpl; [|naive_solver];
    destruct (decide (h_th h = i ∨ h_th h = j)); naive_solver.

  Lemma close_kres_i {Y : Type} (m : gmap cend Y) :
    kres K' i (delete o (delete (edual o) m)) = delete o (kres K i m).
  Proof.
    apply map_eq_some; intros o0 v0.
    rewrite lookup_kres, lookup_kclose, !lookup_delete_Some, lookup_kres. base o0.
  Qed.

  Lemma close_kres_j {Y : Type} (m : gmap cend Y) :
    kres K' j (delete o (delete (edual o) m)) = delete (edual o) (kres K j m).
  Proof.
    apply map_eq_some; intros o0 v0.
    rewrite lookup_kres, lookup_kclose, !lookup_delete_Some, lookup_kres. base o0.
  Qed.

  Lemma close_kres_other {Y : Type} t (m : gmap cend Y) :
    t ≠ i → t ≠ j → kres K' t (delete o (delete (edual o) m)) = kres K t m.
  Proof.
    intros Hti Htj. apply map_eq_some; intros o0 v0.
    rewrite lookup_kres, lookup_kclose, !lookup_delete_Some, lookup_kres. base o0.
  Qed.

  Lemma close_ctrs_i : ctrs K' i = ftick <$> delete o (ctrs K i).
  Proof.
    apply map_eq_some; intros o0 f. rewrite lookup_ctrs, lookup_kclose, lookup_fmap_Some.
    setoid_rewrite lookup_delete_Some. setoid_rewrite lookup_ctrs. base o0.
  Qed.

  Lemma close_ctrs_j : ctrs K' j = ftick <$> delete (edual o) (ctrs K j).
  Proof.
    apply map_eq_some; intros o0 f. rewrite lookup_ctrs, lookup_kclose, lookup_fmap_Some.
    setoid_rewrite lookup_delete_Some. setoid_rewrite lookup_ctrs. base o0.
  Qed.

  Lemma close_ctrs_other t : t ≠ i → t ≠ j → ctrs K' t = ctrs K t.
  Proof.
    intros Hti Htj. apply map_eq_some; intros o0 f. rewrite !lookup_ctrs, lookup_kclose. base o0.
  Qed.
End close.
