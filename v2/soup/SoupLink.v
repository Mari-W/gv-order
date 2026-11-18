(** * The soup along a link (stage S8)

    P-Act-Link: thread i links o1 and o2, which it holds at dual points
    and dual session types. The channel of o1 goes, and every thread is
    renamed by [csub o1 o2], so the partner of o1 now holds o2. The
    linker's obligations remove both ends and spend a ticket. Every other
    thread keeps its term, renamed ([Erel_rename], [FuelE_rename]), and
    the partners of o1 and o2 form one channel ([link_pair]). *)

From stdpp Require Import relations.
From GV Require Export soup.SoupSync soup.LinkMaps.

Lemma pair_set_eq (o1 o2 p1 p2 : cend) :
  ({[o1]} ∪ {[o2]} : gset cend) = {[p1]} ∪ {[p2]} → p1 ≠ p2 →
  (p1 = o1 ∧ p2 = o2) ∨ (p1 = o2 ∧ p2 = o1).
Proof.
  intros Heq Hne.
  assert (p1 ∈ ({[o1]} ∪ {[o2]} : gset cend)) as H1 by (rewrite Heq; set_solver).
  assert (p2 ∈ ({[o1]} ∪ {[o2]} : gset cend)) as H2 by (rewrite Heq; set_solver).
  assert (o1 ∈ ({[p1]} ∪ {[p2]} : gset cend)) as H3 by (rewrite <-Heq; set_solver).
  assert (o2 ∈ ({[p1]} ∪ {[p2]} : gset cend)) as H4 by (rewrite <-Heq; set_solver).
  set_solver.
Qed.

Lemma kdel2_notown {Y : Type} (K : own) t (m : gmap cend Y) o1 o2 :
  (¬ ∃ h, K !! o1 = Some h ∧ h.(h_th) = t) → (¬ ∃ h, K !! o2 = Some h ∧ h.(h_th) = t) →
  kdel2 o1 o2 (kres K t m) = kres K t m.
Proof.
  intros H1 H2.
  assert (kres K t m !! o1 = None) by (apply lookup_kres_None; by right).
  assert (kres K t m !! o2 = None) by (apply lookup_kres_None; by right).
  unfold kdel2. rewrite (delete_id (kres K t m) o2) by done. by rewrite delete_id.
Qed.

Lemma ctrs_notown (K : own) t o1 o2 :
  (¬ ∃ h, K !! o1 = Some h ∧ h.(h_th) = t) → (¬ ∃ h, K !! o2 = Some h ∧ h.(h_th) = t) →
  kdel2 o1 o2 (ctrs K t) = ctrs K t.
Proof.
  intros H1 H2.
  assert (ctrs K t !! o1 = None) by (by apply lookup_ctrs_None).
  assert (ctrs K t !! o2 = None) by (by apply lookup_ctrs_None).
  unfold kdel2. rewrite (delete_id (ctrs K t) o2) by done. by rewrite delete_id.
Qed.

Section link.
  Context (N n : nat) (W : world) (T : ty) (C : gset chan) (Mq : gmap nat expr) (K : own)
    (tk : nat → nat) (A : senv) (Π : penv) (U : nat → ty).
  Context (Hs : soup_inv N (S n) W ∅ T (LFState (C, Mq) K tk) A Π U).

  Local Lemma owner_of' t o v : kres K t A !! o = Some v → ∃ h, K !! o = Some h ∧ h.(h_th) = t.
  Proof. intros H. apply lookup_kres in H as [_ H]. done. Qed.

  Local Lemma inA' t o v : kres K t A !! o = Some v → A !! o = Some v.
  Proof. intros H. apply lookup_kres in H as [H _]. done. Qed.

  Local Lemma inΠ' t o v : kres K t Π !! o = Some v → Π !! o = Some v.
  Proof. intros H. apply lookup_kres in H as [H _]. done. Qed.

  (** The linker's obligations, in the order of the event. *)
  Lemma link_obl i e o1 o2 e' :
    Mq !! i = Some e → tstep e (LSess (SLink ({[o1]} ∪ {[o2]}))) e' →
    o1 ≠ o2 ∧
    (∃ h, K !! o1 = Some h ∧ h.(h_th) = i) ∧ (∃ h, K !! o2 = Some h ∧ h.(h_th) = i) ∧
    (∃ Sa Sb xa, A !! o1 = Some (Sa, xa) ∧ A !! o2 = Some (Sb, pt_dual xa) ∧ sdual Sa Sb) ∧
    (∃ Pa Pb, Π !! o1 = Some Pa ∧ Π !! o2 = Some Pb ∧ sequiv Pb (dual Pa)) ∧
    e' ∈ E[live]^W _ n⟦kdel2 o1 o2 (kres K i A) ⊢ U i⟧^∅ ∧
    1 ≤ tk i ∧
    e' ∈ F^(Some N) _ n⟦RThread ▷ None ; 0⟧(kdel2 o1 o2 (kres K i Π), kdel2 o1 o2 (ctrs K i), tk i - 1).
  Proof.
    intros He Hst. destruct (s_obl _ _ _ _ _ _ _ _ _ _ _ Hs i e _ e' He Hst) as [HE HF].
    cbn [Eobl Fobl] in HE, HF. unfold o_link in HE. unfold f_link in HF.
    destruct HE as (p1 & p2 & S1 & S2 & x & Hos & Hp12 & Hp1 & Hp2 & Hsd & HE').
    destruct HF as (Hpl & _ & Htk & HF').
    rewrite mrem_kdel2, mrem_kdel2 in HF'.
    destruct Hpl as (q1 & q2 & P1 & P2 & Hqs & Hq12 & Hq1 & Hq2 & Hqd).
    destruct (owner_of' _ _ _ Hp1) as (h1 & Kh1 & Eh1). destruct (owner_of' _ _ _ Hp2) as (h2 & Kh2 & Eh2).
    pose proof (inA' _ _ _ Hp1) as HA1. pose proof (inA' _ _ _ Hp2) as HA2.
    pose proof (inΠ' _ _ _ Hq1) as HB1. pose proof (inΠ' _ _ _ Hq2) as HB2.
    assert (Hdel : kdel2 p1 p2 (kres K i A) = kdel2 o1 o2 (kres K i A)).
    { destruct (pair_set_eq _ _ _ _ Hos Hp12) as [[-> ->]|[-> ->]]; [done|apply kdel2_comm]. }
    unfold kdel2 in Hdel. rewrite Hdel in HE'.
    destruct (pair_set_eq _ _ _ _ Hos Hp12) as [[-> ->]|[-> ->]];
      (split; [done|]); (split; [eauto|]); (split; [eauto|]); split_and!.
    - exists S1, S2, x. done.
    - destruct (pair_set_eq _ _ _ _ Hqs Hq12) as [[-> ->]|[-> ->]]; [by exists P1, P2|].
      exists P2, P1. split_and!; [done|done|by apply pdual_sym].
    - eapply at_cost_E_live; [|exact HE']. cbn; lia.
    - done.
    - exact HF'.
    - exists S2, S1, (pt_dual x). split_and!; [done|by rewrite pt_dual_dual|by apply sdual_sym].
    - destruct (pair_set_eq _ _ _ _ Hqs Hq12) as [[-> ->]|[-> ->]]; [by exists P1, P2|].
      exists P2, P1. split_and!; [done|done|by apply pdual_sym].
    - eapply at_cost_E_live; [|exact HE']. cbn; lia.
    - done.
    - exact HF'.
  Qed.
End link.
