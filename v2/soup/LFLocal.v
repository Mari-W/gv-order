(** * One soup, locally (stage S8, proposal §2.13)

    Facts of a closed soup at a positive index that adequacy reads at
    every position of a run. A thread whose redex is a session action
    other than a link acts on an end o it holds ([s_held_end]). Its
    readiness puts the point of o below the partner point of every other
    end it holds ([s_ready]). The partner of o is held by another thread
    ([s_partner]), and when that thread's redex acts on the partner, the
    two redexes fit and the thread is enabled ([compat_enabled]). A
    thread that holds an end is not a value ([s_value_empty]). *)

From stdpp Require Import relations.
From GV Require Export soup.SoupTau.

(** ** The end of a session redex *)

Definition aend (a : action) : option cend :=
  match a with ARecv o | ASend o _ | AClose o | ASel o _ | ABra o => Some o | _ => None end.

Definition rend (q : config) (t : nat) : option cend :=
  q.2 !! t ≫= λ e, act e ≫= aend.

Lemma rend_some q t o : rend q t = Some o → ∃ e a, q.2 !! t = Some e ∧ act e = Some a ∧ aend a = Some o.
Proof.
  unfold rend. destruct (q.2 !! t) as [e|] eqn:He; simpl; [|done].
  destruct (act e) as [a|] eqn:Ha; simpl; [|done]. intros H. exists e, a. done.
Qed.

Lemma aend_sess a o : aend a = Some o → is_sess a ∧ ¬ is_admin a.
Proof. destruct a; simpl; intros H; try discriminate; (split; [unfold is_sess; simpl; by eexists|by intros []]). Qed.

Lemma aend_offers a α o : aend a = Some o → offers a α → ∃ σ, α = LSess σ ∧ sends σ = {[o]}.
Proof.
  destruct a, α as [| | | |[]]; simpl; intros [= <-] Ho; try done; destruct_and?; subst; eauto.
Qed.

Lemma aend_step e a o : act e = Some a → aend a = Some o → ∃ σ e', tstep e (LSess σ) e' ∧ sends σ = {[o]}.
Proof.
  intros Ha Ho. destruct a; simpl in Ho; simplify_eq.
  - destruct (act_offer e (ARecv o) (LSess (SRecv o EUnit)) Ha (conj eq_refl I)) as [e' He']. eauto.
  - destruct (act_offer e (ASend o v) (LSess (SSend o (fends v) v)) Ha (conj eq_refl (conj eq_refl eq_refl)))
      as [e' He']. eauto.
  - destruct (act_offer e (AClose o) (LSess (SClose o)) Ha eq_refl) as [e' He']. eauto.
  - destruct (act_offer e (ASel o i) (LSess (SSel o i)) Ha (conj eq_refl eq_refl)) as [e' He']. eauto.
  - destruct (act_offer e (ABra o) (LSess (SBra o false)) Ha eq_refl) as [e' He']. eauto.
Qed.

(** The kind of a redex against the session type of its end. *)
Definition akind (a : action) (S0 : sty) : Prop :=
  match a with
  | ASend _ _ => ∃ m U b S, unfoldS S0 = SSeq (SSnd m U b) S
  | ARecv _ => ∃ m U b S, unfoldS S0 = SSeq (SRcv m U b) S
  | AClose _ => unfoldS S0 = SEnd
  | ASel _ _ => ∃ S1 S2, unfoldS S0 = SPlus S1 S2
  | ABra _ => ∃ S1 S2, unfoldS S0 = SWith S1 S2
  | _ => True
  end.

(** Two redexes that fit on the two ends of a channel. *)
Definition compat (a1 a2 : action) : Prop :=
  match a1, a2 with
  | ASend o _, ARecv o' | ARecv o, ASend o' _ | AClose o, AClose o' | ASel o _, ABra o'
  | ABra o, ASel o' _ => o' = edual o
  | _, _ => False
  end.

Lemma sdual_compat a1 a2 S0 S0' o :
  sdual S0 S0' → akind a1 S0 → akind a2 S0' → aend a1 = Some o → aend a2 = Some (edual o) → compat a1 a2.
Proof.
  intros Hd H1 H2 Ho1 Ho2. unfold sdual in Hd.
  destruct a1; simpl in Ho1; simplify_eq; destruct a2; simpl in Ho2; simplify_eq; simpl; try done;
    simpl in H1, H2; exfalso.
  all: repeat match goal with H : ∃ _, _ |- _ => destruct H end.
  all: match goal with Hd : seqv _ (dual ?s), H1 : unfoldS ?s = ?u |- _ =>
         assert (unfoldS (dual s) = dual u) as Hdu by (by rewrite <-dual_unfoldS, H1); simpl in Hdu end.
  all: first [ destruct (seqv_unfold_rcv _ _ _ _ _ _ Hd Hdu) as (? & ? & ? & Hx & _)
             | destruct (seqv_unfold_snd _ _ _ _ _ _ Hd Hdu) as (? & ? & ? & Hx & _)
             | pose proof (seqv_unfold_end _ _ Hd Hdu) as Hx
             | destruct (seqv_unfold_with _ _ _ _ Hd Hdu) as (? & ? & Hx & _)
             | destruct (seqv_unfold_plus _ _ _ _ Hd Hdu) as (? & ? & Hx & _) ].
  all: congruence.
Qed.

Lemma compat_enabled C M t s e es a1 a2 :
  t ≠ s → M !! t = Some e → M !! s = Some es → act e = Some a1 → act es = Some a2 → compat a1 a2 →
  (∀ o, a1 = AClose o → ech o ∈ C) → tenabled (C, M) t.
Proof.
  intros Hts He Hes Ha1 Ha2 Hc Hcl.
  destruct a1 as [| | | |o|o w|o|o1 o2|o b|o]; destruct a2 as [| | | |o'|o' w'|o'|o1' o2'|o' b'|o']; simpl in Hc;
    try done; subst.
  - (* t receives, s sends *)
    pose proof (act_send_val _ _ _ Ha2) as Hv.
    destruct (act_offer es (ASend (edual o) w') (LSess (SSend (edual o) (fends w') w')) Ha2
      (conj eq_refl (conj eq_refl eq_refl))) as [es' Hs'].
    destruct (act_offer e (ARecv o) (LSess (SRecv o w')) Ha1 (conj eq_refl Hv)) as [e' He'].
    eexists _, _. split; [split; [eapply (p_act_msg C M s t (edual o)); [done|done|done|exact Hs'|]|done]|].
    + by rewrite edual_edual.
    + simpl. set_solver.
  - pose proof (act_send_val _ _ _ Ha1) as Hv.
    destruct (act_offer e (ASend o w) (LSess (SSend o (fends w) w)) Ha1
      (conj eq_refl (conj eq_refl eq_refl))) as [e' He'].
    destruct (act_offer es (ARecv (edual o)) (LSess (SRecv (edual o) w)) Ha2 (conj eq_refl Hv)) as [es' Hs'].
    eexists _, _. split; [split; [eapply (p_act_msg C M t s o); [done|done|done|exact He'|exact Hs']|done]|].
    simpl. set_solver.
  - destruct (act_offer e (AClose o) (LSess (SClose o)) Ha1 eq_refl) as [e' He'].
    destruct (act_offer es (AClose (edual o)) (LSess (SClose (edual o))) Ha2 eq_refl) as [es' Hs'].
    eexists _, _. split; [split; [eapply (p_act_close C M t s o); [done|done|done|exact He'|exact Hs'|by apply Hcl]|done]|].
    simpl. set_solver.
  - destruct (act_offer e (ASel o b) (LSess (SSel o b)) Ha1 (conj eq_refl eq_refl)) as [e' He'].
    destruct (act_offer es (ABra (edual o)) (LSess (SBra (edual o) b)) Ha2 eq_refl) as [es' Hs'].
    eexists _, _. split; [split; [eapply (p_act_choice C M t s o b); [done|done|done|exact He'|exact Hs']|done]|].
    simpl. set_solver.
  - destruct (act_offer es (ASel (edual o) b') (LSess (SSel (edual o) b')) Ha2 (conj eq_refl eq_refl)) as [es' Hs'].
    destruct (act_offer e (ABra o) (LSess (SBra o b')) Ha1 eq_refl) as [e' He'].
    eexists _, _. split; [split; [eapply (p_act_choice C M s t (edual o) b'); [done|done|done|exact Hs'|]|done]|].
    + by rewrite edual_edual.
    + simpl. set_solver.
Qed.
