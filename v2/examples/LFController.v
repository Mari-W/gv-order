(** * The controller under ⊩ (stage C, proposal #20, plan §7)

      main = let (c, c′) = new_1 in
             let (a, a′) = new_0 in let (a, ⟨b, b′⟩) = new_κ a in
             let () = spawn (λu. let () = u in (force srv) ⟨⟨a′, b′⟩, c′⟩) in
             (force cli) ⟨⟨a, b⟩, c⟩
      cli  = !(f = λp. let (q, k) = p in let (a, b) = q in
                      let a = send ⟨∗, a⟩ in let (u, b) = recv b in
                      let () = u in (force f) ⟨⟨a, b⟩, k⟩)

    and srv the dual loop. The control channel c sits at Skip, an idle
    end on each side, and neither loop acts on it.

    The controller does not type under ⊩ at any finite N. The judgment
    ages every end that a step holds, idle or not. An end is no free type
    ([sess_not_free]), so aging by the cost c of a step lowers its credit
    by c and asks c ≤ credit ([sess_ages], rule [age_credit] of [tage]).
    Only an action on an end gives it the refill N back (E-Send, E-Recv),
    and no rule may act on k. Subtyping never raises a credit
    ([sess_sub_credit], rule [sub_sess]). The box type fixes the credit
    k0 of k at the parameter of the loop. The guard asks an action before
    the self call (rule [gl_tick_*]), and every action costs at least 1.
    So k reaches the self call at k0 − m with m ≥ 1 ([idle_credit_falls]),
    and the argument ⟨⟨a, b⟩, k⟩ of (force f) does not have the parameter
    type at k0. A parameter at credit ∞ is out of reach too, because
    E-New and E-NewAt give credit N, and an end received at ∞ needs a
    sender at ∞ + 1 = ∞.

    The semantic side already accepts idle ends (Q5 (b), fuel/Fuel.v: an
    idle end drops the "≥ 1" checks of F-Tick and of the hand-over). The
    gap is the static aging, which has no case for idle ends. No rule
    changes here. *)

From GV Require Export examples.LFTools.

Lemma sess_not_free S x : ¬ tfree (TSess S x).
Proof. inversion 1. Qed.

(** An end ages by its credit, idle or not. *)
Lemma sess_ages c S x a σ : tage c (TSess S x, a) σ → σ = (TSess S x, fsub a c) ∧ fle c a.
Proof.
  inversion 1; subst; [by exfalso; eapply sess_not_free|done].
Qed.

(** One step of cost 1 + m lowers an idle end at credit k to k − (1 + m). *)
Lemma idle_credit_falls m k x σ :
  tage (Some (S m)) (TSess SSkip x, Some k) σ → σ = (TSess SSkip x, Some (k - S m)) ∧ S m ≤ k.
Proof. intros [-> H]%sess_ages. done. Qed.

(** Subtyping never raises the credit of an end. *)
Lemma sess_sub_credit S x a T' a' : tsub (TSess S x) a T' a' → fle a' a.
Proof. inversion 1; subst; done. Qed.
