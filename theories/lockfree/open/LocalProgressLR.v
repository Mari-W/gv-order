(** * Open, outside the build: local progress from the closed live relation

    Stage 1 item 3 asked for local progress from [∀ n, LPrel n W ∅ T p].
    The statement below is false, so it stays here, outside _CoqProject.

    Reason. At Σ = ∅ the process relation compares no internal entry:
    ready_p W ∅ p only says that a stable process links or is terminated,
    and above_offered over tenv_of ∅ is vacuous. A counterexample, not
    mechanized:

      p = ({a, c}, {[+ recv a ; ping c ; pong c +]})

    where ping c = rec f. send ⟨∗, c⟩; f () and pong c = rec g. recv c; g ().
    The thread recv a is pending on a and no other thread mentions a, so
    its chain of waits is empty and it is never enabled: local progress
    fails at p itself. Every reachable state has a τ step (ping and pong
    alternate administrative steps and a message on c), so P-Stop and the
    readiness clause are vacuous, no session label exists because a and c
    are restricted, Q-Admin is well founded, and Q-Comm returns to the
    same finite set of states. So p is in LPrel n W ∅ T for every n.

    The repaired statement is [local_progress_ready]
    (theories/lockfree/LocalProgress.v): per-thread readiness in one
    strict world gives local progress. *)

From stdpp Require Import base relations.
From LRGV Require Import lockfree.Fair liveness.LiveAdequacy.

Lemma local_progress_LPrel_open W T p :
  (∀ n, LPrel n W ∅ T p) → ∀ q, pred_star p (erase q) → local_progress q.
Abort.
