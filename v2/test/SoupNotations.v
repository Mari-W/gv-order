(** * The notations of stages S8 and S9 parse and print as written *)

From GV Require Import soup.LFAdequacy soup.LFTyped.

Check (λ N W n Σ T a, a ∈ S^{N,W} _ n⟦Σ ⊢ T⟧).
Check (λ N W Σ p T, Σ ⊪^N _ W p : T).
Check idle_dual.
Check lfsoup_step.
Check soup_no_free_divergence.
Check lf_adequacy.
Check lf_thread_progress.
Check (λ N W Σ p T, Σ ⊩^N _ W p : T).
Check lf_fundamental_h.
Check lf_soundness_h.
