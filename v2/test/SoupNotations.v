(** * The notations of stage S8 parse and print as written *)

From GV Require Import soup.LFAdequacy.

Check (λ N W n Σ T a, a ∈ S^{N,W} _ n⟦Σ ⊢ T⟧).
Check (λ W Σ p T, Σ ⊪_W p : T).
Check idle_dual.
Check lfsoup_step.
Check soup_no_tau_divergence.
Check lf_adequacy.
Check lf_thread_progress.
