(** * The guard Λ ⊢▷ t and its process form ⊢▷ p parse and print as written *)

From GV Require Import static.FundamentalProc.

Check (λ L t, L ⊢▷ t).
Check (λ t, ∅ ⊢▷ t).
Check (λ p, ⊢▷ p).
Check gl_box.
Check gl_tick_app.
Check live_fundamental.
Check live_soundness_h.
