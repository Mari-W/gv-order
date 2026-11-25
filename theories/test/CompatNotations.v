(** * The notations of stage S4 parse and print as written *)

From GV Require Import compat.SemTyped.

Check (λ W Θ Δ F t T, Θ ; Δ ⊨^F _ W t : T).
Check (λ W Θ Δ F t T, Θ ; Δ ⊫^F _ W t : T).
Check Erel_bind.
