(** * The notations of stage S7 parse and print as written *)

From GV Require Import cost.CostFund.

Check (λ N Θ Δ e T c ϑ, Θ ; Δ ⊨^N e : T ▷ c ; ϑ).
Check cost_fundamental.
Check fsem_of_cost.
