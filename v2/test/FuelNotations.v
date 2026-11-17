(** * The notations of stage S6 parse and print as written *)

From GV Require Import fuel.FuelSub.

Check (λ N n σ c r Π φ tk e, e ∈ F^N _ n⟦σ ▷ c ; r⟧(Π, φ, tk)).
Check (λ N n σ Π φ v, v ∈ FV^N _ n⟦σ⟧(Π, φ)).
Check FuelE_bind.
Check FuelE_mono.
Check Vfuel_recount.
