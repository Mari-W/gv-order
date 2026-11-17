(** * The notations of stage S3 parse and print as written *)

From GV Require Import relation.Adequacy.

Check (λ κ n W Θ T v, v ∈ V[κ]^W _ n⟦Θ ⊢ T⟧).
Check (λ κ n W Θ T F e, e ∈ E[κ]^W _ n⟦Θ ⊢ T⟧^F).
Check (λ κ n W Σ T p, p ∈ P[κ]^W _ n⟦Σ ⊢ T⟧).
Check (λ n W Θ T v, v ∈ V^W _ n⟦Θ ⊢ T⟧).
Check (λ n W Θ T F e, e ∈ E^W _ n⟦Θ ⊢ T⟧^F).
Check (λ n W Σ T p, p ∈ P^W _ n⟦Σ ⊢ T⟧).
Check (λ n W Θ T v, v ∈ V[live]^W _ n⟦Θ ⊢ T⟧).
Check (λ W Θ F t, ready _ W(Θ ∣ F, t)).
Check (λ W Σ p, ready _ W(Σ, p)).
Check (λ W Σ p T, Σ ⊨_W p : T).
Check (λ W Σ p T, Σ ⊫_W p : T).
Check adequacy.
Check live_adequacy.
