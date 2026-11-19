(** * The notations of stage S2 parse and print as written

    Ends and points share the tokens ⁺ and ‾. An argument of type [cend]
    reads them as ends, one of type [point] as points. *)

From GV Require Import static.Typing.

Check (λ (c : chan) (x : point) (κ : field) (a : fuel), (Chan c⁺, TSess SEnd (x⁺·κ)‾ a)).
Check (λ (o : cend) (x : point), ((o‾)%cend, (x‾)%pt)).
Check (λ (W : world) (x y : point), W ⊢ x ≺ y⁺).
Check (λ W1 W2 : world, W1 ⊑ W1 ⊔ W2).
Check (λ (S : sty) (x : point) (a : fuel), S@x‾^a).
Check (λ W N Θ Γ Δ F e T c ϑ, Θ ; Γ ; Δ ⊢^F _{W,N} e : T ▷ c ; ϑ).
Check (λ W Θ Γ Δ F e T, Θ ; Γ ; Δ ⊢^F _ W e : T).
Check (λ W Σ p T, Σ ⊢_W p : T).
