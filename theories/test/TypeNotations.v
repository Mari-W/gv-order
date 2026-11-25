(** * The notations of stage S2 parse and print as written

    Ends and points share the tokens ⁺ and ‾. An argument of type [cend]
    reads them as ends, one of type [point] as points. *)

From GV Require Import static.Typing.

Check (λ (c : chan) (x : point) (κ : field) (a m : fuel), (Chan c⁺, TSess SEnd (x⁺·κ)‾ a m)).
Check (λ (o : cend) (x : point), ((o‾)%cend, (x‾)%pt)).
Check (λ (W : world) (x y : point), W ⊢ x ≺ y⁺).
Check (λ W1 W2 : sworld, W1 ⊑ₛ W1 ⊔ W2).
Check (λ (W : sworld) (x y : point), W ⊢ₛ x ≺ y⁺).
Check (λ (S : sty) (x : point) (a m : fuel), S@x‾^a;m).
Check (λ W N Θ Γ Δ F e T c, Θ ; Γ ; Δ ⊢^F _{W,N} e : T ▷ c).
Check (λ W Θ Γ Δ F e T, Θ ; Γ ; Δ ⊢^F _ W e : T).
Check (λ W Σ p T, Σ ⊢_W p : T).
