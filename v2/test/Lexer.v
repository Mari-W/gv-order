(** * Lexer test of Appendix A (stage S1)

    Every token of docs/redesign/proposal.md Appendix A, declared over
    dummy carriers, parsed once and printed once. [make test] compares
    the printed forms with test/Lexer.expected. A token that Rocq cannot
    lex as written is replaced here and in the paper at once, and the
    replacement is listed under "Deviations" in
    docs/redesign/progress.md.

    Replacements found by this test.
    - A subscript or superscript that is an identifier is separated by
      spaces, [V[κ]^W _ n], because [W_n] and [_n] lex as identifiers.
      LaTeX ignores the spaces, so the paper can typeset the same string.
    - The field x.κ is written [x·κ], because [x.κ] lexes as a qualified
      name.
    - The dual point x̄ is written [x‾], because [x̄] lexes as an
      identifier.
    - The keyword [ready] is reserved. *)

From stdpp Require Import base.

Module Ends.
  (** The two ends c⁺ and c⁻ of a channel, and the dual end. *)
  Inductive cend (C : Type) := EPos (c : C) | ENeg (c : C).
  Arguments EPos {_} _. Arguments ENeg {_} _.
  Definition edual {C} (o : cend C) : cend C :=
    match o with EPos c => ENeg c | ENeg c => EPos c end.
  Notation "c ⁺" := (EPos c) (at level 1, left associativity, format "c ⁺").
  Notation "c ⁻" := (ENeg c) (at level 1, left associativity, format "c ⁻").
  Notation "o ‾" := (edual o) (at level 1, left associativity, format "o ‾").
  Check (λ c : nat, (c⁺, c⁻, (c⁺)‾)).
End Ends.

Section judgments.
  Context (A : Type).

  (** Points: the shift x⁺, the field x·κ, the dual x‾. *)
  Definition pshift (x : A) : A := x.
  Definition pfield (x κ : A) : A := x.
  Definition pdual (x : A) : A := x.
  Local Notation "x ⁺" := (pshift x) (at level 1, left associativity, format "x ⁺").
  Local Notation "x · κ" := (pfield x κ) (at level 2, left associativity, format "x · κ").
  Local Notation "x ‾" := (pdual x) (at level 1, left associativity, format "x ‾").
  Check (λ x κ : A, ((x⁺)·κ)‾).

  (** Session type at a point, S@x. *)
  Definition tat (S x : A) : A := S.
  Local Notation "S @ x" := (tat S x) (at level 20, format "S @ x").
  Check (λ S x : A, S@x).

  (** order fact, world extension, join *)
  Definition w_lt (W x y : A) : Prop := True.
  Local Notation "W ⊢ x ≺ y" := (w_lt W x y)
    (at level 74, x at level 60, y at level 60, format "W  ⊢  x  ≺  y").
  Check (λ W x y, W ⊢ x ≺ y).
  Definition wext (W W' : A) : Prop := True.
  Definition wjoin (W1 W2 : A) : A := W1.
  Local Notation "W ⊑ W'" := (wext W W') (at level 70).
  Local Notation "W1 ⊔ W2" := (wjoin W1 W2) (at level 50).
  Check (λ W W', W ⊑ W').
  Check (λ W1 W2, W1 ⊔ W2).

  (** readiness *)
  Definition ready_t (W Θ F t : A) : Prop := True.
  Definition ready_p (W Σ p : A) : Prop := True.
  Local Notation "'ready' '_' W ( Θ ∣ F , t )" := (ready_t W Θ F t)
    (at level 10, W at level 0, format "'ready'  '_'  W ( Θ  ∣  F ,  t )").
  Local Notation "'ready' '_' W ( Σ , p )" := (ready_p W Σ p)
    (at level 10, W at level 0, format "'ready'  '_'  W ( Σ ,  p )").
  Check (λ W Θ F t, ready _ W(Θ ∣ F, t)).
  Check (λ W Σ p, ready _ W(Σ, p)).

  (** static term and process typing *)
  Definition typed (Θ Γ Δ F W t T : A) : Prop := True.
  Local Notation "Θ ; Γ ; Δ ⊢^ F '_' W t : T" := (typed Θ Γ Δ F W t T)
    (at level 74, Γ at level 60, Δ at level 60, F at level 0, W at level 0,
     t at level 60, T at level 60,
     format "Θ  ;  Γ  ;  Δ  ⊢^ F  '_'  W  t  :  T").
  Check (λ Θ Γ Δ F W t T, Θ ; Γ ; Δ ⊢^F _ W t : T).
  Definition ptyped (Σ W p T : A) : Prop := True.
  Local Notation "Σ ⊢_ W p : T" := (ptyped Σ W p T)
    (at level 74, W at level 0, p at level 60, T at level 60,
     format "Σ  ⊢_ W  p  :  T").
  Check (λ Σ W p T, Σ ⊢_W p : T).

  (** the merged judgment of decision Q11, two subscripts in braces *)
  Definition mtyped (W N Θ Γ Δ F e T a c ϑ : A) : Prop := True.
  Local Notation "Θ ; Γ ; Δ ⊢^ F '_{' W , N '}' e : T ^ a ▷ c ; ϑ" := (mtyped W N Θ Γ Δ F e T a c ϑ)
    (at level 74, Γ at level 60, Δ at level 60, F at level 0, W at level 0, N at level 0,
     e at level 60, T at level 29, a at level 0, c at level 60, ϑ at level 60,
     format "Θ  ;  Γ  ;  Δ  ⊢^ F  '_{' W , N '}'  e  :  T ^ a  ▷  c  ;  ϑ").
  Check (λ W N Θ Γ Δ F e T a c ϑ, Θ ; Γ ; Δ ⊢^F _{W,N} e : T^a ▷ c ; ϑ).

  (** cost typing and lock-free process typing *)
  Definition ctyped (Θ Γ N e σ c t : A) : Prop := True.
  Local Notation "Θ ; Γ ⊩^ N e : σ ▷ c ; t" := (ctyped Θ Γ N e σ c t)
    (at level 74, Γ at level 60, N at level 0, e at level 60, σ at level 60,
     c at level 60, t at level 60,
     format "Θ  ;  Γ  ⊩^ N  e  :  σ  ▷  c  ;  t").
  Check (λ Θ Γ N e σ c t, Θ ; Γ ⊩^N e : σ ▷ c ; t).
  Definition lfptyped (Σ N W p T : A) : Prop := True.
  Local Notation "Σ ⊩^ N '_' W p : T" := (lfptyped Σ N W p T)
    (at level 74, N at level 0, W at level 0, p at level 60, T at level 60,
     format "Σ  ⊩^ N  '_'  W  p  :  T").
  Check (λ Σ N W p T, Σ ⊩^N _ W p : T).

  (** the relations, [κ] an index in brackets *)
  Definition Vrel (κ n W Θ T v : A) : Prop := True.
  Definition Erel (κ n W Θ T F e : A) : Prop := True.
  Definition Prel (κ n W Σ T p : A) : Prop := True.
  Local Notation "v ∈ V[ κ ]^ W '_' n ⟦ Θ ⊢ T ⟧" := (Vrel κ n W Θ T v)
    (at level 70, W at level 0, n at level 0, Θ at level 60,
     format "v  ∈  V[ κ ]^ W  '_'  n ⟦ Θ  ⊢  T ⟧").
  Local Notation "e ∈ E[ κ ]^ W '_' n ⟦ Θ ⊢ T ⟧^ F" := (Erel κ n W Θ T F e)
    (at level 70, W at level 0, n at level 0, F at level 0, Θ at level 60,
     format "e  ∈  E[ κ ]^ W  '_'  n ⟦ Θ  ⊢  T ⟧^ F").
  Local Notation "p ∈ P[ κ ]^ W '_' n ⟦ Σ ⊢ T ⟧" := (Prel κ n W Σ T p)
    (at level 70, W at level 0, n at level 0, Σ at level 60,
     format "p  ∈  P[ κ ]^ W  '_'  n ⟦ Σ  ⊢  T ⟧").
  Check (λ κ n W Θ T v, v ∈ V[κ]^W _ n⟦Θ ⊢ T⟧).
  Check (λ κ n W Θ T F e, e ∈ E[κ]^W _ n⟦Θ ⊢ T⟧^F).
  Check (λ κ n W Σ T p, p ∈ P[κ]^W _ n⟦Σ ⊢ T⟧).
  (** κ_DF omitted *)
  Context (DF : A).
  Local Notation "v ∈ V^ W '_' n ⟦ Θ ⊢ T ⟧" := (Vrel DF n W Θ T v)
    (at level 70, W at level 0, n at level 0, Θ at level 60,
     format "v  ∈  V^ W  '_'  n ⟦ Θ  ⊢  T ⟧").
  Check (λ n W Θ T v, v ∈ V^W _ n⟦Θ ⊢ T⟧).

  (** semantic term and process typing, three entailments *)
  Definition sem_typed (κ Θ Δ F W t T : A) : Prop := True.
  Context (L : A).
  Local Notation "Θ ; Δ ⊨^ F '_' W t : T" := (sem_typed DF Θ Δ F W t T)
    (at level 74, Δ at level 60, F at level 0, W at level 0, t at level 60,
     T at level 60, format "Θ  ;  Δ  ⊨^ F  '_'  W  t  :  T").
  Local Notation "Θ ; Δ ⊫^ F '_' W t : T" := (sem_typed L Θ Δ F W t T)
    (at level 74, Δ at level 60, F at level 0, W at level 0, t at level 60,
     T at level 60, format "Θ  ;  Δ  ⊫^ F  '_'  W  t  :  T").
  Check (λ Θ Δ F W t T, Θ ; Δ ⊨^F _ W t : T).
  Check (λ Θ Δ F W t T, Θ ; Δ ⊫^F _ W t : T).
  Definition sem_ptyped (κ Σ W p T : A) : Prop := True.
  Definition lf_sem (Σ W p T : A) : Prop := True.
  Local Notation "Σ ⊨_ W p : T" := (sem_ptyped DF Σ W p T)
    (at level 74, W at level 0, p at level 60, T at level 60,
     format "Σ  ⊨_ W  p  :  T").
  Local Notation "Σ ⊫_ W p : T" := (sem_ptyped L Σ W p T)
    (at level 74, W at level 0, p at level 60, T at level 60,
     format "Σ  ⊫_ W  p  :  T").
  Local Notation "Σ ⊪_ W p : T" := (lf_sem Σ W p T)
    (at level 74, W at level 0, p at level 60, T at level 60,
     format "Σ  ⊪_ W  p  :  T").
  Check (λ Σ W p T, Σ ⊨_W p : T).
  Check (λ Σ W p T, Σ ⊫_W p : T).
  Check (λ Σ W p T, Σ ⊪_W p : T).

  (** fuel *)
  Definition FuelE (N n σ c r Π φ tk e : A) : Prop := True.
  Definition Vfuel (N n σ Π φ v : A) : Prop := True.
  Local Notation "e ∈ F^ N '_' n ⟦ σ ▷ c ; r ⟧( Π , φ , tk )" := (FuelE N n σ c r Π φ tk e)
    (at level 70, N at level 0, n at level 0, σ at level 60, c at level 60,
     format "e  ∈  F^ N  '_'  n ⟦ σ  ▷  c  ;  r ⟧( Π ,  φ ,  tk )").
  Local Notation "v ∈ FV^ N '_' n ⟦ σ ⟧( Π , φ )" := (Vfuel N n σ Π φ v)
    (at level 70, N at level 0, n at level 0, σ at level 60,
     format "v  ∈  FV^ N  '_'  n ⟦ σ ⟧( Π ,  φ )").
  Check (λ N n σ c r Π φ tk e, e ∈ F^N _ n⟦σ ▷ c ; r⟧(Π, φ, tk)).
  Check (λ N n σ Π φ v, v ∈ FV^N _ n⟦σ⟧(Π, φ)).

  (** semantic cost typing *)
  Definition csem (Θ Γ N e σ c t : A) : Prop := True.
  Local Notation "Θ ; Γ ⊨^ N e : σ ▷ c ; t" := (csem Θ Γ N e σ c t)
    (at level 74, Γ at level 60, N at level 0, e at level 60, σ at level 60,
     c at level 60, t at level 60,
     format "Θ  ;  Γ  ⊨^ N  e  :  σ  ▷  c  ;  t").
  Check (λ Θ Γ N e σ c t, Θ ; Γ ⊨^N e : σ ▷ c ; t).

  (** soup, the superscript N,W in braces *)
  Definition Soup (N W n Σ T a : A) : Prop := True.
  Local Notation "a ∈ S^{ N , W } '_' n ⟦ Σ ⊢ T ⟧" := (Soup N W n Σ T a)
    (at level 70, n at level 0, Σ at level 60,
     format "a  ∈  S^{ N , W }  '_'  n ⟦ Σ  ⊢  T ⟧").
  Check (λ N W n Σ T a, a ∈ S^{N,W} _ n⟦Σ ⊢ T⟧).

  (** names of A.2 and A.3 without notation, as plain identifiers *)
  Definition wfworld (W : A) : Prop := True.
  Definition strict (W : A) : Prop := True.
  Definition tfree (T : A) : Prop := True.
  Definition deadlock_free (p : A) : Prop := True.
  Definition no_tau_divergence (p : A) : Prop := True.
  Definition lock_free (p : A) : Prop := True.
  Check (λ W Σ p T, strict W ∧ wfworld W ∧ Σ ⊪_W p : T → lock_free p).
  Check (λ Σ W p T, Σ ⊫_W p : T → deadlock_free p ∧ no_tau_divergence p).
End judgments.
