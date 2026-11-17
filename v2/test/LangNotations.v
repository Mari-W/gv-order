(** * The notations of v2/lang/Notations.v parse and print as written *)

From GV Require Import lang.Notations.

Check (λ c : chan, (c⁺, c⁻)).
Check (λ c : chan, (c⁺‾ = c⁻)).
Check (λ o : cend, o‾‾ = o).
Check (λ c : chan, Pair (Chan c⁺) (Chan c⁻)).
Check (λ c : chan, ELet (Chan c⁺) (Pair (Var 0) (Chan c⁻))).
