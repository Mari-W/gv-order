(** * Notations of the language layer (stage S1, Appendix A)

    The ends c⁺ and c⁻ of a channel c and the partner end o‾ (the paper's
    ō, see the lexer deviations in docs/redesign/progress.md). Every
    later file of the language layer imports this module, and
    test/LangNotations.v checks that each notation parses and prints as
    written. *)

From GV Require Export lang.Syntax.

Notation "c ⁺" := (EPos c) (at level 1, left associativity, format "c ⁺").
Notation "c ⁻" := (ENeg c) (at level 1, left associativity, format "c ⁻").
Notation "o ‾" := (edual o) (at level 1, left associativity, format "o ‾").
