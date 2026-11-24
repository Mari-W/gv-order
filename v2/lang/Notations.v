(** * Notations of the language layer (stage S1, Appendix A)

    The ends c⁺ and c⁻ of a channel c and the dual end o‾ (the paper's
    ō, see the lexer deviations in docs/redesign/progress.md). Every
    later file of the language layer imports this module, and
    test/LangNotations.v checks that each notation parses and prints as
    written.

    The tokens ⁺ and ‾ are shared with the shift x⁺ and the dual x‾ of a
    point (types/Points.v). The end notations live in [cend_scope],
    bound to [cend], and the point notations in [point_scope], bound to
    [point]. An argument of type [cend] reads c⁺ as an end and an
    argument of type [point] reads x⁺ as a shift. Elsewhere [(o‾)%cend]
    and [(x‾)%pt] pick one. *)

From GV Require Export lang.Syntax.

Declare Scope cend_scope.
Delimit Scope cend_scope with cend.
Bind Scope cend_scope with cend.

Notation "c ⁺" := (EPos c) (at level 1, left associativity, format "c ⁺") : cend_scope.
Notation "c ⁻" := (ENeg c) (at level 1, left associativity, format "c ⁻") : cend_scope.
Notation "o ‾" := (edual o) (at level 1, left associativity, format "o ‾") : cend_scope.

Open Scope cend_scope.

(** Constants declared before the scope read their end arguments in it. *)
Arguments Chan o%_cend.
Arguments edual o%_cend.
Arguments ech o%_cend.
