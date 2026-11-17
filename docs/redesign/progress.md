# Rewrite progress

The rewrite of docs/redesign/proposal.md lives in v2/ (logical name `GV`).
The old development in theories/ stays untouched.

## Stages

| Stage | Content | Status |
|---|---|---|
| S1 | language | in progress |
| S2 | points, worlds, types | open |
| S3 | generic relation | open |
| S4 | generic compatibility | open |
| S5 | static fundamental theorems | open |
| S6 | fuel | open |
| S7 | cost judgment | open |
| S8 | soup and adequacy | open |
| S9 | lock-free composition and soundness | open |
| S10 | paper | open |

## Deviations

- Lexer (A.1). A subscript or superscript that is an identifier is set off
  by spaces, `V[κ]^W _ n⟦Θ ⊢ T⟧`, `Θ ; Γ ; Δ ⊢^F _ W t : T`,
  `ready _ W(Θ ∣ F, t)`. Rocq lexes `W_n` and `_n` as identifiers. LaTeX
  ignores the spaces, so the paper keeps the same string. Where the
  subscript follows a symbol, `⊢_W`, `⊨_W`, `⊫_W`, `⊪_W`, no space is
  needed.
- Lexer (A.1). The field x.κ is written `x·κ`. Rocq lexes `x.κ` as a
  qualified name.
- Lexer (A.1). The dual point x̄ and the dual end ō are written `x‾` and
  `o‾`. Rocq lexes `x̄` as one identifier.
- Lexer (A.1). The superscript of the soup keeps its braces,
  `S^{N,W} _ n⟦Σ ⊢ T⟧`, because LaTeX needs them for a two-letter
  superscript and Rocq lexes them.
- Lexer (A.1). `ready` is a keyword, so no Rocq name can be `ready`. The
  definitions stay `ready_t` and `ready_p` as A.2 says.

## Log

- S1.0. Lexer test v2/test/Lexer.v of every judgment and token of
  Appendix A over dummy carriers. All parse, and `make test` checks that
  all 26 print as written (v2/test/Lexer.expected).
