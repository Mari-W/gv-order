# GV♯ Rocq development — audit summary

A map of the top-level definitions and theorems of the Rocq/stdpp formalization,
quoted **verbatim** from the sources, with cross-references to the paper
(*A Logical-Relations Approach to Compositional Deadlock Freedom for Session Types*).
Statements only; proofs are in the files.

**Toolchain**: Rocq 9.1 + stdpp (opam switch `lrgv`). Build with
`opam exec --switch=lrgv -- make`.

**Global audit result**: no `Admitted`/`Axiom` anywhere;
`Print Assumptions typed_deadlock_free` = `Classical_Prop.classic` only
(used in Lemma 3.5 / `Prel_safe` and in `connect_progress`).

**Extension (branch `sums`)**: binary sums `T ⊕ U` with `Inj1`/`Inj2`/`Case`
(one-binder branches) through every layer — syntax, β-rule `T-Act-Case`,
`E-Inl`/`E-Inr`/`E-Case` typing, the `TSum` case of `V` (a same-index
structural disjunction), and the fundamental theorem. No new labels, so the
process layer and the compositionality proofs are untouched.

| File | Paper content |
|---|---|
| `theories/Syntax.v` | Fig. 1 syntax, substitution, closedness, free channels |
| `theories/Semantics.v` | Fig. 2 labelled term semantics, Def. 3.1 (irred) |
| `theories/Processes.v` | Fig. 3 process LTS, Defs. 2.4–2.6 |
| `theories/Types.v` | §2.2 types, duality, session environments, constant signatures |
| `theories/Typing.v` | Fig. 4 term typing, process typing |
| `theories/LogRel.v` | Fig. 5 logical relation, Defs. 3.1–3.3, Lemmas 3.4/3.5/3.7, Thm 3.6, Thm 3.11 |
| `theories/Compositionality.v` | Lemmas 3.8–3.10, Thms 3.12/3.13, deadlock-freedom corollary |
| `theories/Examples.v` | Ex. 2.1 (`sync`), Ex. 2.8 (`blocked`), Ex. 2.11 (typing of `sync`) |

Deviations from the draft are marked **[Δ]** inline and collected in the
[last section](#deviations-from-the-draft).

---

## 1. Syntax (Fig. 1) — `Syntax.v`

Term variables are de Bruijn indices; channels are names (`chan := string`).
Single `expr` inductive with an `is_val` predicate (heap_lang style).

```coq
Inductive konst := KFork | KRecv | KSend | KClos.

Inductive expr :=
  | Var (x : nat)
  | EUnit                          (* the unit value ∗ *)
  | Konst (k : konst)
  | Chan (c : chan)
  | Lam (e : expr)                 (* λa.e — binds 1 *)
  | App (e1 e2 : expr)
  | Pair (e1 e2 : expr)            (* ⟨e1,e2⟩ *)
  | LetU (e1 e2 : expr)            (* let ∗ = e1 in e2 *)
  | LetP (e1 e2 : expr)            (* let ⟨a,b⟩ = e1 in e2 — binds 2 in e2:
                                      index 1 = a, index 0 = b *)
  | Inj1 (e : expr)                (* left injection *)
  | Inj2 (e : expr)                (* right injection *)
  | Case (e e1 e2 : expr).         (* case e (a.e1) (a.e2) — each branch
                                      binds 1: index 0 = the payload *)

Fixpoint is_val (e : expr) : bool :=
  match e with
  | EUnit | Konst _ | Chan _ | Lam _ => true
  | Pair e1 e2 => is_val e1 && is_val e2
  | Inj1 e | Inj2 e => is_val e
  | _ => false
  end.
```

Parallel substitution `subst : (nat → expr) → expr → expr` with
`subst1`/`subst2` for the β-redexes; `closed_at`/`closed`; free channels:

```coq
Fixpoint fchans (e : expr) : gset chan :=
  match e with
  | Var _ | EUnit | Konst _ => ∅
  | Chan c => {[c]}
  | Lam e | Inj1 e | Inj2 e => fchans e
  | App e1 e2 | Pair e1 e2 | LetU e1 e2 | LetP e1 e2 => fchans e1 ∪ fchans e2
  | Case e e1 e2 => fchans e ∪ fchans e1 ∪ fchans e2
  end.
```

Also: `allfv`/`freevar` (free-variable predicates, used by the semantic
judgment's well-formedness conjuncts, see §7).

## 2. Labelled term semantics (Fig. 2) — `Semantics.v`

```coq
Inductive slabel :=
  | SRecv (c : chan) (v : expr)    (* c?v : receiving value v on c *)
  | SSend (c : chan) (v : expr)    (* c!v : sending value v on c *)
  | SClos (c : chan).              (* c!  : closing c *)

Inductive tlabel :=
  | LBeta
  | LSess (σ : slabel)
  | LFork (c : chan) (v : expr).   (* (νc)v : fork of thread v on new c *)

Definition subj (σ : slabel) : chan :=
  match σ with SRecv c _ | SSend c _ | SClos c => c end.

Definition sentc (σ : slabel) : gset chan :=
  match σ with SSend _ v => fchans v | _ => ∅ end.
```

Head steps (T-Act-App / Let* / LetPair / Fork / Recv / Send / Close).
**[Δ] `HeadRecv` receives *any* value, not only closed ones** — a receive step
must exist for every value a sender might emit, or the process-level
synchronization in P-Act-Msg could fail against the LR's low-index λ-values:

```coq
Inductive head_step : expr → tlabel → expr → Prop :=
  | HeadApp e v :                                       (* T-Act-App *)
      is_val v →
      head_step (App (Lam e) v) LBeta (subst1 v e)
  | HeadLetU e :                                        (* T-Act-Let* *)
      head_step (LetU EUnit e) LBeta e
  | HeadLetP u v e :                                    (* T-Act-LetPair *)
      is_val u → is_val v →
      head_step (LetP (Pair u v) e) LBeta (subst2 u v e)
  | HeadFork v c :                                      (* T-Act-Fork *)
      is_val v →
      head_step (App EFork v) (LFork c v) (Chan c)
  | HeadRecv c v :                                      (* T-Act-Recv *)
      is_val v →
      head_step (App ERecv (Chan c)) (LSess (SRecv c v)) (Pair v (Chan c))
  | HeadSend v c :                                      (* T-Act-Send *)
      is_val v →
      head_step (App ESend (Pair v (Chan c))) (LSess (SSend c v)) (Chan c)
  | HeadClos c :                                        (* T-Act-Close *)
      head_step (App EClos (Chan c)) (LSess (SClos c)) EUnit
  | HeadCase1 v e1 e2 :                                 (* T-Act-Case-Inl *)
      is_val v →
      head_step (Case (Inj1 v) e1 e2) LBeta (subst1 v e1)
  | HeadCase2 v e1 e2 :                                 (* T-Act-Case-Inr *)
      is_val v →
      head_step (Case (Inj2 v) e1 e2) LBeta (subst1 v e2).
```

Context closure (T-Act-Ctx) is by congruence rules rather than explicit
evaluation contexts (`tstep`, 10 rules: `TStepHead`, `TStepAppL/R`,
`TStepPairL/R`, `TStepLetU`, `TStepLetP`, `TStepInj1/2`, `TStepCase`,
with `is_val` side conditions for the right-of-value frames). A separate one-frame presentation
(`frame`/`fill_frame`) with `tstep_fill`/`tstep_fill_inv` is derived for the
bind lemma.

```coq
Definition reduction (e e' : expr) : Prop := tstep e LBeta e'.
Definition irred (e : expr) : Prop := ∀ α e', ¬ tstep e α e'.      (* Def. 3.1 *)
```

## 3. Process LTS (Fig. 3) and deadlock freedom (Defs. 2.4–2.6) — `Processes.v`

```coq
Definition proc : Type := gset chan * gmultiset expr.

Inductive plabel := PTau | PSess (σ : slabel).

Definition echans (E : gmultiset expr) : gset chan :=
  ⋃ (fchans <$> elements E).
```

**[Δ]** In `PStepFork` the new channel is required to be *globally* fresh
(not restricted, not free in any thread) — implicit "new name"
well-formedness in the paper. P-Act-Msg/Close write the paper's `C ∪ {c}`
source as membership `c ∈ C`.

```coq
Inductive proc_step : proc → plabel → proc → Prop :=
  | PStepSession C E e σ e' :                          (* P-Act-Session *)
      tstep e (LSess σ) e' →
      subj σ ∉ C →
      proc_step (C, E ⊎ {[+ e +]}) (PSess σ)
                (C ∖ sentc σ, E ⊎ {[+ e' +]})
  | PStepBeta C E e e' :                               (* P-Act-Beta *)
      tstep e LBeta e' →
      proc_step (C, E ⊎ {[+ e +]}) PTau (C, E ⊎ {[+ e' +]})
  | PStepFork C E e c v e' :                           (* P-Act-Fork *)
      tstep e (LFork c v) e' →
      c ∉ C → c ∉ echans E → c ∉ fchans e →
      proc_step (C, E ⊎ {[+ e +]}) PTau
                (C ∪ {[c]}, E ⊎ {[+ e' +]} ⊎ {[+ App v (Chan c) +]})
  | PStepMsg C E c v e e' f f' :                       (* P-Act-Msg *)
      tstep e (LSess (SSend c v)) e' →
      tstep f (LSess (SRecv c v)) f' →
      c ∈ C →
      proc_step (C, E ⊎ {[+ e +]} ⊎ {[+ f +]}) PTau
                (C, E ⊎ {[+ e' +]} ⊎ {[+ f' +]})
  | PStepClose C E c e e' f f' :                       (* P-Act-Close *)
      tstep e (LSess (SClos c)) e' →
      tstep f (LSess (SClos c)) f' →
      c ∈ C →
      proc_step (C, E ⊎ {[+ e +]} ⊎ {[+ f +]}) PTau
                (C ∖ {[c]}, E ⊎ {[+ e' +]} ⊎ {[+ f' +]}).

Definition preduction (p p' : proc) : Prop := proc_step p PTau p'.
Definition pirred (p : proc) : Prop := ∀ π p', ¬ proc_step p π p'.  (* Def. 3.1 *)

(* Def. 2.4 *)
Definition terminated (p : proc) : Prop :=
  ∃ v E, p = (∅, {[+ v +]} ⊎ E) ∧ is_val v ∧ (∀ e, e ∈ E → e = EUnit).

(* Def. 2.5 *)
Definition safe (p : proc) : Prop :=
  terminated p ∨ ∃ p', preduction p p'.

(* Def. 2.6 *)
Definition deadlock_free (p : proc) : Prop :=
  ∀ p', pred_star p p' → safe p'.
```

Also `internalize_comm` — **[Δ]** the derivable direction of the draft's
Lemma 2.3: the draft's Eq (9) subtracts `sentc` from `C`, which is *not*
derivable from Fig. 3's P-Act-Msg (which keeps `C`); the formalized statement
keeps `C`.

## 4. Types, duality, environments (§2.2) — `Types.v`

```coq
Inductive ty :=
  | TUnit                          (* ∗ *)
  | TLolli (T U : ty)              (* T ⊸ U *)
  | TProd (T U : ty)               (* T ⊗ U *)
  | TSum (T U : ty)                (* T ⊕ U *)
  | TSess (S : sty)
with sty :=
  | SRcv (T : ty) (S : sty)        (* ?T.S *)
  | SSnd (T : ty) (S : sty)        (* !T.S *)
  | SEnd.                          (* Close *)

Fixpoint dual (s : sty) : sty :=
  match s with
  | SRcv T s' => SSnd T (dual s')
  | SSnd T s' => SRcv T (dual s')
  | SEnd => SEnd
  end.

Lemma dual_involutive s : dual (dual s) = s.

Inductive prim : ty → Prop :=
  | prim_unit : prim TUnit
  | prim_prod U V : prim U → prim V → prim (TProd U V)
  | prim_sum U V : prim U → prim V → prim (TSum U V).

Notation senv := (gmap chan sty).

Definition senv_split (Σ Σ1 Σ2 : senv) : Prop :=
  Σ = Σ1 ∪ Σ2 ∧ Σ1 ##ₘ Σ2.
```

Type-indexed constant signatures (Fig. 4's `fork : (S ⊸ ∗) ⊸ dual S`, etc.):

```coq
Inductive konst_ty : konst → ty → Prop :=
  | KTFork S :
      konst_ty KFork (TLolli (TLolli (TSess S) TUnit) (TSess (dual S)))
  | KTRecv T S :
      konst_ty KRecv (TLolli (TSess (SRcv T S)) (TProd T (TSess S)))
  | KTSend T S :
      konst_ty KSend (TLolli (TProd T (TSess (SSnd T S))) (TSess S))
  | KTClos :
      konst_ty KClos (TLolli (TSess SEnd) TUnit).
```

## 5. Syntactic typing (Fig. 4) — `Typing.v`

The linear variable environment is a "resource vector"
`lenv := list (option ty)` indexed by de Bruijn index, with pointwise
splitting `lenv_split` (each `Some` goes to exactly one side), emptiness
`lenv_empty`, and single-availability `lenv_only Δ x T` (exactly one `Some`,
at `x`, of type `T` — this is how the linear axiom rule reads).

```coq
Inductive typed : senv → lenv → expr → ty → Prop :=
  | typed_unit Δ :                                     (* E-Unit *)
      lenv_empty Δ → typed ∅ Δ EUnit TUnit
  | typed_konst Δ k T :                                (* E-Const *)
      lenv_empty Δ → konst_ty k T → typed ∅ Δ (Konst k) T
  | typed_var Δ x T :                                  (* E-LVar *)
      lenv_only Δ x T → typed ∅ Δ (Var x) T
  | typed_chan Δ c s :                                 (* E-Ch *)
      lenv_empty Δ → typed {[c := s]} Δ (Chan c) (TSess s)
  | typed_lam Σ Δ e T U :                              (* E-Abs *)
      typed Σ (Some T :: Δ) e U →
      typed Σ Δ (Lam e) (TLolli T U)
  | typed_app Σ Σ1 Σ2 Δ Δ1 Δ2 e1 e2 T U :             (* E-App *)
      senv_split Σ Σ1 Σ2 → lenv_split Δ Δ1 Δ2 →
      typed Σ1 Δ1 e1 (TLolli T U) → typed Σ2 Δ2 e2 T →
      typed Σ Δ (App e1 e2) U
  | typed_pair Σ Σ1 Σ2 Δ Δ1 Δ2 e1 e2 T U :            (* E-Pair *)
      senv_split Σ Σ1 Σ2 → lenv_split Δ Δ1 Δ2 →
      typed Σ1 Δ1 e1 T → typed Σ2 Δ2 e2 U →
      typed Σ Δ (Pair e1 e2) (TProd T U)
  | typed_letu Σ Σ1 Σ2 Δ Δ1 Δ2 e1 e2 T :              (* E-Let* *)
      senv_split Σ Σ1 Σ2 → lenv_split Δ Δ1 Δ2 →
      typed Σ1 Δ1 e1 TUnit → typed Σ2 Δ2 e2 T →
      typed Σ Δ (LetU e1 e2) T
  | typed_letp Σ Σ1 Σ2 Δ Δ1 Δ2 e1 e2 U V T :          (* E-LetPair *)
      senv_split Σ Σ1 Σ2 → lenv_split Δ Δ1 Δ2 →
      typed Σ1 Δ1 e1 (TProd U V) →
      typed Σ2 (Some V :: Some U :: Δ2) e2 T →
      typed Σ Δ (LetP e1 e2) T
  | typed_inj1 Σ Δ e T U :                             (* E-Inl *)
      typed Σ Δ e T →
      typed Σ Δ (Inj1 e) (TSum T U)
  | typed_inj2 Σ Δ e T U :                             (* E-Inr *)
      typed Σ Δ e U →
      typed Σ Δ (Inj2 e) (TSum T U)
  | typed_case Σ Σ1 Σ2 Δ Δ1 Δ2 e e1 e2 U V T :        (* E-Case *)
      senv_split Σ Σ1 Σ2 → lenv_split Δ Δ1 Δ2 →
      typed Σ1 Δ1 e (TSum U V) →
      typed Σ2 (Some U :: Δ2) e1 T →
      typed Σ2 (Some V :: Δ2) e2 T →
      typed Σ Δ (Case e e1 e2) T.
```

Process typing. **[Δ]** P-Independent and P-Connect carry the paper's
implicit "Σ and C do not share channels" as explicit cross-disjointness
premises (`C1 ## dom Σ2`, `C2 ## dom Σ1`); the *self*-disjointness
(`C ## dom Σ`) is derived as the invariant `ptyped_chan_disj`.

```coq
Inductive ptyped : senv → proc → ty → Prop :=
  | ptyped_term Σ e T :                                (* P-Term *)
      prim T →
      typed Σ [] e T →
      ptyped Σ (∅, {[+ e +]}) T
  | ptyped_independent Σ Σ1 Σ2 C1 E1 C2 E2 T :        (* P-Independent *)
      senv_split Σ Σ1 Σ2 →
      C1 ## C2 → C1 ## dom Σ2 → C2 ## dom Σ1 →
      ptyped Σ1 (C1, E1) T →
      ptyped Σ2 (C2, E2) TUnit →
      ptyped Σ (C1 ∪ C2, E1 ⊎ E2) T
  | ptyped_connect Σ Σ1 Σ2 c s C1 E1 C2 E2 T :        (* P-Connect *)
      senv_split Σ Σ1 Σ2 →
      c ∉ dom Σ1 → c ∉ dom Σ2 →
      C1 ## C2 → c ∉ C1 → c ∉ C2 →
      C1 ## dom Σ2 → C2 ## dom Σ1 →
      ptyped (<[c := s]> Σ1) (C1, E1) T →
      ptyped (<[c := dual s]> Σ2) (C2, E2) TUnit →
      ptyped Σ (C1 ∪ C2 ∪ {[c]}, E1 ⊎ E2) T.

Lemma ptyped_prim Σ p T : ptyped Σ p T → prim T.
Lemma ptyped_chan_disj Σ p T : ptyped Σ p T → p.1 ## dom Σ.
```

**[Δ]** `prim T` is a premise of P-Term (possible thread return types); the
draft states primitivity for Lemmas 3.8–3.10 but not in the syntactic
P-rules — it is recovered via `ptyped_prim` in Theorem 3.13.

## 6. The logical relation (Fig. 5) — `LogRel.v`

### 6.1 Step-index encoding

The three layers at one index form a `level` record
(`lV`/`lE`/`lP`); `Vdef`/`Edef`/`Pdef` build level *n* given the family
`below : nat → level` of all lower levels (course-of-values recursion — `V_n`
mentions `E_j`, `j < n`, contravariantly; `E_n`/`P_n` mention `V_n` at the
same index and everything below). The family is a structural fixpoint, and
all later proofs go through the interface lemmas only:

```coq
Definition mk_level (below : nat → level) (n : nat) : level :=
  {| lV := Vdef below n;
     lE := Edef below (Vdef below n) n;
     lP := Pdef below (Vdef below n) n |}.

Fixpoint fam (n : nat) : nat → level :=
  match n with
  | 0 => λ _, dummy_level
  | S n' => λ j, if decide (j < n') then fam n' j else mk_level (fam n') n'
  end.

Definition lvl (n : nat) : level := fam (S n) n.

Definition Vrel (n : nat) : senv → ty → expr → Prop := lV (lvl n).
Definition Erel (n : nat) : senv → ty → expr → Prop := lE (lvl n).
Definition Prel (n : nat) : senv → ty → proc → Prop := lP (lvl n).

Lemma lvl_eq n : lvl n = mk_level (fam n) n.
Lemma fam_lvl n j : j < n → fam n j = lvl j.
```

Unfolding characterizations used everywhere: `Vrel_unit_iff` /
`Vrel_sess_iff` / `Vrel_prod_iff` / `Vrel_lolli_iff`, `Erel_S_iff` (via
`Ecase`), `Prel_S_iff` / `Prel_S_intro` / `Prel_S_step` (via `Pcase`,
which is `Pdef`'s per-label match reified as a definition);
`Erel_0`/`Prel_0` (index 0 is trivial).

### 6.2 Value relation `V_n⟦Σ ⊢ T⟧`

**[Δ]** The ⊸ case additionally requires `fchans eb = dom Σ` (the
abstraction owns exactly its channels) — needed for CONNECT: a value sent to
the environment must not mention channels restricted by an independent
component. For all other value forms this coverage holds by construction
(`Vrel_fchans : Vrel n Σ T v → fchans v = dom Σ`).

```coq
Fixpoint Vdef (below : nat → level) (n : nat)
    (Σ : senv) (T : ty) (v : expr) {struct T} : Prop :=
  match T with
  | TUnit => Σ = ∅ ∧ v = EUnit
  | TSess s => ∃ c, v = Chan c ∧ Σ = {[c := s]}
  | TLolli T1 U =>
      (∃ eb, v = Lam eb ∧ fchans eb = dom Σ ∧
         ∀ j Σ' w, j < n → Σ' ##ₘ Σ →
           lV (below j) Σ' T1 w →
           lE (below j) (Σ ∪ Σ') U (subst1 w eb))
      ∨ (∃ k, v = Konst k ∧ Σ = ∅ ∧ konst_ty k (TLolli T1 U))
  | TProd T1 U =>
      ∃ v1 v2 Σ1 Σ2, v = Pair v1 v2 ∧ senv_split Σ Σ1 Σ2 ∧
        Vdef below n Σ1 T1 v1 ∧ Vdef below n Σ2 U v2
  | TSum T1 U =>
      (∃ v', v = Inj1 v' ∧ Vdef below n Σ T1 v')
      ∨ (∃ v', v = Inj2 v' ∧ Vdef below n Σ U v')
  end.
```

### 6.3 Term relation `E_n⟦Σ ⊢ T⟧`

**[Δ]** The fork case (case 2) is guarded by freshness `c ∉ dom Σ`: fork
labels exist for *every* name, but only fresh ones are process-level enabled
— without the guard no forking term could inhabit E.
**[Δ]** The input case (case 3) quantifies the received value at every
`j ≤ n'`, not just `n'` (needed for CONNECT, where the peer's value is one
index lower).

```coq
Definition Edef (below : nat → level) (Vn : senv → ty → expr → Prop)
    (n : nat) (Σ : senv) (T : ty) (e : expr) : Prop :=
  match n with
  | 0 => True
  | S n' =>
      (irred e → Vn Σ T e) ∧
      (∀ α e', tstep e α e' →
        match α with
        | LBeta =>                                     (* case 1 *)
            lE (below n') Σ T e'
        | LFork c w =>                                 (* case 2 *)
            c ∉ dom Σ →
            ∃ Σ1 Σ2 s,
              senv_split Σ Σ1 Σ2 ∧
              Vn Σ1 (TLolli (TSess s) TUnit) w ∧
              lE (below n') (<[c := dual s]> Σ2) T e'
        | LSess (SRecv c w) =>                         (* case 3 *)
            ∃ Σ1 U s,
              Σ = <[c := SRcv U s]> Σ1 ∧ c ∉ dom Σ1 ∧
              ∀ j Σ2, j ≤ n' → Σ2 ##ₘ Σ1 → c ∉ dom Σ2 →
                lV (below j) Σ2 U w →
                lE (below j) (<[c := s]> (Σ1 ∪ Σ2)) T e'
        | LSess (SSend c w) =>                         (* case 4 *)
            ∃ Σ1 Σ2 U s,
              Σ = <[c := SSnd U s]> (Σ1 ∪ Σ2) ∧
              Σ1 ##ₘ Σ2 ∧ c ∉ dom Σ1 ∧ c ∉ dom Σ2 ∧
              Vn Σ2 U w ∧
              lE (below n') (<[c := s]> Σ1) T e'
        | LSess (SClos c) =>                           (* case 5 *)
            ∃ Σ1, Σ = <[c := SEnd]> Σ1 ∧ c ∉ dom Σ1 ∧
              lE (below n') Σ1 T e'
        end)
  end.
```

### 6.4 Escaped-channel owner families

**[Δ]** The process relation's output case is an *iterated* form of Fig. 5's
case 3: instead of one process owning all escaped channels, one independent
piece per escaped channel (a single piece owning two escaped channels could
create a cyclic dependency through the environment; the finer decomposition
is also what CONNECT needs when a message carries several restricted
channels).

```coq
Definition ty_one_of (A B C : ty) : Prop :=
  (A = C ∧ B = TUnit) ∨ (A = TUnit ∧ B = C).

Inductive Powners (P : senv → ty → proc → Prop)
    : gmap chan sty → senv → ty → proc → Prop :=
  | Powners_nil : Powners P ∅ ∅ TUnit (∅, ∅)
  | Powners_cons σ d s Σd Σr Td Tr Tt Cd Ed Cr Er :
      σ !! d = None →
      d ∉ dom Σd → d ∉ dom Σr → d ∉ Cd → d ∉ Cr →
      dom σ ## dom Σd → dom σ ## Cd →
      Σd ##ₘ Σr → Cd ## Cr → Cd ## dom Σr → Cr ## dom Σd →
      P (<[d := s]> Σd) Td (Cd, Ed) →
      Powners P σ Σr Tr (Cr, Er) →
      ty_one_of Td Tr Tt →
      Powners P (<[d := s]> σ) (Σd ∪ Σr) Tt (Cd ∪ Cr, Ed ⊎ Er).
```

### 6.5 Process relation `P_n⟦Σ ⊢ T⟧`

**[Δ]** vs. Fig. 5: (i) the τ obligation is guarded by `p'.1 ## dom Σ`
(fork picks a globally fresh channel; only names also fresh for Σ are
constrained — the paper's implicit well-formedness); (ii) the input case
additionally assumes the received channels are fresh for the restricted set
(`dom Σ2 ## p.1`); (iii) the output case is the iterated `Powners` form,
with the sent value typed against the *duals* of the owners' session types
(`Σv ∪ (dual <$> σe)`) and `dom σe = fchans w ∩ p.1` (exactly the restricted
channels leaked by the message).

```coq
Definition Pdef (below : nat → level) (Vn : senv → ty → expr → Prop)
    (n : nat) (Σ : senv) (T : ty) (p : proc) : Prop :=
  match n with
  | 0 => True
  | S n' =>
      (pirred p →
        ∃ v E, p = (∅, {[+ v +]} ⊎ E) ∧ is_val v ∧ Vn Σ T v ∧
               (∀ e, e ∈ E → e = EUnit)) ∧
      (∀ π p', proc_step p π p' →
        match π with
        | PTau =>                                      (* case 1 *)
            p'.1 ## dom Σ →
            lP (below n') Σ T p'
        | PSess (SRecv c w) =>                         (* case 2 *)
            ∃ Σ1 U s,
              Σ = <[c := SRcv U s]> Σ1 ∧ c ∉ dom Σ1 ∧
              ∀ j Σ2, j ≤ n' → Σ2 ##ₘ Σ1 → c ∉ dom Σ2 → dom Σ2 ## p.1 →
                lV (below j) Σ2 U w →
                lP (below j) (<[c := s]> (Σ1 ∪ Σ2)) T p'
        | PSess (SSend c w) =>                         (* case 3, iterated *)
            ∃ Σ0 Σv U s (σe : gmap chan sty) Σw C0 E0 Cw Ew T0 Tw,
              Σ = <[c := SSnd U s]> (Σ0 ∪ Σv ∪ Σw) ∧
              Σ0 ##ₘ Σv ∧ Σ0 ##ₘ Σw ∧ Σv ##ₘ Σw ∧
              c ∉ dom Σ0 ∧ c ∉ dom Σv ∧ c ∉ dom Σw ∧
              dom σe = fchans w ∩ p.1 ∧
              dom σe ## dom Σ ∧ c ∉ dom σe ∧
              p'.1 = C0 ∪ Cw ∧ C0 ## Cw ∧
              p'.2 = E0 ⊎ Ew ∧
              Vn (Σv ∪ (dual <$> σe)) U w ∧
              lP (below n') (<[c := s]> Σ0) T0 (C0, E0) ∧
              Powners (lP (below n')) σe Σw Tw (Cw, Ew) ∧
              ty_one_of T0 Tw T
        | PSess (SClos c) =>                           (* case 4 *)
            ∃ Σ1, Σ = <[c := SEnd]> Σ1 ∧ c ∉ dom Σ1 ∧
              lP (below n') Σ1 T p'
        end)
  end.
```

## 7. Semantic judgments (Defs. 3.2, 3.3) — `LogRel.v`

Grounding substitutions `G_n⟦Σ; Δ⟧`:

```coq
Fixpoint grounding (n : nat) (Σ : senv) (Δ : lenv) (γ : nat → expr) : Prop :=
  match Δ with
  | [] => Σ = ∅
  | None :: Δ' => grounding n Σ Δ' (γ ∘ S)
  | Some T :: Δ' =>
      ∃ Σ1 Σ2, senv_split Σ Σ1 Σ2 ∧ Vrel n Σ1 T (γ 0) ∧
               grounding n Σ2 Δ' (γ ∘ S)
  end.
```

**[Δ]** Def. 3.3 as printed in the draft conflates the environment of `e`
with that of the substitution, making judgments with `Σ ≠ ∅`, `Δ = ·`
vacuous. Formalized: `Σ` covers `e`'s own channels; the grounding brings a
*disjoint* `Σ'`; the conclusion lives at `Σ ∪ Σ'`. The judgment also records
three well-formedness facts the paper leaves implicit (channels of `e` are
exactly `dom Σ`; free variables are available in `Δ`; relevance — no
weakening); without them E-Abs (Thm 3.11) is false.

```coq
Definition sem_typed (Σ : senv) (Δ : lenv) (e : expr) (T : ty) : Prop :=
  fchans e = dom Σ ∧
  allfv (lenv_avail Δ) e ∧
  (∀ x, lenv_avail Δ x → freevar x e) ∧
  ∀ n Σ' γ, Σ' ##ₘ Σ → grounding n Σ' Δ γ →
    Erel n (Σ ∪ Σ') T (subst γ e).

Definition sem_ptyped (Σ : senv) (p : proc) (T : ty) : Prop :=
  ∀ n, Prel n Σ T p.
```

## 8. Adequacy chain (Lemmas 3.4, 3.5, Theorem 3.6) — `LogRel.v`

```coq
(* Lemma 3.4, at the closed environment (what adequacy needs) *)
Lemma Prel_steps m n T p p' :
  nsteps preduction m p p' → Prel (m + n) ∅ T p → Prel n ∅ T p'.

(* Lemma 3.5 — uses Classical_Prop.classic *)
Lemma Prel_safe n T p : Prel (S n) ∅ T p → safe p.

(* Theorem 3.6 *)
Theorem adequacy T p : sem_ptyped ∅ p T → deadlock_free p.
```

## 9. Downward closure (Lemma 3.7) — `LogRel.v`

```coq
Lemma Vrel_down n m Σ T v : m ≤ n → Vrel n Σ T v → Vrel m Σ T v.
Lemma Erel_down n m Σ T e : m ≤ n → Erel n Σ T e → Erel m Σ T e.
Lemma Prel_down n m Σ T p : m ≤ n → Prel n Σ T p → Prel m Σ T p.
```

## 10. Compositionality (Lemmas 3.8–3.10) — `Compositionality.v`

The three principles are proved *simultaneously* by strong induction on the
step index (TERM's fork case builds a CONNECT redex; CONNECT's internal
communication/close cases fall back on CONNECT/INDEPENDENT one index below):

```coq
Definition term_at (n : nat) : Prop :=
  ∀ Σ T e, prim T → Erel n Σ T e → Prel n Σ T (∅, {[+ e +]}).

Definition independent_at (n : nat) : Prop :=
  ∀ Σ Σ1 Σ2 C1 E1 C2 E2 T,
    prim T → senv_split Σ Σ1 Σ2 →
    C1 ## C2 → C1 ## dom Σ2 → C2 ## dom Σ1 →
    C1 ## dom Σ1 → C2 ## dom Σ2 →
    Prel n Σ1 T (C1, E1) → Prel n Σ2 TUnit (C2, E2) →
    Prel n Σ T (C1 ∪ C2, E1 ⊎ E2).

Definition connect_at (n : nat) : Prop :=
  ∀ Σ1 Σ2 c s C1 E1 C2 E2 T,
    prim T → Σ1 ##ₘ Σ2 →
    c ∉ dom Σ1 → c ∉ dom Σ2 →
    C1 ## C2 → c ∉ C1 → c ∉ C2 →
    C1 ## dom Σ2 → C2 ## dom Σ1 →
    C1 ## dom Σ1 → C2 ## dom Σ2 →
    Prel n (<[c := s]> Σ1) T (C1, E1) →
    Prel n (<[c := dual s]> Σ2) TUnit (C2, E2) →
    Prel n (Σ1 ∪ Σ2) T (C1 ∪ C2 ∪ {[c]}, E1 ⊎ E2).

Definition comp_at (n : nat) : Prop :=
  term_at n ∧ independent_at n ∧ connect_at n.
```

The induction steps: `term_S`, `independent_S`, and for CONNECT the split
`connect_progress` (irreducibility, classical) / `connect_tau` (β, fork,
internal message, internal close) / `connect_sess` (external session steps,
including grafting an incoming piece into an owner family via
`connect_owners` / `Powners_graft`) assembled by `connect_S`. Knot tied by
`comp_0` and `comp_all n : comp_at n`. The user-facing statements
(**[Δ]** with `prim T` and the explicit disjointness well-formedness, cf. §5):

```coq
(* Lemma 3.8 (TERM) *)
Lemma Prel_term n Σ T e :
  prim T → Erel n Σ T e → Prel n Σ T (∅, {[+ e +]}).

(* Lemma 3.9 (INDEPENDENT) *)
Lemma Prel_independent n Σ Σ1 Σ2 C1 E1 C2 E2 T :
  prim T → senv_split Σ Σ1 Σ2 →
  C1 ## C2 → C1 ## dom Σ2 → C2 ## dom Σ1 →
  C1 ## dom Σ1 → C2 ## dom Σ2 →
  Prel n Σ1 T (C1, E1) → Prel n Σ2 TUnit (C2, E2) →
  Prel n Σ T (C1 ∪ C2, E1 ⊎ E2).

(* Lemma 3.10 (CONNECT) *)
Lemma Prel_connect n Σ Σ1 Σ2 c s C1 E1 C2 E2 T :
  prim T → senv_split Σ Σ1 Σ2 →
  c ∉ dom Σ1 → c ∉ dom Σ2 →
  C1 ## C2 → c ∉ C1 → c ∉ C2 →
  C1 ## dom Σ2 → C2 ## dom Σ1 →
  C1 ## dom Σ1 → C2 ## dom Σ2 →
  Prel n (<[c := s]> Σ1) T (C1, E1) →
  Prel n (<[c := dual s]> Σ2) TUnit (C2, E2) →
  Prel n Σ T (C1 ∪ C2 ∪ {[c]}, E1 ⊎ E2).
```

## 11. Semantic typing rules and fundamental properties

### Theorem 3.11 (term rules) — `LogRel.v`

One lemma per rule of Fig. 4, mirroring the syntactic premises
(base rules: `sem_typed_unit`, `sem_typed_konst`, `sem_typed_var`,
`sem_typed_chan`); the binder/splitting rules:

```coq
Lemma sem_typed_lam Σ Δ e T U :
  sem_typed Σ (Some T :: Δ) e U →
  sem_typed Σ Δ (Lam e) (TLolli T U).

Lemma sem_typed_app Σ Σ1 Σ2 Δ Δ1 Δ2 e1 e2 T U :
  senv_split Σ Σ1 Σ2 → lenv_split Δ Δ1 Δ2 →
  sem_typed Σ1 Δ1 e1 (TLolli T U) → sem_typed Σ2 Δ2 e2 T →
  sem_typed Σ Δ (App e1 e2) U.

Lemma sem_typed_pair Σ Σ1 Σ2 Δ Δ1 Δ2 e1 e2 T U : (* … analogous … *)
Lemma sem_typed_letu Σ Σ1 Σ2 Δ Δ1 Δ2 e1 e2 T :  (* … analogous … *)
Lemma sem_typed_letp Σ Σ1 Σ2 Δ Δ1 Δ2 e1 e2 U V T : (* … analogous … *)
Lemma sem_typed_inj1 Σ Δ e T U :  (* … and sem_typed_inj2 … *)
  sem_typed Σ Δ e T → sem_typed Σ Δ (Inj1 e) (TSum T U).
Lemma sem_typed_case Σ Σ1 Σ2 Δ Δ1 Δ2 e e1 e2 U V T : (* … as E-Case … *)

Theorem fundamental_term Σ Δ e T : typed Σ Δ e T → sem_typed Σ Δ e T.
```

(Key workhorses: `Erel_bind` — the bind lemma over one-frame contexts —
and `Vrel_app_head`, which handles all four constants' head behaviors.)

### Theorem 3.12 (process rules) and Theorem 3.13 — `Compositionality.v`

```coq
Lemma sem_ptyped_term Σ e T :
  prim T → sem_typed Σ [] e T → sem_ptyped Σ (∅, {[+ e +]}) T.

Lemma sem_ptyped_independent Σ Σ1 Σ2 C1 E1 C2 E2 T : (* premises as P-Independent *)
  … → sem_ptyped Σ (C1 ∪ C2, E1 ⊎ E2) T.

Lemma sem_ptyped_connect Σ Σ1 Σ2 c s C1 E1 C2 E2 T : (* premises as P-Connect *)
  … → sem_ptyped Σ (C1 ∪ C2 ∪ {[c]}, E1 ⊎ E2) T.

Theorem fundamental_proc Σ p T : ptyped Σ p T → sem_ptyped Σ p T.

Corollary typed_deadlock_free p T : ptyped ∅ p T → deadlock_free p.
```

## 12. Examples (sanity checks) — `Examples.v`

- Ex. 2.1: `sync_reduces` — the closed process `(∅, {sync})` performs the
  paper's τ-sequence to a terminated process (axiom-free).
- Ex. 2.8: `blocked_pirred`, `blocked_not_safe`,
  `blocked_not_deadlock_free`.
- Ex. 2.11: `sync_typed : ptyped ∅ sync_proc TUnit`, hence
  `sync_deadlock_free` by `typed_deadlock_free`.

---

## Deviations from the draft

Collected from the **[Δ]** marks above — the points to reconcile when
auditing against the paper text:

1. **T-Act-Recv receives arbitrary values** (not only closed ones); a
   receive step must exist for anything a semantically-good sender might
   emit, or CONNECT fails at index 1 (the LR admits open λ-values at low
   index).
2. **P-Act-Fork freshness is global** (`c ∉ C`, `c ∉ echans E`,
   `c ∉ fchans e`) — implicit in the paper's "new name".
3. **Lemma 2.3, Eq (9)**: the draft subtracts `sentc` from `C` after an
   internalized communication; that is not derivable from Fig. 3's
   P-Act-Msg (which keeps `C`). `internalize_comm` proves the derivable
   version.
4. **E's fork case is freshness-guarded** (`c ∉ dom Σ`), and **P's τ case is
   guarded by `p'.1 ## dom Σ`**; P's input case assumes `dom Σ2 ## p.1` —
   all instances of the paper's implicit "Σ and C share no channels".
5. **V's ⊸ case requires `fchans eb = dom Σ`** (a λ-value owns exactly its
   channels); automatic for every other value form (`Vrel_fchans`).
6. **E/P input cases quantify the received value at all `j ≤ n'`**, not just
   at `n'` (needed by CONNECT, where the peer arrives one index lower).
7. **P's output case is iterated**: one independent owner piece per escaped
   channel (`Powners`) instead of Fig. 5's single owner of all escaped
   channels; the sent value is typed against the duals of the owners' types,
   and `dom σe = fchans w ∩ C` pins the escaped set exactly.
8. **Def. 3.3 disentangled**: `Σ` for the term's own channels plus a
   disjoint `Σ'` from the grounding substitution, conclusion at `Σ ∪ Σ'`;
   `sem_typed` additionally records channel coverage, free-variable
   availability, and relevance (no weakening) — required for E-Abs.
9. **Well-formedness made explicit in P-rules and Lemmas 3.8–3.10**:
   `prim T` (recovered syntactically via `ptyped_prim`) and the
   cross/self-disjointness of restricted sets and environments
   (`C1 ## dom Σ2`, `C2 ## dom Σ1`, self-disjointness via
   `ptyped_chan_disj`).
10. **Classical logic**: `Classical_Prop.classic` is used in Lemma 3.5
    (`Prel_safe`) and in CONNECT's progress case (`connect_progress`) —
    the only axiom in the development.
