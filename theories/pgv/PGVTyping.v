(** * Static typing of repaired Priority GV

    Fig. 2 of Kokke and Dardha (pdf p. 9), on our terms (lang/Syntax.v).
    PGV's close and wait are both our close, and PGV's fork is derived
    from new and spawn (Fig. 3, p. 12). The judgment Γ ⊢^p M : T
    carries one bound p, an upper bound on the priorities of M's
    actions (p. 10). Environments are linear (p. 10), with de Bruijn
    variables as in LinearEnv.v and no unlimited types.

    Two repairs from docs/extensions/adequacy/pgv-counterexamples.txt.
    R1: send and recv ask o < pr(T) of the payload T. R2: T-Pair asks
    q < pr(T), because the left value is held while the right component
    runs. 0 and absurd are left out.

    The judgment takes a predicate [ok] on the session types that send
    and recv act on. With [ok = λ _, True] it is repaired PGV. The
    fragment of our worlds is [ok = pgv_mono] ([pgv_frag]). *)

From stdpp Require Import base list.
From LRGV Require Export lang.Syntax pgv.PGVTypes.

(** ** Linear environments *)

Definition penv := list (option pty).

Definition penv_empty (Γ : penv) : Prop := ∀ o, o ∈ Γ → o = None.

Definition penv_only (Γ : penv) (x : nat) (T : pty) : Prop :=
  Γ !! x = Some (Some T) ∧ ∀ y T', Γ !! y = Some (Some T') → y = x ∧ T' = T.

(** Γ = Γ₁, Γ₂: every binding goes to exactly one side. *)
Inductive psplit : penv → penv → penv → Prop :=
  | psplit_nil : psplit [] [] []
  | psplit_none Γ Γ1 Γ2 : psplit Γ Γ1 Γ2 → psplit (None :: Γ) (None :: Γ1) (None :: Γ2)
  | psplit_l T Γ Γ1 Γ2 : psplit Γ Γ1 Γ2 → psplit (Some T :: Γ) (Some T :: Γ1) (None :: Γ2)
  | psplit_r T Γ Γ1 Γ2 : psplit Γ Γ1 Γ2 → psplit (Some T :: Γ) (None :: Γ1) (Some T :: Γ2).

(** pr(Γ), the smallest priority of the bindings, ⊤ when there is none. *)
Fixpoint pr_env (Γ : penv) : prio :=
  match Γ with
  | [] => PTop
  | None :: Γ' => pr_env Γ'
  | Some T :: Γ' => prio_min (pr T) (pr_env Γ')
  end.

(** ** Type schemas for constants (p. 9)

    new   : 1 ⊸ S × S̄
    spawn : (1 ⊸^{p,q} 1) ⊸ 1
    send  : T × !ᵒT.S ⊸^{⊤,o} S      o < pr(T)  (R1)
    recv  : ?ᵒT.S ⊸^{⊤,o} T × S      o < pr(T)  (R1)
    close : endᵒ_! ⊸^{⊤,o} 1
    wait  : endᵒ_? ⊸^{⊤,o} 1
    link  : S × S̄ ⊸ 1

    T ⊸ U is the pure arrow T ⊸^{⊤,⊥} U (p. 5). *)

Inductive pgv_konst (ok : psty → Prop) : konst → pty → Prop :=
  | pk_new S :
      pgv_konst ok KNew (PLolli PTop PBot PUnit (PProd (PSess S) (PSess (pdual S))))
  | pk_spawn p q :
      pgv_konst ok KSpawn (PLolli PTop PBot (PLolli p q PUnit PUnit) PUnit)
  | pk_send o T S :
      prio_lt (PNat o) (pr T) → ok (PSnd o T S) →
      pgv_konst ok KSend (PLolli PTop (PNat o) (PProd T (PSess (PSnd o T S))) (PSess S))
  | pk_recv o T S :
      prio_lt (PNat o) (pr T) → ok (PRcv o T S) →
      pgv_konst ok KRecv (PLolli PTop (PNat o) (PSess (PRcv o T S)) (PProd T (PSess S)))
  | pk_close o :
      pgv_konst ok KClos (PLolli PTop (PNat o) (PSess (PEndS o)) PUnit)
  | pk_wait o :
      pgv_konst ok KClos (PLolli PTop (PNat o) (PSess (PEndR o)) PUnit)
  | pk_link S :
      pgv_konst ok KLink (PLolli PTop PBot (PProd (PSess S) (PSess (pdual S))) PUnit).

(** ** Typing rules for terms (p. 9)

    In T-LetPair the environment Δ, x : T, y : T′ is the list
    T′ :: T :: Δ, because index 0 is the second component. *)

Inductive pgv_typed (ok : psty → Prop) : penv → prio → expr → pty → Prop :=
  | pt_var Γ x T :                                       (* T-Var *)
      penv_only Γ x T →
      pgv_typed ok Γ PBot (Var x) T
  | pt_const Γ k T :                                     (* T-Const *)
      penv_empty Γ → pgv_konst ok k T →
      pgv_typed ok Γ PBot (Konst k) T
  | pt_unit Γ :                                          (* T-Unit *)
      penv_empty Γ →
      pgv_typed ok Γ PBot EUnit PUnit
  | pt_lam Γ M T U q :                                   (* T-Lam *)
      pgv_typed ok (Some T :: Γ) q M U →
      pgv_typed ok Γ PBot (Lam M) (PLolli (pr_env Γ) q T U)
  | pt_app Γ Γ1 Γ2 M N T U p q p' q' :                   (* T-App *)
      psplit Γ Γ1 Γ2 →
      pgv_typed ok Γ1 p M (PLolli p' q' T U) →
      pgv_typed ok Γ2 q N T →
      prio_lt p (pr_env Γ2) → prio_lt q p' →
      pgv_typed ok Γ (prio_max (prio_max p q) q') (App M N) U
  | pt_letu Γ Γ1 Γ2 M N T p q :                          (* T-LetUnit *)
      psplit Γ Γ1 Γ2 →
      pgv_typed ok Γ1 p M PUnit →
      pgv_typed ok Γ2 q N T →
      prio_lt p (pr_env Γ2) →
      pgv_typed ok Γ (prio_max p q) (LetU M N) T
  | pt_pair Γ Γ1 Γ2 M N T U p q :                        (* T-Pair, with R2 *)
      psplit Γ Γ1 Γ2 →
      pgv_typed ok Γ1 p M T →
      pgv_typed ok Γ2 q N U →
      prio_lt p (pr_env Γ2) → prio_lt q (pr T) →
      pgv_typed ok Γ (prio_max p q) (Pair M N) (PProd T U)
  | pt_letp Γ Γ1 Γ2 M N T T' U p q :                     (* T-LetPair *)
      psplit Γ Γ1 Γ2 →
      pgv_typed ok Γ1 p M (PProd T T') →
      pgv_typed ok (Some T' :: Some T :: Γ2) q N U →
      prio_lt p (pr_env (Some T' :: Some T :: Γ2)) →
      pgv_typed ok Γ (prio_max p q) (LetP M N) U
  | pt_inl Γ M T U p :                                   (* T-Inl *)
      pgv_typed ok Γ p M T → pr T = pr U →
      pgv_typed ok Γ p (Inj1 M) (PSum T U)
  | pt_inr Γ M T U p :                                   (* T-Inr *)
      pgv_typed ok Γ p M U → pr T = pr U →
      pgv_typed ok Γ p (Inj2 M) (PSum T U)
  | pt_case Γ Γ1 Γ2 L M N T T' U p q :                   (* T-CaseSum *)
      psplit Γ Γ1 Γ2 →
      pgv_typed ok Γ1 p L (PSum T T') →
      pgv_typed ok (Some T :: Γ2) q M U →
      pgv_typed ok (Some T' :: Γ2) q N U →
      prio_lt p (pr_env Γ2) →
      pgv_typed ok Γ (prio_max p q) (Case L M N) U.

(** Repaired PGV, and its fragment with monotone sessions. *)
Abbreviation pgv_rep := (pgv_typed (λ _, True)).
Abbreviation pgv_frag := (pgv_typed pgv_mono).

Lemma pgv_frag_rep Γ p M T : pgv_frag Γ p M T → pgv_rep Γ p M T.
Proof.
  induction 1; econstructor; eauto.
  destruct select (pgv_konst _ _ _); constructor; done.
Qed.

(** ** Sugar (p. 6)

    let x = M in N is (λx.N) M. GV's fork is derived from new and spawn
    (Fig. 3, p. 12), and the examples write it out. *)

Definition plet (M N : expr) : expr := App (Lam N) M.
