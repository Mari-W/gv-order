(** * Soup states (stage S8)

    The records of soup/Soup.v live in a file of their own, because the
    record syntax clashes with the notation of the typing judgment
    (docs/redesign/progress.md, S3, syntax). *)

From GV Require Export fuel.Fuel lang.Process types.Erasure.

(** ** Ownership *)

Record hold := Hold { h_th : nat; h_pt : point; h_ctr : fuel }.

Global Instance hold_eq_dec : EqDecision hold.
Proof. solve_decision. Defined.

Abbreviation own := (gmap cend hold).

Record lfstate := LFState { s_q : config; s_K : own; s_tk : nat → nat }.

(** The entries of thread t, its counters, and the part of a map on its
    ends. *)
Definition kth (K : own) (t : nat) : own := filter (λ kv : cend * hold, kv.2.(h_th) = t) K.
Definition ctrs (K : own) (t : nat) : cenv := h_ctr <$> kth K t.
Definition kres {Y : Type} (K : own) (t : nat) (m : gmap cend Y) : gmap cend Y :=
  filter (λ kv : cend * Y, kv.1 ∈ dom (kth K t)) m.

(** ** The clauses of the soup at one index

    [Erl Θ U e] is the relation of a thread at its environment and result
    type, [Frl Π φ tk e] its fuel. soup/Soup.v instantiates them with
    E[live] and FuelE^N at one index. The duality of session types up
    to annotations is spelled out, [sdual S S'] of relation/Relation.v. *)
Record soup_gen (Erl : senv → ty → expr → Prop) (Frl : penv → cenv → nat → expr → Prop)
    (Σ : senv) (T : ty) (a : lfstate) (A : senv) (Π : penv) (U : nat → ty) : Prop := SoupGen {
  sp_prim : prim T;
  sp_rel t e : (s_q a).2 !! t = Some e → Erl (kres (s_K a) t A) (U t) e;
  sp_ty t e : (s_q a).2 !! t = Some e → U t = T ∨ U t = TUnit;
  sp_fuel t e : (s_q a).2 !! t = Some e → Frl (kres (s_K a) t Π) (ctrs (s_K a) t) (s_tk a t) e;
  sp_pts : snd <$> A = h_pt <$> s_K a;
  sp_dom : dom Π = dom (s_K a);
  sp_owner o h : s_K a !! o = Some h → is_Some ((s_q a).2 !! h.(h_th));
  sp_closed o : o ∈ dom (s_K a) → ech o ∈ (s_q a).1 ∨ o ∈ dom Σ;
  sp_pair o : o ∈ dom (s_K a) → ech o ∈ (s_q a).1 → edual o ∈ dom (s_K a);
  sp_sdual o S x S' x' : A !! o = Some (S, x) → A !! edual o = Some (S', x') →
    ech o ∈ (s_q a).1 → x' = x‾ ∧ sequiv (sty_df S') (sty_df (dual S));
  sp_pdual o P P' : Π !! o = Some P → Π !! edual o = Some P' → ech o ∈ (s_q a).1 →
    sequiv P' (dual P);
  sp_sig o y : Σ !! o = Some y → A !! o = Some y
}.
