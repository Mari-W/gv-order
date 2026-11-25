(** * Soup states (stage S8)

    The records of soup/Soup.v live in a file of their own, because the
    record syntax clashes with the notation of the typing judgment
    (.claude/notes/redesign/progress.md, S3, syntax). *)

From GV Require Export fuel.Fuel lang.Process types.Erasure.

(** ** Ownership *)

Record hold := Hold { h_th : nat; h_pt : point; h_ctr : fuel; h_cap : fuel }.

Global Instance hold_eq_dec : EqDecision hold.
Proof. solve_decision. Defined.

Abbreviation own := (gmap cend hold).

(** A state carries the ranked world of its run so far. A creation may
    grow it, and no step shrinks it. *)
Record lfstate := LFState { s_q : config; s_K : own; s_W : world }.

(** The choice of a creation: the tickets of its two ends, the point of
    its positive end and the grown world (O-New, F-New). Every other
    event ignores it. *)
Record tchoice := TChoice { tc_m1 : fuel; tc_m2 : fuel; tc_pt : point; tc_W : world }.

(** The entries of thread t, its counters with their tickets, and the
    part of a map on its ends. *)
Definition kth (K : own) (t : nat) : own := filter (λ kv : cend * hold, kv.2.(h_th) = t) K.
Definition hctr (h : hold) : fuel * fuel := (h.(h_ctr), h.(h_cap)).
Definition ctrs (K : own) (t : nat) : cenv := hctr <$> kth K t.
Definition kres {Y : Type} (K : own) (t : nat) (m : gmap cend Y) : gmap cend Y :=
  filter (λ kv : cend * Y, kv.1 ∈ dom (kth K t)) m.

(** Every counter is finite. *)
Definition kfin (K : own) : Prop := ∀ o h, K !! o = Some h → is_Some h.(h_ctr).

(** ** The clauses of the soup at one index

    [Erl Θ U e] is the relation of a thread at its environment and result
    type, [Frl Π φ e] its fuel, φ the counters and tickets of its ends. soup/Soup.v instantiates them with
    E[live] and FuelE^N at one index. The duality of session types up
    to annotations is spelled out, [sdual S S'] of relation/Relation.v.
    An end of the interface Σ is held at its entry of Σ in A and at the
    session type of that entry in Π ([sp_sig], [sp_psig]). Every counter
    is at most the tickets of its end, which are at most N ([sp_cap]),
    and the tickets of the two ends of an internal channel sum to at most
    N ([sp_tsum], decision of 2026-11-21). An end o of the interface has
    at most the tickets (η o).2 of the interface annotations η
    ([sp_sigcap]), so a cut of two interfaces whose annotations meet the
    bound meets it. *)
Record soup_gen (N : fuel) (η : iann) (Erl : senv → ty → expr → Prop) (Frl : penv → cenv → expr → Prop)
    (Σ : senv) (T : ty) (a : lfstate) (A : senv) (Π : penv) (U : nat → ty) : Prop := SoupGen {
  sp_tfree : tfree T;
  sp_rel t e : (s_q a).2 !! t = Some e → Erl (kres (s_K a) t A) (U t) e;
  sp_ty t e : (s_q a).2 !! t = Some e → U t = T ∨ U t = TUnit;
  sp_fuel t e : (s_q a).2 !! t = Some e → Frl (kres (s_K a) t Π) (ctrs (s_K a) t) e;
  sp_pts : snd <$> A = h_pt <$> s_K a;
  sp_dom : dom Π = dom (s_K a);
  sp_owner o h : s_K a !! o = Some h → is_Some ((s_q a).2 !! h.(h_th));
  sp_closed o : o ∈ dom (s_K a) → ech o ∈ (s_q a).1 ∨ o ∈ dom Σ;
  sp_pair o : o ∈ dom (s_K a) → ech o ∈ (s_q a).1 → edual o ∈ dom (s_K a);
  sp_sdual o S x S' x' : A !! o = Some (S, x) → A !! edual o = Some (S', x') →
    ech o ∈ (s_q a).1 → x' = x‾ ∧ sequiv (sty_df S') (sty_df (dual S));
  sp_pdual o P P' : Π !! o = Some P → Π !! edual o = Some P' → ech o ∈ (s_q a).1 →
    ssub (dual P) P';
  sp_sig o y : Σ !! o = Some y → A !! o = Some y;
  sp_fin o h : s_K a !! o = Some h → is_Some h.(h_ctr);
  sp_psig o S x : Σ !! o = Some (S, x) → Π !! o = Some S;
  sp_cap o h : s_K a !! o = Some h → fle h.(h_ctr) h.(h_cap) ∧ fle h.(h_cap) N;
  sp_tsum o h h' : s_K a !! o = Some h → s_K a !! edual o = Some h' → ech o ∈ (s_q a).1 →
    tsum_ok N h.(h_cap) h'.(h_cap);
  sp_sigcap o h : o ∈ dom Σ → s_K a !! o = Some h → fle h.(h_cap) (η o).2
}.

(** ** The soup as relation, fuel and consistency

    The map reads a soup state as three parts: every thread in the
    relation at its result type, every thread fueled, and the state
    consistent with A and Π ([soup_consistent]). [soup_gen_iff] shows the
    record is exactly the three parts beside [tfree T]. *)
Definition soup_consistent (N : fuel) (η : iann) (Σ : senv) (a : lfstate) (A : senv) (Π : penv) : Prop :=
  snd <$> A = h_pt <$> s_K a ∧ dom Π = dom (s_K a) ∧
  (∀ o h, s_K a !! o = Some h → is_Some ((s_q a).2 !! h.(h_th))) ∧
  (∀ o, o ∈ dom (s_K a) → ech o ∈ (s_q a).1 ∨ o ∈ dom Σ) ∧
  (∀ o, o ∈ dom (s_K a) → ech o ∈ (s_q a).1 → edual o ∈ dom (s_K a)) ∧
  (∀ o S x S' x', A !! o = Some (S, x) → A !! edual o = Some (S', x') →
     ech o ∈ (s_q a).1 → x' = x‾ ∧ sequiv (sty_df S') (sty_df (dual S))) ∧
  (∀ o P P', Π !! o = Some P → Π !! edual o = Some P' → ech o ∈ (s_q a).1 → ssub (dual P) P') ∧
  (∀ o y, Σ !! o = Some y → A !! o = Some y) ∧
  (∀ o h, s_K a !! o = Some h → is_Some h.(h_ctr)) ∧
  (∀ o S x, Σ !! o = Some (S, x) → Π !! o = Some S) ∧
  (∀ o h, s_K a !! o = Some h → fle h.(h_ctr) h.(h_cap) ∧ fle h.(h_cap) N) ∧
  (∀ o h h', s_K a !! o = Some h → s_K a !! edual o = Some h' → ech o ∈ (s_q a).1 →
     tsum_ok N h.(h_cap) h'.(h_cap)) ∧
  (∀ o h, o ∈ dom Σ → s_K a !! o = Some h → fle h.(h_cap) (η o).2).

Lemma soup_gen_iff N η Erl Frl Σ T a A Π U :
  soup_gen N η Erl Frl Σ T a A Π U ↔
    tfree T ∧
    (∀ t e, (s_q a).2 !! t = Some e → Erl (kres (s_K a) t A) (U t) e ∧ (U t = T ∨ U t = TUnit)) ∧
    (∀ t e, (s_q a).2 !! t = Some e → Frl (kres (s_K a) t Π) (ctrs (s_K a) t) e) ∧
    soup_consistent N η Σ a A Π.
Proof.
  split.
  - intros []. split_and!; try done; intros; split; eauto.
  - intros (Ht & Hr & Hf & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13).
    exact (SoupGen _ _ _ _ _ _ _ _ _ _ Ht (λ t e H, proj1 (Hr t e H)) (λ t e H, proj2 (Hr t e H)) Hf
             H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13).
Qed.

(** Over the empty interface the annotations are not read. *)
Lemma soup_gen_ann N η η' Erl Frl T a A Π U :
  soup_gen N η Erl Frl ∅ T a A Π U → soup_gen N η' Erl Frl ∅ T a A Π U.
Proof.
  intros []. constructor; try done. all: intros o h Ho; by rewrite dom_empty_L in Ho.
Qed.
