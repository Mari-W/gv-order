(** * Renamings of ends, families and generated roots (stage S2)

    - [typed_emap]: an injective renaming g of ends maps a derivation
      over Θ and e to one over [kmap g Θ] and [emap g e]. Points do not
      change.
    - [typed_gmap]: a renaming r of generated roots that sends the roots
      of every family ℓ of W into the family f ℓ maps a derivation at W
      to one at [wfrename f W], with every point renamed by r and every
      [new_ℓ] of the term relabelled to [new_(f ℓ)]. The box rule
      quantifies over all session instances, so r needs a right inverse
      r' (r ∘ r' = id): the instance ss at [wfrename f W] comes from the
      instance r'(ss) at W.
    - [typed_grename]: the instance f = id, renaming roots inside their
      families, stays at W. *)

From GV Require Export static.Weakening types.Erasure.

(** ** Renaming of ends *)

Section emap.
  Context (g : cend → cend) `{!base.Inj eq eq g}.

  Local Abbreviation km Θ := (kmap (M2:=gmap cend) g Θ : tenv).

End emap.

(** ** Renaming of generated roots in types *)

Section gmap_types.
  Context (r : family * nat → family * nat).

  Fixpoint gmap_ty (T : ty) : ty :=
    match T with
    | TUnit => TUnit
    | TLolli ub lb c t T1 U a =>
        TLolli (ub_map (pt_gmap r) ub) (lb_map (pt_gmap r) lb) c t (gmap_ty T1) (gmap_ty U) a
    | TProd T1 U => TProd (gmap_ty T1) (gmap_ty U)
    | TSum T1 U => TSum (gmap_ty T1) (gmap_ty U)
    | TBox n k C ub c t U => TBox n k (bcs_gmap r C) (pt_gmap r <$> ub) c t (gmap_ty U)
    | TSess s x a => TSess (gmap_sty s) (pt_gmap r x) a
    | TEx lb n C T1 => TEx (lb_map (pt_gmap r) lb) n (bcs_gmap r C) (gmap_ty T1)
    end
  with gmap_sty (s : sty) : sty :=
    match s with
    | SRcv m T => SRcv m (gmap_ty T)
    | SSnd m T => SSnd m (gmap_ty T)
    | SMu s' => SMu (gmap_sty s')
    | SSeq s1 s2 => SSeq (gmap_sty s1) (gmap_sty s2)
    | SPlus s1 s2 => SPlus (gmap_sty s1) (gmap_sty s2)
    | SWith s1 s2 => SWith (gmap_sty s1) (gmap_sty s2)
    | s => s
    end.

  (** *** Points *)

  (** *** Heads, kinds, annotations *)

  Lemma heads_gmap T : heads (gmap_ty T) = set_map (pt_gmap r) (heads T).
  Proof.
    induction T; simpl; rewrite ?set_map_union_L, ?IHT1, ?IHT2; try set_solver.
    - destruct lb; simpl; set_solver.
    - by rewrite set_map_singleton_L.
    - destruct lb; simpl; set_solver.
  Qed.

  Lemma hbot_gmap T : hbot (gmap_ty T) = hbot T.
  Proof. induction T; simpl; try done; try congruence; by destruct lb. Qed.

  (** *** Session operations *)

  (** *** ≈ and subtyping *)

End gmap_types.

(** ** Renaming of generated roots in contexts *)

Section gmap_ctx.
  Context (r : family * nat → family * nat).

  Definition tentry_gmap (e : tentry) : tentry :=
    TE (gmap_sty r (te_sty e)) (pt_gmap r (te_pt e)) (te_cr e).
  Definition tenv_gmap (Θ : tenv) : tenv := tentry_gmap <$> Θ.
  Definition lenv_gmap (Δ : lenv) : lenv := fmap (M:=option) (gmap_ty r) <$> Δ.
  Definition sf_gmap (F : sfuture) : sfuture := (set_map (pt_gmap r) F.1, F.2).
  (** *** Θ *)

  Lemma tenv_heads_gmap Θ : tenv_heads (tenv_gmap Θ) = set_map (pt_gmap r) (tenv_heads Θ).
  Proof.
    apply set_eq. intros y. rewrite elem_of_map, elem_of_tenv_heads. unfold tenv_gmap.
    setoid_rewrite elem_of_tenv_heads. setoid_rewrite lookup_fmap. split.
    - intros (o & e & He & ->). destruct (Θ !! o) as [e0|] eqn:E; simplify_eq/=.
      exists (te_pt e0)‾. split; [done|]. eauto.
    - intros (y0 & -> & o & e & He & ->). exists o, (tentry_gmap e). by rewrite He.
  Qed.

  (** *** Δ *)

  Lemma lenv_heads_gmap Δ : lenv_heads (lenv_gmap Δ) = set_map (pt_gmap r) (lenv_heads Δ).
  Proof.
    induction Δ as [|[T|] Δ IH]; simpl; [by rewrite set_map_empty|..|done].
    by rewrite set_map_union_L, heads_gmap, IH.
  Qed.

  Lemma lenv_bot_gmap Δ : lenv_bot (lenv_gmap Δ) = lenv_bot Δ.
  Proof. induction Δ as [|[T|] Δ IH]; simpl; rewrite ?hbot_gmap; congruence. Qed.

  (** *** F *)

  Lemma sf_gmap_unionb F X b :
    sf_gmap (sf_unionb F X b) = sf_unionb (sf_gmap F) (set_map (pt_gmap r) X) b.
  Proof. destruct b; unfold sf_gmap, sf_unionb; simpl; by rewrite set_map_union_L. Qed.

  Lemma opt_heads_gmap o : opt_heads (pt_gmap r <$> o) = set_map (pt_gmap r) (opt_heads o).
  Proof. destruct o; simpl; [by rewrite set_map_singleton_L|by rewrite set_map_empty]. Qed.

  (** *** Γ *)

End gmap_ctx.

(** ** Facts under a renaming of generated roots *)

Section gmap_facts.
  Context (W : world) (f : family → family) (r : family * nat → family * nat).
  Context (Hwf : world_wf W) (Hr : ∀ ℓ g, ℓ ∈ w_fams W → (r (ℓ, g)).1 = f ℓ).

  Local Abbreviation W' := (wfrename f W).

End gmap_facts.

(** ** Relabelling families in terms *)

(** ** The renaming theorem *)

Section gmap_typed.
  Context (W : world) (f : family → family) (r r' : family * nat → family * nat).
  Context (Hwf : world_wf W) (Hr : ∀ ℓ g, ℓ ∈ w_fams W → (r (ℓ, g)).1 = f ℓ).
  Context (Hrr : ∀ lg, r (r' lg) = lg).

  Local Abbreviation W' := (wfrename f W).

  Local Ltac heads_g :=
    rewrite ?tenv_heads_gmap, ?lenv_heads_gmap, ?lenv_bot_gmap, ?heads_gmap, ?hbot_gmap,
      ?opt_heads_gmap, <-?set_map_union_L, <-?sf_gmap_unionb.

End gmap_typed.

