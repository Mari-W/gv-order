(** * The world of the n-ary P-Connect (fx-gap, 2026-11-22, Q12)

    [p_connect_n] (static/ConnectN.v) concludes a hidden derivation at
    some world W whose facts are facts of the join of the component
    worlds restricted to the final interface I. This file names W and
    shows why inclusion, and not equality, is the right statement.

    [p_connect_n_exact]: W is the fold of the binary joins, each
    restricted to the interface of the composite so far,

      W = (((W_1 ⊔ W_2)|I_2 ⊔ W_3)|I_3 ⊔ …)|I_n,   I_n = I       [sw_fold]

    which is the world that n − 1 binary P-Connects build.

    [fold_join_gap]: the fold can derive strictly fewer facts than the
    restricted join (W_1 ⊔ … ⊔ W_n)|I. A constant a that the composite
    of p_1 and p_2 hides drops out of I_2, so a fact c₀ ≺ a of W_1 and a
    fact a ≺ c₁ of a later W_3 never meet in the fold, while the join
    chains them to c₀ ≺ c₁. The hidden judgment treats a hidden
    constant as private to its composite, and a later component may
    pick the same constant for an unrelated point (the comment on
    [ptyped], static/Typing.v). The join then identifies two different
    points, and its fact c₀ ≺ c₁ is no fact of the composite. So
    equality with the restricted join fails, and the restricted join is
    an upper bound of the exact world. The n-ary premise, [wok] of the
    whole join, is sufficient for every binary premise but asks more
    than the fold needs. *)

From GV Require Export static.ConnectN.

(** ** The fold of binary joins *)

Definition sw_fold (W0 : sworld) (l : list (sworld * gset nat)) : sworld :=
  foldl (λ acc WI, swrestrict (acc ⊔ WI.1) WI.2) W0 l.

Lemma sw_fold_snoc W0 l W I : sw_fold W0 (l ++ [(W, I)]) = swrestrict (sw_fold W0 l ⊔ W) I.
Proof. unfold sw_fold. by rewrite foldl_app. Qed.

(** The n-ary rule at its exact world. Each step restricts to the
    interface of the composite so far, the last one to the final
    interface, and the fold derives only facts of the join. *)
Theorem p_connect_n_exact N Ws Σ p T :
  pcomps N Ws Σ p T → wok N (sw_joins Ws) →
  ∃ W0 l, Ws = W0 :: l.*1 ∧ (l ≠ [] → ∃ l' W', l = l' ++ [(W', iface Σ T)]) ∧
    ptyped N (sw_fold W0 l) Σ p T ∧ (∀ x y, sw_fold W0 l ⊢ₛ x ≺ y → sw_joins Ws ⊢ₛ x ≺ y).
Proof.
  induction 1 as [W Σ p T Hty|Ws W Σ1 Σ2 ΣC C1 C2 E1 E2 T _ IH Hty HD1 HD2 Hf H12 H1C H2C HC HC1 HC2];
    intros HS.
  - exists W, []. split_and!; [done|done|done|]. intros x y. apply sw_lt_mono, swext_joins. set_solver.
  - destruct IH as (W0 & l & -> & _ & Hta & Hlt).
    { eapply (wok_sub N); [|exact HS]. intros x y. apply sw_lt_mono, swext_joins_app. }
    assert (∀ x y, sw_fold W0 l ⊔ W ⊢ₛ x ≺ y → sw_joins ((W0 :: l.*1) ++ [W]) ⊢ₛ x ≺ y) as Hj.
    { intros x y H. eapply sw_lt_mono; [|eapply (join_sub (sw_fold W0 l) (sw_joins (W0 :: l.*1)) W W);
        [exact Hlt|done|exact H]].
      split; simpl.
      - pose proof (swext_consts _ _ (swext_joins_app (W0 :: l.*1) [W])) as K1.
        pose proof (swext_consts _ _ (swext_joins W ((W0 :: l.*1) ++ [W]) ltac:(set_solver))) as K2.
        simpl in K1, K2. set_solver.
      - intros g [Hg|Hg].
        + by apply (swext_facts _ _ (swext_joins_app (W0 :: l.*1) [W])).
        + apply (swext_facts _ _ (swext_joins W ((W0 :: l.*1) ++ [W]) ltac:(set_solver))), Hg. }
    exists W0, (l ++ [(W, iface (Σ1 ∪ Σ2) T)]). split_and!.
    + by rewrite fmap_app.
    + intros _. by eexists _, _.
    + rewrite sw_fold_snoc. apply p_connect; try done.
      apply (wok_sub N _ (sw_joins ((W0 :: l.*1) ++ [W]))); [exact Hj|exact HS].
    + intros x y H. rewrite sw_fold_snoc in H. by apply Hj, (swrestrict_lt _ (iface (Σ1 ∪ Σ2) T)).
Qed.

(** ** The fold may derive fewer facts than the restricted join *)

Definition cpt (k : nat) : point := MkPt (NConst k) true 0.

(** p_1 holds an end at c₀ and a cut end at a, ordered c₀ ≺ a. p_2
    holds the partner at a. p_3 holds an end at a and one at c₁,
    ordered a ≺ c₁. The constants are c₀ = 0, a = 1, c₁ = 2. The
    composite of p_1 and p_2 keeps c₀ only, the final interface keeps
    all three. *)
Definition gW1 : sworld := SWorld ({[0]} ∪ {[1]}) (λ g, g = FLt (cpt 0) (cpt 1)).
Definition gW2 : sworld := SWorld {[1]} (λ _, False).
Definition gW3 : sworld := SWorld ({[1]} ∪ {[2]}) (λ g, g = FLt (cpt 1) (cpt 2)).
Definition gI12 : gset nat := {[0]}.
Definition gI : gset nat := ({[0]} ∪ {[1]} ∪ {[2]}).

(** A world whose facts leave the root r only towards r keeps r along
    every chain. *)
Lemma sw_lt_root_closed V r x y :
  (∀ u v, sw_facts V (FLt u v) → pt_root u = r → pt_root v = r) →
  V ⊢ₛ x ≺ y → pt_root x = r → pt_root y = r.
Proof.
  intros HV. induction 1 as [x y Hs|x y z Hs _ IH]; intros Hx.
  - destruct Hs as [u v Hf|u|u]; [by apply (HV u v)|done|done].
  - apply IH. destruct Hs as [u v Hf|u|u]; [by apply (HV u v)|done|done].
Qed.

Theorem fold_join_gap :
  swrestrict (sw_joins (gW1 :: gW2 :: gW3 :: [])) gI ⊢ₛ cpt 0 ≺ cpt 2 ∧
  ¬ sw_fold gW1 ((gW2, gI12) :: (gW3, gI) :: []) ⊢ₛ cpt 0 ≺ cpt 2.
Proof.
  split.
  - apply sw_lt_fact. simpl. split_and!.
    + eapply sw_lt_trans; apply sw_lt_fact.
      * exists gW1. split; [set_solver|done].
      * exists gW3. split; [set_solver|done].
    + exists 0. split; [done|]. set_solver.
    + exists 2. split; [done|]. set_solver.
  - intros H. cbn [sw_fold foldl] in H.
    assert (∀ u v, (swrestrict (gW1 ⊔ gW2) gI12 ⊔ gW3) ⊢ₛ u ≺ v → pt_root u = NConst 0 → pt_root v = NConst 0)
      as Hin.
    { intros u v. apply sw_lt_root_closed. intros u' v' [(_ & _ & (c & Hc & Hc'))|Hf] Hu'; simpl in *.
      - rewrite Hc. f_equal. set_solver.
      - injection Hf as -> ->. done. }
    assert (pt_root (cpt 2) = NConst 0) as E.
    { simpl in H. apply (sw_lt_root_closed (swrestrict (swrestrict (gW1 ⊔ gW2) gI12 ⊔ gW3) gI) (NConst 0) (cpt 0) (cpt 2)); [|exact H|done].
      intros u v (Huv & _ & _) Hu. by apply (Hin u v). }
    discriminate E.
Qed.
