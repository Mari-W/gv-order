(** * Session instantiation does not preserve typing

    The lemma [typed_sinst] that finding 6.1 of
    docs/redesign/algorithmic-plan.md asks for, "a derivation instantiated
    at scoped, contractive session types is a derivation", is false for
    the judgment as it stands. The counterexample is one channel and one
    use of E-Sub.

      s0 = α ; X        s1 = (α ; Skip) ; X        X = µβ.β

    [unfoldS] reads both as α followed by X, so s0 ≈ s1, and
    c : (s0@x) ⊢ c : s1@x by E-Chan and E-Sub. At the instance
    α := ?(∗) ; (Skip ; Skip), which [sinsts] admits, the two heads are
    the same receive, but the continuations (Skip ; Skip) ; X and
    ((Skip ; Skip) ; Skip) ; X are distinct terms whose unfolding is stuck,
    because X never reaches a head. [sequiv] compares stuck terms on the
    nose, so the instances are not equivalent, and no derivation types c
    at the instance of s1 ([inv_chan_sty]). The tail X is not contractive.
    Contractive instances cannot repair a session type of the derivation
    that is not contractive itself. *)

From GV Require Export static.Inversion.

Definition ss_X : sty := SMu (SVar 0).
Definition ss_s0 : sty := SSeq (SVar 0) ss_X.
Definition ss_s1 : sty := SSeq (SSeq (SVar 0) SSkip) ss_X.

(** The instance ?(∗) ; (Skip ; Skip). *)
Definition ss_t : sty := SSeq (SRcv 0 TUnit) (SSeq SSkip SSkip).

Lemma ss_s0_s1 : sequiv ss_s0 ss_s1.
Proof.
  apply (sequiv_coind (λ s r, (s = ss_s0 ∧ r = ss_s1) ∨ s = r)); [|by left].
  intros s r [[-> ->]| ->].
  - unfold eq_step. vm_compute. split; [done|]. by right.
  - unfold eq_step. hd_cases r; try done; split_and?; try done; try (by right);
      apply eqT_refl; intros; by right.
Qed.

Lemma ss_t_sinsts N : sinsts N [ss_t].
Proof.
  split; [split|]; [|by repeat constructor|by repeat constructor].
  constructor; [|constructor]. intros [|[|n]]; vm_compute; done.
Qed.

Lemma ss_inst_not_sequiv : ¬ sequiv (sinst (slist [ss_t]) ss_s0) (sinst (slist [ss_t]) ss_s1).
Proof. intros H. specialize (H 2). vm_compute in H. destruct H as (_ & _ & H). discriminate H. Qed.

(** E-Chan and E-Sub type c at s1, the instance at [ss_t] of that
    derivation has no typing. *)
Theorem typed_sinst_false W N Γ F o x a :
  sinsts N [ss_t] ∧
  typed W N {[o := TE ss_s0 x a a]} Γ [] F (Chan o) (TSess ss_s1 x a a) (Some 0) ∧
  ¬ typed W N {[o := TE (sinst (slist [ss_t]) ss_s0) x a a]} Γ [] F (Chan o)
      (sinst_ty (slist [ss_t]) (TSess ss_s1 x a a)) (Some 0).
Proof.
  split_and!.
  - apply ss_t_sinsts.
  - eapply e_sub; [apply e_chan; intros ? Hin; inversion Hin| |apply fle_refl].
    apply sub_sess; [apply ss_s0_s1|apply fle_refl].
  - intros H. simpl in H. destruct (inv_chan_sty _ _ _ _ _ _ _ _ _ H _ _ _ _ eq_refl) as (e & He & Hs).
    simplify_map_eq. by apply ss_inst_not_sequiv.
Qed.
