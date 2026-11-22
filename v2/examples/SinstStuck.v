(** * Why session types must be contractive

    [typed_sinst] (static/Sinst.v) instantiates a derivation over
    contexts whose session types are contractive. Two counterexamples
    show what fails without contractivity.

    The first one is one channel and one use of E-Sub.

      s0 = α ; X        s1 = (α ; Skip) ; X        X = µβ.β

    [unfoldS] reads both as α followed by X, so s0 ≈ s1, and
    c : (s0@x) ⊢ c : s1@x by E-Chan and E-Sub. E-Sub accepts the target
    s1 because its source s0 is not contractive either. At the
    contractive instance α := ?(∗) ; (Skip ; Skip) the two heads are the
    same receive, and the continuations (Skip ; Skip) ; X and
    ((Skip ; Skip) ; Skip) ; X are distinct terms whose unfolding is
    stuck, because X never reaches a head. [sequiv] compares stuck terms
    on the nose, so the instances are not equivalent, and no derivation
    types c at the instance of s1 ([inv_chan_sty], [typed_sinst_false]).
    The context of this derivation holds s0, which is not contractive,
    and [typed_sinst] asks the context contractive.

    The second one shows that a session variable does not guard.

      t0 = µβ. α ; β        t1 = α ; t0

    Both have the head α followed by t0, so t0 ≈ t1, and both are
    [hcontractive]. At α := Skip the instances are µβ. Skip ; β and
    Skip ; µβ. Skip ; β, two distinct stuck terms ([ss_var_guard]).
    [scontr] therefore rejects t0, because β is reached through α with no
    action before it. *)

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
  constructor; [|constructor]. vm_compute. exact I.
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
  - eapply e_sub; [apply e_chan; intros ? Hin; inversion Hin| |apply fle_refl|].
    2: { intros HC. exfalso. vm_compute in HC. exact HC. }
    apply sub_sess; [apply ss_s0_s1|apply fle_refl].
  - intros H. simpl in H. destruct (inv_chan_sty _ _ _ _ _ _ _ _ _ H _ _ _ _ eq_refl) as (e & He & Hs).
    simplify_map_eq. by apply ss_inst_not_sequiv.
Qed.

(** A session variable does not guard. *)
Definition ss_t0 : sty := SMu (SSeq (SVar 1) (SVar 0)).
Definition ss_t1 : sty := SSeq (SVar 0) ss_t0.

Lemma ss_var_guard :
  sequiv ss_t0 ss_t1 ∧ hcontractive ss_t0 ∧ ¬ scontr ss_t0 ∧
  ¬ sequiv (sinst (slist [SSkip]) ss_t0) (sinst (slist [SSkip]) ss_t1).
Proof.
  split_and!.
  - by apply sequiv_hd_eq.
  - intros n. induction n as [|n IH]; [done|]. simpl. unfold hc_step. vm_compute. done.
  - vm_compute. done.
  - intros H. specialize (H 1). vm_compute in H. discriminate H.
Qed.
