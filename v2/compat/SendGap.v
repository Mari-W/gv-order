(** * A value in V that no send can hand over (stage S4, report)

    O-Send asks the moved environment Θ_M to have exactly the ends of
    the transfer set M, the ends the payload mentions (decision Q3). No
    V clause relates the ends of a value to its environment (§2.7). So a
    value in V may mention an end it does not own, and then no Θ_M fits.

    The closure w' = λ_. let ∗ = Ω in close q⁺ mentions q⁺, owns
    nothing, and is in V^W _ n⟦∅ ⊢ ∗ ⊸ ∗⟧ at every level, because its
    body only takes β steps. The pair ⟨w', d⁺⟩ is in V at the payload
    type of d⁺, but send ⟨w', d⁺⟩ is not in E at level 1: the label moves
    {q⁺}, and the sender holds no q⁺ ([send_gap]).

    The same holds for every value of V from outside a thread: O-Recv
    and Q-Recv quantify over every received value in V, and the arrow
    over every argument in V. A forwarder that receives a closure and
    sends it on is typable, and for the received w' it is not in E, so
    the fundamental theorem fails for it. *)

From GV Require Export compat.SemTyped.

Definition ω : expr := Lam (App (Var 0) (Var 0)).
Definition Ω : expr := App ω ω.

Lemma tstep_Ω α e' : tstep Ω α e' → α = LBeta ∧ e' = Ω.
Proof.
  intros H. apply tstep_inv in H as [Hh|(f & e0 & e0' & Hf & Heq & -> & Hs)].
  - inversion Hh; subst. done.
  - destruct f; simpl in Heq; try discriminate; injection Heq as <- <-;
      exfalso; apply (val_no_tstep _ _ _ Hs); done.
Qed.

Lemma tstep_dead e α e' : tstep (LetU Ω e) α e' → α = LBeta ∧ e' = LetU Ω e.
Proof.
  intros H. destruct (tstep_fill_inv (FLetU e) Ω α e' I ltac:(simpl; tauto) H) as (e0 & Hs & ->).
  apply tstep_Ω in Hs as [-> ->]. done.
Qed.

(** let ∗ = Ω in e is in E of κ_DF at every level, environment, type and
    future: its only step is a β step back to itself, of cost 1. *)
Lemma Erel_dead n W Θ T F e : Erel κ_DF n W Θ T F (LetU Ω e).
Proof.
  revert W Θ T F. induction n as [|n IH]; intros W Θ T F; [apply Erel_0|].
  apply Erel_S_iff. intros W1 HW1.
  assert (tstep (LetU Ω e) LBeta (LetU Ω e)) as Hst.
  { apply (t_act_ctx (FLetU e)); [done|]. apply tstep_head. by apply (t_act_app (App (Var 0) (Var 0)) ω). }
  split; [|split; [|unfold Esteps; split_and!]].
  4-12: intros; match goal with H : tstep _ _ _ |- _ => apply tstep_dead in H as [? _]; discriminate end.
  - intros Hirr. exfalso. exact (Hirr _ _ Hst).
  - intros _ Hs. destruct (Hs _ _ Hst) as [σ Hσ]. discriminate.
  - intros e' He'. apply tstep_dead in He' as [_ ->]. split; [done|]. intros _. simpl. rewrite Nat.sub_0_r. apply IH.
Qed.

Definition w_dead (q : cend) : expr := Lam (LetU Ω (EClose (Chan q))).

Definition T_thunk : ty := TLolli None None None tinf None TUnit None TUnit None.

Lemma Vrel_dead n W q : Vrel κ_DF n W ∅ T_thunk (w_dead q).
Proof.
  apply Vrel_lolli_iff. exists (LetU Ω (EClose (Chan q))). split_and!; [done| |].
  - simpl. by rewrite senv_heads_empty.
  - intros W' j Θ' w F _ _ _ _ _. apply Erel_dead.
Qed.

Definition wempty : world := World ∅ (λ _, False) ∅ (λ _ _, False).

Definition S_snd : sty := SSeq (SSnd 0 T_thunk None) SEnd.

Lemma unfoldS_S_snd : unfoldS S_snd = SSeq (SSnd 0 T_thunk None) SEnd.
Proof. reflexivity. Qed.

(** The semantic E-Send rule fails: the argument is in V at every level,
    and the send is not in E at level 1. *)
Theorem send_gap (q d : chan) (z : point) :
  let v := Pair (w_dead q⁺) (Chan d⁺) in
  let Θ := {[(d⁺)%cend := (S_snd, z)]} : senv in
  unfoldS S_snd = SSeq (SSnd 0 T_thunk None) SEnd ∧
  (∀ n, Vrel κ_DF n wempty Θ (TProd T_thunk None (TSess S_snd z) None) v) ∧
  ¬ Erel κ_DF 1 wempty Θ (TSess SEnd z⁺) ∅ (ESend v).
Proof.
  intros v Θ. split_and!; [reflexivity| |].
  - intros n. apply Vrel_prod_iff. exists (w_dead q⁺), (Chan d⁺), ∅, Θ.
    split_and!; [done|apply map_disjoint_empty_l|by rewrite map_empty_union|apply Vrel_dead|].
    apply Vrel_sess_iff. exists (d⁺)%cend, S_snd. split_and!; [done|done|apply seqv_refl].
  - intros HE.
    assert (tstep (ESend v) (LSess (SSend (d⁺)%cend (fends (w_dead q⁺)) (w_dead q⁺))) (Chan d⁺)) as Hst.
    { apply tstep_head. by apply t_act_send. }
    pose proof (Erel_S_step κ_DF 0 _ _ _ _ _ _ _ _ HE (wext_refl _) Hst) as H. simpl in H.
    destruct H as (S0 & x & m & U & b & S & ΘM & Θr & A1 & A2 & A3 & A4 & A5 & _).
    assert (delete (d⁺)%cend Θ = ∅) as Hdel by (unfold Θ; apply delete_singleton_eq).
    rewrite Hdel in A4. symmetry in A4. apply map_positive_l in A4 as ->.
    rewrite dom_empty_L in A5. set_solver.
Qed.
