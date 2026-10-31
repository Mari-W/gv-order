(** * Examples of Mordido and Pérez through the general translation, version 2

    Each program is typed in [mtyped], the judgment of Mordido and Pérez
    on our terms, and [mp2_deadlock_free] makes its translation deadlock
    free. No derivation in the static system is written by hand. *)

From stdpp Require Import base list numbers sets.
From LRGV Require Export mp.MP2Translate.

(** ** Tactics *)

Ltac msp := repeat (first [apply ms_nil | apply ms_none | apply ms_l | apply ms_r | (apply ms_un; [exact I|])]).

Definition okun (o : option mty) : Prop := match o with Some t => mun t | None => True end.

Fixpoint ouc (Γ : menv) (k : option nat) : Prop :=
  match Γ with
  | [] => True
  | o :: Γ' => (k = Some 0 ∨ okun o) ∧ ouc Γ' (match k with Some (S k') => Some k' | _ => None end)
  end.

Lemma ouc_sound Γ x : ouc Γ (Some x) → ∀ y t', y ≠ x → Γ !! y = Some (Some t') → mun t'.
Proof.
  assert (∀ Γ, ouc Γ None → ∀ y t', Γ !! y = Some (Some t') → mun t') as Hn.
  { intros Γ0. induction Γ0 as [|o Γ0 IH]; intros HH [|y] t' Hy; simpl in *; try done;
      destruct HH as [Ho H].
    - injection Hy as ->. by destruct Ho.
    - by apply (IH H y). }
  revert x. induction Γ as [|o Γ IH]; intros x HH [|y] t' Hne Hy; simpl in *; try done;
    destruct HH as [Ho H].
  - injection Hy as ->. destruct Ho as [[=->]|Ho]; [done|exact Ho].
  - destruct x as [|x].
    + by apply (Hn Γ H y).
    + apply (IH x H y); [lia|done].
Qed.

Ltac onlyun := split; [reflexivity|]; apply ouc_sound; cbn; tauto.

Ltac allun :=
  let t := fresh "t" in let Ht := fresh "Ht" in
  intros t Ht; repeat (apply elem_of_cons in Ht as [Ht|Ht]; [first [discriminate Ht | injection Ht as ->; exact I]|]);
  by apply elem_of_nil in Ht.

Lemma plt_nil Θ lo : plt Θ [] lo.
Proof. by left. Qed.

Lemma plt_none Θ ef : plt Θ ef [].
Proof. right. intros v ts _ l Hl. by apply elem_of_nil in Hl. Qed.

Lemma pntop_nil Θ : pntop Θ [].
Proof. intros v ts _. done. Qed.

Lemma sinst_nil s : sinst (slist []) s = s.
Proof. apply sinst_id_mut. intros a. unfold slist. simpl. f_equal. lia. Qed.

(** ** The tree channel and receiveTree (p. 5, p. 21)

      TreeChannel = µβ.∀^S ι. &^ι{LeafC: Skip, NodeC: ?^{ι+1} Unit; β; β}
      receiveTree : ∀a. TreeChannel; a →^{⊤,⊤} ∃. a
      receiveTree c = match c with
                        { LeafC c → c
                        , NodeC c → let (x, c) = receive c in
                                    let c = receiveTree[TreeChannel; a] c in
                                    receiveTree[a] c }

    The paper's Int becomes Unit, and the function returns the channel
    without the tree, as in Fig. 1 there are no data types. The latent
    effect ⊤ makes it a function over a segment. *)

Definition TCb : msty := MBra (PI 0) MSkip (MSeq (MRcv (PI 1) MPUnit) (MSeq MVar MVar)).
Definition TC : msty := MRec TCb.

Definition rt_ty : mty := MSeg false 1 (MSeq TC (MTV 0)) (MTV 0).

Definition receiveTree : expr :=
  EBox (Lam (Case (App EBra (Var 0))
    (Var 0)
    (LetP (App ERecv (Var 0)) (App (Lam (App (Var 5) (Var 0))) (App (Var 4) (Var 0)))))).

Definition TDu : sty := SMu (SWith SSkip (SSeq (SRcv 0 U) (SSeq (SVar 0) (SVar 0)))).

Lemma ers_TC : ers TC = TDu.
Proof. done. Qed.

Lemma sinst_TDu σ : sinst σ TDu = TDu.
Proof. done. Qed.

Lemma unfoldS_TDu : unfoldS TDu = SWith SSkip (SSeq (SRcv 0 U) (SSeq TDu TDu)).
Proof. reflexivity. Qed.

Lemma TDu_contractive : contractive TDu.
Proof. unfold contractive. by rewrite unfoldS_TDu. Qed.

Lemma TDu_hc : hcontractive TDu.
Proof.
  apply (hc_ind (λ s, s = TDu)); [|done]. intros n s -> IH.
  specialize (IH TDu eq_refl). rewrite ahc_S. unfold hc_step.
  rewrite (hd_of _ _ unfoldS_TDu). cbn [view]. split; [apply hcontractive_skip|].
  apply ahc_seq; [apply hcontractive_rcv|by apply ahc_seq].
Qed.

Lemma TDu_seq s :
  seq (SSeq TDu s) (SWith (SSeq SSkip s) (SSeq (SSeq (SRcv 0 U) (SSeq TDu TDu)) s)).
Proof.
  apply seq_unf. rewrite unfoldS_seq_hd; [|apply TDu_contractive|by rewrite unfoldS_TDu].
  by rewrite unfoldS_TDu, unfoldS_with.
Qed.

Lemma node_rcvu s : hcontractive s →
  seq (SSeq (SSeq (SRcv 0 U) (SSeq TDu TDu)) s) (SSeq (SRcv 0 U) (SSeq TDu (SSeq TDu s))).
Proof.
  intros Hs. eapply seq_trans; [apply seq_assoc|apply seq_rcv_cong, seq_assoc];
    auto using hcontractive_rcv, hcontractive_seq, TDu_hc.
Qed.

Lemma hc1 (P : sty → Prop) ss : length ss = 1 → Forall hcontractive ss →
  (∀ s, hcontractive s → P s) → ∃ s, ss = [s] ∧ P s.
Proof. intros Hl Hf H. destruct ss as [|s [|]]; try discriminate. exists s. split; [done|]. apply H. by inversion Hf. Qed.

Ltac one_inst := let ss := fresh "ss" in let Hl := fresh "Hl" in let Hf := fresh "Hf" in
  intros ss Hl Hf; destruct ss as [|?s [|]]; try discriminate; rewrite Forall_singleton in Hf.

Lemma receiveTree_typed Θ : ∃ e', mtyped Θ [] receiveTree rt_ty [] e'.
Proof.
  eexists. unfold receiveTree, rt_ty. eapply m_fixseg; [allun|cbn; split; [done|lia]|cbn; lia|].
  (* match on the tree *)
  eapply (m_match _ _ [Some _; None] [None; Some _] _ _ _ _ _ _ false (PZ 0)
            (MSeq MSkip (MTV 0)) (MSeq (MSeq (MRcv (PZ 1) MPUnit) (MSeq TC TC)) (MTV 0)) (PX 0 []));
    [msp| | done | | |apply plt_none].
  - eapply m_eq; [apply m_var; onlyun|]. split; [|split; done].
    one_inst. cbn. apply TDu_seq.
  - (* LeafC *)
    eapply (m_sub _ _ _ _ _ [] [PTop]); [|right; left; set_solver].
    eapply (m_pack _ _ _ _ _ _ (PX 0 [WB false])). eapply m_eq; [apply m_var; onlyun|]. split; [|split; done].
    one_inst. cbn. match goal with H : hcontractive _ |- _ => exact (seq_skip_l _ (hcontractive_contractive _ H)) end.
  - (* NodeC *)
    eapply m_sub; [|right; left; set_solver].
    eapply (m_recv _ _ [Some _; None; None] [None; None; Some _] _ _ _ _ false (PZ 1) MPUnit
              (MSeq TC (MSeq TC (MTV 0))) (PX 0 [WB true])); [msp| |done| |apply plt_none].
    + eapply m_eq; [apply m_var; onlyun|]. split; [|split; done].
      one_inst. cbn. by apply node_rcvu.
    + eapply (m_let _ _ [Some _; None; None; None; Some _] [None; Some _; None; None; Some _]); [msp| | |].
      * eapply (m_appseg _ _ [None; None; None; None; Some _] [Some _; None; None; None; None] _ _ _ _
                  false 1 (MSeq TC (MTV 0)) (MTV 0) [MSeq TC (MTV 0)]);
          [msp|apply m_var; onlyun|done|apply Forall_singleton; cbn; split; [done|lia]| |cbn; split; [done|lia]|cbn; lia
          |apply m_var; onlyun|apply plt_nil|apply pntop_nil].
        one_inst. apply Forall_singleton. cbn.
        by apply hcontractive_seq; [apply TDu_hc|].
      * eapply (m_open _ _ _ _ 0 false (MSeq TC (MTV 0)) 1 (MEx false (MTV 0))); [done|cbn; set_solver|cbn; set_solver|].
        cbn. eapply (m_appseg _ _ [None; None; Some _; None; None; Some _] [Some _; None; None; None; None; None] _ _ _ _
                  false 1 (MSeq TC (MTV 0)) (MTV 0) [MTV 0]);
          [msp|apply m_var; onlyun|done|apply Forall_singleton; cbn; lia| |cbn; split; [done|lia]|cbn; lia
          |apply m_var; onlyun|apply plt_nil|apply pntop_nil].
        one_inst. apply Forall_singleton. done.
      * apply plt_none.
Qed.
