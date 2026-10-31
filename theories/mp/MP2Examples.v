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

(** A main program: one thread selects the tree Node(Leaf, Leaf) on a
    channel of type TreeChannel; Wait⁹ with sequence 1 + 2k, the other
    receives it with receiveTree and waits. *)

Definition K0 : msty := MEnd (PZ 9) true.
Definition Qc : msty := MSeq TC K0.

Definition rt_sender : expr :=
  App EClos (App ESel1 (App ESel1 (App ESend (Pair EUnit (App ESel2 (Var 1)))))).

Definition rt_main : expr :=
  App (Lam (LetP (App ENew EUnit)
    (LetU (App ESpawn (Lam rt_sender))
          (App (Lam (App EClos (Var 0))) (App (Var 2) (Var 1)))))) receiveTree.

Definition NN (h : Z) : msty := MSeq (MRcv (PZ h) MPUnit) (MSeq TC TC).

Lemma pc0_val v ts : models pc0 v ts → v = [] ∧ ts = [].
Proof. done. Qed.

Ltac oeq0 := intros ?v ?ts [-> ->]; apply oeq_hdt; vm_compute; reflexivity.
Ltac plt0 := right; intros ?v ?ts [-> ->] ?l ?Hl; simpl in Hl;
  repeat (apply elem_of_cons in Hl as [->|Hl]; [vm_compute; done|]); by apply elem_of_nil in Hl.
Ltac seq0 := intros ?ss ?Hl ?Hf; destruct ss; [|discriminate]; rewrite !sinst_nil.

Lemma rt_sender_typed : ∃ ef e',
  mtyped pc0 [Some MUnit; Some (MCh true Qc (PR (PZ 1) 2)); None; None] rt_sender MUnit ef e'.
Proof.
  do 2 eexists. unfold rt_sender.
  eapply (m_close _ _ _ _ true (PZ 9) true (PR (PZ 7) 2)); [|done].
  eapply (m_eq _ _ _ _ true (MSeq MSkip K0) _ (PR (PZ 7) 2) (PR (PZ 7) 2)); [|split; [|split; [done|oeq0]]].
  2:{ seq0. apply seq_skip_l, hcontractive_contractive, hcontractive_end. }
  eapply (m_sel _ _ _ _ true (PZ 5) (MSeq MSkip K0) (MSeq (NN 6) K0) (PR (PZ 7) 2) _ false); [|split; [done|plt0]].
  eapply (m_eq _ _ _ _ true (MSeq (MSeq MSkip TC) K0) _ (PR (PZ 5) 2) (PR (PZ 7) 2)); [|split; [|split; [done|oeq0]]].
  2:{ seq0. apply seq_unf. vm_compute. reflexivity. }
  eapply (m_sel _ _ _ _ true (PZ 3) (MSeq (MSeq MSkip TC) K0) (MSeq (MSeq (NN 4) TC) K0) (PR (PZ 5) 2) _ false);
    [|split; [done|plt0]].
  eapply (m_eq _ _ _ _ true (MSeq (MSeq TC TC) K0) _ (PR (PZ 3) 2) (PR (PZ 5) 2)); [|split; [|split; [done|oeq0]]].
  2:{ seq0. apply seq_unf. vm_compute. reflexivity. }
  eapply (m_send _ _ [None; None; None; None] [Some _; Some _; None; None] _ _ _ _ true (PZ 2) MPUnit
            (MSeq (MSeq TC TC) K0) (PR (PZ 3) 2)); [msp|apply m_unit; allun| |split; [done|split; [apply plt_none|plt0]]|apply plt_nil|apply plt_none].
  eapply (m_eq _ _ _ _ true (MSeq (NN 2) K0) _ (PR (PZ 3) 2) (PR (PZ 3) 2)); [|split; [|split; [done|oeq0]]].
  2:{ seq0. cbn. apply seq_assoc; [apply hcontractive_rcv|apply hcontractive_seq; apply TDu_hc|apply hcontractive_end]. }
  eapply (m_sel _ _ _ _ true (PZ 1) (MSeq MSkip K0) (MSeq (NN 2) K0) (PR (PZ 3) 2) _ true); [|split; [done|plt0]].
  eapply (m_eq _ _ _ _ true Qc _ (PR (PZ 1) 2) (PR (PZ 3) 2)); [|split; [|split; [done|oeq0]]].
  2:{ seq0. apply seq_unf. vm_compute. reflexivity. }
  apply m_var. onlyun.
Qed.

Lemma rt_main_typed : ∃ ef e', mtyped pc0 [] rt_main MUnit ef e'.
Proof.
  destruct (receiveTree_typed pc0) as [er Hr]. destruct rt_sender_typed as (es & es' & Hs).
  do 2 eexists. unfold rt_main.
  eapply (m_let _ _ [] []); [msp|exact Hr| |apply plt_nil].
  eapply (m_new _ _ _ _ Qc (PZ 1) 2).
  eapply (m_letu _ _ [Some _; None; None] [None; Some _; Some _]); [msp| | |apply plt_nil].
  - eapply m_fork. eapply m_lam. exact Hs.
  - eapply (m_let _ _ [None; Some _; Some _] [None; None; Some _]); [msp| | |apply plt_none].
    + eapply (m_appseg _ _ [None; None; Some _] [None; Some _; None] _ _ _ _ false 1 (MSeq TC (MTV 0)) (MTV 0) [K0]);
        [msp|apply m_var; onlyun|done|by apply Forall_singleton| |cbn; split; [done|lia]|cbn; lia
        |apply m_var; onlyun|apply plt_nil|apply pntop_nil].
      intros ss Hl _. destruct ss; [|discriminate]. apply Forall_singleton. apply hcontractive_end.
    + eapply (m_open _ _ _ _ 0 false K0 0 MUnit); [done|cbn; set_solver|cbn; set_solver|].
      cbn. eapply (m_close _ _ _ _ false (PZ 9) true (PX 0 [])); [apply m_var; onlyun|done].
Qed.

Theorem rt_mp2_deadlock_free : ∃ ef e', mtyped pc0 [] rt_main MUnit ef e' ∧ deadlock_free (∅, {[+ e' +]}).
Proof.
  destruct rt_main_typed as (ef & e' & H). exists ef, e'. split; [done|]. by eapply mp2_deadlock_free.
Qed.

(** ** Branches that order a channel differently (mordido-perez.md §9.5, T2)

      c : ⊕¹{A: !⁵Unit; Close⁶, B: !²Unit; Close⁶}      d : Close³
      T1 = select A c; send () c; close c
      T2 = match c′ with { A → wait d′; receive c′; wait c′
                         , B → receive c′; wait d′; wait c′ }
      T3 = close d
      main = new c, new d, fork T1, fork T3, T2

    The two branches of T2 order c′ and d′ in opposite ways. Version 1
    already typed it through branch roots; here it runs through the
    version 2 judgment. *)

Definition t2K1 : msty := MSeq (MSnd (PZ 5) MPUnit) (MEnd (PZ 6) false).
Definition t2K2 : msty := MSeq (MSnd (PZ 2) MPUnit) (MEnd (PZ 6) false).
Definition t2Qc : msty := MSel (PZ 1) t2K1 t2K2.
Definition t2Qd : msty := MEnd (PZ 3) false.

Definition t2_T1 : expr := App EClos (App ESend (Pair EUnit (App ESel1 (Var 4)))).
Definition t2_T3 : expr := App EClos (Var 1).
Definition t2_T2 : expr :=
  Case (App EBra (Var 2))
    (LetU (App EClos (Var 2)) (LetP (App ERecv (Var 0)) (App EClos (Var 0))))
    (LetP (App ERecv (Var 0)) (LetU (App EClos (Var 4)) (App EClos (Var 0)))).

Definition t2_main : expr :=
  LetP (App ENew EUnit) (LetP (App ENew EUnit)
    (LetU (App ESpawn (Lam t2_T1)) (LetU (App ESpawn (Lam t2_T3)) t2_T2))).

Abbreviation p01 := (PR (PZ 0) 1).

Lemma t2_main_typed : ∃ ef e', mtyped pc0 [] t2_main MUnit ef e'.
Proof.
  do 2 eexists. unfold t2_main.
  eapply (m_new _ _ _ _ t2Qc (PZ 0) 1). eapply (m_new _ _ _ _ t2Qd (PZ 0) 1).
  eapply (m_letu _ _ [None; None; None; Some _] [Some _; Some _; Some _; None]); [msp| | |apply plt_nil].
  { (* T1 *)
    eapply m_fork. eapply m_lam. unfold t2_T1.
    eapply (m_close _ _ _ _ false (PZ 6) false p01); [|done].
    eapply (m_send _ _ [None; None; None; None; None] [Some _; None; None; None; Some _] _ _ _ _ false (PZ 5) MPUnit
              (MEnd (PZ 6) false) p01); [msp|apply m_unit; allun| |split; [done|split; [apply plt_none|plt0]]|apply plt_nil|apply plt_none].
    change (sndQ false (PZ 5) MPUnit (MEnd (PZ 6) false)) with t2K1.
    eapply (m_sel _ _ _ _ false (PZ 1) t2K1 t2K2 p01 _ false); [|split; [done|plt0]].
    apply m_var; onlyun. }
  eapply (m_letu _ _ [Some _; None; None; None] [None; Some _; Some _; None]); [msp| | |apply plt_nil].
  { (* T3 *)
    eapply m_fork. eapply m_lam. unfold t2_T3.
    eapply (m_close _ _ _ _ true (PZ 3) false p01); [apply m_var; onlyun|done]. }
  (* T2 *)
  unfold t2_T2. eapply (m_sub _ _ _ _ _ _ [PTop]); [|right; left; set_solver].
  eapply (m_match _ _ [None; None; Some _; None] [None; Some _; None; None] _ _ _ _ _ _ true (PZ 1) t2K1 t2K2 p01);
    [msp|apply m_var; onlyun|split; [done|plt0]| | |plt0].
  - (* A *)
    eapply (m_sub _ _ _ _ _ _ [PTop]); [|right; left; set_solver].
    eapply (m_letu _ _ [None; None; Some _; None; None] [Some _; None; None; None; None]); [msp| | |].
    + eapply (m_close _ _ _ _ false (PZ 3) false p01); [apply m_var; onlyun|done].
    + eapply (m_recv _ _ [Some _; None; None; None; None] [None; None; None; None; None] _ _ _ _ true (PZ 5) MPUnit
                (MEnd (PZ 6) false) p01); [msp|apply m_var; onlyun|split; [done|split; [apply plt_none|plt0]]| |apply plt_none].
      eapply (m_close _ _ _ _ true (PZ 6) false p01); [apply m_var; onlyun|done].
    + plt0.
  - (* B *)
    eapply (m_sub _ _ _ _ _ _ [PTop]); [|right; left; set_solver].
    eapply (m_recv _ _ [Some _; None; None; None; None] [None; None; Some _; None; None] _ _ _ _ true (PZ 2) MPUnit
              (MEnd (PZ 6) false) p01); [msp|apply m_var; onlyun|split; [done|split; [apply plt_none|plt0]]| |plt0].
    eapply (m_letu _ _ [None; None; None; None; Some _; None; None] [Some _; Some _; None; None; None; None; None]);
      [msp| | |].
    + eapply (m_close _ _ _ _ false (PZ 3) false p01); [apply m_var; onlyun|done].
    + eapply (m_close _ _ _ _ true (PZ 6) false p01); [apply m_var; onlyun|done].
    + plt0.
Qed.

Theorem t2_mp2_deadlock_free : ∃ ef e', mtyped pc0 [] t2_main MUnit ef e' ∧ deadlock_free (∅, {[+ e' +]}).
Proof.
  destruct t2_main_typed as (ef & e' & H). exists ef, e'. split; [done|]. by eapply mp2_deadlock_free.
Qed.
