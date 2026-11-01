(** * Examples of Mordido and Pérez through the general translation, version 3

    Version 3 (docs/extensions/adequacy/mordido-perez.md, section 15)
    is version 2 with n-ary choices and with channels created after a
    segment call. The text below describes version 2 where version 3
    agrees with it.

    Each program is typed in [mtyped], the judgment of Mordido and Pérez
    on our terms, and [mp3_deadlock_free] makes its translation deadlock
    free. No derivation in the static system is written by hand. *)

From stdpp Require Import base list numbers sets.
From LRGV Require Export mp.MP3Translate.

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
  eexists. unfold receiveTree, rt_ty. eapply m_fixseg; [allun|cbn; split; [done|lia]|cbn; lia| |shelve].
  (* match on the tree *)
  eapply (m_match _ _ [Some _; None] [None; Some _] _ _ _ _ _ _ false (PZ 0)
            (MSeq MSkip (MTV 0)) (MSeq (MSeq (MRcv (PZ 1) MPUnit) (MSeq TC TC)) (MTV 0)) (PX 0 []));
    [msp| | done | | |apply plt_none].
  - eapply m_eq; [apply m_var; onlyun|]. split; [|split; done].
    one_inst. cbn. apply TDu_seq.
  - (* LeafC *)
    eapply (m_sub _ _ _ _ _ [] [PTop]); [|right; left; split; [set_solver|shelve]].
    eapply (m_pack _ _ _ _ _ _ (PX 0 [WB false])); [|done]. eapply m_eq; [apply m_var; onlyun|]. split; [|split; done].
    one_inst. cbn. match goal with H : hcontractive _ |- _ => exact (seq_skip_l _ (hcontractive_contractive _ H)) end.
  - (* NodeC *)
    eapply m_sub; [|right; left; split; [set_solver|shelve]].
    eapply (m_recv _ _ [Some _; None; None] [None; None; Some _] _ _ _ _ false (PZ 1) MPUnit
              (MSeq TC (MSeq TC (MTV 0))) (PX 0 [WB true])); [msp| |done| |apply plt_none].
    + eapply m_eq; [apply m_var; onlyun|]. split; [|split; done].
      one_inst. cbn. by apply node_rcvu.
    + eapply (m_let _ _ [Some _; None; None; None; Some _] [None; Some _; None; None; Some _]); [msp| | |].
      * eapply (m_appseg _ _ [None; None; None; None; Some _] [Some _; None; None; None; None] _ _ _ _
                  false 1 (MSeq TC (MTV 0)) (MTV 0) [MSeq TC (MTV 0)]);
          [msp|apply m_var; onlyun|done|apply Forall_singleton; cbn; split; [done|lia]| |cbn; split; [done|lia]|cbn; lia
          |apply m_var; onlyun|done|apply plt_nil|apply pntop_nil|set_solver].
        one_inst. apply Forall_singleton. cbn.
        by apply hcontractive_seq; [apply TDu_hc|].
      * eapply (m_open _ _ _ _ 0 false (MSeq TC (MTV 0)) 1 (MEx false (MTV 0))); [done|cbn; set_solver|cbn; set_solver|].
        cbn. eapply (m_appseg _ _ [None; None; Some _; None; None; Some _] [Some _; None; None; None; None; None] _ _ _ _
                  false 1 (MSeq TC (MTV 0)) (MTV 0) [MTV 0]);
          [msp|apply m_var; onlyun|done|apply Forall_singleton; cbn; lia| |cbn; split; [done|lia]|cbn; lia
          |apply m_var; onlyun|done|apply plt_nil|apply pntop_nil|set_solver].
        one_inst. apply Forall_singleton. done.
      * apply plt_none.
  Unshelve. all: set_solver.
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
  eapply (m_sel _ _ _ _ true (PZ 5) (MSeq MSkip K0) (MSeq (NN 6) K0) (PR (PZ 7) 2) _ false); [|split; [done|left; plt0]].
  eapply (m_eq _ _ _ _ true (MSeq (MSeq MSkip TC) K0) _ (PR (PZ 5) 2) (PR (PZ 7) 2)); [|split; [|split; [done|oeq0]]].
  2:{ seq0. apply seq_unf. vm_compute. reflexivity. }
  eapply (m_sel _ _ _ _ true (PZ 3) (MSeq (MSeq MSkip TC) K0) (MSeq (MSeq (NN 4) TC) K0) (PR (PZ 5) 2) _ false);
    [|split; [done|left; plt0]].
  eapply (m_eq _ _ _ _ true (MSeq (MSeq TC TC) K0) _ (PR (PZ 3) 2) (PR (PZ 5) 2)); [|split; [|split; [done|oeq0]]].
  2:{ seq0. apply seq_unf. vm_compute. reflexivity. }
  eapply (m_send _ _ [None; None; None; None] [Some _; Some _; None; None] _ _ _ _ true (PZ 2) MPUnit
            (MSeq (MSeq TC TC) K0) (PR (PZ 3) 2)); [msp|apply m_unit; allun| |split; [done|split; [apply plt_none|plt0]]|apply plt_nil|apply plt_none].
  eapply (m_eq _ _ _ _ true (MSeq (NN 2) K0) _ (PR (PZ 3) 2) (PR (PZ 3) 2)); [|split; [|split; [done|oeq0]]].
  2:{ seq0. cbn. apply seq_assoc; [apply hcontractive_rcv|apply hcontractive_seq; apply TDu_hc|apply hcontractive_end]. }
  eapply (m_sel _ _ _ _ true (PZ 1) (MSeq MSkip K0) (MSeq (NN 2) K0) (PR (PZ 3) 2) _ true); [|split; [done|left; plt0]].
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
        |apply m_var; onlyun|done|apply plt_nil|apply pntop_nil|set_solver].
      intros ss Hl _. destruct ss; [|discriminate]. apply Forall_singleton. apply hcontractive_end.
    + eapply (m_open _ _ _ _ 0 false K0 0 MUnit); [done|cbn; set_solver|cbn; set_solver|].
      cbn. eapply (m_close _ _ _ _ false (PZ 9) true (PX 0 [])); [apply m_var; onlyun|done].
Qed.

Theorem rt_mp3_deadlock_free : ∃ ef e', mtyped pc0 [] rt_main MUnit ef e' ∧ deadlock_free (∅, {[+ e' +]}).
Proof.
  destruct rt_main_typed as (ef & e' & H). exists ef, e'. split; [done|]. by eapply mp3_deadlock_free.
Qed.

(** ** A channel created after receiveTree (section 15)

    After the call, c′ has type Wait⁹ in their system and acts with
    effect ⊤ at an abstract position here. Their rules let the caller
    create d and order it against c′ in either direction.

      rtA: d : Close⁵.  close d while holding c′, then wait c′  (5 < 9)
      rtB: d : Close¹². wait c′ while holding d, then close d  (9 < 12)

    The partner of d runs in its own thread. rtA creates d below the
    floor, so every point of d lies below every walk of c′. rtB creates
    d above the ceiling, at the successor of the ceiling, so every walk
    of c′ lies below every point of d. *)

Definition QdA : msty := MEnd (PZ 5) false.
Definition QdB : msty := MEnd (PZ 12) false.

Definition rtA_cont : expr :=
  LetP (App ENew EUnit) (LetU (App ESpawn (Lam (App EClos (Var 1))))
    (LetU (App EClos (Var 1)) (App EClos (Var 2)))).
Definition rtB_cont : expr :=
  LetP (App ENew EUnit) (LetU (App ESpawn (Lam (App EClos (Var 1))))
    (LetU (App EClos (Var 2)) (App EClos (Var 1)))).

Definition rtd_main (k : expr) : expr :=
  App (Lam (LetP (App ENew EUnit)
    (LetU (App ESpawn (Lam rt_sender))
          (App (Lam k) (App (Var 2) (Var 1)))))) receiveTree.

Definition rtA_main : expr := rtd_main rtA_cont.
Definition rtB_main : expr := rtd_main rtB_cont.

Lemma rtd_main_typed k :
  (∃ ef e', mtyped pc0 [Some (MCh false K0 (PX 0 [])); None; None; Some rt_ty] k MUnit ef e') →
  ∃ ef e', mtyped pc0 [] (rtd_main k) MUnit ef e'.
Proof.
  intros (ef & ek & Hk).
  destruct (receiveTree_typed pc0) as [er Hr]. destruct rt_sender_typed as (es & es' & Hs).
  do 2 eexists. unfold rtd_main.
  eapply (m_let _ _ [] []); [msp|exact Hr| |apply plt_nil].
  eapply (m_new _ _ _ _ Qc (PZ 1) 2).
  eapply (m_letu _ _ [Some _; None; None] [None; Some _; Some _]); [msp| | |apply plt_nil].
  - eapply m_fork. eapply m_lam. exact Hs.
  - eapply (m_let _ _ [None; Some _; Some _] [None; None; Some _]); [msp| | |apply plt_none].
    + eapply (m_appseg _ _ [None; None; Some _] [None; Some _; None] _ _ _ _ false 1 (MSeq TC (MTV 0)) (MTV 0) [K0]);
        [msp|apply m_var; onlyun|done|by apply Forall_singleton| |cbn; split; [done|lia]|cbn; lia
        |apply m_var; onlyun|done|apply plt_nil|apply pntop_nil|set_solver].
      intros ss Hl _. destruct ss; [|discriminate]. apply Forall_singleton. apply hcontractive_end.
    + eapply (m_open _ _ _ _ 0 false K0 0 MUnit); [done|cbn; set_solver|cbn; set_solver|].
      cbn. exact Hk.
Qed.

Lemma rtA_main_typed : ∃ ef e', mtyped pc0 [] rtA_main MUnit ef e'.
Proof.
  apply rtd_main_typed. do 2 eexists. unfold rtA_cont.
  eapply (m_newlo _ _ _ _ QdA).
  eapply (m_letu _ _ [Some _; None; None; None; None; None] [None; Some _; Some _; None; None; Some _]);
    [msp| | |apply plt_nil].
  - eapply m_fork. eapply m_lam.
    eapply (m_close _ _ _ _ true (PZ 5) false (PL [])); [apply m_var; onlyun|done].
  - eapply (m_letu _ _ [None; Some _; None; None; None; None] [None; None; Some _; None; None; Some _]); [msp| | |].
    + eapply (m_close _ _ _ _ false (PZ 5) false (PL [])); [apply m_var; onlyun|done].
    + eapply (m_close _ _ _ _ false (PZ 9) true (PX 0 [])); [apply m_var; onlyun|done].
    + right. intros v ts _ l Hl. simpl in Hl. apply list_elem_of_singleton in Hl as ->. simpl. lia.
Qed.

Lemma rtB_main_typed : ∃ ef e', mtyped pc0 [] rtB_main MUnit ef e'.
Proof.
  apply rtd_main_typed. do 2 eexists. unfold rtB_cont.
  eapply (m_newhi _ _ _ _ QdB).
  eapply (m_letu _ _ [Some _; None; None; None; None; None] [None; Some _; Some _; None; None; Some _]);
    [msp| | |apply plt_nil].
  - eapply m_fork. eapply m_lam.
    eapply (m_close _ _ _ _ true (PZ 12) false (PH [])); [apply m_var; onlyun|done].
  - eapply (m_letu _ _ [None; None; Some _; None; None; None] [None; Some _; None; None; None; Some _]); [msp| | |].
    + eapply (m_close _ _ _ _ false (PZ 9) true (PX 0 [])); [apply m_var; onlyun|done].
    + eapply (m_close _ _ _ _ false (PZ 12) false (PH [])); [apply m_var; onlyun|done].
    + right. intros v ts _ l Hl. simpl in Hl. apply list_elem_of_singleton in Hl as ->. simpl. lia.
Qed.

Theorem rtA_mp3_deadlock_free : ∃ ef e', mtyped pc0 [] rtA_main MUnit ef e' ∧ deadlock_free (∅, {[+ e' +]}).
Proof.
  destruct rtA_main_typed as (ef & e' & H). exists ef, e'. split; [done|]. by eapply mp3_deadlock_free.
Qed.

Theorem rtB_mp3_deadlock_free : ∃ ef e', mtyped pc0 [] rtB_main MUnit ef e' ∧ deadlock_free (∅, {[+ e' +]}).
Proof.
  destruct rtB_main_typed as (ef & e' & H). exists ef, e'. split; [done|]. by eapply mp3_deadlock_free.
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
    eapply (m_sel _ _ _ _ false (PZ 1) t2K1 t2K2 p01 _ false); [|split; [done|left; plt0]].
    apply m_var; onlyun. }
  eapply (m_letu _ _ [Some _; None; None; None] [None; Some _; Some _; None]); [msp| | |apply plt_nil].
  { (* T3 *)
    eapply m_fork. eapply m_lam. unfold t2_T3.
    eapply (m_close _ _ _ _ true (PZ 3) false p01); [apply m_var; onlyun|done]. }
  (* T2 *)
  unfold t2_T2. eapply (m_sub _ _ _ _ _ _ [PTop]); [|right; left; split; [set_solver|shelve]].
  eapply (m_match _ _ [None; None; Some _; None] [None; Some _; None; None] _ _ _ _ _ _ true (PZ 1) t2K1 t2K2 p01);
    [msp|apply m_var; onlyun|split; [done|left; plt0]| | |plt0].
  - (* A *)
    eapply (m_sub _ _ _ _ _ _ [PTop]); [|right; left; split; [set_solver|shelve]].
    eapply (m_letu _ _ [None; None; Some _; None; None] [Some _; None; None; None; None]); [msp| | |].
    + eapply (m_close _ _ _ _ false (PZ 3) false p01); [apply m_var; onlyun|done].
    + eapply (m_recv _ _ [Some _; None; None; None; None] [None; None; None; None; None] _ _ _ _ true (PZ 5) MPUnit
                (MEnd (PZ 6) false) p01); [msp|apply m_var; onlyun|split; [done|split; [apply plt_none|plt0]]| |apply plt_none].
      eapply (m_close _ _ _ _ true (PZ 6) false p01); [apply m_var; onlyun|done].
    + plt0.
  - (* B *)
    eapply (m_sub _ _ _ _ _ _ [PTop]); [|right; left; split; [set_solver|shelve]].
    eapply (m_recv _ _ [Some _; None; None; None; None] [None; None; Some _; None; None] _ _ _ _ true (PZ 2) MPUnit
              (MEnd (PZ 6) false) p01); [msp|apply m_var; onlyun|split; [done|split; [apply plt_none|plt0]]| |plt0].
    eapply (m_letu _ _ [None; None; None; None; Some _; None; None] [Some _; Some _; None; None; None; None; None]);
      [msp| | |].
    + eapply (m_close _ _ _ _ false (PZ 3) false p01); [apply m_var; onlyun|done].
    + eapply (m_close _ _ _ _ true (PZ 6) false p01); [apply m_var; onlyun|done].
    + plt0.
  Unshelve. all: set_solver.
Qed.

Theorem t2_mp3_deadlock_free : ∃ ef e', mtyped pc0 [] t2_main MUnit ef e' ∧ deadlock_free (∅, {[+ e' +]}).
Proof.
  destruct t2_main_typed as (ef & e' & H). exists ef, e'. split; [done|]. by eapply mp3_deadlock_free.
Qed.

(** ** A choice with three labels (section 15)

      c : ⊕¹{A: Close², B: Close², C: Close²}
      T1 = select C c; close c
      T2 = match c with { A → wait c, B → wait c, C → wait c }
      main = new c, fork T1, T2

    Every continuation sits at 1 + 1. The choice nests as
    ⊕¹(A, ⊕^{1·1}(B, C)), where the inner node has the priority 1 at
    depth 1. Its rank lies strictly between 1 and 2, so the outer
    branch rises to it and it rises to the continuations at 2. *)

Definition K3 : msty := MEnd (PZ 2) false.
Definition Qi3 : msty := MSel (PD (PZ 1) 1) K3 K3.
Definition Q3 : msty := MSel (PZ 1) K3 Qi3.

Definition ch3_T1 : expr := App EClos (App ESel2 (App ESel2 (Var 2))).
Definition ch3_T2 : expr :=
  Case (App EBra (Var 0)) (App EClos (Var 0))
    (Case (App EBra (Var 0)) (App EClos (Var 0)) (App EClos (Var 0))).
Definition ch3_main : expr :=
  LetP (App ENew EUnit) (LetU (App ESpawn (Lam ch3_T1)) ch3_T2).

Lemma ch3_brok : br_ok pc0 p01 (PZ 1) K3 Qi3.
Proof.
  split; [done|]. right. split; [left; plt0|]. right. exists 1. split; [lia|done].
Qed.

Lemma ch3_main_typed : ∃ ef e', mtyped pc0 [] ch3_main MUnit ef e'.
Proof.
  do 2 eexists. unfold ch3_main.
  eapply (m_new _ _ _ _ Q3 (PZ 0) 1).
  eapply (m_letu _ _ [None; Some _] [Some _; None]); [msp| | |apply plt_nil].
  { (* T1 *)
    eapply m_fork. eapply m_lam. unfold ch3_T1.
    eapply (m_close _ _ _ _ false (PZ 2) false p01); [|done].
    eapply (m_sel _ _ _ _ false (PD (PZ 1) 1) K3 K3 p01 _ true); [|split; [done|left; plt0]].
    eapply (m_sel _ _ _ _ false (PZ 1) K3 Qi3 p01 _ true); [|apply ch3_brok].
    apply m_var; onlyun. }
  unfold ch3_T2.
  eapply (m_match _ _ [Some _; None] [None; None] _ _ _ _ _ _ true (PZ 1) K3 Qi3 p01);
    [msp|apply m_var; onlyun|apply ch3_brok| | |apply plt_none].
  - eapply (m_sub _ _ _ _ _ _ [PTop]); [|right; left; split; [set_solver|shelve]].
    eapply (m_close _ _ _ _ true (PZ 2) false p01); [apply m_var; onlyun|done].
  - eapply (m_sub _ _ _ _ _ _ [PTop]); [|right; left; split; [set_solver|shelve]].
    eapply (m_match _ _ [Some _; None; None] [None; None; None] _ _ _ _ _ _ true (PD (PZ 1) 1) K3 K3 p01);
      [msp|apply m_var; onlyun|split; [done|left; plt0]| | |apply plt_none].
    + eapply (m_close _ _ _ _ true (PZ 2) false p01); [apply m_var; onlyun|done].
    + eapply (m_close _ _ _ _ true (PZ 2) false p01); [apply m_var; onlyun|done].
  Unshelve. all: set_solver.
Qed.

Theorem ch3_mp3_deadlock_free : ∃ ef e', mtyped pc0 [] ch3_main MUnit ef e' ∧ deadlock_free (∅, {[+ e' +]}).
Proof.
  destruct ch3_main_typed as (ef & e' & H). exists ef, e'. split; [done|]. by eapply mp3_deadlock_free.
Qed.

(** ** The repair of the classic deadlock (p. 3)

      a : ?¹Unit; Wait³        b : ?²Unit; Wait⁴
      T1 = let (_, a) = receive a in let b = send () b in wait a; close b
      T2 = let a′ = send () a′ in let (_, b′) = receive b′ in close a′; wait b′
      main = new a, new b, fork T1, T2

    The paper's priorities R = ?^p Int; Wait^{p+2} and S = ?^q Int;
    Wait^{q+2} at p = 1, q = 2, with the two variants of f inlined. The
    deadlocking original receives first in both threads and fails the
    check of T-LetPair in one of them. *)

Definition dfQa : msty := MSeq (MRcv (PZ 1) MPUnit) (MEnd (PZ 3) true).
Definition dfQb : msty := MSeq (MRcv (PZ 2) MPUnit) (MEnd (PZ 4) true).

Definition df_T1 : expr :=
  LetP (App ERecv (Var 4)) (App (Lam (LetU (App EClos (Var 1)) (App EClos (Var 0)))) (App ESend (Pair EUnit (Var 3)))).
Definition df_T2 : expr :=
  App (Lam (LetP (App ERecv (Var 2)) (LetU (App EClos (Var 2)) (App EClos (Var 0))))) (App ESend (Pair EUnit (Var 2))).

Definition df_main : expr :=
  LetP (App ENew EUnit) (LetP (App ENew EUnit) (LetU (App ESpawn (Lam df_T1)) df_T2)).

Lemma df_main_typed : ∃ ef e', mtyped pc0 [] df_main MUnit ef e'.
Proof.
  do 2 eexists. unfold df_main.
  eapply (m_new _ _ _ _ dfQa (PZ 0) 1). eapply (m_new _ _ _ _ dfQb (PZ 0) 1).
  eapply (m_letu _ _ [Some _; None; None; Some _] [None; Some _; Some _; None]); [msp| | |apply plt_nil].
  { (* T1 *)
    eapply m_fork. eapply m_lam. unfold df_T1.
    eapply (m_recv _ _ [None; None; None; None; Some _] [Some _; Some _; None; None; None] _ _ _ _ false (PZ 1) MPUnit
              (MEnd (PZ 3) true) p01); [msp|apply m_var; onlyun|split; [done|split; [apply plt_none|plt0]]| |plt0].
    eapply (m_let _ _ [None; None; None; Some _; None; None; None] [Some _; Some _; Some _; None; None; None; None]);
      [msp| | |].
    - eapply (m_send _ _ [None; None; None; None; None; None; None] [None; None; None; Some _; None; None; None]
                _ _ _ _ true (PZ 2) MPUnit (MEnd (PZ 4) true) p01);
        [msp|apply m_unit; allun|apply m_var; onlyun|split; [done|split; [apply plt_none|plt0]]|apply plt_nil|apply plt_none].
    - eapply (m_letu _ _ [None; Some _; None; None; None; None; None; None] [Some _; None; Some _; Some _; None; None; None; None]);
        [msp| | |].
      + eapply (m_close _ _ _ _ false (PZ 3) true p01); [apply m_var; onlyun|done].
      + eapply (m_close _ _ _ _ true (PZ 4) true p01); [apply m_var; onlyun|done].
      + plt0.
    - plt0. }
  (* T2 *)
  unfold df_T2.
  eapply (m_let _ _ [None; None; Some _; None] [None; Some _; None; None]); [msp| | |].
  - eapply (m_send _ _ [None; None; None; None] [None; None; Some _; None]
              _ _ _ _ true (PZ 1) MPUnit (MEnd (PZ 3) true) p01);
      [msp|apply m_unit; allun|apply m_var; onlyun|split; [done|split; [apply plt_none|plt0]]|apply plt_nil|apply plt_none].
  - eapply (m_recv _ _ [None; None; Some _; None; None] [Some _; None; None; None; None] _ _ _ _ false (PZ 2) MPUnit
              (MEnd (PZ 4) true) p01); [msp|apply m_var; onlyun|split; [done|split; [apply plt_none|plt0]]| |].
    + eapply (m_letu _ _ [None; None; Some _; None; None; None; None] [Some _; Some _; None; None; None; None; None]);
        [msp| | |].
      * eapply (m_close _ _ _ _ true (PZ 3) true p01); [apply m_var; onlyun|done].
      * eapply (m_close _ _ _ _ false (PZ 4) true p01); [apply m_var; onlyun|done].
      * plt0.
    + plt0.
  - plt0.
Qed.

Theorem df_mp3_deadlock_free : ∃ ef e', mtyped pc0 [] df_main MUnit ef e' ∧ deadlock_free (∅, {[+ e' +]}).
Proof.
  destruct df_main_typed as (ef & e' & H). exists ef, e'. split; [done|]. by eapply mp3_deadlock_free.
Qed.

(** ** Two streams in a cycle (Listings 1.1 and 1.2, p. 4)

      Stream    = µβ.∀^S ι. !^ι Unit; β
      client    : ∀p q (p < q < p + 2). Stream⟨p, 2⟩ →^{⊤,⊥}_un dual Stream⟨q, 2⟩ →^{p,⊤}_lin Unit
      newclient : ∀p q (q < p < q + 2). the same type
      main = let (w1, r1) = new Stream 1 2 in let (w2, r2) = new Stream 2 2 in
             fork (λ_. client{1, 2} w1 r2); newclient{2, 1} w2 r1

    As in version 1 the abstraction names the head q of c2 as well. inst
    is T-Eq at the sequence, which unfolds µ and pops the head. *)

Definition st0 : msty := MSeq (MSnd (PI 0) MPUnit) MVar.
Definition stream : msty := MRec st0.

Definition cl_ctx (lt : Z → Z → Prop) : pctx :=
  PCtx 2 0 (λ v ts, ts = [] ∧ ∃ p q, v = [p; q] ∧ lt p q).

Definition cl_ty (lt : Z → Z → Prop) : mty :=
  MPoly (cl_ctx lt) (MCh false stream (PR (PV 0 0) 2)) []
    (MArr (MCh true stream (PR (PV 1 0) 2)) [LC stream (PV 0 0) 2] [PTop] MUnit).

Definition cl_lt (p q : Z) : Prop := (p < q < p + 2)%Z.
Definition ncl_lt (p q : Z) : Prop := (q < p < q + 2)%Z.

Definition client : expr :=
  EBox (Lam (Lam (App (Lam (LetP (App ERecv (Var 1)) (App (App (Var 5) (Var 2)) (Var 0))))
                      (App ESend (Pair EUnit (Var 1)))))).

Definition newclient : expr :=
  EBox (Lam (Lam (LetP (App ERecv (Var 0))
                   (App (Lam (App (App (Var 5) (Var 0)) (Var 1)))
                        (App ESend (Pair EUnit (Var 3))))))).

Definition st_body : expr :=
  LetP (App ENew EUnit) (LetP (App ENew EUnit)
    (LetU (App ESpawn (Lam (App (App (Var 6) (Var 4)) (Var 1))))
          (App (App (Var 4) (Var 1)) (Var 2)))).

(** client and newclient are arguments, so both are typed under the
    empty environment. *)
Definition st_main : expr := App (App (Lam (Lam st_body)) client) newclient.

Lemma m_app_poly' Θ Γ Γ1 Γ2 e1 e2 e1' e2' Θ' T σ V ef1 ef2 σs τs V' ef :
  msplit Γ Γ1 Γ2 → mtyped Θ Γ1 e1 (MPoly Θ' T σ V) ef1 e1' → pinst_ok Θ Θ' σs τs →
  tpure (pc_nt Θ') T → tpure (pc_nt Θ') V →
  mtyped Θ Γ2 e2 (msub σs τs T) ef2 e2' → plt Θ ef1 (envp Γ2) → pntop Θ ef2 →
  V' = msub σs τs V → ef = ef1 ++ ef2 ++ (psub σs <$> σ) →
  mtyped Θ Γ (App e1 e2) V' ef (App (App EForce e1') e2').
Proof. intros ???????? -> ->. by eapply m_app_poly. Qed.

Lemma oeq_st v ts j n :
  oeq (DCh (mclose v ts stream) (pclose v (PV j n)) 2)
      (DCh (mclose v ts (MSeq (MSnd (PV j n) MPUnit) stream)) (pclose v (PV j (n + 2))) 2).
Proof. apply oeq_hdt. cbn. by rewrite Z.add_0_r, Z.add_assoc. Qed.

Lemma seq_st : seq (ers stream) (ers (MSeq (MSnd (PV 0 0) MPUnit) stream)).
Proof. apply seq_unf. vm_compute. reflexivity. Qed.

(** T-Eq at a stream: the head ι + n becomes an action, the sequence pops. *)
Lemma m_inst_st Θ Γ e e' pol j n ef :
  pc_nt Θ = 0 →
  mtyped Θ Γ e (MCh pol stream (PR (PV j n) 2)) ef e' →
  mtyped Θ Γ e (MCh pol (MSeq (MSnd (PV j n) MPUnit) stream) (PR (PV j (n + 2)) 2)) ef e'.
Proof.
  intros Hnt H. eapply m_eq; [exact H|]. split.
  - intros ss Hl _. rewrite Hnt in Hl. destruct ss; [|discriminate]. rewrite !sinst_nil.
    exact seq_st.
  - split; [done|]. intros v ts _. apply oeq_st.
Qed.

Ltac plt_cl :=
  right; intros ?v ?ts [-> (?p & ?q & -> & ?Hpq)] ?l ?Hl; simpl in Hl;
  repeat (apply elem_of_cons in Hl as [->|Hl]; [cbn; unfold cl_lt, ncl_lt in *; lia|]); by apply elem_of_nil in Hl.

Lemma pok_cl lt : (∀ p q, lt p q → lt (p + 2) (q + 2))%Z →
  pinst_ok (cl_ctx lt) (cl_ctx lt) [PV 0 2; PV 1 2] [].
Proof.
  intros Hlt. split_and!; [done|done|repeat constructor|constructor|intros ss _ _; constructor|].
  intros v ts [-> (p & q & -> & Hpq)]. split; [done|]. exists (p + 2)%Z, (q + 2)%Z. split; [done|]. by apply Hlt.
Qed.

Lemma tpure_cl k : tpure k (MCh false stream (PR (PV 0 0) 2)) ∧
  tpure k (MArr (MCh true stream (PR (PV 1 0) 2)) [LC stream (PV 0 0) 2] [PTop] MUnit).
Proof. split; cbn; repeat split; repeat constructor. Qed.

Lemma client_typed Θ : ∃ e', mtyped Θ [] client (cl_ty cl_lt) [] e'.
Proof.
  eexists. unfold client, cl_ty.
  eapply m_fix; [allun|apply tpure_cl|apply tpure_cl|exists [0%Z; 1%Z], []; split; [done|]; exists 0%Z, 1%Z; split; [done|]; unfold cl_lt; lia| |left; done].
  eapply m_lam.
  eapply (m_sub _ _ _ _ _ _ [PTop]); [|right; left; split; [set_solver|shelve]].
  eapply (m_let _ _ [None; Some _; None] [Some _; None; Some _]); [msp| | |].
  - eapply (m_send _ _ [None; None; None] [None; Some _; None] _ _ _ _ false (PV 0 0) MPUnit stream (PR (PV 0 2) 2));
      [msp|apply m_unit; allun| |split; [done|split; [apply plt_none|plt_cl]]|apply plt_nil|apply plt_none].
    apply m_inst_st; [done|]. apply m_var; onlyun.
  - eapply (m_recv _ _ [None; Some _; None; None] [Some _; None; None; Some _] _ _ _ _ true (PV 1 0) MPUnit stream (PR (PV 1 2) 2));
      [msp| |split; [done|split; [apply plt_none|plt_cl]]| |].
    + apply m_inst_st; [done|]. apply m_var; onlyun.
    + eapply (m_app _ _ [None; None; Some _; None; None; Some _] [Some _; Some _; None; None; None; None]); [msp| | |apply plt_nil|apply plt_nil].
      * eapply (m_app_poly' _ _ [None; None; None; None; None; Some _] [None; None; Some _; None; None; None]
                  _ _ _ _ _ _ _ _ _ _ [PV 0 2; PV 1 2] []);
          [msp|apply m_var; onlyun|apply pok_cl; unfold cl_lt; lia|apply tpure_cl|apply tpure_cl|apply m_var; onlyun|apply plt_nil|apply pntop_nil|reflexivity|reflexivity].
      * apply m_var; onlyun.
    + plt_cl.
  - plt_cl.
  Unshelve. all: set_solver.
Qed.

Lemma newclient_typed Θ : ∃ e', mtyped Θ [] newclient (cl_ty ncl_lt) [] e'.
Proof.
  eexists. unfold newclient, cl_ty.
  eapply m_fix; [allun|apply tpure_cl|apply tpure_cl|exists [1%Z; 0%Z], []; split; [done|]; exists 1%Z, 0%Z; split; [done|]; unfold ncl_lt; lia| |left; done].
  eapply m_lam.
  eapply (m_sub _ _ _ _ _ _ [PTop]); [|right; left; split; [set_solver|shelve]].
  eapply (m_recv _ _ [Some _; None; None] [None; Some _; Some _] _ _ _ _ true (PV 1 0) MPUnit stream (PR (PV 1 2) 2));
    [msp| |split; [done|split; [apply plt_none|plt_cl]]| |].
  - apply m_inst_st; [done|]. apply m_var; onlyun.
  - eapply (m_let _ _ [None; None; None; Some _; None] [Some _; Some _; None; None; Some _]); [msp| | |].
    + eapply (m_send _ _ [None; None; None; None; None] [None; None; None; Some _; None] _ _ _ _ false (PV 0 0) MPUnit stream (PR (PV 0 2) 2));
        [msp|apply m_unit; allun| |split; [done|split; [apply plt_none|plt_cl]]|apply plt_nil|apply plt_none].
      apply m_inst_st; [done|]. apply m_var; onlyun.
    + eapply (m_app _ _ [Some _; None; None; None; None; Some _] [None; Some _; Some _; None; None; None]); [msp| | |apply plt_nil|apply plt_nil].
      * eapply (m_app_poly' _ _ [None; None; None; None; None; Some _] [Some _; None; None; None; None; None]
                  _ _ _ _ _ _ _ _ _ _ [PV 0 2; PV 1 2] []);
          [msp|apply m_var; onlyun|apply pok_cl; unfold ncl_lt; lia|apply tpure_cl|apply tpure_cl|apply m_var; onlyun|apply plt_nil|apply pntop_nil|reflexivity|reflexivity].
      * apply m_var; onlyun.
    + plt_cl.
  - plt_cl.
  Unshelve. all: set_solver.
Qed.

Lemma pok_main lt p q : lt p q → pinst_ok pc0 (cl_ctx lt) [PZ p; PZ q] [].
Proof.
  intros H. split_and!; [done|done|repeat constructor|constructor|intros ss _ _; constructor|].
  intros v ts [-> ->]. split; [done|]. exists p, q. split; [done|done].
Qed.

Lemma st_main_typed : ∃ ef e', mtyped pc0 [] st_main MUnit ef e'.
Proof.
  destruct (client_typed pc0) as [ec Hc]. destruct (newclient_typed pc0) as [en Hn].
  do 2 eexists. unfold st_main.
  eapply (m_app _ _ [] []); [msp| |exact Hn|apply plt_none|apply plt_nil].
  eapply (m_app _ _ [] []); [msp| |exact Hc|apply plt_none|apply plt_nil].
  eapply m_lam. eapply m_lam. unfold st_body.
  eapply (m_new _ _ _ _ stream (PZ 1) 2). eapply (m_new _ _ _ _ stream (PZ 2) 2).
  eapply (m_letu _ _ [Some _; None; None; Some _; None; Some _] [None; Some _; Some _; None; Some _; Some _]);
    [msp| | |apply plt_nil].
  - eapply m_fork. eapply m_lam.
    eapply (m_app _ _ [None; None; None; None; Some _; None; Some _] [Some _; Some _; None; None; None; None; None]);
      [msp| | |apply plt_nil|apply plt_nil].
    + eapply (m_app_poly' _ _ [None; None; None; None; None; None; Some _] [None; None; None; None; Some _; None; None]
                _ _ _ _ _ _ _ _ _ _ [PZ 1; PZ 2] []);
        [msp|apply m_var; onlyun|apply pok_main; unfold cl_lt; lia|apply tpure_cl|apply tpure_cl|apply m_var; onlyun
        |apply plt_nil|apply pntop_nil|reflexivity|reflexivity].
    + apply m_var; onlyun.
  - eapply (m_app _ _ [None; Some _; None; None; Some _; Some _] [None; None; Some _; None; None; None]);
      [msp| | |apply plt_nil|apply plt_nil].
    + eapply (m_app_poly' _ _ [None; None; None; None; Some _; Some _] [None; Some _; None; None; None; None]
                _ _ _ _ _ _ _ _ _ _ [PZ 2; PZ 1] []);
        [msp|apply m_var; onlyun|apply pok_main; unfold ncl_lt; lia|apply tpure_cl|apply tpure_cl|apply m_var; onlyun
        |apply plt_nil|apply pntop_nil|reflexivity|reflexivity].
    + apply m_var; onlyun.
Qed.

Theorem st_mp3_deadlock_free : ∃ ef e', mtyped pc0 [] st_main MUnit ef e' ∧ deadlock_free (∅, {[+ e' +]}).
Proof.
  destruct st_main_typed as (ef & e' & H). exists ef, e'. split; [done|]. by eapply mp3_deadlock_free.
Qed.

(** ** A partial send as a value (R1)

    send v with v bound to x is λc. send x c. T-AbsLin gives the
    closure the lower bound |x|, the priority of the payload, which is
    repair R1. No rule of its own is needed. *)

Lemma psend_typed Θ P pol a K p : snd_ok Θ p a P K →
  ∃ e', mtyped Θ [Some (payty P)] (Lam (App ESend (Pair (Var 1) (Var 0))))
          (MArr (MCh pol (sndQ pol a P K) p) (tprios (payty P) ++ []) [aeff p a] (MCh pol K (pnext p))) [] e'.
Proof.
  intros Hok. eexists. eapply m_lam.
  eapply (m_sub _ _ _ _ _ ([] ++ [] ++ [aeff p a])); [|right; right; right; left; by exists [], []].
  eapply (m_send _ _ [None; Some _] [Some _; None]); [msp| | |exact Hok|apply plt_nil|].
  - apply m_var. split; [done|]. intros [|[|y]] t' Hy Hl; simpl in Hl; try done.
  - apply m_var. split; [done|]. intros [|[|y]] t' Hy Hl; simpl in Hl; try done.
  - apply plt_nil.
Qed.

(** ** After a segment the rank of the channel depends on the data

    The channel of [rt_main] has type TreeChannel; Wait⁹ and sequence
    1 + 2k. After the tree Node(Leaf, Leaf) it reaches Wait⁹ at rank 9.
    After a tree with four nodes on its left spine its last leaf is
    offered at 17, so Wait⁹ does not rise and the point is junk, above
    every finite level. A fact fixed when receiveTree is defined cannot
    put the returned channel below a finite priority, and the latent
    effect ⊤ after the call is forced (mordido-perez.md §13). *)

Definition rt_wsmall : list wstep := [WB true; WS; WB false; WB false].
Definition rt_wbig : list wstep :=
  [WB true; WS; WB true; WS; WB true; WS; WB true; WS; WB false; WB false; WB false; WB false; WB false].

Lemma rt_rank_data :
  rank (dwalk (DCh Qc (PZ 1) 2) rt_wsmall) = KZ 9 1 0 ∧
  ∀ z s j, rlt (KZ z s j) (rank (dwalk (DCh Qc (PZ 1) 2) rt_wbig)).
Proof.
  split; [vm_compute; reflexivity|]. intros z s j.
  assert (rank (dwalk (DCh Qc (PZ 1) 2) rt_wbig) = KT 0) as -> by (vm_compute; reflexivity). simpl. lia.
Qed.

(** ** Unequal increments with matching rates (MPRounds.v, section 15) *)

(** ** The two loops

      dsend b a = let (_, a) = receive a in let b = send () b in
                  let b = send () b in dsend b a
      hrecv a b = let a = send () a in let (_, b) = receive b in
                  let (_, b) = receive b in hrecv a b *)

Definition dsend : expr :=
  EBox (Lam (Lam (LetP (App ERecv (Var 0))
    (App (Lam (App (Lam (App (App (Var 6) (Var 0)) (Var 2))) (App ESend (Pair EUnit (Var 0)))))
         (App ESend (Pair EUnit (Var 3))))))).

Definition hrecv : expr :=
  EBox (Lam (Lam (App (Lam (LetP (App ERecv (Var 1)) (LetP (App ERecv (Var 0))
                                (App (App (Var 7) (Var 4)) (Var 0)))))
                      (App ESend (Pair EUnit (Var 1)))))).

Definition rr_main : expr := App (App (Lam (Lam st_body)) hrecv) dsend.

(** ** Matching rates go through version 3

    a has the sequence 1 + 4k, b has 2 + 2k. Both functions name the
    heads p of a and q of b and ask p < q < p + 2. A round of hrecv
    acts at p, q and q + 2 while it holds the other channel at q, p + 4
    and p + 4, and the recursive call moves both heads by 4. dsend acts
    at p, q and q + 2 in the same pattern. *)

Lemma oeq_std v ts j n d :
  oeq (DCh (mclose v ts stream) (pclose v (PV j n)) d)
      (DCh (mclose v ts (MSeq (MSnd (PV j n) MPUnit) stream)) (pclose v (PV j (n + d))) d).
Proof. apply oeq_hdt. cbn. by rewrite Z.add_0_r, Z.add_assoc. Qed.

Lemma m_inst_std Θ Γ e e' pol j n d ef :
  pc_nt Θ = 0 →
  mtyped Θ Γ e (MCh pol stream (PR (PV j n) d)) ef e' →
  mtyped Θ Γ e (MCh pol (MSeq (MSnd (PV j n) MPUnit) stream) (PR (PV j (n + d)) d)) ef e'.
Proof.
  intros Hnt H. eapply m_eq; [exact H|]. split.
  - intros ss Hl _. rewrite Hnt in Hl. destruct ss; [|discriminate]. rewrite !sinst_nil.
    exact seq_st.
  - split; [done|]. intros v ts _. apply oeq_std.
Qed.

Definition rr_ty (lt : Z → Z → Prop) (d1 d2 : Z) : mty :=
  MPoly (cl_ctx lt) (MCh false stream (PR (PV 0 0) d1)) []
    (MArr (MCh true stream (PR (PV 1 0) d2)) [LC stream (PV 0 0) d1] [PTop] MUnit).

(** hrecv names (p, q), dsend names (q, p). *)
Definition hr_lt (p q : Z) : Prop := (p < q < p + 2)%Z.
Definition ds_lt (q p : Z) : Prop := (p < q < p + 2)%Z.

Ltac plt_rr :=
  right; intros ?v ?ts [-> (?p & ?q & -> & ?Hpq)] ?l ?Hl; simpl in Hl;
  repeat (apply elem_of_cons in Hl as [->|Hl]; [cbn; unfold hr_lt, ds_lt in *; lia|]); by apply elem_of_nil in Hl.

Lemma pok_rr lt : (∀ p q, lt p q → lt (p + 4) (q + 4))%Z →
  pinst_ok (cl_ctx lt) (cl_ctx lt) [PV 0 4; PV 1 4] [].
Proof.
  intros Hlt. split_and!; [done|done|repeat constructor|constructor|intros ss _ _; constructor|].
  intros v ts [-> (p & q & -> & Hpq)]. split; [done|]. exists (p + 4)%Z, (q + 4)%Z. split; [done|]. by apply Hlt.
Qed.

Lemma tpure_rr k d1 d2 : tpure k (MCh false stream (PR (PV 0 0) d1)) ∧
  tpure k (MArr (MCh true stream (PR (PV 1 0) d2)) [LC stream (PV 0 0) d1] [PTop] MUnit).
Proof. split; cbn; repeat split; repeat constructor. Qed.

Lemma hrecv_typed Θ : ∃ e', mtyped Θ [] hrecv (rr_ty hr_lt 4 2) [] e'.
Proof.
  eexists. unfold hrecv, rr_ty.
  eapply m_fix; [allun|apply (tpure_rr 0 4 2)|apply (tpure_rr 0 4 2)|exists [0%Z; 1%Z], []; split; [done|]; exists 0%Z, 1%Z; split; [done|]; unfold hr_lt; lia| |left; done].
  eapply m_lam.
  eapply (m_sub _ _ _ _ _ _ [PTop]); [|right; left; split; [set_solver|shelve]].
  eapply (m_let _ _ [None; Some _; None] [Some _; None; Some _]); [msp| | |].
  - eapply (m_send _ _ [None; None; None] [None; Some _; None] _ _ _ _ false (PV 0 0) MPUnit stream (PR (PV 0 4) 4));
      [msp|apply m_unit; allun| |split; [done|split; [apply plt_none|plt_rr]]|apply plt_nil|apply plt_none].
    apply (m_inst_std _ _ _ _ _ 0 0 4); [done|]. apply m_var; onlyun.
  - eapply (m_recv _ _ [None; Some _; None; None] [Some _; None; None; Some _] _ _ _ _ true (PV 1 0) MPUnit stream (PR (PV 1 2) 2));
      [msp| |split; [done|split; [apply plt_none|plt_rr]]| |].
    + apply (m_inst_std _ _ _ _ _ 1 0 2); [done|]. apply m_var; onlyun.
    + eapply (m_recv _ _ [Some _; None; None; None; None; None] [None; Some _; Some _; None; None; Some _]
                _ _ _ _ true (PV 1 2) MPUnit stream (PR (PV 1 4) 2));
        [msp| |split; [done|split; [apply plt_none|plt_rr]]| |].
      * apply (m_inst_std _ _ _ _ _ 1 2 2); [done|]. apply m_var; onlyun.
      * eapply (m_app _ _ [None; Some _; None; Some _; Some _; None; None; Some _] [Some _; None; None; None; None; None; None; None]);
          [msp| | |apply plt_nil|apply plt_nil].
        -- eapply (m_app_poly' _ _ [None; Some _; None; Some _; None; None; None; Some _] [None; None; None; None; Some _; None; None; None]
                    _ _ _ _ _ _ _ _ _ _ [PV 0 4; PV 1 4] []);
             [msp|apply m_var; onlyun|apply pok_rr; unfold hr_lt; lia|apply (tpure_rr 0 4 2)|apply (tpure_rr 0 4 2)|apply m_var; onlyun
             |apply plt_nil|apply pntop_nil|reflexivity|reflexivity].
        -- apply m_var; onlyun.
      * plt_rr.
    + plt_rr.
  - plt_rr.
  Unshelve. all: set_solver.
Qed.

Lemma dsend_typed Θ : ∃ e', mtyped Θ [] dsend (rr_ty ds_lt 2 4) [] e'.
Proof.
  eexists. unfold dsend, rr_ty.
  eapply m_fix; [allun|apply (tpure_rr 0 2 4)|apply (tpure_rr 0 2 4)|exists [1%Z; 0%Z], []; split; [done|]; exists 1%Z, 0%Z; split; [done|]; unfold ds_lt; lia| |left; done].
  eapply m_lam.
  eapply (m_sub _ _ _ _ _ _ [PTop]); [|right; left; split; [set_solver|shelve]].
  eapply (m_recv _ _ [Some _; None; None] [None; Some _; Some _] _ _ _ _ true (PV 1 0) MPUnit stream (PR (PV 1 4) 4));
    [msp| |split; [done|split; [apply plt_none|plt_rr]]| |].
  - apply (m_inst_std _ _ _ _ _ 1 0 4); [done|]. apply m_var; onlyun.
  - eapply (m_let _ _ [None; None; None; Some _; None] [Some _; Some _; None; None; Some _]); [msp| | |].
    + eapply (m_send _ _ [None; None; None; None; None] [None; None; None; Some _; None] _ _ _ _ false (PV 0 0) MPUnit stream (PR (PV 0 2) 2));
        [msp|apply m_unit; allun| |split; [done|split; [apply plt_none|plt_rr]]|apply plt_nil|apply plt_none].
      apply (m_inst_std _ _ _ _ _ 0 0 2); [done|]. apply m_var; onlyun.
    + eapply (m_let _ _ [Some _; None; None; None; None; None] [None; Some _; Some _; None; None; Some _]); [msp| | |].
      * eapply (m_send _ _ [None; None; None; None; None; None] [Some _; None; None; None; None; None] _ _ _ _ false (PV 0 2) MPUnit stream (PR (PV 0 4) 2));
          [msp|apply m_unit; allun| |split; [done|split; [apply plt_none|plt_rr]]|apply plt_nil|apply plt_none].
        apply (m_inst_std _ _ _ _ _ 0 2 2); [done|]. apply m_var; onlyun.
      * eapply (m_app _ _ [Some _; None; None; Some _; None; None; Some _] [None; None; Some _; None; None; None; None]);
          [msp| | |apply plt_nil|apply plt_nil].
        -- eapply (m_app_poly' _ _ [None; None; None; Some _; None; None; Some _] [Some _; None; None; None; None; None; None]
                    _ _ _ _ _ _ _ _ _ _ [PV 0 4; PV 1 4] []);
             [msp|apply m_var; onlyun|apply pok_rr; unfold ds_lt; lia|apply (tpure_rr 0 2 4)|apply (tpure_rr 0 2 4)|apply m_var; onlyun
             |apply plt_nil|apply pntop_nil|reflexivity|reflexivity].
        -- apply m_var; onlyun.
      * plt_rr.
    + plt_rr.
  - plt_rr.
  Unshelve. all: set_solver.
Qed.

Lemma rr_main_typed : ∃ ef e', mtyped pc0 [] rr_main MUnit ef e'.
Proof.
  destruct (hrecv_typed pc0) as [eh Hh]. destruct (dsend_typed pc0) as [ed Hd].
  do 2 eexists. unfold rr_main.
  eapply (m_app _ _ [] []); [msp| |exact Hd|apply plt_none|apply plt_nil].
  eapply (m_app _ _ [] []); [msp| |exact Hh|apply plt_none|apply plt_nil].
  eapply m_lam. eapply m_lam. unfold st_body.
  eapply (m_new _ _ _ _ stream (PZ 1) 4). eapply (m_new _ _ _ _ stream (PZ 2) 2).
  eapply (m_letu _ _ [Some _; None; None; Some _; None; Some _] [None; Some _; Some _; None; Some _; Some _]);
    [msp| | |apply plt_nil].
  - eapply m_fork. eapply m_lam.
    eapply (m_app _ _ [None; None; None; None; Some _; None; Some _] [Some _; Some _; None; None; None; None; None]);
      [msp| | |apply plt_nil|apply plt_nil].
    + eapply (m_app_poly' _ _ [None; None; None; None; None; None; Some _] [None; None; None; None; Some _; None; None]
                _ _ _ _ _ _ _ _ _ _ [PZ 1; PZ 2] []);
        [msp|apply m_var; onlyun|apply pok_main; unfold hr_lt; lia|apply (tpure_rr 0 4 2)|apply (tpure_rr 0 4 2)|apply m_var; onlyun
        |apply plt_nil|apply pntop_nil|reflexivity|reflexivity].
    + apply m_var; onlyun.
  - eapply (m_app _ _ [None; Some _; None; None; Some _; Some _] [None; None; Some _; None; None; None]);
      [msp| | |apply plt_nil|apply plt_nil].
    + eapply (m_app_poly' _ _ [None; None; None; None; Some _; Some _] [None; Some _; None; None; None; None]
                _ _ _ _ _ _ _ _ _ _ [PZ 2; PZ 1] []);
        [msp|apply m_var; onlyun|apply pok_main; unfold ds_lt; lia|apply (tpure_rr 0 2 4)|apply (tpure_rr 0 2 4)|apply m_var; onlyun
        |apply plt_nil|apply pntop_nil|reflexivity|reflexivity].
    + apply m_var; onlyun.
Qed.

Theorem rr_mp3_deadlock_free : ∃ ef e', mtyped pc0 [] rr_main MUnit ef e' ∧ deadlock_free (∅, {[+ e' +]}).
Proof.
  destruct rr_main_typed as (ef & e' & H). exists ef, e'. split; [done|]. by eapply mp3_deadlock_free.
Qed.

