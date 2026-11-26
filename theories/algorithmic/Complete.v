(** * Completeness of the algorithmic judgment

    [algo_complete]: every declarative derivation over contractive
    contexts has an annotation of its term that synthesizes the same
    type and cost. The annotation puts [AAsc] at every E-Sub, [APack] at
    every E-Pack and [AOpen] at every E-Open, and an [AAsc] above every
    λ, injection, case and box. new carries its constraint or field and
    its tickets, force its instances.

    The statement quantifies over every weakening Δ' of Δ by unlimited
    entries. The algorithm gives an unlimited entry to both premises of a
    binary rule, where the declarative split may give it to one, and the
    weakening absorbs the difference ([lpart_wk]). Contractive contexts
    are what the E-Box check at one instance needs, and every program
    typed by P-Term starts from them. *)

From GV Require Export algorithmic.Sound.

Section complete.
  Context (W : sworld) (N : fuel).

  (** Synthesis followed by subtyping is checking, for every form that
      synthesizes. *)
  Lemma syn_chk_sub t : ∀ Θ Γ Δ F T c T',
    syn W N Θ Γ Δ F t T c → tsub W Γ T T' → (tcontr T → tcontr T') →
    chk W N Θ Γ Δ F t T' c.
  Proof.
    induction t; intros Θ0 Γ0 Δ0 F0 T0 c0 T' H Hs Hc;
      try (by eapply c_sub; [reflexivity|exact H|exact Hs|exact Hc]);
      inversion H; subst.
    - eapply c_letu; [done|done|done|done|done|]. by eapply IHt2.
    - eapply c_letp; [done|done|done|done|done|]. by eapply IHt2.
  Qed.

  Lemma syn_chk t Θ Γ Δ F T c : syn W N Θ Γ Δ F t T c → chk W N Θ Γ Δ F t T c.
  Proof. intros H. eapply syn_chk_sub; [exact H|apply tsub_refl|done]. Qed.

  (** The split of a binary rule, computed on a weakened context. *)
  Lemma split_setup Θ Θ1 Θ2 Γ Δ Δ1 Δ2 Δ' F1 e1 T1 c1 :
    tsplit Θ Θ1 Θ2 → lenv_split Δ Δ1 Δ2 → typed W N Θ1 Γ Δ1 F1 e1 T1 c1 →
    tenv_contr Θ → lenv_wk Δ Δ' → lenv_contr Δ' →
    ∃ A1 A2, tpart e1 Θ = (Θ1, Θ2) ∧ lpart e1 Δ' = (A1, A2) ∧
      lenv_wk Δ1 A1 ∧ lenv_wk Δ2 A2 ∧ lenv_contr A1 ∧ lenv_contr A2 ∧
      tenv_contr Θ1 ∧ tenv_contr Θ2 ∧ lenv_contr Δ1 ∧
      ∀ F, fut1 F Θ2 A2 = sf_unionb F (tenv_heads Θ2 ∪ lenv_heads Δ2) (lenv_bot Δ2).
  Proof.
    intros Hsp Hl H1 HΘ Hw HΔ'.
    destruct (typed_tfacts _ _ _ _ _ _ _ _ _ H1) as [Hd Hv].
    destruct (lpart_wk e1 Δ Δ' Δ1 Δ2 Hw Hl Hv) as [Hw1 Hw2].
    destruct (lpart e1 Δ') as [A1 A2] eqn:EA. simpl in Hw1, Hw2.
    destruct (lenv_split_contr _ _ _ (lpart_lsplit _ _ _ _ EA) HΔ') as [HA1 HA2].
    destruct (tsplit_contr _ _ _ Hsp HΘ) as [HΘ1 HΘ2].
    exists A1, A2. split_and!; try done.
    - by apply tpart_eq.
    - by eapply lenv_wk_contr.
    - intros F. unfold fut1. by destruct (lenv_wk_heads _ _ Hw2) as [-> ->].
  Qed.

  Lemma age_setup c Δ2 Δ2' A2 :
    lenv_wk Δ2 A2 → lage c Δ2 Δ2' → lenv_contr A2 →
    ∃ A2', lage c A2 A2' ∧ lenv_wk Δ2' A2' ∧ lenv_contr A2'.
  Proof.
    intros Hw Ha HA. destruct (lenv_wk_lage _ _ _ _ Hw Ha) as (A2' & Ha' & Hw').
    exists A2'. split_and!; [done|done|by eapply lage_contr].
  Qed.

  Lemma lenv_pinst_lookup σ Δ i : lenv_pinst σ Δ !! i = fmap (M:=option) (pinst_ty σ) <$> Δ !! i.
  Proof. unfold lenv_pinst. by rewrite list_lookup_fmap. Qed.

  Theorem algo_complete Θ Γ Δ F e T c :
    typed W N Θ Γ Δ F e T c → tenv_contr Θ →
    ∀ Δ', lenv_wk Δ Δ' → lenv_contr Δ' →
    ∃ t, erase t = e ∧ syn W N Θ Γ Δ' F t T c.
  Proof.
    induction 1 as
      [Γ Δ F HΔ
      |Γ Δ F x T HΔ
      |Γ Δ F o S x a mt HΔ Ham
      |Θ Θh Γ Δ Δh F e T U ub lb c a Hlb Hth Hlc HTc Hb IH
      |Θ Θ1 Θ2 Θ2' Γ Δ Δ1 Δ2 Δ2' F e1 e2 ub lb c T U a1 c1 c2 Hsp Hl Hub H1 IH1 Hta Hla H2 IH2 Hc
      |Θ Θ1 Θ2 Θ2' Γ Δ Δ1 Δ2 Δ2' F e1 e2 T1 T1' T2 c1 c2 Hsp Hl H1 IH1 Hta Hla H2 IH2 Hag
      |Θ Θ1 Θ2 Θ2' Γ Δ Δ1 Δ2 Δ2' F e1 e2 T c1 c2 Hsp Hl H1 IH1 Hta Hla H2 IH2
      |Θ Θ1 Θ2 Θ2' Γ Δ Δ1 Δ2 Δ2' F e1 e2 T1 T2 T c1 c2 Hsp Hl H1 IH1 Hta Hla H2 IH2
      |i Θ Γ Δ F e T U c HTc H IH
      |Θ Θ1 Θ2 Θ2' Γ Δ Δ1 Δ2 Δ2' F e e1 e2 T1 T2 T c0 c1 c2 Hsp Hl H0 IH0 Hta Hla H1 IH1 H2 IH2
      |Γ Δ F e m k C ub c U HΔ HUc Hb IH
      |Θ Γ Δ F e m k C ub c U xs ss c0 Hxs HC Hss Hsi Hub H IH
      |Θ Γ Δ F e S0 x m T S aS mS Tp Tp' c0 Hu Hsc Hbt Hub H IH Hag Hsub
      |Θ Γ Δ F e S0 x m T S a mS c0 Hu Hsc Hub H IH
      |Θ Γ Δ F e S0 x a mS c0 Hu Hub H IH
      |i Θ Γ Δ F e S0 x S1 S2 a mS c0 Hu Hub H IH
      |Θ Γ Δ F e S0 x S1 S2 a mS c0 Hu Hub H IH
      |Θ Γ Δ F e S x a1 m1 a2 m2 c0 H IH Hl1 Hl2
      |Θ Γ Δ F e ub lb c' a c0 H IH
      |Γ Δ F C S m1 m2 HΔ HC Htk HSc
      |Γ Δ F x κf S m1 m2 HΔ Htk HSc
      |Θ Γ Δ F e T T' c c' H IH Hsub Hc HTc
      |Θ Γ Δ F e lb m C T xs c Hxs HC Hlb Hwf H IH
      |Θ Γ Δ F e i lb m C T U c Hi Hun Hcons H IH];
      intros HΘ Δ' Hw HΔ'.
    - exists AUnit. split; [done|]. apply a_unit. by eapply lenv_wk_unl.
    - exists (AVar x). split; [done|]. apply a_var. by eapply lenv_wk_only.
    - exists (AChan o). split; [done|]. apply a_chan; [by eapply lenv_wk_unl|done].
    - (* E-Abs *)
      destruct (age_setup _ _ _ _ Hw Hlc HΔ') as (Δ'h & Hla' & Hwh & HΔh).
      destruct (IH (thage_contr _ _ _ Hth HΘ) (Some T :: Δ'h)) as (t & Et & Ht);
        [by constructor|by apply lenv_contr_some|].
      exists (AAsc (TLolli ub lb c T U a) (Some 0) (ALam t)). split; [simpl; congruence|].
      apply a_asc with (c := Some 0); [|apply fle_refl]. eapply c_lam; [|exact Hth|exact Hla'|done|by apply syn_chk|apply fle_refl].
      by destruct (lenv_wk_heads _ _ Hw) as [-> ->].
    - (* E-App *)
      destruct (split_setup _ _ _ _ _ _ _ _ _ _ _ _ Hsp Hl H1 HΘ Hw HΔ')
        as (A1 & A2 & Et & EA & Hw1 & Hw2 & HA1 & HA2 & HΘ1 & HΘ2 & HΔ1 & Hf).
      destruct (IH1 HΘ1 A1 Hw1 HA1) as (t1 & Et1 & Ht1).
      destruct (age_setup _ _ _ _ Hw2 Hla HA2) as (A2' & Hla' & Hw2' & HA2').
      destruct (IH2 (thage_contr _ _ _ Hta HΘ2) A2' Hw2' HA2') as (t2 & Et2 & Ht2).
      exists (AApp t1 t2). split; [simpl; congruence|].
      eapply a_app; [by rewrite Et1|by rewrite Et1|rewrite Hf; exact Ht1|done|done|exact Hla'|by apply syn_chk|done].
    - (* E-Pair *)
      destruct (split_setup _ _ _ _ _ _ _ _ _ _ _ _ Hsp Hl H1 HΘ Hw HΔ')
        as (A1 & A2 & Et & EA & Hw1 & Hw2 & HA1 & HA2 & HΘ1 & HΘ2 & HΔ1 & Hf).
      destruct (IH1 HΘ1 A1 Hw1 HA1) as (t1 & Et1 & Ht1).
      destruct (age_setup _ _ _ _ Hw2 Hla HA2) as (A2' & Hla' & Hw2' & HA2').
      destruct (IH2 (thage_contr _ _ _ Hta HΘ2) A2' Hw2' HA2') as (t2 & Et2 & Ht2).
      exists (APair t1 t2). split; [simpl; congruence|].
      eapply a_pair; [by rewrite Et1|by rewrite Et1|rewrite Hf; exact Ht1|done|exact Hla'|exact Ht2|done].
    - (* E-LetU *)
      destruct (split_setup _ _ _ _ _ _ _ _ _ _ _ _ Hsp Hl H1 HΘ Hw HΔ')
        as (A1 & A2 & Et & EA & Hw1 & Hw2 & HA1 & HA2 & HΘ1 & HΘ2 & HΔ1 & Hf).
      destruct (IH1 HΘ1 A1 Hw1 HA1) as (t1 & Et1 & Ht1).
      destruct (age_setup _ _ _ _ Hw2 Hla HA2) as (A2' & Hla' & Hw2' & HA2').
      destruct (IH2 (thage_contr _ _ _ Hta HΘ2) A2' Hw2' HA2') as (t2 & Et2 & Ht2).
      exists (ALetU t1 t2). split; [simpl; congruence|].
      eapply a_letu; [by rewrite Et1|by rewrite Et1|apply syn_chk; rewrite Hf; exact Ht1|done|exact Hla'|exact Ht2].
    - (* E-LetP *)
      destruct (split_setup _ _ _ _ _ _ _ _ _ _ _ _ Hsp Hl H1 HΘ Hw HΔ')
        as (A1 & A2 & Et & EA & Hw1 & Hw2 & HA1 & HA2 & HΘ1 & HΘ2 & HΔ1 & Hf).
      destruct (IH1 HΘ1 A1 Hw1 HA1) as (t1 & Et1 & Ht1).
      pose proof (typed_scontr _ _ _ _ _ _ _ _ _ H1 HΘ1 HΔ1) as HP.
      cbn [tcontr] in HP. apply Is_true_andb in HP as [HT1 HT2].
      destruct (age_setup _ _ _ _ Hw2 Hla HA2) as (A2' & Hla' & Hw2' & HA2').
      destruct (IH2 (thage_contr _ _ _ Hta HΘ2) (Some T2 :: Some T1 :: A2')) as (t2 & Et2 & Ht2);
        [by do 2 constructor|apply lenv_contr_some; [done|by apply lenv_contr_some]|].
      exists (ALetP t1 t2). split; [simpl; congruence|].
      eapply a_letp; [by rewrite Et1|by rewrite Et1|rewrite Hf; exact Ht1|done|exact Hla'|exact Ht2].
    - (* E-Inj *)
      destruct (IH HΘ Δ' Hw HΔ') as (t & Et & Ht).
      exists (AAsc (TSum T U) c (AInj i t)). split; [simpl; congruence|].
      apply a_asc with (c := c); [|apply fle_refl]. apply c_inj; [done|by apply syn_chk].
    - (* E-Case *)
      destruct (split_setup _ _ _ _ _ _ _ _ _ _ _ _ Hsp Hl H0 HΘ Hw HΔ')
        as (A1 & A2 & Et & EA & Hw1 & Hw2 & HA1 & HA2 & HΘ1 & HΘ2 & HΔ1 & Hf).
      destruct (IH0 HΘ1 A1 Hw1 HA1) as (t0 & Et0 & Ht0).
      pose proof (typed_scontr _ _ _ _ _ _ _ _ _ H0 HΘ1 HΔ1) as HP.
      cbn [tcontr] in HP. apply Is_true_andb in HP as [HT1 HT2].
      destruct (age_setup _ _ _ _ Hw2 Hla HA2) as (A2' & Hla' & Hw2' & HA2').
      destruct (IH1 (thage_contr _ _ _ Hta HΘ2) (Some T1 :: A2')) as (t1 & Et1 & Ht1);
        [by constructor|by apply lenv_contr_some|].
      destruct (IH2 (thage_contr _ _ _ Hta HΘ2) (Some T2 :: A2')) as (t2 & Et2 & Ht2);
        [by constructor|by apply lenv_contr_some|].
      exists (AAsc T (fadd c0 (fmax c1 c2)) (ACase t0 t1 t2)). split; [simpl; congruence|].
      apply a_asc with (c := fadd c0 (fmax c1 c2)); [|apply fle_refl].
      eapply c_case; [by rewrite Et0|by rewrite Et0|rewrite Hf; exact Ht0|done|exact Hla'|by apply syn_chk|by apply syn_chk].
    - (* E-Box *)
      set (ss := box_inst (box_base k U Δ') k).
      destruct (IH ss (box_inst_length _ _) (sinsts_box_inst _ _ _) tenv_contr_empty
                  (lenv_pinst (pshift m) (Some (TBox m k C ub c U) :: Δ'))) as (t & Et & Ht).
      { apply lenv_wk_pinst. by constructor. }
      { apply lenv_contr_pinst, lenv_contr_some; done. }
      exists (AAsc (TBox m k C ub c U) (Some 0) (ABox t)). split; [simpl; congruence|].
      apply a_asc with (c := Some 0); [|apply fle_refl]. eapply c_box; [by eapply lenv_wk_unl|done|done|by apply syn_chk|apply fle_refl].
    - (* E-Force *)
      destruct (IH HΘ Δ' Hw HΔ') as (t & Et & Ht).
      exists (AForce xs ss t). split; [simpl; congruence|]. by eapply a_force.
    - destruct (IH HΘ Δ' Hw HΔ') as (t & Et & Ht).
      exists (AOp PSend t). split; [simpl; congruence|]. by eapply a_send.
    - destruct (IH HΘ Δ' Hw HΔ') as (t & Et & Ht).
      exists (AOp PRecv t). split; [simpl; congruence|]. by eapply a_recv.
    - destruct (IH HΘ Δ' Hw HΔ') as (t & Et & Ht).
      exists (AOp PClose t). split; [simpl; congruence|]. by eapply a_close.
    - destruct (IH HΘ Δ' Hw HΔ') as (t & Et & Ht).
      exists (AOp (PSel i) t). split; [simpl; congruence|]. by eapply a_select.
    - destruct (IH HΘ Δ' Hw HΔ') as (t & Et & Ht).
      exists (AOp PBra t). split; [simpl; congruence|]. by eapply a_branch.
    - destruct (IH HΘ Δ' Hw HΔ') as (t & Et & Ht).
      exists (AOp PLink t). split; [simpl; congruence|]. by eapply a_link.
    - destruct (IH HΘ Δ' Hw HΔ') as (t & Et & Ht).
      exists (AOp PSpawn t). split; [simpl; congruence|]. by eapply a_spawn.
    - exists (ANew C S m1 m2). split; [done|]. apply a_new; [by eapply lenv_wk_unl|done|done|done].
    - exists (ANewF x κf S m1 m2). split; [done|]. apply a_new_fld; [by eapply lenv_wk_unl|done|done].
    - (* E-Sub *)
      destruct (IH HΘ Δ' Hw HΔ') as (t & Et & Ht).
      exists (AAsc T' c' t). split; [done|]. apply a_asc with (c := c); [|done]. by eapply syn_chk_sub.
    - (* E-Pack *)
      destruct (IH HΘ Δ' Hw HΔ') as (t & Et & Ht).
      exists (APack lb m C T xs t). split; [done|]. eapply a_pack; [done|done|done|done|by apply syn_chk].
    - (* E-Open *)
      pose proof (lenv_wk_sub _ _ _ _ Hw Hi) as Hi'.
      assert (tcontr T) as HT by (by apply (HΔ' i (TEx lb m C T))).
      destruct (IH (tenv_contr_pinst _ _ HΘ) (<[i := Some T]> (lenv_pinst (pshift m) Δ'))) as (t & Et & Ht).
      { eapply lenv_wk_insert; [by apply lenv_wk_pinst|]. by rewrite lenv_pinst_lookup, Hi. }
      { apply lenv_contr_insert; [done|by apply lenv_contr_pinst]. }
      exists (AOpen i U t). split; [done|]. eapply a_open; [exact Hi'|done|done|by apply syn_chk].
  Qed.

  (** The theorem at the context itself. *)
  Corollary algo_complete_at Θ Γ Δ F e T c :
    typed W N Θ Γ Δ F e T c → tenv_contr Θ → lenv_contr Δ →
    ∃ t, erase t = e ∧ syn W N Θ Γ Δ F t T c.
  Proof. intros H HΘ HΔ. eapply algo_complete; [exact H|done|apply lenv_wk_refl|done]. Qed.

  (** Algorithmic and declarative typing agree, up to annotation. *)
  Corollary algo_iff Θ Γ Δ F e T c :
    tenv_contr Θ → lenv_contr Δ →
    typed W N Θ Γ Δ F e T c ↔ ∃ t, erase t = e ∧ syn W N Θ Γ Δ F t T c.
  Proof.
    intros HΘ HΔ. split; [intros H; by apply algo_complete_at|].
    intros (t & <- & Ht). by apply (proj1 (algo_sound W N)).
  Qed.
End complete.

(** The deadlock-freedom instance, N = ∞ with the annotations of N = ∞. *)
Corollary algo_iff_df W Θ Γ Δ F e T :
  tenv_contr Θ → lenv_contr Δ →
  dftyped W Θ Γ Δ F e T ↔
  ∃ t, erase t = e ∧ syn W None (tenv_df Θ) Γ (lenv_df Δ) F t (ty_df T) None.
Proof.
  intros HΘ HΔ. unfold dftyped. apply algo_iff.
  - intros o te. unfold tenv_df. rewrite lookup_fmap. destruct (Θ !! o) as [e0|] eqn:E; [|done].
    intros [= <-]. simpl. rewrite scontr_df. by apply (HΘ o e0).
  - intros i T0. unfold lenv_df. rewrite list_lookup_fmap. destruct (Δ !! i) as [[T1|]|] eqn:E; try done.
    intros [= <-]. rewrite tcontr_df. by apply (HΔ i T1).
Qed.
