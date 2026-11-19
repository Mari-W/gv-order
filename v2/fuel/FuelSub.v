(** * Fuel: subtyping (stage S6, F4 and F5 along ⊑)

    [Vfuel_teq]: Vfuel does not tell types apart that are equal up to
    ≈ of their session types. [Vfuel_sub]: Vfuel follows the subtyping
    [tsub] of the merged judgment (static/Contexts.v): costs, ticket
    transformers and floors are covariant, arguments contravariant,
    results covariant, and the credit of an end or a closure may fall. [FuelE_sub]: FuelE follows
    it in the result type. *)

From GV Require Export fuel.FuelBind.

Lemma sinst_slist_id_mut :
  (∀ T σ, (∀ a, σ a = SVar a) → sinst_ty σ T = T) ∧
  (∀ s σ, (∀ a, σ a = SVar a) → sinst σ s = s).
Proof.
  assert (∀ σ, (∀ a, σ a = SVar a) → ∀ a, sty_up σ a = SVar a) as Hup
    by (intros σ H [|a]; simpl; [done|]; unfold compose; by rewrite H).
  assert (∀ k σ, (∀ a, σ a = SVar a) → ∀ a, Nat.iter k sty_up σ a = SVar a) as Hit.
  { induction k as [|k IH]; intros σ H; simpl; [done|]. apply Hup. by apply IH. }
  apply ty_sty_mut_ind; intros; simpl; f_equal; eauto.
  all: by rewrite H.
Qed.

Lemma sinst_slist_nil T : sinst_ty (slist []) T = T.
Proof. apply sinst_slist_id_mut. intros a. unfold slist. simpl. f_equal. lia. Qed.

(** ** Equal types *)

Section teq.
  Context (n : nat).
  Context (IH : ∀ j, j < n → ∀ N T T' Π φ v, teq T T' →
    v ∈ FV^N _ j⟦RTy T⟧(Π, φ) ↔ v ∈ FV^N _ j⟦RTy T'⟧(Π, φ)).

  Lemma FuelE_teq_below j N U U' c r Π φ tk e : j < n → teq U U' →
    e ∈ F^N _ j⟦RTy U ▷ c ; r⟧(Π, φ, tk) → e ∈ F^N _ j⟦RTy U' ▷ c ; r⟧(Π, φ, tk).
  Proof. intros Hj Ht. apply FuelE_res_mono. intros N' m Π0 φ0 v Hm. apply (IH m ltac:(lia) N' U U' Π0 φ0 v Ht). Qed.

  Lemma Vty_teq N T : ∀ T' Π φ v, teq T T' →
    Vty N (λ j N, FuelE N j) (λ j N, Vfuel N j) n T Π φ v →
    Vty N (λ j N, FuelE N j) (λ j N, Vfuel N j) n T' Π φ v.
  Proof.
    induction T as [|ub lb c t h T1 IH1 U IH2 a|T1 IH1 T2 IH2|T1 IH1 T2 IH2
                   |m k C ub c t U IHU|s x a|lb m C T1 IHT];
      intros [|ub' lb' c' t' h' T1' U' a'|T1' T2'|T1' T2'
             |m' k' C' ub' c' t' U'|s' x' a'|lb' m' C' T1'] Π φ v Ht; simpl in Ht |- *;
      try contradiction.
    - done.
    - destruct Ht as (<- & <- & <- & <- & <- & <- & H1 & H2).
      intros (e & -> & Hx & Hd & Hf & H). exists e. split_and!; [done|done|done|done|].
      intros N' j φ1 Πu φu u r tk HN Hj Hd1 Hh HΠ Hφ Hu Hm.
      apply (FuelE_teq_below j N' U); [done|done|]. apply H; try done.
      apply (IH j Hj N' T1 T1'); [done|]. done.
    - destruct Ht as (H1 & H2).
      intros (v1 & v2 & Π1 & Π2 & φ1 & φ2 & -> & HΠ & Hφ & -> & -> & Hv1 & Hv2).
      exists v1, v2, Π1, Π2, φ1, φ2. split_and!; try done; [by apply (IH1 T1')|by apply (IH2 T2')].
    - destruct Ht as (H1 & H2).
      intros [(v' & -> & Hv)|(v' & -> & Hv)]; [left|right]; exists v'; split; try done;
        [by apply (IH1 T1')|by apply (IH2 T2')].
    - destruct Ht as (<- & <- & <- & <- & <- & <- & HU).
      intros (e & -> & Hx & -> & -> & H). exists e. split_and!; [done|done|done|done|].
      intros N' j ss r tk HN Hj Hl Hs Hm. specialize (H N' j ss r tk HN Hj Hl Hs Hm).
      destruct k as [|k].
      + destruct ss; [|done]. rewrite !sinst_slist_nil in H |- *.
        by apply (FuelE_teq_below j N' U).
      + by subst.
    - destruct Ht as (<- & <- & Hs). intros (o & S' & f & -> & -> & -> & HS & Hf).
      exists o, S', f. split_and!; try done. by eapply sequiv_trans.
    - destruct Ht as (<- & <- & <- & H1). apply IHT. done.
  Qed.
End teq.

Lemma Vfuel_teq n : ∀ N T T' Π φ v, teq T T' →
  v ∈ FV^N _ n⟦RTy T⟧(Π, φ) ↔ v ∈ FV^N _ n⟦RTy T'⟧(Π, φ).
Proof.
  induction n as [n IH] using lt_wf_ind. intros N T T' Π φ v Ht. rewrite !Vfuel_eq. simpl.
  assert (HIH : ∀ j, j < n → ∀ N T T' Π φ v, teq T T' →
    v ∈ FV^N _ j⟦RTy T⟧(Π, φ) ↔ v ∈ FV^N _ j⟦RTy T'⟧(Π, φ)) by (intros j Hj; intros; by apply IH).
  split; intros H.
  - eapply Vty_teq; [exact HIH|exact Ht|exact H].
  - eapply Vty_teq; [exact HIH|by apply teq_sym|exact H].
Qed.

(** ** Subtyping *)

Section sub.
  Context (n : nat).
  Context (IH : ∀ j, j < n → ∀ N T T' Π φ v, tsub T T' →
    v ∈ FV^N _ j⟦RTy T⟧(Π, φ) → v ∈ FV^N _ j⟦RTy T'⟧(Π, φ)).

  Lemma Vty_sub N T T' Π φ v :
    tsub T T' →
    Vty N (λ j N, FuelE N j) (λ j N, Vfuel N j) n T Π φ v →
    Vty N (λ j N, FuelE N j) (λ j N, Vfuel N j) n T' Π φ v.
  Proof.
    intros Hs. revert Π φ v.
    induction Hs as [
                    |ub lb c t h T1 U a c' t' h' T1' U' a' Hc Ht Hh Ha HT HU IHT IHU
                    |T1 U T1' U' H1 IH1 H2 IH2
                    |T1 U T1' U' H1 IH1 H2 IH2
                    |m k C ub c t U U' c' t' Hc Ht HU
                    |s s' x a a' Hss Ha
                    |lb m C C' T T' HC HC' HT IHT];
      intros Π φ v; simpl.
    - done.
    - intros (e & -> & Hx & Hd & Hf & H). exists e. split_and!; [done|done|done| |].
      + intros o f Ho. eapply fle_trans; [exact Ha|]. by apply (Hf o).
      + intros N' j φ1 Πu φu u r tk HN Hj Hd1 Hh1 HΠ Hφ Hu Hm.
        eapply FuelE_res_mono; [|eapply FuelE_frame_mono; [exact Hc|]].
        * intros N'' m0 Π0 φ0 w Hm0. apply (IH m0 ltac:(lia)). done.
        * apply H; try done.
          -- intros o f Ho. eapply fle_trans; [exact Hh|]. by apply (Hh1 o).
          -- apply (IH j Hj N' T1' T1); done.
          -- by apply Ht.
    - intros (v1 & v2 & Π1 & Π2 & φ1 & φ2 & -> & HΠ & Hφ & -> & -> & Hv1 & Hv2).
      exists v1, v2, Π1, Π2, φ1, φ2. split_and!; auto.
    - intros [(v' & -> & Hv)|(v' & -> & Hv)]; [left|right]; exists v'; split; auto.
    - intros (e & -> & Hx & -> & -> & H). exists e. split_and!; [done|done|done|done|].
      intros N' j ss r tk HN Hj Hl Hss Hm.
      eapply FuelE_frame_mono; [exact Hc|].
      specialize (H N' j ss r tk HN Hj Hl Hss (Ht r tk Hm)).
      destruct k as [|k].
      + destruct ss; [|done]. rewrite !sinst_slist_nil in H |- *.
        eapply FuelE_res_mono; [|exact H].
        intros N'' m0 Π0 φ0 w Hm0 Hw. by apply (Vfuel_teq m0 N'' U U').
      + by subst.
    - intros (o & S' & f & -> & -> & -> & HS & Hf).
      exists o, S', f. split_and!; try done; [by eapply sequiv_trans|by eapply fle_trans].
    - intros Hv. by apply IHT.
  Qed.
End sub.

(** F5 along ⊑. *)
Lemma Vfuel_sub n : ∀ N T T' Π φ v, tsub T T' →
  v ∈ FV^N _ n⟦RTy T⟧(Π, φ) → v ∈ FV^N _ n⟦RTy T'⟧(Π, φ).
Proof.
  induction n as [n IH] using lt_wf_ind. intros N T T' Π φ v Hs. rewrite !Vfuel_eq. simpl.
  by apply Vty_sub.
Qed.

(** F4 along ⊑: FuelE follows subtyping of its result type. *)
Lemma FuelE_sub N n T T' d r Π φ tk e :
  tsub T T' →
  e ∈ F^N _ n⟦RTy T ▷ d ; r⟧(Π, φ, tk) → e ∈ F^N _ n⟦RTy T' ▷ d ; r⟧(Π, φ, tk).
Proof. intros Hs. apply FuelE_res_mono. intros. by eapply Vfuel_sub. Qed.
