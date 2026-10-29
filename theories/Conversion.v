(** * Entry conversion and Type point conversion (§10)

    Aliased points are interchangeable:

      x ≡_W y  ⇒  t ∈ E^W_n⟦Θ, c : S@x ⊢ T ≺ F⟧ ⇔ t ∈ E^W_n⟦Θ, c : S@y ⊢ T ≺ F⟧
                                                      (Entry conversion)
      T ≈_W T′ ⇒  V, E, P at T ⇔ V, E, P at T′       (Type point conversion)

    and likewise for V and P. One induction on the step index carries
    both ([rel_conv]): converting an entry changes the payload type
    P[x] of a receive into P[y], and converting a type converts the
    environments of the values it takes. An entry conversion moves the
    ends of one channel, each to an aliased point; payloads stay typed
    by slot congruence, continuations by successor congruence. *)

From stdpp Require Import base tactics gmap.
From LRGV Require Export Monotone.

(** ** Types up to aliases *)

Section teqW.
  Context (W : world) (HW : world_wf W).

  Lemma pteqW_eq x y : pteqW W x y → w_eq W x y.
  Proof. intros [->|(_ & _ & H)]; [apply HW|done]. Qed.

  Lemma pteqW_refl x : pteqW W x x.
  Proof. by left. Qed.

  Lemma pteqW_sym x y : pteqW W x y → pteqW W y x.
  Proof. intros [->|(? & ? & ?)]; [by left|right; split_and!; auto using wf_eq_sym]. Qed.

  Lemma pteqW_trans x y z : pteqW W x y → pteqW W y z → pteqW W x z.
  Proof.
    intros [->|(? & ? & ?)] [->|(? & ? & ?)]; [by left|by right..|].
    right. split_and!; [done|done|]. by eapply wf_eq_trans.
  Qed.

  (** In a well-formed world only ground points have proper aliases. *)
  Lemma w_eq_pteqW x y : w_eq W x y → pteqW W x y.
  Proof.
    intros H. destruct (wf_eq_supp _ HW x y H) as [->|[Hx Hy]]; [by left|right].
    destruct (wf_names_const _ HW _ Hx) as [a Ha].
    destruct (wf_names_const _ HW _ Hy) as [b Hb].
    split_and!; [by exists a|by exists b|done].
  Qed.

  Lemma opt_rel_refl o : opt_rel (pteqW W) o o.
  Proof. destruct o; simpl; [apply pteqW_refl|done]. Qed.

  Lemma opt_rel_sym o o' : opt_rel (pteqW W) o o' → opt_rel (pteqW W) o' o.
  Proof. destruct o, o'; simpl; try done. apply pteqW_sym. Qed.

  Lemma opt_rel_trans o o' o'' :
    opt_rel (pteqW W) o o' → opt_rel (pteqW W) o' o'' → opt_rel (pteqW W) o o''.
  Proof. destruct o, o', o''; simpl; try done. apply pteqW_trans. Qed.

  Lemma teqW_refl T : teqW W T T.
  Proof.
    induction T; simpl; repeat split; auto using opt_rel_refl, pteqW_refl, seq_refl.
  Qed.

  Lemma teqW_sym T : ∀ U, teqW W T U → teqW W U T.
  Proof.
    induction T; intros [] H; simpl in *; try done; try naive_solver.
    - destruct H as (? & ? & ? & ?). split_and!; auto using opt_rel_sym.
    - destruct H as [? ?]. split; [by apply pteqW_sym|by apply seq_sym].
  Qed.

  Lemma teqW_trans T : ∀ U V, teqW W T U → teqW W U V → teqW W T V.
  Proof.
    induction T; intros [] [] H1 H2; simpl in *; try done; try naive_solver.
    - destruct H1 as (? & ? & ? & ?), H2 as (? & ? & ? & ?).
      split_and!; eauto using opt_rel_trans.
    - destruct H1 as [? ?], H2 as [? ?]. split; [by eapply pteqW_trans|by eapply seq_trans].
  Qed.

  Lemma pteqW_shift n x y : pteqW W x y → pteqW W (pt_shift n x) (pt_shift n y).
  Proof.
    intros H. apply w_eq_pteqW. apply wf_eq_shift_n; [done|]. by apply pteqW_eq.
  Qed.

  Lemma pteqW_slot x y i : pteqW W x y → pteqW W (pt_slot x i) (pt_slot y i).
  Proof.
    intros H. apply w_eq_pteqW. apply (wf_eq_slot _ HW). by apply pteqW_eq.
  Qed.

  (** A ground point is fixed by instantiation. *)
  Lemma pn_inst_ground σ p a : pn_root p = NConst a → pn_inst σ p = Pt p 0.
  Proof.
    induction p; simpl; intros H; try done. rewrite IHp by done.
    unfold pt_slot, pt_shift. simpl. by rewrite ?Nat.add_0_l.
  Qed.

  Lemma pt_inst_ground σ x : pt_ground x → pt_inst σ x = x.
  Proof.
    intros [a Ha]. destruct x as [p o]. unfold pt_inst. simpl.
    rewrite (pn_inst_ground σ p a Ha). unfold pt_shift. simpl. by rewrite ?Nat.add_0_l.
  Qed.

  Lemma pteqW_inst_r ρ x y : pteqW W x y → pteqW W (pt_inst ρ x) (pt_inst ρ y).
  Proof.
    intros [->|(Hx & Hy & H)]; [by left|right].
    by rewrite !pt_inst_ground.
  Qed.

  Lemma pteqW_inst_l σ τ x :
    (∀ i, pteqW W (σ i) (τ i)) → pteqW W (pt_inst σ x) (pt_inst τ x).
  Proof.
    intros H. destruct x as [p o]. unfold pt_inst. simpl. apply pteqW_shift.
    induction p; simpl; [by left|apply H|]. apply pteqW_slot, pteqW_shift, IHp.
  Qed.

  Lemma pup_pteqW m σ τ :
    (∀ i, pteqW W (σ i) (τ i)) → ∀ i, pteqW W (pup m σ i) (pup m τ i).
  Proof. intros H i. unfold pup. case_decide; [by left|]. by apply pteqW_inst_r. Qed.

  (** Instantiating with aliased points gives types up to aliases. *)
  Lemma teqW_pinst_l T : ∀ σ τ,
    (∀ i, pteqW W (σ i) (τ i)) → teqW W (pinst_ty σ T) (pinst_ty τ T).
  Proof.
    induction T; intros σ τ H; simpl; repeat split; auto using seq_refl.
    - destruct ub; simpl; [by apply pteqW_inst_l|done].
    - destruct lb; simpl; [by apply pteqW_inst_l|done].
    - apply IHT. by apply pup_pteqW.
    - by apply pteqW_inst_l.
  Qed.

  Lemma teqW_pinst_r T : ∀ U σ, teqW W T U → teqW W (pinst_ty σ T) (pinst_ty σ U).
  Proof.
    induction T; intros [] σ H; simpl in *; try done.
    - destruct H as (Hu & Hl & ? & ?). split_and!; auto.
      + destruct ub, ub0; simpl in *; try done. by apply pteqW_inst_r.
      + destruct lb, lb0; simpl in *; try done. by apply pteqW_inst_r.
    - destruct H. split; auto.
    - destruct H. split; auto.
    - destruct H as [<- ?]. split; [done|]. by apply IHT.
    - destruct H as [? ?]. split; [by apply pteqW_inst_r|done].
  Qed.

  Lemma teqW_ty_inst xs T U : teqW W T U → teqW W (ty_inst xs T) (ty_inst xs U).
  Proof. apply teqW_pinst_r. Qed.

  Lemma teqW_payload m U x y : w_eq W x y → teqW W (payload_at m U x) (payload_at m U y).
  Proof.
    intros H. apply teqW_pinst_l. intros i. unfold plist, slots.
    rewrite !list_lookup_fmap, !length_fmap, length_seq.
    destruct (List.seq 0 m !! i); simpl; [|by left].
    apply pteqW_slot. by apply w_eq_pteqW.
  Qed.
End teqW.

Lemma teqW_mono' W W' T U :
  (∀ x y, w_eq W x y → w_eq W' x y) → teqW W T U → teqW W' T U.
Proof. apply teqW_mono. Qed.
