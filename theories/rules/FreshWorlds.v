(** * Worlds with a fresh point related to known points

    The fresh extension that places a new name a and relates its points
    to known points by two relations [Lo] (x ≺ p) and [Hi] (q ≺ y), and
    the substitution [pfresh] that puts a in place of the variable of a
    fresh constraint. The existential signature of new
    (rules/TermRules.v, sharp edges 93, 97, 103) uses them. The
    material moved here from rules/FreshRules.v, which went with the
    rule E-NewFresh. *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export rules.Bind.

Set Default Proof Using "All".

(** ** Facts on every instant and carried point of the fresh channel

    The facts of a general E-NewFresh relate points x known to W and
    points p of the fresh name a: (a, k), its carried points (a, k).i,
    their successors, and so on. [Lo x p] states x ≺ p and [Hi q y]
    states q ≺ y. A path through a enters at some p, moves along program
    order of one name of a to some q, and leaves. Betweenness asks
    x ≺ y in W for every such pair, that is, for every Lo x p and Hi q y
    with q on the name of p at an offset at least that of p
    (sharp edges 93). Program order is the only order between points of
    a, because C has no ≡ fact and W does not know a. *)


Section between_gen.
  Context (W : world) (a : nat) (Lo Hi : point → point → Prop).
  Context (HW : strict W).
  Context (HLo : ∀ x p, Lo x p → pt_known W x ∧ pt_root p = NConst a).
  Context (HHi : ∀ q y, Hi q y → pt_root q = NConst a ∧ pt_known W y).
  Context (Hbt : ∀ x p q y, Lo x p → Hi q y → ple p q → w_lt W x y).
  Context (Ha : NConst a ∉ w_names W).

  Let Hwf : world_wf W := proj1 HW.

  Definition gfacts (x y : point) : Prop := w_lt W x y ∨ Lo x y ∨ Hi x y.

  Definition Wg : world := wgen (w_names W ∪ {[NConst a]}) (w_eq W) gfacts.

  Definition gblt (u v : point) : Prop :=
    w_lt W u v ∨
    (∃ x p, Lo x p ∧ w_le W u x ∧ ple p v) ∨
    (∃ q y, Hi q y ∧ ple u q ∧ w_le W y v) ∨
    (∃ q y x p, Hi q y ∧ Lo x p ∧ ple u q ∧ w_le W y x ∧ ple p v).

  Lemma ple_root p v : ple p v → pt_root p = pt_root v.
  Proof. intros [H _]. unfold pt_root. by rewrite H. Qed.

  Lemma ple_trans p q v : ple p q → ple q v → ple p v.
  Proof. intros [H1 H2] [H3 H4]. split; [congruence|lia]. Qed.

  Lemma g_eq_a z u : pt_root z = NConst a → w_eq W z u → z = u.
  Proof.
    intros Hz He. destruct (wf_eq_supp _ Hwf _ _ He) as [->|[Hz' _]]; [done|].
    exfalso. apply Ha. by rewrite <-Hz.
  Qed.

  Lemma g_eq_a' z u : pt_root z = NConst a → w_eq W u z → u = z.
  Proof. intros Hz He. symmetry. apply g_eq_a; [done|]. by apply (wf_eq_sym _ Hwf). Qed.

  Lemma g_lt_a_l z u : pt_root z = NConst a → w_lt W z u → ple z u.
  Proof.
    intros Hz Hl. destruct (wf_lt_supp _ Hwf _ _ Hl) as [[? ?]|[Hz' _]]; [split; [done|lia]|].
    exfalso. apply Ha. by rewrite <-Hz.
  Qed.

  Lemma g_lt_a_r z u : pt_root z = NConst a → w_lt W u z → ple u z.
  Proof.
    intros Hz Hl. destruct (wf_lt_supp _ Hwf _ _ Hl) as [[? ?]|[_ Hz']]; [split; [done|lia]|].
    exfalso. apply Ha. by rewrite <-Hz.
  Qed.

  Lemma g_le_known_a x z : pt_known W x → pt_root z = NConst a → ¬ w_le W x z.
  Proof.
    intros Hx Hz [He|Hl].
    - apply g_eq_a' in He; [|done]. subst. apply Ha. unfold pt_known in Hx. congruence.
    - apply (g_lt_a_r _ _ Hz), ple_root in Hl. apply Ha. unfold pt_known in Hx. congruence.
  Qed.

  Lemma g_le_a_known x z : pt_known W x → pt_root z = NConst a → ¬ w_le W z x.
  Proof.
    intros Hx Hz [He|Hl].
    - apply g_eq_a in He; [|done]. subst. apply Ha. unfold pt_known in Hx. congruence.
    - apply (g_lt_a_l _ _ Hz), ple_root in Hl. apply Ha. unfold pt_known in Hx. congruence.
  Qed.

  Lemma g_le_lt x y z : w_le W x y → w_lt W y z → w_lt W x z.
  Proof.
    intros [He|Hl] H2.
    - eapply (wf_lt_eq _ Hwf); [exact He|exact H2|apply (wf_eq_refl _ Hwf)].
    - by eapply (wf_lt_trans _ Hwf).
  Qed.

  Lemma g_lt_le x y z : w_lt W x y → w_le W y z → w_lt W x z.
  Proof.
    intros H1 [He|Hl].
    - eapply (wf_lt_eq _ Hwf); [apply (wf_eq_refl _ Hwf)|exact H1|exact He].
    - by eapply (wf_lt_trans _ Hwf).
  Qed.

  Lemma g_le_le x y z : w_le W x y → w_le W y z → w_le W x z.
  Proof.
    intros [He|Hl] H2.
    - destruct H2 as [He'|Hl'].
      + left. by eapply (wf_eq_trans _ Hwf).
      + right. by eapply g_le_lt; [left|].
    - right. by eapply g_lt_le.
  Qed.

  Lemma g_le_refl x : w_le W x x.
  Proof. left. apply (wf_eq_refl _ Hwf). Qed.

  Lemma g_root_lo x p : Lo x p → pt_root p = NConst a.
  Proof. intros H. apply (HLo _ _ H). Qed.

  Lemma g_root_hi q y : Hi q y → pt_root q = NConst a.
  Proof. intros H. apply (HHi _ _ H). Qed.

  Lemma g_geq_W x y : geq (w_eq W) x y → w_eq W x y.
  Proof.
    induction 1; eauto using wf_eq_refl, wf_eq_sym, wf_eq_trans, wf_eq_shift, wf_eq_slot.
  Qed.

  Lemma g_lt_strict_ple u v w : pt_root w = NConst a → w_lt W u v → ple v w → ple u w.
  Proof.
    intros Hw H1 Hvw. eapply ple_trans; [|exact Hvw].
    apply g_lt_a_r in H1; [destruct H1; split; [done|lia]|].
    by rewrite (ple_root _ _ Hvw).
  Qed.

  Lemma g_ple_lt p v w : pt_root p = NConst a → ple p v → w_lt W v w → ple p w.
  Proof.
    intros Hp Hpv H2. eapply ple_trans; [exact Hpv|].
    apply g_lt_a_l in H2; [destruct H2; split; [done|lia]|].
    by rewrite <-(ple_root _ _ Hpv).
  Qed.

  Lemma glt_gblt u v : glt (w_eq W) gfacts u v → gblt u v.
  Proof.
    induction 1 as [u v Hb|u|u u' v v' Hu _ IH Hv|u v w _ IH1 _ IH2].
    - destruct Hb as [Hb|[Hb|Hb]].
      + by left.
      + right; left. exists u, v. split_and!; [done|apply g_le_refl|split; [done|lia]].
      + right; right; left. exists u, v. split_and!; [done|split; [done|lia]|apply g_le_refl].
    - left. apply (wf_lt_po _ Hwf).
    - apply g_geq_W in Hu, Hv.
      destruct IH as [IH|[(x & p & Hl & Hle & Hp)|[(q & y & Hh & Hq & Hle)|
                      (q & y & x & p & Hh & Hl & Hq & Hyx & Hp)]]].
      + left. by eapply (wf_lt_eq _ Hwf).
      + right; left. exists x, p. split_and!; [done|eapply g_le_le; [left; exact Hu|exact Hle]|].
        assert (pt_root v' = NConst a) as Hr by (rewrite <-(ple_root _ _ Hp); by apply (g_root_lo x)).
        apply (g_eq_a _ _ Hr) in Hv. by subst.
      + right; right; left. exists q, y.
        assert (pt_root u' = NConst a) as Hr by (rewrite (ple_root _ _ Hq); by apply (g_root_hi _ y)).
        apply (g_eq_a' _ _ Hr) in Hu. subst. split_and!; [done|done|].
        eapply g_le_le; [exact Hle|left; exact Hv].
      + right; right; right. exists q, y, x, p.
        assert (pt_root u' = NConst a) as Hr by (rewrite (ple_root _ _ Hq); by apply (g_root_hi _ y)).
        apply (g_eq_a' _ _ Hr) in Hu. subst.
        assert (pt_root v' = NConst a) as Hr' by (rewrite <-(ple_root _ _ Hp); by apply (g_root_lo x)).
        apply (g_eq_a _ _ Hr') in Hv. by subst.
    - destruct IH1 as [H1|[(x & p & Hl & Hle & Hp)|[(q & y & Hh & Hq & Hle)|
                      (q & y & x & p & Hh & Hl & Hq & Hyx & Hp)]]];
      destruct IH2 as [H2|[(x' & p' & Hl' & Hle' & Hp')|[(q' & y' & Hh' & Hq' & Hle')|
                      (q' & y' & x' & p' & Hh' & Hl' & Hq' & Hyx' & Hp')]]].
      (* B1 then _ *)
      + left. by eapply (wf_lt_trans _ Hwf).
      + right; left. exists x', p'. split_and!; [done|right; by eapply g_lt_le|done].
      + right; right; left. exists q', y'. split_and!; [done| |done].
        apply (g_lt_strict_ple u v); [by apply (g_root_hi _ y')|done|done].
      + right; right; right. exists q', y', x', p'. split_and!; [done|done| |done|done].
        apply (g_lt_strict_ple u v); [by apply (g_root_hi _ y')|done|done].
      (* B2 then _ *)
      + right; left. exists x, p. split_and!; [done|done|].
        apply (g_ple_lt p v); [by apply (g_root_lo x)|done|done].
      + exfalso. apply (g_le_a_known x' v); [by apply (HLo _ _ Hl')| |done].
        rewrite <-(ple_root _ _ Hp). by apply (g_root_lo x).
      + left. eapply g_le_lt; [exact Hle|]. eapply g_lt_le; [|exact Hle'].
        apply (Hbt x p q' y'); [done|done|]. by eapply ple_trans.
      + right; left. exists x', p'. split_and!; [done| |done].
        right. eapply g_le_lt; [exact Hle|]. eapply g_lt_le; [|exact Hyx'].
        apply (Hbt x p q' y'); [done|done|]. by eapply ple_trans.
      (* B3 then _ *)
      + right; right; left. exists q, y. split_and!; [done|done|]. right. by eapply g_le_lt.
      + right; right; right. exists q, y, x', p'. split_and!; try done. by eapply g_le_le.
      + exfalso. apply (g_le_known_a y v); [by apply (HHi _ _ Hh)| |done].
        rewrite (ple_root _ _ Hq'). by apply (g_root_hi _ y').
      + exfalso. apply (g_le_known_a y v); [by apply (HHi _ _ Hh)| |done].
        rewrite (ple_root _ _ Hq'). by apply (g_root_hi _ y').
      (* B4 then _ *)
      + right; right; right. exists q, y, x, p. split_and!; [done|done|done|done|].
        apply (g_ple_lt p v); [by apply (g_root_lo x)|done|done].
      + exfalso. apply (g_le_a_known x' v); [by apply (HLo _ _ Hl')| |done].
        rewrite <-(ple_root _ _ Hp). by apply (g_root_lo x).
      + right; right; left. exists q, y. split_and!; [done|done|].
        right. eapply g_le_lt; [exact Hyx|]. eapply g_lt_le; [|exact Hle'].
        apply (Hbt x p q' y'); [done|done|]. by eapply ple_trans.
      + right; right; right. exists q, y, x', p'. split_and!; [done|done|done| |done].
        right. eapply g_le_lt; [exact Hyx|]. eapply g_lt_le; [|exact Hyx'].
        apply (Hbt x p q' y'); [done|done|]. by eapply ple_trans.
  Qed.

  Lemma Wg_wf : world_wf Wg.
  Proof.
    apply wgen_wf.
    - intros p [Hp|Hp%elem_of_singleton]%elem_of_union; [by apply (wf_names_const _ Hwf)|].
      by eexists.
    - intros x y Hxy. eapply eq_or_supp_mono; [|by apply (wf_eq_supp _ Hwf)]. set_solver.
    - intros x y [Hxy|[Hxy|Hxy]].
      + eapply po_or_supp_mono; [|by apply (wf_lt_supp _ Hwf)]. set_solver.
      + destruct (HLo _ _ Hxy) as [Hx Hy]. right. unfold pt_known in Hx. rewrite Hy. set_solver.
      + destruct (HHi _ _ Hxy) as [Hx Hy]. right. unfold pt_known in Hy. rewrite Hx. set_solver.
  Qed.

  Lemma Wg_strict : strict Wg.
  Proof.
    split; [apply Wg_wf|]. intros u Hu. apply glt_gblt in Hu.
    destruct Hu as [Hu|[(x & p & Hl & Hle & Hp)|[(q & y & Hh & Hq & Hle)|
                    (q & y & x & p & Hh & Hl & Hq & Hyx & Hp)]]].
    - by apply (proj2 HW u).
    - apply (g_le_a_known x u); [by apply (HLo _ _ Hl)| |done].
      rewrite <-(ple_root _ _ Hp). by apply (g_root_lo x).
    - apply (g_le_known_a y u); [by apply (HHi _ _ Hh)| |done].
      rewrite (ple_root _ _ Hq). by apply (g_root_hi _ y).
    - apply (proj2 HW x). eapply g_lt_le; [|exact Hyx].
      apply (Hbt x p q y); [done|done|]. by eapply ple_trans.
  Qed.

  Lemma Wg_fresh : wext_fresh W {[NConst a]} Wg.
  Proof.
    split_and!.
    - split_and!.
      + simpl. set_solver.
      + intros x y Hxy. by apply geq_base.
      + intros x y Hxy. apply glt_base. by left.
      + apply Wg_strict.
    - set_solver.
    - done.
    - intros x y Hx Hy. split.
      + simpl. apply g_geq_W.
      + intros Hxy. apply glt_gblt in Hxy.
        destruct Hxy as [Hxy|[(x' & p & Hl & _ & Hp)|[(q & y' & Hh & Hq & _)|
                        (q & y' & x' & p & Hh & _ & Hq & _ & _)]]]; [done|..]; exfalso.
        * apply Hy. apply elem_of_singleton. rewrite <-(ple_root _ _ Hp). by apply (g_root_lo x').
        * apply Hx. apply elem_of_singleton. rewrite (ple_root _ _ Hq). by apply (g_root_hi _ y').
        * apply Hx. apply elem_of_singleton. rewrite (ple_root _ _ Hq). by apply (g_root_hi _ y').
  Qed.
End between_gen.

Lemma wext_fresh_between_gen W a (Lo Hi : point → point → Prop) :
  strict W →
  (∀ x p, Lo x p → pt_known W x ∧ pt_root p = NConst a) →
  (∀ q y, Hi q y → pt_root q = NConst a ∧ pt_known W y) →
  (∀ x p q y, Lo x p → Hi q y → ple p q → w_lt W x y) →
  NConst a ∉ w_names W →
  ∃ W', wext_fresh W {[NConst a]} W' ∧
    (∀ x p, Lo x p → w_lt W' x p) ∧ (∀ q y, Hi q y → w_lt W' q y).
Proof.
  intros HW HL HH Hbt Ha. exists (Wg W a Lo Hi). split_and!.
  - by apply Wg_fresh.
  - intros x p H. apply glt_base. right. by left.
  - intros q y H. apply glt_base. by right; right.
Qed.

(** ** Points of the fresh name

    A fact of E-NewFresh names a point of the fresh channel by a point
    whose root is the variable 0. [pfresh a p] puts the constant a
    there. It keeps the offset and the shape of carried points, so it
    is injective on such points and keeps program order both ways. *)

Definition pfresh (a : nat) (p : point) : point := pt_inst (λ _, pconst a) p.

Fixpoint rn (a : nat) (n : pname) : pname :=
  match n with
  | NVar _ => NConst a
  | NConst c => NConst c
  | NSlot q b i => NSlot (rn a q) b i
  end.

Lemma pn_inst_fresh a n : pn_inst (λ _, pconst a) n = Pt (rn a n) 0.
Proof. induction n as [c|v|q IH b i]; simpl; [done|done|]. by rewrite IH. Qed.

Lemma pfresh_name a p : pt_name (pfresh a p) = rn a (pt_name p).
Proof. destruct p as [n o]. unfold pfresh, pt_inst. simpl. by rewrite pn_inst_fresh. Qed.

Lemma pfresh_off a p : pt_off (pfresh a p) = pt_off p.
Proof. destruct p as [n o]. unfold pfresh, pt_inst. simpl. rewrite pn_inst_fresh. simpl. lia. Qed.

Lemma rn_root a n v : pn_root n = NVar v → pn_root (rn a n) = NConst a.
Proof. induction n as [c|w|q IH b i]; simpl; [done|done|exact IH]. Qed.

Lemma pfresh_root a p v : pt_root p = NVar v → pt_root (pfresh a p) = NConst a.
Proof. intros H. unfold pt_root. rewrite pfresh_name. by apply (rn_root _ _ v). Qed.

Lemma rn_inj a n m : pn_root n = NVar 0 → pn_root m = NVar 0 → rn a n = rn a m → n = m.
Proof.
  revert m. induction n as [c|v|q IH b i]; intros [c'|v'|q' b' i'];
    simpl; intros Hn Hm E; try congruence.
  injection E as E -> ->. f_equal. by apply IH.
Qed.

Lemma pfresh_ple a p q :
  pt_root p = NVar 0 → pt_root q = NVar 0 → ple (pfresh a p) (pfresh a q) → ple p q.
Proof.
  intros Hp Hq [Hn Ho]. rewrite !pfresh_name in Hn. rewrite !pfresh_off in Ho.
  split; [|done]. by apply (rn_inj a).
Qed.

(** ** The world of a fresh constraint (sharp edges 97)

    A ground constraint C of one variable whose facts relate points of
    the fresh channel to known outer points, with betweenness in W,
    holds at a fresh constant a in a fresh extension of W. The
    existential signature of new and E-NewFresh both read C this way. *)

Section fresh_con.
  Local Lemma fw_pn_inst_ext_root σ τ p :
    (∀ b, pn_root p = NVar b → σ b = τ b) → pn_inst σ p = pn_inst τ p.
  Proof. induction p as [c|c|p IH b i]; simpl; intros H; [done|by apply H|by rewrite IH]. Qed.

  Local Lemma fw_pt_inst_ext_root σ τ x :
    (∀ b, pt_root x = NVar b → σ b = τ b) → pt_inst σ x = pt_inst τ x.
  Proof. intros H. unfold pt_inst. f_equal. by apply fw_pn_inst_ext_root. Qed.

  Local Lemma fw_pn_root_inst σ p b :
    pn_root p = NVar b → pt_root (pn_inst σ p) = pt_root (σ b).
  Proof. induction p as [c|c|p IH b' i]; simpl; intros H; [done|by injection H as ->|by apply IH]. Qed.

  Local Lemma fw_pt_root_inst σ x b :
    pt_root x = NVar b → pt_root (pt_inst σ x) = pt_root (σ b).
  Proof. intros H. destruct x as [p o]. unfold pt_inst, pt_root in *. simpl in *. by apply fw_pn_root_inst. Qed.

  Local Lemma fw_pn_vb_root k p b : pn_vb k p → pn_root p = NVar b → b < k.
  Proof. induction p as [c|c|q IH b' i]; simpl; [done|congruence|exact IH]. Qed.

  (** An outer point of a constraint reads to a point of its environment. *)
  Lemma fresh_outer_known W C u :
    Forall (pt_known W) (bc_env C) → pn_vb (S (length (bc_env C))) (pt_name u) →
    pt_root u ≠ NVar 0 → pt_known W (fresh_outer C u).
  Proof.
    intros HK Hs Hr. destruct (pn_root (pt_name u)) as [c|b|q b' i] eqn:Hb.
    - exfalso. clear -Hs Hb. induction (pt_name u) as [c'|c'|q IH b' i]; simpl in *; congruence || auto.
    - pose proof (fw_pn_vb_root _ _ _ Hs Hb) as Hlt. destruct b as [|j]; [done|].
      destruct (lookup_lt_is_Some_2 (bc_env C) j) as [y Hy]; [lia|].
      unfold pt_known, fresh_outer. rewrite (fw_pt_root_inst _ _ (S j)) by done.
      unfold plist. simpl. rewrite Hy. rewrite Forall_lookup in HK. apply (HK j y Hy).
    - exfalso. clear -Hb. induction (pt_name u) as [c'|c'|q' IH b'' i']; simpl in *; congruence || auto.
  Qed.

  Local Lemma fw_unshift x z : pt_inst (plist [x]) (pt_inst (λ a', pvar (a' + 1)) z) = z.
  Proof.
    rewrite tpt_inst_comp. transitivity (pt_inst pvar z); [|apply tpt_inst_pvar].
    apply tpt_inst_ext. intros b. simpl. rewrite tpt_inst_pvar_at. unfold plist. simpl.
    replace (b + 1) with (S b) by lia. simpl. unfold pvar. f_equal. f_equal. lia.
  Qed.

  Local Lemma fw_open1 x env f :
    fact_map (pt_inst (plist [x])) (fact_map (pt_inst (pup 1 (plist env))) f)
    = fact_map (pt_inst (plist (x :: env))) f.
  Proof.
    rewrite fact_map_comp. apply fact_map_ext. intros z. simpl.
    rewrite tpt_inst_comp. apply tpt_inst_ext. intros b. unfold compose, pup.
    destruct (decide (b < 1)).
    - assert (b = 0) as -> by lia. by rewrite tpt_inst_pvar_at.
    - rewrite fw_unshift. destruct b as [|b]; [lia|]. replace (S b - 1) with b by lia.
      unfold plist. simpl. destruct (env !! b); [done|]. unfold pvar. repeat f_equal.
  Qed.

  Lemma bcs_hold_fresh_con (eq lt : point → point → Prop) C x :
    (∀ f, bc_facts C f → fact_scoped (S (length (bc_env C))) f →
       fact_holds eq lt (fact_map (pt_inst (plist (x :: bc_env C))) f)) →
    bcs_hold eq lt C [x].
  Proof. intros H g (f & Hf & Hs & ->). rewrite fw_open1. by apply H. Qed.

  Lemma fresh_outer_at C a u :
    pt_root u ≠ NVar 0 → pt_inst (plist (pconst a :: bc_env C)) u = fresh_outer C u.
  Proof.
    intros Hr. unfold fresh_outer. apply fw_pt_inst_ext_root. intros [|b] Hb; [done|].
    unfold plist. done.
  Qed.

  Lemma fresh_point_at C a p :
    pt_root p = NVar 0 → pt_inst (plist (pconst a :: bc_env C)) p = pfresh a p.
  Proof.
    intros Hr. unfold pfresh. apply fw_pt_inst_ext_root. intros b Hb.
    rewrite Hr in Hb. by injection Hb as <-.
  Qed.
End fresh_con.

Lemma wext_fresh_con W a C :
  strict W → fresh_lt C → Forall (pt_known W) (bc_env C) →
  (∀ u p q v, fresh_lo C u p → fresh_hi C q v → ple p q →
     w_lt W (fresh_outer C u) (fresh_outer C v)) →
  NConst a ∉ w_names W →
  ∃ W', wext_fresh W {[NConst a]} W' ∧ bcs_hold (w_eq W') (w_lt W') C [pconst a] ∧
    (∀ u p, fresh_lo C u p → w_lt W' (fresh_outer C u) (pfresh a p)).
Proof.
  intros HW HC HK Hbt Ha.
  destruct (wext_fresh_between_gen W a
              (λ x p', ∃ u p, fresh_lo C u p ∧ x = fresh_outer C u ∧ p' = pfresh a p)
              (λ q' y, ∃ q v, fresh_hi C q v ∧ y = fresh_outer C v ∧ q' = pfresh a q) HW)
    as (W' & Hfr & HL & HH).
  { intros x p' (u & p & Hu & -> & ->). pose proof Hu as (_ & [Hs _] & Hp & Hr). split.
    - by apply fresh_outer_known.
    - by apply (pfresh_root _ _ 0). }
  { intros q' y (q & v & Hv & -> & ->). pose proof Hv as (_ & [_ Hs] & Hq & Hr). split.
    - by apply (pfresh_root _ _ 0).
    - by apply fresh_outer_known. }
  { intros x p' q' y (u & p & Hu & -> & ->) (q & v & Hv & -> & ->) Hpq.
    apply (Hbt u p q v Hu Hv). apply (pfresh_ple a); [apply Hu|apply Hv|done]. }
  { done. }
  exists W'. split_and!; [done| |].
  - apply bcs_hold_fresh_con. intros f Hf Hs.
    destruct (HC f Hf Hs) as [(u & p & -> & Hu)|(q & v & -> & Hv)]; simpl.
    + pose proof Hu as (_ & _ & Hp & Hr).
      rewrite (fresh_outer_at C a u), (fresh_point_at C a p) by done. apply HL. by exists u, p.
    + pose proof Hv as (_ & _ & Hq & Hr).
      rewrite (fresh_point_at C a q), (fresh_outer_at C a v) by done. apply HH. by exists q, v.
  - intros u p Hu. apply HL. by exists u, p.
Qed.
