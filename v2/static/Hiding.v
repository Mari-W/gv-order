(** * Renaming the constants of a derivation

    Process typing concludes at the world of its derivation ([ptyped],
    static/Typing.v). Two components may use one private constant for
    unrelated points, and P-Connect then reads the facts of both at that
    constant. Renaming lets such components compose: a bijection of
    constants maps a derivation to a derivation at the renamed world.

      swrestrict_iff  : W|S orders the points with roots in S exactly as
                        W does, through private constants too
      typed_ren       : a bijection of constants renames a derivation of
                        the term judgment
      ptyped_ren      : and one of the process judgment, exactly
      ptyped_apart    : two components renamed by bijections that fix
                        their interfaces share only interface constants

    In [ptyped_apart] the first component is renamed to keep its private
    constants off the interface of the second ([cb_avoid]), and the
    second to keep its private constants off the whole world of the
    first. *)

From GV Require Export static.Typing.

(** ** The restriction keeps the derived order *)

Lemma swrestrict_iff W S x y :
  croot_in (sw_consts W ∩ S) x → croot_in (sw_consts W ∩ S) y →
  swrestrict W S ⊢ₛ x ≺ y ↔ W ⊢ₛ x ≺ y.
Proof.
  intros Hx Hy. split; [apply swrestrict_lt|]. intros H. by apply sw_lt_fact.
Qed.

(** An order follows from orders that cover the facts. *)
Lemma sw_lt_by W W' : (∀ x y, sw_facts W (FLt x y) → W' ⊢ₛ x ≺ y) → ∀ x y, W ⊢ₛ x ≺ y → W' ⊢ₛ x ≺ y.
Proof.
  intros H. assert (∀ x y, swstep W x y → W' ⊢ₛ x ≺ y) as Hs.
  { intros x y [x' y' Hf|x'|x']; [by apply H|apply sw_lt_po|apply sw_lt_dpo]. }
  intros x y. induction 1 as [x y Hxy|x z y Hxz _ IH]; [by apply Hs|]. eapply sw_lt_trans; [by apply Hs|done].
Qed.

(** The point of an interface end has its constants in the interface. *)
Lemma senv_pt_iface (Σ : senv) T o S x : Σ !! o = Some (S, x) → pt_consts x ⊆ iface Σ T.
Proof. intros H a Ha. unfold iface. apply elem_of_union_l, elem_of_senv_consts. eauto 10. Qed.

(** ** Renaming a derivation *)

Section ren.
  Context (π : cbij).
  Local Abbreviation f := (cb_f π).

  Lemma lenv_ren_cons o Δ : lenv_ren f (o :: Δ) = (ty_ren f <$> o) :: lenv_ren f Δ.
  Proof. done. Qed.

  Lemma lenv_ren_insert i o Δ : lenv_ren f (<[i := o]> Δ) = <[i := ty_ren f <$> o]> (lenv_ren f Δ).
  Proof. unfold lenv_ren. by rewrite list_fmap_insert. Qed.

  Lemma sty_ren_if (i : bool) a b : sty_ren f (if i then a else b) = if i then sty_ren f a else sty_ren f b.
  Proof. by destruct i. Qed.
  Lemma ty_ren_if (i : bool) a b : ty_ren f (if i then a else b) = if i then ty_ren f a else ty_ren f b.
  Proof. by destruct i. Qed.

  Theorem typed_ren W N Θ Γ Δ F e T c :
    typed W N Θ Γ Δ F e T c →
    typed (sw_ren π W) N (tenv_ren f Θ) (hctx_ren f Γ) (lenv_ren f Δ) (sf_ren f F) e (ty_ren f T) c.
  Proof.
    induction 1; cbn [ty_ren sty_ren] in *.
    - rewrite tenv_ren_empty. apply e_unit. by apply lenv_unl_ren.
    - rewrite tenv_ren_empty. apply e_var. by apply lenv_only_ren.
    - unfold tenv_ren. rewrite map_fmap_singleton. apply e_chan; [by apply lenv_unl_ren|done].
    - rewrite abs_fut_ren in IHtyped. eapply e_abs; [|by apply thage_ren|by apply lage_ren|by rewrite tcontr_ren|exact IHtyped].
      rewrite tenv_heads_ren, lenv_heads_ren, lenv_bot_ren, <-set_map_union_L. by apply lbx_below_h_ren.
    - rewrite sf_unionb_ren, set_map_union_L, <-tenv_heads_ren, <-lenv_heads_ren, <-(lenv_bot_ren f Δ2) in IHtyped1.
      rewrite sf_unionb_ren, <-lb_heads_ren, <-(lb_bot_map (pt_ren f) lb) in IHtyped2.
      eapply e_app; [by apply tsplit_ren|by apply lenv_split_ren|by apply ub_below_u_ren
        |exact IHtyped1|by apply thage_ren|by apply lage_ren|exact IHtyped2|done].
    - rewrite sf_unionb_ren, set_map_union_L, <-tenv_heads_ren, <-lenv_heads_ren, <-(lenv_bot_ren f Δ2) in IHtyped1.
      rewrite sf_unionb_ren, <-heads_ren, <-(hbot_ren f T1) in IHtyped2.
      eapply e_pair; [by apply tsplit_ren|by apply lenv_split_ren|exact IHtyped1|by apply thage_ren
        |by apply lage_ren|exact IHtyped2|by apply tage_ren].
    - rewrite sf_unionb_ren, set_map_union_L, <-tenv_heads_ren, <-lenv_heads_ren, <-(lenv_bot_ren f Δ2) in IHtyped1.
      eapply e_letu; [by apply tsplit_ren|by apply lenv_split_ren|exact IHtyped1|by apply thage_ren
        |by apply lage_ren|exact IHtyped2].
    - rewrite sf_unionb_ren, set_map_union_L, <-tenv_heads_ren, <-lenv_heads_ren, <-(lenv_bot_ren f Δ2) in IHtyped1.
      eapply e_letp; [by apply tsplit_ren|by apply lenv_split_ren|exact IHtyped1|by apply thage_ren
        |by apply lage_ren|exact IHtyped2].
    - apply e_inj; [change (tcontr (ty_ren f (TSum T U))); by rewrite tcontr_ren|]. by rewrite <-ty_ren_if.
    - rewrite sf_unionb_ren, set_map_union_L, <-tenv_heads_ren, <-lenv_heads_ren, <-(lenv_bot_ren f Δ2) in IHtyped1.
      eapply e_case; [by apply tsplit_ren|by apply lenv_split_ren|exact IHtyped1|by apply thage_ren
        |by apply lage_ren|exact IHtyped2|exact IHtyped3].
    - rewrite tenv_ren_empty. apply e_box; [by apply lenv_unl_ren|by rewrite tcontr_ren|]. intros ss Hl Hs.
      pose proof (H2 (sty_ren (cb_g π) <$> ss) ltac:(by rewrite length_fmap) (sinsts_ren _ _ _ Hs)) as Hb.
      rewrite tenv_ren_empty, hc_open_ren, lenv_pinst_pshift_ren, lenv_ren_cons, ty_ren_sinst_slist in Hb.
      cbn [ty_ren fmap option_fmap option_map] in Hb.
      rewrite <-list_fmap_compose, (list_fmap_fix (sty_ren f ∘ sty_ren (cb_g π))) in Hb
        by (intros; apply sty_ren_inv, cb_fg).
      unfold sf_ren in Hb. simpl in Hb. rewrite set_map_empty in Hb. simpl in Hb.
      replace (frest_ren f (rest_of ub)) with (rest_of (pt_ren f <$> ub)) in Hb by (by destruct ub). exact Hb.
    - rewrite ty_ren_sinst_slist, ty_ren_inst. eapply e_force; [by rewrite length_fmap|by apply hold_at_ren
        |by rewrite length_fmap|by apply sinsts_ren| |exact IHtyped].
      rewrite <-option_fmap_compose. apply (ub_below_s_ren π) in H3. rewrite <-option_fmap_compose in H3.
      erewrite option_fmap_ext; [exact H3|]. intros x. simpl. symmetry. apply pt_inst_plist_ren.
    - rewrite pt_ren_shift. destruct H1 as [Hb1 Hh1].
      eapply e_send; [by rewrite unfoldS_ren, H|by apply pscoped_ren_mut|split; [by rewrite <-ty_ren_payload, hbot_ren|]
        |by apply (ub_below_s_ren π W Γ (Some x))|exact IHtyped|by apply tage_ren|].
      + intros y Hy. rewrite <-ty_ren_payload, heads_ren in Hy. apply elem_of_map in Hy as (y0 & -> & Hy0).
        by apply slt_ren, Hh1.
      + rewrite <-ty_ren_payload. by apply (tsub_ren π).
    - rewrite pt_ren_shift, ty_ren_payload. eapply e_recv; [by rewrite unfoldS_ren, H|by apply pscoped_ren_mut
        |by apply (ub_below_s_ren π W Γ (Some x))|exact IHtyped].
    - eapply e_close; [by rewrite unfoldS_ren, H|by apply (ub_below_s_ren π W Γ (Some x))|exact IHtyped].
    - rewrite sty_ren_if, pt_ren_sel. eapply e_select; [by rewrite unfoldS_ren, H|by apply (ub_below_s_ren π W Γ (Some x))
        |exact IHtyped].
    - rewrite !pt_ren_bra. eapply e_branch; [by rewrite unfoldS_ren, H|by apply (ub_below_s_ren π W Γ (Some x))|exact IHtyped].
    - rewrite dual_ren, pt_ren_dual in IHtyped. eapply e_link; [exact IHtyped|done|done].
    - by eapply e_spawn.
    - rewrite tenv_ren_empty, dual_ren. apply e_new; [by apply lenv_unl_ren|by apply new_ok_ren|done|by rewrite scontr_ren].
    - rewrite tenv_ren_empty, dual_ren, pt_ren_dual, pt_ren_field. apply e_new_fld; [by apply lenv_unl_ren|done|by rewrite scontr_ren].
    - eapply e_sub; [exact IHtyped|by apply (tsub_ren π)|done|by rewrite !tcontr_ren].
    - rewrite ty_ren_inst in IHtyped. eapply (e_pack _ _ _ _ _ _ _ _ _ _ _ (pt_ren f <$> xs)); [by rewrite length_fmap|by apply hold_at_ren| |by apply ex_wf_ren
        |exact IHtyped].
      rewrite <-ty_ren_inst, heads_ren, hbot_ren. by apply lbx_below_h_ren.
    - rewrite tenv_pinst_pshift_ren, hc_open_ren, lenv_ren_insert, lenv_pinst_pshift_ren, sf_pinst_pshift_ren,
        ty_ren_pshift in IHtyped.
      eapply e_open; [unfold lenv_ren; by rewrite list_lookup_fmap, H|by rewrite unlimited_ren
        |by apply cons_open_ren|exact IHtyped].
  Qed.
End ren.

(** ** Renaming interfaces and worlds *)

Lemma senv_dual_ren f Σ : senv_ren f (senv_dual Σ) = senv_dual (senv_ren f Σ).
Proof.
  apply map_eq. intros o. rewrite <-(edual_edual o). unfold senv_ren, senv_dual.
  rewrite lookup_fmap, !(lookup_kmap edual), !lookup_fmap. destruct (Σ !! edual o) as [[s x]|]; simpl; [|done].
  by rewrite dual_ren.
Qed.

Lemma senv_ren_union f Σ1 Σ2 : senv_ren f (Σ1 ∪ Σ2) = senv_ren f Σ1 ∪ senv_ren f Σ2.
Proof. apply map_fmap_union. Qed.

Lemma dom_senv_ren f Σ : dom (senv_ren f Σ) = dom Σ.
Proof. apply dom_fmap_L. Qed.

Lemma chans_of_ren f Σ : chans_of (senv_ren f Σ) = chans_of Σ.
Proof. unfold chans_of. by rewrite dom_senv_ren. Qed.

Lemma pfree_ren f Σ : pfree Σ → pfree (senv_ren f Σ).
Proof. unfold pfree. by rewrite dom_senv_ren. Qed.

Lemma sw_lt_facts W W' x y : (∀ g, sw_facts W g → sw_facts W' g) → W ⊢ₛ x ≺ y → W' ⊢ₛ x ≺ y.
Proof.
  intros H. apply tc_congruence with (f := id). intros a b [a' b' Hf|a'|a'];
    [apply ws_fact; by apply H|apply ws_po|apply ws_dpo].
Qed.

Lemma swf_sub W W' : (∀ x y, W ⊢ₛ x ≺ y → W' ⊢ₛ x ≺ y) → swf W' → swf W.
Proof. intros H [ρ Hρ]. exists ρ. intros x y Hxy. by apply Hρ, H. Qed.

Lemma sacyc_sub W W' : (∀ x y, W ⊢ₛ x ≺ y → W' ⊢ₛ x ≺ y) → sacyc W' → sacyc W.
Proof. intros H HW x Hx. exact (HW x (H x x Hx)). Qed.

Lemma wok_sub N W W' : (∀ x y, W ⊢ₛ x ≺ y → W' ⊢ₛ x ≺ y) → wok N W' → wok N W.
Proof. destruct N; [apply swf_sub|apply sacyc_sub]. Qed.

(** A world without facts joins any world at no cost. *)
Lemma wok_join_bare_r N A B : (∀ g, ¬ sw_facts B g) → wok N A → wok N (A ⊔ B).
Proof.
  intros HB. apply wok_sub. apply sw_lt_by. intros x y [H|H]; [by apply tc_once, ws_fact|by destruct (HB _ H)].
Qed.

Lemma wok_join_bare_l N A B : (∀ g, ¬ sw_facts A g) → wok N B → wok N (A ⊔ B).
Proof.
  intros HA. apply wok_sub. apply sw_lt_by. intros x y [H|H]; [by destruct (HA _ H)|by apply tc_once, ws_fact].
Qed.

(** ** Renaming private constants apart *)

Definition cb_id : cbij := CBij id id (λ _, eq_refl) (λ _, eq_refl).

(** A bijection that fixes I and moves the finite set P, disjoint from
    I, out of B. *)
Lemma cb_avoid (I P B : gset nat) : P ## I → ∃ π, (∀ a, a ∈ I → cb_f π a = a) ∧ (∀ a, a ∈ P → cb_f π a ∉ B).
Proof.
  revert I B. induction P as [|p P Hp IH] using set_ind_L; intros I B HPI.
  - exists cb_id. split; [done|set_solver].
  - set (d := fresh (I ∪ B ∪ {[p]})).
    assert (d ∉ I ∪ B ∪ {[p]}) as Hd by apply is_fresh.
    destruct (IH (I ∪ {[p]}) (B ∪ {[d]}) ltac:(set_solver)) as (π & HI & HP).
    exists (cb_comp (cb_swap p d) π). split.
    + intros a Ha. simpl. rewrite HI by set_solver. unfold cswap.
      rewrite !decide_False; [done|set_solver|set_solver].
    + intros a Ha. simpl. apply elem_of_union in Ha as [Ha|Ha].
      * apply elem_of_singleton in Ha as ->. rewrite HI by set_solver. unfold cswap.
        rewrite decide_True by done. set_solver.
      * pose proof (HP a Ha) as Hn. assert (cb_f π a ≠ p) as Hne.
        { intros E. rewrite <-(HI p) in E by set_solver. apply cb_f_inj in E as ->. done. }
        unfold cswap. rewrite !decide_False; [set_solver|set_solver|done].
Qed.

(** ** Renaming a derivation of the process judgment

    A bijection of constants renames a derivation exactly: the renamed
    derivation sits at the renamed world ([ptyped_ren]). *)

Theorem ptyped_ren π N η W Σ p T : ptyped N η W Σ p T →
  ptyped N η (sw_ren π W) (senv_ren (cb_f π) Σ) p (ty_ren (cb_f π) T).
Proof.
  induction 1 as [W Σ ΘB C0 t T c Hp HB HΣ Hpf HΣc Hd Htk Ht [Hw HW]
                 |W1 W2 Σ1 Σ2 ΣC C1 C2 E1 E2 T Hty1 IH1 Hty2 IH2 H12 H1C H2C HC HC1 HC2 Hts HS].
  - apply (p_term N η (sw_ren π W) _ (tenv_ren (cb_f π) ΘB) C0 t _ c).
    + by apply tfree_ren.
    + intros o. unfold tenv_ren. by rewrite dom_fmap_L.
    + by rewrite chans_of_ren.
    + by apply pfree_ren.
    + intros o e. unfold senv_ren. rewrite lookup_fmap. destruct (Σ !! o) as [e0|] eqn:E; [|done].
      intros [= <-]. simpl. rewrite scontr_ren. exact (HΣc o e0 E).
    + intros c' Hc'. destruct (Hd c' Hc') as (S & x & m & m' & Hm & HS & H1 & H2).
      exists (sty_ren (cb_f π) S), (pt_ren (cb_f π) x), m, m'. unfold tenv_ren. rewrite !lookup_fmap, H1, H2.
      simpl. rewrite scontr_ren. by rewrite <-dual_ren.
    + by rewrite dom_senv_ren.
    + pose proof (typed_ren π _ _ _ _ _ _ _ _ _ Ht) as H.
      rewrite tenv_ren_union, tenv_ofk_ren in H. unfold sf_ren in H. simpl in H. rewrite set_map_empty in H. exact H.
    + split; [by apply sworld_wf_ren|by apply wok_ren].
  - rewrite senv_ren_union in IH1, IH2 |- *. rewrite senv_dual_ren in IH2. simpl in IH2.
    rewrite sw_ren_join, <-(chans_of_ren (cb_f π) ΣC).
    apply p_connect; [exact IH1|exact IH2|by rewrite ?chans_of_ren..|by rewrite dom_senv_ren|].
    rewrite <-sw_ren_join. by apply wok_ren.
Qed.

(** A renaming that fixes the interface keeps the interface and the
    type. *)
Lemma ptyped_ren_fix π N η W Σ p T : (∀ a, a ∈ iface Σ T → cb_f π a = a) →
  ptyped N η W Σ p T → ptyped N η (sw_ren π W) Σ p T.
Proof.
  intros HI Hty. pose proof (ptyped_ren π _ _ _ _ _ _ Hty) as H.
  rewrite (senv_ren_fix (cb_f π) Σ), (ty_ren_fix (cb_f π) T) in H; [exact H| |];
    intros a Ha; apply HI; unfold iface; set_solver.
Qed.

(** ** Renaming two components apart

    One component renamed by a bijection that fixes its interface moves
    its private constants out of any finite set ([ptyped_side]). Two
    components renamed so share only constants of both interfaces
    ([ptyped_apart]). P-Connect has no premise that keeps private
    constants apart. When two components use one private constant for
    unrelated points, renaming one of them first gives a join with
    fewer facts. *)

Lemma ptyped_side N η W Σ p T (B : gset nat) : ptyped N η W Σ p T →
  ∃ π, (∀ a, a ∈ iface Σ T → cb_f π a = a) ∧ ptyped N η (sw_ren π W) Σ p T ∧
    ∀ a, a ∈ sw_consts (sw_ren π W) → a ∉ iface Σ T → a ∉ B.
Proof.
  intros Hty. set (I := iface Σ T).
  destruct (cb_avoid I (sw_consts W ∖ I) B ltac:(set_solver)) as (π & HI & HP).
  exists π. split_and!; [exact HI|by apply ptyped_ren_fix|].
  intros a. simpl. rewrite elem_of_map. intros (b & -> & Hb) Ha.
  destruct (decide (b ∈ I)) as [HbI|HbI]; [rewrite HI in Ha by done; done|]. apply HP. set_solver.
Qed.

Theorem ptyped_apart N η W1 W2 Σ1 Σ2 p1 p2 T1 T2 :
  ptyped N η W1 Σ1 p1 T1 → ptyped N η W2 Σ2 p2 T2 →
  ∃ π1 π2, (∀ a, a ∈ iface Σ1 T1 → cb_f π1 a = a) ∧ (∀ a, a ∈ iface Σ2 T2 → cb_f π2 a = a) ∧
    ptyped N η (sw_ren π1 W1) Σ1 p1 T1 ∧ ptyped N η (sw_ren π2 W2) Σ2 p2 T2 ∧
    sw_consts (sw_ren π1 W1) ∩ sw_consts (sw_ren π2 W2) ⊆ iface Σ1 T1 ∩ iface Σ2 T2.
Proof.
  intros H1 H2.
  destruct (ptyped_side _ _ _ _ _ _ (iface Σ2 T2) H1) as (π1 & HI1 & H1' & Hav1).
  destruct (ptyped_side _ _ _ _ _ _ (sw_consts (sw_ren π1 W1) ∪ iface Σ1 T1) H2) as (π2 & HI2 & H2' & Hav2).
  exists π1, π2. split_and!; [done..|]. intros a. rewrite !elem_of_intersection. intros [Ha1 Ha2].
  destruct (decide (a ∈ iface Σ2 T2)) as [Hb|Hb]; [|destruct (Hav2 a Ha2 Hb); set_solver].
  destruct (decide (a ∈ iface Σ1 T1)) as [Hc|Hc]; [done|by destruct (Hav1 a Ha1 Hc)].
Qed.
