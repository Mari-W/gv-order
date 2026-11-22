(** * Hiding (decision of 2026-11-22, repair (b) of the overlap of P-Connect)

    The world of a process judgment lives on the constants of its
    interface ([ptyped], static/Typing.v). This file proves hiding
    sound by a translation into the judgment with whole worlds
    ([fptyped]), whose semantics static/FundamentalProc.v and
    soup/LFTyped.v give.

      swrestrict_iff  : W|S orders the points with roots in S exactly as
                        W does, through private constants too
      typed_ren       : a bijection of constants renames a derivation of
                        the term judgment
      fptyped_ren     : and of the full process judgment
      ptyped_full     : Σ ⊢_W p : T gives a full derivation at some world
                        W' with W'|iface Σ T inside W
      fptyped_ptyped  : a full derivation gives a hidden one

    P-Connect of [ptyped] compares the two interface worlds. In the
    translation the two components may share private constants, so the
    first is renamed to keep its private constants off the interface of
    the second ([cb_avoid]), and the second to keep its private
    constants off the whole world of the first. Then the two worlds
    share only interface constants of both, at which they order as
    their interface worlds do, and the full P-Connect applies
    ([connect_hidden]). The order the join derives between interface
    points is the order of the join of the interface worlds
    ([join_vis]), because a chain of the join changes sides only at
    shared constants. *)

From GV Require Export static.Typing.

(** ** The restriction keeps the derived order *)

Lemma swrestrict_iff W S x y :
  croot_in (sw_consts W ∩ S) x → croot_in (sw_consts W ∩ S) y →
  swrestrict W S ⊢ₛ x ≺ y ↔ W ⊢ₛ x ≺ y.
Proof.
  intros Hx Hy. split; [apply swrestrict_lt|]. intros H. by apply sw_lt_fact.
Qed.

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

(** ** Renaming a full process derivation *)

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

Lemma swshared_ren π W1 W2 : swshared (sw_ren π W1) (sw_ren π W2) = set_map (cb_f π) (swshared W1 W2).
Proof.
  apply set_eq. intros a. unfold swshared. simpl. rewrite elem_of_intersection, !elem_of_map. split.
  - intros [(b & -> & Hb) (b' & E & Hb')]. apply cb_f_inj in E as <-. exists b. set_solver.
  - intros (b & -> & Hb). split; exists b; set_solver.
Qed.

Lemma set_map_inter π (A B : gset nat) : set_map (C:=gset nat) (D:=gset nat) (cb_f π) A ∩ set_map (C:=gset nat) (D:=gset nat) (cb_f π) B ⊆ set_map (C:=gset nat) (D:=gset nat) (cb_f π) (A ∩ B).
Proof.
  intros a. rewrite elem_of_intersection, !elem_of_map. intros [(b & -> & Hb) (b' & E & Hb')].
  apply cb_f_inj in E as <-. exists b. set_solver.
Qed.

Lemma croot_in_mono S S' x : S ⊆ S' → croot_in S x → croot_in S' x.
Proof. intros HS (a & Ha & Hin). exists a. split; [done|]. by apply HS. Qed.

(** The restriction of a renamed world is the renamed restriction. *)
Lemma swrestrict_ren_facts π W S g :
  sw_facts (swrestrict (sw_ren π W) (set_map (cb_f π) S)) g → sw_facts (sw_ren π (swrestrict W S)) g.
Proof.
  destruct g as [x y]. simpl. intros (H & Hx & Hy). split_and!.
  - by apply sw_lt_ren_inv.
  - apply (croot_in_ren_inv π). eapply croot_in_mono; [apply set_map_inter|exact Hx].
  - apply (croot_in_ren_inv π). eapply croot_in_mono; [apply set_map_inter|exact Hy].
Qed.

Theorem fptyped_ren π N W Σ p T :
  fptyped N W Σ p T → fptyped N (sw_ren π W) (senv_ren (cb_f π) Σ) p (ty_ren (cb_f π) T).
Proof.
  induction 1 as [W Σ ΘB C0 t T c Hp HB HΣ Hpf HΣc Hd Ht [Hw HW]
                 |W1 W2 Σ1 Σ2 ΣC C1 C2 E1 E2 T _ IH1 _ IH2 H12 H1C H2C HC HC1 HC2 HS].
  - apply (fp_term N _ _ (tenv_ren (cb_f π) ΘB) C0 t _ c).
    + by apply tfree_ren.
    + intros o. unfold tenv_ren. by rewrite dom_fmap_L.
    + by rewrite chans_of_ren.
    + by apply pfree_ren.
    + intros o e. unfold senv_ren. rewrite lookup_fmap. destruct (Σ !! o) as [e0|] eqn:E; [|done].
      intros [= <-]. simpl. rewrite scontr_ren. exact (HΣc o e0 E).
    + intros c' Hc'. destruct (Hd c' Hc') as (S & x & m & m' & Hm & HS & H1 & H2).
      exists (sty_ren (cb_f π) S), (pt_ren (cb_f π) x), m, m'. unfold tenv_ren. rewrite !lookup_fmap, H1, H2.
      simpl. rewrite scontr_ren. by rewrite <-dual_ren.
    + pose proof (typed_ren π _ _ _ _ _ _ _ _ _ Ht) as H.
      rewrite tenv_ren_union, tenv_of_ren in H. unfold sf_ren in H. simpl in H. rewrite set_map_empty in H. exact H.
    + split; [by apply sworld_wf_ren|by apply wok_ren].
  - rewrite senv_ren_union in IH1, IH2 |- *. rewrite senv_dual_ren in IH2. simpl in IH2.
    rewrite sw_ren_join, <-(chans_of_ren (cb_f π) ΣC).
    apply fp_connect; [exact IH1|exact IH2|by rewrite !chans_of_ren|by rewrite !chans_of_ren|by rewrite !chans_of_ren
      |done|by rewrite !chans_of_ren|by rewrite !chans_of_ren|].
    rewrite swshared_ren. apply (wok_sub N _ (sw_ren π (swrestrict W1 (swshared W1 W2) ⊔ swrestrict W2 (swshared W1 W2)))).
    + intros x y. apply sw_lt_facts. intros g [Hg|Hg]; [left|right]; by apply swrestrict_ren_facts.
    + by apply wok_ren.
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

(** ** Hiding a world on an interface *)

(** W' hides to W on I: the constants of W' in I are constants of W,
    and every fact W' derives between points with roots in I holds in
    W. *)
Definition hides (W' : sworld) (I : gset nat) (W : sworld) : Prop :=
  sw_consts W' ∩ I ⊆ sw_consts W ∧
  ∀ x y, croot_in I x → croot_in I y → W' ⊢ₛ x ≺ y → W ⊢ₛ x ≺ y.

Lemma croot_in_union_l S S' x : croot_in S x → croot_in (S ∪ S') x.
Proof. apply croot_in_mono. set_solver. Qed.
Lemma croot_in_union_r S S' x : croot_in S' x → croot_in (S ∪ S') x.
Proof. apply croot_in_mono. set_solver. Qed.

Lemma croot_in_same S S' x : croot_in S x → croot_in S' x → croot_in (S ∩ S') x.
Proof.
  intros (a & Ha & HS) (b & Hb & HS'). exists a. split; [done|]. rewrite Ha in Hb. injection Hb as <-. set_solver.
Qed.

(** A world hides to its restriction. *)
Lemma hides_restrict W I : sworld_wf W → hides W I (swrestrict W I).
Proof.
  intros Hwf. split; [simpl; set_solver|]. intros x y Hx Hy H.
  destruct (lt_zone W x y Hwf H) as [Hp|[Zx Zy]]; [by apply po_slt|].
  apply sw_lt_fact. simpl. split_and!; [done|by apply croot_in_same|by apply croot_in_same].
Qed.

(** ** The order of a join between visible points

    A chain of W1 ⊔ W2 changes sides only at a point both worlds own,
    which is visible on both sides. So every fact the join derives
    between visible points is a fact of V, when V holds every fact each
    side derives between its own visible points. *)
Section join_vis.
  Context (W1 W2 V : sworld) (I1 I2 : gset nat).
  Context (Hw1 : sworld_wf W1) (Hw2 : sworld_wf W2).
  Context (H1 : ∀ x y, croot_in I1 x → croot_in I1 y → W1 ⊢ₛ x ≺ y → V ⊢ₛ x ≺ y).
  Context (H2 : ∀ x y, croot_in I2 x → croot_in I2 y → W2 ⊢ₛ x ≺ y → V ⊢ₛ x ≺ y).
  Context (A1 : ∀ a, a ∈ sw_consts W1 → a ∈ I2 → a ∈ I1).
  Context (A2 : ∀ a, a ∈ sw_consts W2 → a ∈ I1 → a ∈ I2).
  Context (S12 : ∀ a, a ∈ sw_consts W1 → a ∈ sw_consts W2 → a ∈ I1 ∧ a ∈ I2).

  Local Abbreviation vis := (croot_in (I1 ∪ I2)).

  Local Lemma vis_side (W : sworld) (I : gset nat) x :
    (∀ a, a ∈ sw_consts W → a ∈ I1 ∪ I2 → a ∈ I) → zone W x → vis x → croot_in I x.
  Proof.
    intros HA (a & Ha & HaW) (b & Hb & HbI). rewrite Ha in Hb. injection Hb as <-. exists a. split; [done|].
    by apply HA.
  Qed.

  Local Lemma side1 x y : vis x → vis y → W1 ⊢ₛ x ≺ y → V ⊢ₛ x ≺ y.
  Proof.
    intros Hx Hy H. destruct (lt_zone W1 x y Hw1 H) as [Hp|[Zx Zy]]; [by apply po_slt|].
    assert (∀ a, a ∈ sw_consts W1 → a ∈ I1 ∪ I2 → a ∈ I1) as HA
      by (intros a Ha Hu; apply elem_of_union in Hu as [?|?]; auto).
    apply H1; [by apply (vis_side W1)|by apply (vis_side W1)|done].
  Qed.

  Local Lemma side2 x y : vis x → vis y → W2 ⊢ₛ x ≺ y → V ⊢ₛ x ≺ y.
  Proof.
    intros Hx Hy H. destruct (lt_zone W2 x y Hw2 H) as [Hp|[Zx Zy]]; [by apply po_slt|].
    assert (∀ a, a ∈ sw_consts W2 → a ∈ I1 ∪ I2 → a ∈ I2) as HA
      by (intros a Ha Hu; apply elem_of_union in Hu as [?|?]; auto).
    apply H2; [by apply (vis_side W2)|by apply (vis_side W2)|done].
  Qed.

  Local Lemma shared_vis z : zone W1 z → zone W2 z → vis z.
  Proof.
    intros (a & Ha & Ha1) (b & Hb & Hb2). rewrite Ha in Hb. injection Hb as <-.
    destruct (S12 a Ha1 Hb2). exists a. split; [done|set_solver].
  Qed.

  Local Abbreviation Q y w := (∀ v, vis v → W1 ⊢ₛ v ≺ w ∨ W2 ⊢ₛ v ≺ w → V ⊢ₛ v ≺ y).

  (** A step of one side from z to w, entered from v by the other side. *)
  Local Lemma cross (A B : sworld) y v z w :
    sworld_wf A → sworld_wf B →
    (∀ x y, vis x → vis y → A ⊢ₛ x ≺ y → V ⊢ₛ x ≺ y) →
    (∀ z, zone A z → zone B z → vis z) →
    ((B = W1 ∨ B = W2) ∧ (A = W1 ∨ A = W2)) →
    Q y w → vis v → A ⊢ₛ v ≺ z → swstep B z w → V ⊢ₛ v ≺ y.
  Proof.
    intros HA HB HsA Hsh HAB HQ Hv Hvz Hs.
    assert (∀ u, B ⊢ₛ u ≺ w → W1 ⊢ₛ u ≺ w ∨ W2 ⊢ₛ u ≺ w) as HBw by (destruct HAB as [[->| ->] _]; auto).
    assert (∀ u, A ⊢ₛ u ≺ w → W1 ⊢ₛ u ≺ w ∨ W2 ⊢ₛ u ≺ w) as HAw by (destruct HAB as [_ [->| ->]]; auto).
    destruct (lt_zone A v z HA Hvz) as [Hp|[_ Za]].
    - apply HQ; [done|]. apply HBw. eapply sw_lt_trans; [by apply (po_slt B)|by apply tc_once].
    - destruct (lt_zone B z w HB (tc_once _ _ _ Hs)) as [Hp|[Zb _]].
      + apply HQ; [done|]. apply HAw. eapply sw_lt_trans; [exact Hvz|by apply po_slt].
      + pose proof (Hsh z Za Zb) as Hz. eapply sw_lt_trans; [by apply HsA|].
        apply HQ; [done|]. apply HBw. by apply tc_once.
  Qed.

  Lemma join_vis x y : vis x → vis y → W1 ⊔ W2 ⊢ₛ x ≺ y → V ⊢ₛ x ≺ y.
  Proof.
    intros Hx Hy H.
    assert (Q y y) as Qy by (intros v Hv [Hvy|Hvy]; [by apply side1|by apply side2]).
    assert (∀ z w, swstep (W1 ⊔ W2) z w → Q y w → Q y z ∧ (vis z → V ⊢ₛ z ≺ y)) as Hstep.
    { intros z w Hs HQ. apply swstep_join_inv in Hs as [Hs|Hs]; split.
      - intros v Hv [Hvz|Hvz].
        + apply HQ; [done|]. left. eapply sw_lt_trans; [exact Hvz|by apply tc_once].
        + eapply (cross W2 W1); [done|done|apply side2|intros u Zu1 Zu2; by apply shared_vis|by split; [left|right]
            |exact HQ|done|exact Hvz|exact Hs].
      - intros Hz. apply HQ; [done|]. left. by apply tc_once.
      - intros v Hv [Hvz|Hvz].
        + eapply (cross W1 W2); [done|done|apply side1|intros u Zu1 Zu2; by apply shared_vis|by split; [right|left]
            |exact HQ|done|exact Hvz|exact Hs].
        + apply HQ; [done|]. right. eapply sw_lt_trans; [exact Hvz|by apply tc_once].
      - intros Hz. apply HQ; [done|]. right. by apply tc_once. }
    assert (∀ z, W1 ⊔ W2 ⊢ₛ z ≺ y → Q y z ∧ (vis z → V ⊢ₛ z ≺ y)) as Hall.
    { intros z Hz. induction Hz as [z w Hs|z u w Hs _ IH]; [exact (Hstep z w Hs Qy)|exact (Hstep z u Hs (proj1 (IH Hy H Qy Hstep)))]. }
    by apply Hall.
  Qed.
End join_vis.

(** ** From hidden derivations to full ones *)

Lemma join_sub A A' B B' x y :
  (∀ x y, A ⊢ₛ x ≺ y → A' ⊢ₛ x ≺ y) → (∀ x y, B ⊢ₛ x ≺ y → B' ⊢ₛ x ≺ y) →
  A ⊔ B ⊢ₛ x ≺ y → A' ⊔ B' ⊢ₛ x ≺ y.
Proof.
  intros HA HB. assert (∀ x y, swstep (A ⊔ B) x y → A' ⊔ B' ⊢ₛ x ≺ y) as Hs.
  { intros a b Hs. apply swstep_join_inv in Hs as [Hs|Hs]; apply tc_once in Hs.
    - eapply sw_lt_mono; [apply swext_join_l|]. by apply HA.
    - eapply sw_lt_mono; [apply swext_join_r|]. by apply HB. }
  induction 1 as [x y H|x z y H _ IH]; [by apply Hs|]. eapply sw_lt_trans; [by apply Hs|done].
Qed.

Lemma pt_ren_fix_croot π I x : (∀ a, a ∈ I → cb_f π a = a) → croot_in I x → pt_ren (cb_g π) x = x.
Proof.
  intros HI (a & Ha & HaI). apply pt_ren_fix. intros b Hb. rewrite (pt_consts_root x a Ha) in Hb.
  apply elem_of_singleton in Hb as ->. rewrite <-(HI a HaI) at 1. apply cb_gf.
Qed.

(** One component renamed: its private constants leave B, its interface
    and its hidden world stay. *)
Lemma rename_side N W' Σ p T W (B : gset nat) :
  fptyped N W' Σ p T → hides W' (iface Σ T) W →
  ∃ W'', fptyped N W'' Σ p T ∧ hides W'' (iface Σ T) W ∧
    ∀ a, a ∈ sw_consts W'' → a ∉ iface Σ T → a ∉ B.
Proof.
  intros Hty [Hc Ho]. set (I := iface Σ T).
  destruct (cb_avoid I (sw_consts W' ∖ I) B ltac:(set_solver)) as (π & HI & HP).
  assert (∀ b, cb_f π b ∈ I → b ∈ I) as Hback.
  { intros b Hb. destruct (decide (b ∈ I)) as [|Hn]; [done|]. exfalso.
    assert (cb_f π (cb_f π b) = cb_f π b) as E by (by apply HI). apply cb_f_inj in E. rewrite E in Hb. done. }
  exists (sw_ren π W'). split_and!.
  - pose proof (fptyped_ren π _ _ _ _ _ Hty) as H.
    rewrite senv_ren_fix, ty_ren_fix in H; [exact H| |]; intros a Ha; apply HI; unfold I, iface; set_solver.
  - split.
    + intros a. simpl. rewrite elem_of_intersection, elem_of_map. intros [(b & -> & Hb) Ha].
      pose proof (Hback b Ha) as HbI. rewrite HI in Ha |- * by done. apply Hc. set_solver.
    + intros x y Hx Hy H. apply sw_lt_ren_inv in H. rewrite !(pt_ren_fix_croot π I) in H by done. by apply Ho.
  - intros a. simpl. rewrite elem_of_map. intros (b & -> & Hb) Ha.
    destruct (decide (b ∈ I)) as [HbI|HbI]; [rewrite HI in Ha by done; done|]. apply HP. set_solver.
Qed.

Lemma iface_connect Σ1 Σ2 ΣC T :
  iface (Σ1 ∪ Σ2) T ⊆ iface (Σ1 ∪ ΣC) T ∪ iface (Σ2 ∪ senv_dual ΣC) TUnit.
Proof.
  unfold iface. pose proof (senv_consts_union Σ1 Σ2). pose proof (senv_consts_union_l Σ1 ΣC).
  pose proof (senv_consts_union_l Σ2 (senv_dual ΣC)). set_solver.
Qed.

(** Two full worlds whose private constants are apart compose when
    their hidden worlds do. V1 keeps its private constants off I2, V2
    off V1 and I1. Then V1 and V2 share only constants of I1 ∩ I2, at
    which they order as W1 and W2 do, so the restrictions to the shared
    constants are acyclic together (well-founded at a finite N), and
    the join hides to the hidden join on every I ⊆ I1 ∪ I2. *)
Lemma connect_hidden N V1 V2 W1 W2 (I1 I2 I : gset nat) :
  sworld_wf V1 → sworld_wf V2 →
  hides V1 I1 W1 → hides V2 I2 W2 →
  (∀ a, a ∈ sw_consts V1 → a ∉ I1 → a ∉ I2) →
  (∀ a, a ∈ sw_consts V2 → a ∉ I2 → a ∉ sw_consts V1 ∪ I1) →
  I ⊆ I1 ∪ I2 → wok N (W1 ⊔ W2) →
  wok N (swrestrict V1 (swshared V1 V2) ⊔ swrestrict V2 (swshared V1 V2)) ∧
  hides (V1 ⊔ V2) I (swrestrict (W1 ⊔ W2) I).
Proof.
  intros Hw1 Hw2 [Hc1 Ho1] [Hc2 Ho2] Hav1 Hav2 HI HS.
  assert (∀ a, a ∈ sw_consts V1 → a ∈ sw_consts V2 → a ∈ I1 ∧ a ∈ I2) as S12.
  { intros a Ha1 Ha2. destruct (decide (a ∈ I2)) as [Ha|Ha]; [|by destruct (Hav2 a Ha2 Ha); set_solver].
    destruct (decide (a ∈ I1)) as [Hb|Hb]; [done|by destruct (Hav1 a Ha1 Hb)]. }
  assert (∀ a, a ∈ sw_consts V1 → a ∈ I2 → a ∈ I1) as A1.
  { intros a Ha Hi. destruct (decide (a ∈ I1)) as [|Hn]; [done|by destruct (Hav1 a Ha Hn)]. }
  assert (∀ a, a ∈ sw_consts V2 → a ∈ I1 → a ∈ I2) as A2.
  { intros a Ha Hi. destruct (decide (a ∈ I2)) as [|Hn]; [done|]. destruct (Hav2 a Ha Hn). set_solver. }
  assert (∀ x y, croot_in I1 x → croot_in I1 y → V1 ⊢ₛ x ≺ y → W1 ⊔ W2 ⊢ₛ x ≺ y) as Hj1.
  { intros x y Hx Hy H. eapply sw_lt_mono; [apply swext_join_l|]. by apply Ho1. }
  assert (∀ x y, croot_in I2 x → croot_in I2 y → V2 ⊢ₛ x ≺ y → W1 ⊔ W2 ⊢ₛ x ≺ y) as Hj2.
  { intros x y Hx Hy H. eapply sw_lt_mono; [apply swext_join_r|]. by apply Ho2. }
  assert (sw_consts V1 ∩ swshared V1 V2 ⊆ I1) as HS1.
  { intros a. unfold swshared. rewrite !elem_of_intersection. intros (Ha & Ha' & Hb). by apply S12. }
  assert (sw_consts V2 ∩ swshared V1 V2 ⊆ I2) as HS2.
  { intros a. unfold swshared. rewrite !elem_of_intersection. intros (Ha & Ha' & Hb). by apply S12. }
  assert (sw_consts (V1 ⊔ V2) ∩ I ⊆ sw_consts (swrestrict (W1 ⊔ W2) I)) as Hcons.
  { intros a. simpl. rewrite !elem_of_intersection, !elem_of_union. intros [[Ha|Ha] HaI].
    - assert (a ∈ I1) as Ha1.
      { destruct (decide (a ∈ I1)) as [|Hn]; [done|]. pose proof (Hav1 a Ha Hn). set_solver. }
      split; [left; apply Hc1; set_solver|done].
    - assert (a ∈ I2) as Ha2.
      { destruct (decide (a ∈ I2)) as [|Hn]; [done|]. pose proof (Hav2 a Ha Hn). set_solver. }
      split; [right; apply Hc2; set_solver|done]. }
  split.
  - apply (wok_sub N _ (W1 ⊔ W2)); [|done].
    assert (∀ x y, swstep (swrestrict V1 (swshared V1 V2) ⊔ swrestrict V2 (swshared V1 V2)) x y →
              W1 ⊔ W2 ⊢ₛ x ≺ y) as Hs.
    { intros a b Hs. apply swstep_join_inv in Hs as [Hs|Hs];
        (destruct Hs as [a b (H & Ha & Hb)|a|a]; [|apply sw_lt_po|apply sw_lt_dpo]).
      - apply Hj1; [|by eapply croot_in_mono..|done]. by eapply croot_in_mono.
      - apply Hj2; [|by eapply croot_in_mono..|done]. by eapply croot_in_mono. }
    intros x y. induction 1 as [x y H|x z y H _ IH]; [by apply Hs|]. eapply sw_lt_trans; [by apply Hs|done].
  - split; [exact Hcons|]. intros x y Hx Hy H.
    assert (W1 ⊔ W2 ⊢ₛ x ≺ y) as HJ.
    { apply (join_vis V1 V2 (W1 ⊔ W2) I1 I2); try done; by eapply croot_in_mono. }
    destruct (lt_zone (V1 ⊔ V2) x y (swjoin_wf _ _ Hw1 Hw2) H) as [Hp|[Zx Zy]]; [by apply po_slt|].
    apply sw_lt_fact. simpl. split_and!; [done| |].
    + eapply croot_in_mono; [|apply (croot_in_same _ _ _ Zx Hx)]. exact Hcons.
    + eapply croot_in_mono; [|apply (croot_in_same _ _ _ Zy Hy)]. exact Hcons.
Qed.

(** Every hidden derivation is the hiding of a full derivation. *)
Theorem ptyped_full N W Σ p T : ptyped N W Σ p T → ∃ W', fptyped N W' Σ p T ∧ hides W' (iface Σ T) W.
Proof.
  induction 1 as [W Σ ΘB C0 t T c Hp HB HΣ Hpf HΣc Hd Ht HW
                 |W1 W2 Σ1 Σ2 ΣC C1 C2 E1 E2 T _ IH1 _ IH2 H12 H1C H2C HC HC1 HC2 HS].
  - exists W. split; [by eapply fp_term|]. apply hides_restrict, HW.
  - destruct IH1 as (W1' & Hty1 & Hh1), IH2 as (W2' & Hty2 & Hh2).
    destruct (rename_side _ _ _ _ _ _ (iface (Σ2 ∪ senv_dual ΣC) TUnit) Hty1 Hh1) as (V1 & Hv1 & Hh1' & Hav1).
    destruct (rename_side _ _ _ _ _ _ (sw_consts V1 ∪ iface (Σ1 ∪ ΣC) T) Hty2 Hh2) as (V2 & Hv2 & Hh2' & Hav2).
    destruct (connect_hidden N V1 V2 W1 W2 _ _ (iface (Σ1 ∪ Σ2) T) (proj1 (fptyped_wf _ _ _ _ _ Hv1))
                (proj1 (fptyped_wf _ _ _ _ _ Hv2)) Hh1' Hh2' Hav1 Hav2 (iface_connect _ _ _ _) HS) as [HR Hh].
    exists (V1 ⊔ V2). split; [by apply fp_connect|exact Hh].
Qed.

(** ** From full derivations to hidden ones

    Hiding loses no program: every full derivation hides to one whose
    world derives only facts of the full world. *)
Theorem fptyped_ptyped N W Σ p T :
  fptyped N W Σ p T → ∃ Wi, ptyped N Wi Σ p T ∧ ∀ x y, Wi ⊢ₛ x ≺ y → W ⊢ₛ x ≺ y.
Proof.
  intros Hty. pose proof Hty as Hty'. revert Hty'.
  induction Hty as [W Σ ΘB C0 t T c Hp HB HΣ Hpf HΣc Hd Ht HW
                   |W1 W2 Σ1 Σ2 ΣC C1 C2 E1 E2 T Hty1 IH1 Hty2 IH2 H12 H1C H2C HC HC1 HC2 HS];
    intros Hfull.
  - exists (swrestrict W (iface Σ T)). split; [by eapply p_term|]. intros x y. apply swrestrict_lt.
  - destruct (IH1 Hty1) as (Wi1 & Hi1 & Hs1), (IH2 Hty2) as (Wi2 & Hi2 & Hs2).
    assert (wok N (W1 ⊔ W2)) as HJ by apply (fptyped_wf _ _ _ _ _ Hfull).
    exists (swrestrict (Wi1 ⊔ Wi2) (iface (Σ1 ∪ Σ2) T)). split.
    + eapply p_connect; try done. apply (wok_sub N _ (W1 ⊔ W2)); [|done]. intros x y. by apply join_sub.
    + intros x y H. apply swrestrict_lt in H. by eapply join_sub.
Qed.
