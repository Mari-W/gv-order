(** * Rank, the well-founded order of a world (lock-freedom plan §19.5, T3)

    Lock freedom needs the order ≺ of the world to be well founded
    ([wf_world]), beside the cost judgment (static/CostTyping.v) and the
    guard (liveness/GuardRules.v). Rank is a property of the world and
    reads no code. A closed program creates its channels at its top
    level, at the constants of its hypotheses Ψ ([created]), and its run
    starts in [cworld Ψ], which supports these constants and has exactly
    the facts of Ψ closed under program order ([cworld_hold]).

    A rank into a well-founded order that rises along program order,
    along x ≺ x̄+1 and along the facts makes the world well founded
    ([wgen_rank_wf], [cworld_rank_wf]). A descending chain refutes it
    ([chain_not_wf]). The examples' worlds are well founded ([fw_wf] to
    [sched_wf]). Kobayashi's forwarder and the spawner chain C1 of plan
    §10.1 are not ([kob_cworld_not_wf], [c1_rank_fails]). *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Import static.Fundamental examples.ExampleTools examples.LitTools.
From LRGV Require examples.Sync examples.Scheduler examples.Forwarder examples.TailCall
  examples.KobForwarder examples.cfst.CfstTools examples.cfst.CfstScheduler
  examples.ReceivedChain examples.GrowRing examples.ABP.

Definition wf_world (W : world) : Prop := well_founded (w_lt W).

(** ** Rank, general facts *)

(** Rank from a rank into a well-founded order. A world generated
    without ≡ facts is well founded when the rank rises along program
    order, along x ≺ x̄+1 and along its ≺ facts. The facts may form
    infinite ascending chains. *)
Lemma wgen_rank_wf {A} (R : A → A → Prop) N (E L : prel) (r : point → A) :
  well_founded R → (∀ a b c, R a b → R b c → R a c) →
  (∀ x y, ¬ E x y) → (∀ x y, L x y → R (r x) (r y)) →
  (∀ x, R (r x) (r (pt_shift 1 x))) → (∀ x, R (r x) (r (pt_shift 1 (pt_dual x)))) →
  wf_world (wgen N E L).
Proof.
  intros Hwf Htr HE HL Hs Hd.
  assert (∀ x y, geq E x y → x = y) as Hq.
  { induction 1 as [x y H| | | | | |]; [by destruct (HE x y H)|..]; subst; done. }
  assert (∀ x y, glt E L x y → R (r x) (r y)) as Hlt.
  { induction 1 as [x y H|x|x x' y y' Hx _ IH Hy|x y z _ IH1 _ IH2|x].
    - by apply HL.
    - apply Hs.
    - apply Hq in Hx, Hy. by subst.
    - by eapply Htr.
    - apply Hd. }
  assert (∀ a, Acc R a → ∀ x, r x = a → Acc (glt E L) x) as H.
  { induction 1 as [a _ IH]. intros x <-. constructor. intros y Hy. exact (IH (r y) (Hlt y x Hy) y eq_refl). }
  intros x. exact (H (r x) (Hwf (r x)) x eq_refl).
Qed.

Lemma lexlt_wf : well_founded lexlt.
Proof.
  assert (∀ a b, Acc lexlt (a, b)) as H.
  { intros a. induction a as [a IHa] using (well_founded_induction Wf_nat.lt_wf).
    intros b. induction b as [b IHb] using (well_founded_induction Wf_nat.lt_wf).
    constructor. intros [a' b'] [Hlt|[Heq Hlt]]; cbn in *; [by apply IHa|subst; by apply IHb]. }
  intros [a b]. apply H.
Qed.

(** A descending chain refutes Rank. *)
Lemma chain_not_wf W (f : nat → point) : (∀ n, w_lt W (f (S n)) (f n)) → ¬ wf_world W.
Proof.
  intros Hf Hwf.
  assert (∀ x, Acc (w_lt W) x → ∀ n, f n = x → False) as H.
  { induction 1 as [x _ IH]. intros n <-. exact (IH (f (S n)) (Hf n) (S n) eq_refl). }
  exact (H (f 0) (Hwf (f 0)) 0 eq_refl).
Qed.

(** ** Rank under the constant world (sharp edges 172, 173)

    A closed program creates its channels at its top level, at the
    constants of its hypotheses Ψ ([created]). Its run starts in
    [cworld Ψ], which supports these constants and has exactly the
    facts of Ψ, closed under program order. The creation facts are
    facts of this world, and Rank asks that its ≺ be well founded. A
    descending chain in a creation constraint, as in Kobayashi's
    forwarder, refutes it ([kob_cworld_not_wf]). Under syntactic points
    the hypotheses name constants already, so no instantiation sits
    between Ψ and the world. *)

(** The ≺ facts that the hypotheses Ψ state at their instances. *)
Definition hyps_lt (Ψ : hyps) : prel := λ x y, hyp_fact Ψ (FLt x y).

(** The root names of the instances of Ψ. *)
Definition hroots (Ψ : hyps) : gset pname := list_to_set (Ψ ≫= (λ g, pt_root <$> g.2)).

Definition cworld (Ψ : hyps) : world := wgen (hroots Ψ) (λ _ _, False) (hyps_lt Ψ).

Lemma hroots_elem Ψ p : p ∈ hroots Ψ ↔ ∃ C xs y, (C, xs) ∈ Ψ ∧ y ∈ xs ∧ p = pt_root y.
Proof.
  unfold hroots. rewrite elem_of_list_to_set, list_elem_of_bind. split.
  - intros ([C xs] & Hp & Hin). apply list_elem_of_fmap in Hp as (y & -> & Hy). by exists C, xs, y.
  - intros (C & xs & y & Hin & Hy & ->). exists (C, xs). split; [|done]. apply list_elem_of_fmap. by exists y.
Qed.

(** The instances of created hypotheses are constants. *)
Lemma created_consts W Ψ : created W Ψ → ∀ C xs y, (C, xs) ∈ Ψ → y ∈ xs → ∃ a, y = pconst a.
Proof.
  induction 1 as [|Ψ C a HΨ IH _ _ _]; intros C' xs y Hin Hy; [by apply elem_of_nil in Hin|].
  apply elem_of_app in Hin as [Hin|Hin]; [by eapply IH|].
  apply list_elem_of_singleton in Hin. injection Hin as -> ->. apply list_elem_of_singleton in Hy as ->.
  by exists a.
Qed.

(** A world contains the world its facts generate. *)
Lemma glt_into (W : world) (L : prel) :
  world_wf W → (∀ x y, L x y → w_lt W x y) → ∀ x y, glt (λ _ _, False) L x y → w_lt W x y.
Proof.
  intros HW HL.
  assert (∀ x y, geq (λ _ _ : point, False) x y → x = y) as Hq.
  { induction 1 as [x y []| | | | | |]; subst; done. }
  induction 1 as [x y H|x|x x' y y' Hx _ IH Hy|x y z _ IH1 _ IH2|x].
  - by apply HL.
  - apply (wf_lt_po _ HW).
  - apply Hq in Hx, Hy. by subst.
  - by eapply (wf_lt_trans _ HW).
  - apply (wf_lt_dpo _ HW).
Qed.

(** [cworld Ψ] is strict and realizes Ψ. *)
Lemma cworld_hold Ψ : created (Wpo []) Ψ →
  strict (cworld Ψ) ∧ hyps_hold (w_eq (cworld Ψ)) (w_lt (cworld Ψ)) (pt_known (cworld Ψ)) Ψ.
Proof.
  intros HΨ. destruct (created_world_names (Wpo []) Ψ Wpo_nil_strict' HΨ) as (W1 & HW1 & Hh & Hkn).
  destruct (proj2 (proj2 (proj2 HW1))) as [HW1wf HW1irr].
  assert (∀ x y, hyps_lt Ψ x y → w_lt W1 x y) as HL.
  { intros x y (C & xs & Hin & g & Hg & E). destruct (Hh C xs Hin) as [Hb _].
    specialize (Hb g Hg). rewrite <-E in Hb. exact Hb. }
  assert (w_names W1 ⊆ hroots Ψ) as HN.
  { intros p Hp. destruct (wf_names_const _ HW1wf p Hp) as [a ->].
    destruct (Hkn (pconst a) Hp) as [Hk|(C & xs & y & Hin & Hy & E)].
    - unfold pt_known in Hk. rewrite Wpo_nil_names in Hk. set_solver.
    - apply hroots_elem. exists C, xs, y. split_and!; [done|done|]. by rewrite <-E. }
  pose proof (glt_into W1 _ HW1wf HL) as Hin.
  split; [split|].
  - apply wgen_wf.
    + intros p Hp. apply hroots_elem in Hp as (C & xs & y & HC & Hy & ->).
      destruct (created_consts _ _ HΨ C xs y HC Hy) as [a ->]. by exists a.
    + by intros ? ? [].
    + intros x y H. destruct (wf_lt_supp _ HW1wf x y (HL x y H)) as [Hp|[Hx Hy]]; [by left|].
      right. split; by apply HN.
  - intros x Hx. apply (HW1irr x). by apply Hin.
  - intros C xs Hc. split.
    + intros g Hg. destruct (fact_map (pt_inst (plist xs)) g) as [x y] eqn:E. cbn [fact_holds].
      apply glt_base. exists C, xs. split; [done|]. exists g. split; [done|]. by rewrite E.
    + destruct (Hh C xs Hc) as [_ Hk]. eapply Forall_impl; [exact Hk|]. intros x Hx.
      unfold pt_known in *. apply HN. exact Hx.
Qed.

(** The process of a closed program over Ψ is typed in every strict
    world that realizes Ψ. *)
Lemma world_ptyped W Ψ t T :
  strict W → hyps_hold (w_eq W) (w_lt W) (pt_known W) Ψ → prim T →
  styped ∅ Ψ [] (∅, None) t T → ptyped W ∅ (∅, {[+ t +]}) T.
Proof.
  intros HS Hh HT Ht. apply ptyped_closed; [done|].
  pose proof (typed_pinst W ∅ Ψ ∅ [] (∅, None) t T HS (styped_typed W _ _ _ _ _ _ Ht) pvar []) as H.
  rewrite tenv_pinst_pvar, lenv_pinst_pvar, sf_pinst_pvar, pinst_ty_pvar in H.
  unfold fhyps_pinst in H. rewrite fmap_empty in H. apply H; [|apply tenv_pol_pvar].
  rewrite hyps_inst_pvar.
  apply (hyps_hold_mono (w_eq W) _ (w_lt W) _ (pt_known W)); [| | |exact Hh].
  - intros ? ? ?. by apply se_w.
  - intros ? ? ?. by apply sl_w.
  - intros ? ?. by left.
Qed.

(** *** The facts of Ψ

    A hypothesis (C, [a]) whose constraint has constants as outer
    points states its facts at the constants. The variable 0 becomes a
    and the variable j + 1 the j-th outer point ([pt_open]). *)

Fixpoint pn_open (xs : list point) (p : pname) : pname :=
  match p with
  | NVar j => match xs !! j with Some z => pt_name z | None => NVar j end
  | NConst a => NConst a
  | NPayload q b i => NPayload (pn_open xs q) b i
  end.

Definition pt_open (xs : list point) (x : point) : point :=
  MkPt (pn_open xs (pt_name x)) (pt_pol x) (pt_off x).

Lemma pn_inst_open σ xs p :
  (∀ a, pn_root p = NVar a → ∃ c, xs !! a = Some (pconst c) ∧ σ a = pconst c) →
  pn_inst σ p = Pt (pn_open xs p) 0.
Proof.
  induction p as [a|a|q IH b i]; intros H; cbn [pn_inst pn_open].
  - done.
  - destruct (H a eq_refl) as (c & -> & ->). done.
  - rewrite IH by exact H. unfold pt_payload, pt_shift. done.
Qed.

Lemma pt_inst_open σ xs x :
  (∀ a, pt_root x = NVar a → ∃ c, xs !! a = Some (pconst c) ∧ σ a = pconst c) →
  pt_inst σ x = pt_open xs x.
Proof.
  intros H. destruct x as [p b o]. unfold pt_inst, pt_open. cbn [pt_name pt_pol pt_off].
  rewrite (pn_inst_open σ xs p H). destruct b; unfold pt_polar, pt_shift, pt_dual; done.
Qed.

Definition all_const (env : list point) : Prop := Forall (λ z, ∃ c, z = pconst c) env.

Lemma open_sub a env j :
  all_const env → j < S (length env) →
  ∃ c, (pconst a :: env) !! j = Some (pconst c) ∧
    (pt_inst (plist [pconst a]) ∘ pup 1 (plist env)) j = pconst c.
Proof.
  intros Henv Hj. destruct j as [|j].
  - exists a. split; [done|]. unfold compose, pup. rewrite decide_True by lia. done.
  - destruct (lookup_lt_is_Some_2 env j) as [z Hz]; [lia|].
    destruct (proj1 (Forall_lookup _ _) Henv j z Hz) as [c ->]. exists c. split; [done|].
    unfold compose, pup. rewrite decide_False by lia. cbn. unfold plist at 2. rewrite Nat.sub_0_r, Hz. done.
Qed.

Lemma hyps_lt_nil x y : ¬ hyps_lt [] x y.
Proof. intros (C & xs & Hin & _). by apply elem_of_nil in Hin. Qed.

Lemma hyps_lt_snoc Ψ env P a x y :
  all_const env → hyps_lt (Ψ ++ [(BCs env P, [pconst a])]) x y →
  hyps_lt Ψ x y ∨ ∃ x0 y0, P (FLt x0 y0) ∧ fact_scoped (S (length env)) (FLt x0 y0) ∧
    x = pt_open (pconst a :: env) x0 ∧ y = pt_open (pconst a :: env) y0.
Proof.
  intros Henv (C & xs & Hin & g & Hg & E). apply elem_of_app in Hin as [Hin|Hin].
  - left. exists C, xs. split; [done|]. by exists g.
  - right. apply list_elem_of_singleton in Hin. injection Hin as -> ->.
    destruct Hg as (f & Hf & Hs & ->). destruct f as [x0 y0]. cbn [bc_facts bc_env length] in Hf, Hs, E.
    cbn [fact_map] in E. injection E as -> ->. exists x0, y0. split_and!; [done|done| |];
      rewrite pt_inst_comp; apply pt_inst_open; intros j Hj; apply open_sub; [done| |done|];
      destruct Hs as [Hx Hy]; [exact (pn_vb_root _ _ _ Hx Hj)|exact (pn_vb_root _ _ _ Hy Hj)].
Qed.

Lemma hyps_lt_snoc_intro Ψ env P a x0 y0 :
  all_const env → P (FLt x0 y0) → fact_scoped (S (length env)) (FLt x0 y0) →
  hyps_lt (Ψ ++ [(BCs env P, [pconst a])]) (pt_open (pconst a :: env) x0) (pt_open (pconst a :: env) y0).
Proof.
  intros Henv Hf Hs. exists (BCs env P), [pconst a]. split; [apply elem_of_app; right; by left|].
  exists (FLt (pt_inst (pup 1 (plist env)) x0) (pt_inst (pup 1 (plist env)) y0)). split.
  - exists (FLt x0 y0). split_and!; [done|exact Hs|done].
  - cbn [fact_map]. destruct Hs as [Hx Hy]. rewrite !pt_inst_comp.
    f_equal; symmetry; apply pt_inst_open; intros j Hj; apply open_sub;
      [done|exact (pn_vb_root _ _ _ Hx Hj)|done|exact (pn_vb_root _ _ _ Hy Hj)].
Qed.

(** *** Ranks *)

(** Rank holds when a rank into a well-founded order rises along program
    order, along x ≺ x̄+1 and along the facts of Ψ. *)
Lemma cworld_rank_wf {A} (R : A → A → Prop) Ψ (r : point → A) :
  well_founded R → (∀ a b c, R a b → R b c → R a c) →
  (∀ x y, hyps_lt Ψ x y → R (r x) (r y)) →
  (∀ x, R (r x) (r (pt_shift 1 x))) → (∀ x, R (r x) (r (pt_shift 1 (pt_dual x)))) →
  wf_world (cworld Ψ).
Proof. intros Hwf Htr HL Hs Hd. apply (wgen_rank_wf R _ _ _ r Hwf Htr); [by intros ? ? []|done|done|done]. Qed.

(** The rank of depth and offset, read lexicographically. *)
Definition drank (x : point) : nat * nat := (sdepth (pt_name x), pt_off x).

Lemma cworld_depth_wf Ψ : (∀ x y, hyps_lt Ψ x y → lexlt (drank x) (drank y)) → wf_world (cworld Ψ).
Proof.
  intros HL. apply (cworld_rank_wf lexlt Ψ drank lexlt_wf); [unfold lexlt; intros ? ? ?; lia|done| |].
  - intros x. unfold drank, lexlt, pt_shift. cbn. lia.
  - intros x. unfold drank, lexlt, pt_shift. cbn. lia.
Qed.

(** *** The shared constant ladder

    CfstScheduler.v and ABP.v create a ceiling z = N without facts,
    then channels 0, …, a-1, channel b at the constant N - 1 - b
    ([CfstTools.cl_Ψ]). The constraint of channel a relates its instants
    to those of each earlier channel by a rank rkf and puts them below
    z. The world is well founded under the rank that reads channel b at
    rkf b and puts z above all of them. *)
Section ladder_rank.
  Context (rkf : nat → nat → nat) (Hrk : ∀ b k, rkf b k < rkf b (S k)) (N : nat).

  Definition lad_rel (a : nat) (x y : point) : Prop :=
    ∃ v, v < a ∧ pt_name x = NConst (N - 1 - v) ∧
      ((∃ w, w < a ∧ pt_name y = NConst (N - 1 - w) ∧ rkf v (pt_off x) < rkf w (pt_off y)) ∨
       pt_name y = NConst N).

  Lemma cl_env_const a : all_const (CfstTools.cl_env N a).
  Proof. unfold CfstTools.cl_env. apply Forall_fmap, Forall_forall. intros i _. by eexists. Qed.

  Lemma cl_open_name a v x : pt_name x = NVar (S v) → v ≤ a →
    pt_name (pt_open (pconst (N - 1 - a) :: CfstTools.cl_env N a) x) = NConst (N - a + v).
  Proof.
    intros Hx Hv. unfold pt_open. cbn [pt_name]. rewrite Hx. cbn [pn_open].
    change ((pconst (N - 1 - a) :: CfstTools.cl_env N a) !! S v) with (CfstTools.cl_env N a !! v).
    rewrite (CfstTools.cl_env_lookup rkf Hrk) by lia. done.
  Qed.

  Lemma ladder_lt a x y : a ≤ N → hyps_lt (CfstTools.cl_Ψ rkf N a) x y → lad_rel a x y.
  Proof.
    revert x y. induction a as [|a IH]; intros x y Ha H.
    - destruct H as (C & xs & Hin & g & Hg & _). apply list_elem_of_singleton in Hin.
      injection Hin as -> ->. destruct Hg as (f & Hf & _). destruct Hf.
    - cbn [CfstTools.cl_Ψ] in H. unfold CfstTools.cl_C in H.
      destruct (hyps_lt_snoc _ _ _ _ x y (cl_env_const a) H) as [H0|(x0 & y0 & Hf & _ & -> & ->)].
      + destruct (IH x y ltac:(lia) H0) as (v & Hv & Hx & Hy). exists v. split; [lia|]. split; [done|].
        destruct Hy as [(w & Hw & Hy & Hr)|Hy]; [left; exists w; split_and!; [lia|done|done]|by right].
      + destruct Hf as [(b & k & j & c & c' & Hb & Hr & E)|[(b & k & j & c & c' & Hb & Hr & E)|(j & c & E)]];
          injection E as -> ->.
        * exists b. split; [lia|]. split.
          -- rewrite (cl_open_name a (a - b - 1)); [f_equal; lia| |lia].
             destruct c; cbn; f_equal; lia.
          -- left. exists a. split; [lia|]. split; [by destruct c'|].
             replace (a - b) with (S (a - b - 1)) by lia. destruct c, c'; exact Hr.
        * exists a. split; [lia|]. split; [by destruct c|].
          left. exists b. split; [lia|]. split.
          -- rewrite (cl_open_name a (a - b - 1)); [f_equal; lia| |lia].
             destruct c'; cbn; f_equal; lia.
          -- destruct c, c'; exact Hr.
        * exists a. split; [lia|]. split; [by destruct c|]. right.
          rewrite (cl_open_name a a); [f_equal; lia|done|lia].
  Qed.

  Definition lad_rank (x : point) : nat * nat :=
    match pt_name x with
    | NConst v => if decide (v < N) then (0, rkf (N - 1 - v) (pt_off x))
                  else if decide (v = N) then (1, pt_off x) else (0, pt_off x)
    | _ => (0, pt_off x)
    end.

  Lemma lad_rank_shift x : lexlt (lad_rank x) (lad_rank (pt_shift 1 x)).
  Proof.
    unfold lad_rank, lexlt, pt_shift. cbn [pt_name pt_off].
    destruct (pt_name x) as [v|v|q b i]; [|cbn; lia|cbn; lia].
    repeat case_decide; cbn; try lia. right. split; [done|]. rewrite Nat.add_1_r. apply Hrk.
  Qed.

  Lemma ladder_wf a : a ≤ N → wf_world (cworld (CfstTools.cl_Ψ rkf N a)).
  Proof.
    intros Ha. apply (cworld_rank_wf lexlt _ lad_rank lexlt_wf); [unfold lexlt; intros ? ? ?; lia| |apply lad_rank_shift|].
    - intros x y H. destruct (ladder_lt a x y Ha H) as (v & Hv & Hx & [(w & Hw & Hy & Hr)|Hy]);
        unfold lad_rank, lexlt; rewrite Hx, Hy; repeat case_decide; cbn; try lia.
      right. split; [done|].
      replace (N - 1 - (N - 1 - v)) with v by lia. replace (N - 1 - (N - 1 - w)) with w by lia. exact Hr.
    - intros x. exact (lad_rank_shift (pt_dual x)).
  Qed.
End ladder_rank.

(** Budgets do not enter strictness. *)
Lemma strict_budgets W B P : strict W → strict (World (w_names W) (w_lt W) B P).
Proof. intros [[Ht Hp Hs Hn Hd] Hi]. split; [split|]; cbn; auto. Qed.

(** ** The worlds of the examples *)

(** The forwarder. fwd forwards the payload it receives on a to b. In
    the world of the forwarder (Forwarder.v) a is the constant 1 and
    b the constant 0. Round k of both sits at 6k, a at 6k, b at 6k+1, and
    the field points a[k], b[k] in between, at 6k+2 or 6k+3 by
    polarity. *)
Definition fw_k (p : pname) : nat :=
  match p with NPayload (NConst 1) k 0 | NPayload (NConst 0) k 0 => k | _ => 0 end.
Definition fw_b (p : pname) (c : bool) : nat :=
  match p with
  | NConst 0 => 1
  | NPayload (NConst 1) _ 0 => if c then 2 else 3
  | NPayload (NConst 0) _ 0 => if c then 3 else 2
  | _ => 0
  end.
Definition fw_rank (x : point) : nat := 6 * (pt_off x + fw_k (pt_name x)) + fw_b (pt_name x) (pt_pol x).

Lemma fw_b_le p c : fw_b p c ≤ 3.
Proof. unfold fw_b. repeat case_match; lia. Qed.

Lemma fw_wf : wf_world (cworld Forwarder.fw_Ψ).
Proof.
  apply (cworld_rank_wf lt _ fw_rank Wf_nat.lt_wf); [intros ? ? ?; lia| | |].
  - intros x y H.
    destruct (hyps_lt_snoc ([] ++ [(Forwarder.fpa_C, [pconst 1])]) [pconst 1] Forwarder.fwb_P 0 x y
      ltac:(by repeat econstructor) H) as [H0|(x0 & y0 & Hf & _ & -> & ->)].
    + destruct (hyps_lt_snoc [] [] Forwarder.fpa_P 1 x y ltac:(constructor) H0) as [Hn|(x0 & y0 & Hf & _ & -> & ->)];
        [by apply hyps_lt_nil in Hn|].
      destruct Hf as (k & b & b' & [E|E]); injection E as -> ->; destruct b, b'; cbn; lia.
    + destruct Hf as (k & E); repeat destruct E as [E|E]; injection E as -> ->; cbn; lia.
  - intros x. unfold fw_rank, pt_shift. cbn. lia.
  - intros x. unfold fw_rank, pt_shift, pt_dual. cbn. pose proof (fw_b_le (pt_name x) (pt_pol x)). lia.
Qed.

(** The tail call. The facts ι+k ≺ ι[0] climb in depth. *)
Lemma tc_wf : wf_world (cworld TailCall.tc_Ψ).
Proof.
  apply cworld_depth_wf. intros x y H.
  destruct (hyps_lt_snoc [] [] TailCall.tcc_P 0 x y ltac:(constructor) H) as [Hn|(x0 & y0 & Hf & _ & -> & ->)];
    [by apply hyps_lt_nil in Hn|].
  destruct Hf as (k & b & E). injection E as -> ->. destruct b; unfold drank, lexlt; cbn; lia.
Qed.

(** The recursive CFST scheduler, over the ceiling and the six channels
    of the ring. Its world is the shared constant ladder. *)
Lemma cs_wf : wf_world (cworld (CfstScheduler.sch_Ψ 6)).
Proof. apply (ladder_wf CfstScheduler.rk CfstScheduler.rk_S 6 6). lia. Qed.

(** The received chain. *)
Lemma sdepth_chv n : sdepth (ReceivedChain.chv n) = n.
Proof. induction n as [|n IH]; [done|]. cbn. by rewrite IH. Qed.

(** Opening at constants keeps the depth of a name. *)
Lemma sdepth_open xs p : all_const xs → sdepth (pn_open xs p) = sdepth p.
Proof.
  intros Hxs. induction p as [a|a|q IH b i]; cbn [pn_open sdepth]; [done| |by rewrite IH].
  destruct (xs !! a) as [z|] eqn:E; [|done].
  by destruct (proj1 (Forall_lookup _ _) Hxs a z E) as [c ->].
Qed.

Lemma rc_wf : wf_world (cworld ReceivedChain.ch_Ψ).
Proof.
  apply cworld_depth_wf. intros x y H.
  destruct (hyps_lt_snoc [] [] ReceivedChain.chc_P 0 x y ltac:(constructor) H) as [Hn|(x0 & y0 & Hf & _ & -> & ->)];
    [by apply hyps_lt_nil in Hn|].
  unfold drank. cbn [pt_open pt_name pt_off]. rewrite !sdepth_open by (repeat econstructor).
  destruct Hf as [(n & E)|(n & [E|E])]; injection E as -> ->; unfold lexlt;
    cbn [pt_name pt_off fst snd ReceivedChain.chv sdepth]; rewrite ?sdepth_chv; lia.
Qed.

(** The growing ring (GrowRing.v, Padovani III.7). The facts of e climb
    without end, and the rank 2·depth + offset still makes the world
    well founded. *)
Lemma pdepth_open xs p : all_const xs → GrowRing.pdepth (pn_open xs p) = GrowRing.pdepth p.
Proof.
  intros Hxs. induction p as [a|a|q IH b i]; cbn [pn_open GrowRing.pdepth]; [done| |by rewrite IH].
  destruct (xs !! a) as [z|] eqn:E; [|done].
  by destruct (proj1 (Forall_lookup _ _) Hxs a z E) as [c ->].
Qed.

Lemma rg_wf : wf_world (cworld GrowRing.rg_Ψ).
Proof.
  apply (cworld_rank_wf lt _ GrowRing.rg_rank Wf_nat.lt_wf); [intros a b c; lia| | |].
  - intros x y H.
    destruct (hyps_lt_snoc [] [] GrowRing.rg0_P 0 x y ltac:(constructor) H) as [Hn|(x0 & y0 & Hf & _ & -> & ->)];
      [by apply hyps_lt_nil in Hn|].
    pose proof (GrowRing.rg0_rank x0 y0 Hf) as Hr. unfold GrowRing.rg_rank in *.
    cbn [pt_open pt_name pt_off]. by rewrite !pdepth_open by (repeat econstructor).
  - intros x. unfold GrowRing.rg_rank, pt_shift. cbn. lia.
  - intros x. unfold GrowRing.rg_rank, pt_shift, pt_dual. cbn. lia.
Qed.

(** The alternating bit protocol (ABP.v, Padovani III.8). The world has
    the ceiling θ above three interleaved ascending chains. *)
Lemma abp_wf : wf_world (cworld ABP.abp_Ψ).
Proof. unfold ABP.abp_Ψ. apply (ladder_wf ABP.rkc ABP.rkc_S 3 3). lia. Qed.

(** Rank for the scheduler's world. Its facts are γ ≺ γ̄, γ+1 ≺ ε and
    γ̄+1 ≺ ε̄, with γ the constant 1 and ε the constant 0. *)
Definition sched_rank (x : point) : nat :=
  (if bool_decide (pt_name x = NConst 0) then 4 else 0) + 2 * pt_off x + (if pt_pol x then 0 else 1).

Lemma sched_wf : wf_world (cworld Scheduler.sched_Ψ).
Proof.
  apply (cworld_rank_wf lt _ sched_rank Wf_nat.lt_wf); [intros a b c; lia| | |].
  - intros x y (C & xs & Hin & g0 & (f & Hf & Hs & ->) & E).
    unfold Scheduler.sched_Ψ in Hin. rewrite !elem_of_app, !list_elem_of_singleton in Hin.
    destruct Hin as [[Hin|Hin]|Hin]; [by apply elem_of_nil in Hin| |].
    + injection Hin as -> ->. cbn in Hf. unfold FreshTools.ccd_P in Hf. subst f.
      cbn in E. injection E as -> ->. vm_compute. lia.
    + injection Hin as -> ->. cbn in Hf. unfold FreshTools.freshp_facts in Hf.
      destruct Hf as [(i & l & b & Hl & ->)|(j & h & b & Hl & _)]; [|by rewrite lookup_nil in Hl].
      destruct i as [|[|i]]; cbn in Hl; [..|discriminate]; injection Hl as <- <-;
        cbn in E; injection E as -> ->; vm_compute; lia.
  - intros x. unfold sched_rank, pt_shift. cbn. lia.
  - intros x. unfold sched_rank, pt_shift, pt_dual. cbn. destruct (pt_pol x); cbn; lia.
Qed.

(** sync. Its facts climb in depth. *)
Lemma sync_wf : wf_world (cworld Sync.sync_Ψ).
Proof.
  apply cworld_depth_wf. intros x y (C & xs & Hin & g0 & (f & Hf & Hs & ->) & E).
  unfold Sync.sync_Ψ in Hin. rewrite elem_of_app, list_elem_of_singleton in Hin.
  destruct Hin as [Hin|Hin]; [by apply elem_of_nil in Hin|]. injection Hin as -> ->.
  destruct Hf as [(i & Hi & _)|(j & Hj & _)]; cbn in *; lia.
Qed.

(** ** Worlds that Rank rejects *)

(** Under the constant world (plan §10.4) the creation facts of the
    reply channels are facts of W, at a constant a. Then Rank fails. *)
Theorem kob_rank_fails W a :
  (∀ x y, KobForwarder.fw_P (FLt x y) →
     w_lt W (pt_inst (plist [pconst a]) x) (pt_inst (plist [pconst a]) y)) →
  ¬ wf_world W.
Proof.
  intros H. apply (chain_not_wf W (λ n, pt_inst (plist [pconst a]) (Pt (payloadv n) 0))).
  intros n. apply H. exists n, true, true. left. reflexivity.
Qed.

(** The world where the run of Kobayashi's forwarder starts has these
    facts at the constant 0, so Rank rejects it already there. *)
Lemma payloadv_vb n : pn_vb 1 (payloadv n).
Proof. induction n as [|n IH]; cbn; [lia|done]. Qed.

Theorem kob_cworld_not_wf : ¬ wf_world (cworld KobForwarder.kfw_Ψ).
Proof.
  apply (chain_not_wf _ (λ n, pt_open [pconst 0] (Pt (payloadv n) 0))). intros n.
  apply glt_base. apply (hyps_lt_snoc_intro [] [] KobForwarder.fw_P 0); [constructor| |].
  - exists n, true, true. by left.
  - split; apply payloadv_vb.
Qed.

(** C1 of plan §10.1, the spawner chain.

      c1 = !(f = λπ. λ⟨prev, chat⟩. let chat′ = send ⟨∗, chat⟩ in let (a, b) = new (π[0]) in
                 let () = spawn (λw. let () = w in let () = recvclose a in close prev) in
                 (force f) (π[0]) ⟨b, chat′⟩)

    The box takes the point κ of prev as π, and a and b are created at
    κ[0], where the call places the next round. The spawned thread
    blocks on a while it holds prev, so the gate of C1 needs
    κ[0]ⁿ⁺¹ ≺ κ[0]ⁿ for every n. *)
Definition c1_P (g : fact) : Prop := ∃ n, g = FLt (Pt (payloadv (S n)) 0) (Pt (payloadv n) 0).

(** Rank rejects C1 once these facts are facts of W, at a constant a. *)
Theorem c1_rank_fails W a :
  (∀ x y, c1_P (FLt x y) →
     w_lt W (pt_inst (plist [pconst a]) x) (pt_inst (plist [pconst a]) y)) →
  ¬ wf_world W.
Proof.
  intros H. apply (chain_not_wf W (λ n, pt_inst (plist [pconst a]) (Pt (payloadv n) 0))).
  intros n. apply H. by exists n.
Qed.
