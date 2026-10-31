(** * Dropping a fresh conservative extension fails (sharp edges 54)

    The claim: if W′ places a fresh constant μ over W and adds nothing
    between old points, then V and E at W′ give V and E at W for
    environments, types and frames without μ. It fails at V-Const. The
    witness T₀ of a constant is existential, and force's instance xs
    may use μ.

    b = 0 and μ = 1. W knows b and has only program order. W′ adds the
    alias (μ,1) ≡ (b,0) and places μ ([Wm_fresh]). force is in V^{W′}
    at □(∀ι. Close@(ι+1)) ⊸ Close@(b,0) with xs = [(μ,0)], and in no
    V^W at that type, because no point x of W has x+1 ≡_W (b,0). This is
    why E-Abs and E-Exp use a frame variable φ instead of a fresh point
    (static/FactTheory.v). *)
From stdpp Require Import base gmap.
From LRGV Require Import relation.LogicalRelation.

Definition b0 : nat := 0.
Definition mu : nat := 1.

(* canonical representative: b-points move onto the μ line, one later *)
Fixpoint cnm (p : pname) (o : nat) : point :=
  match p with
  | NConst a => if decide (a = b0) then Pt (NConst mu) (S o) else Pt (NConst a) o
  | NVar a => Pt (NVar a) o
  | NSlot q o' i => Pt (NSlot (pt_name (cnm q o')) (pt_off (cnm q o')) i) o
  | NBr q o' i => Pt (NBr (pt_name (cnm q o')) (pt_off (cnm q o')) i) o
  end.
Definition cpt (x : point) : point := cnm (pt_name x) (pt_off x).

Lemma cnm_name p o o' : pt_name (cnm p o) = pt_name (cnm p o').
Proof. destruct p; simpl; repeat case_decide; done. Qed.
Lemma cnm_off p o : pt_off (cnm p o) = o + pt_off (cnm p 0).
Proof. destruct p; simpl; repeat case_decide; simpl; lia. Qed.

Lemma cpt_shift x : cpt (pt_shift 1 x) = pt_shift 1 (cpt x).
Proof.
  destruct x as [p o]. unfold cpt, pt_shift. simpl.
  destruct p; simpl; repeat case_decide; simpl; repeat f_equal; lia.
Qed.
Lemma cpt_slot x i : cpt (pt_slot x i) = pt_slot (cpt x) i.
Proof. done. Qed.
Lemma cpt_br x i : cpt (pt_br x i) = pt_br (cpt x) i.
Proof. done. Qed.

Lemma cnm_root p o :
  pt_root (cnm p o) = if decide (pn_root p = NConst b0) then NConst mu else pn_root p.
Proof.
  revert o. induction p as [a|a|q IH o' i|q IH o' i]; intros o; simpl.
  - unfold pt_root. repeat case_decide; simpl; subst; try done; congruence.
  - done.
  - unfold pt_root in *. simpl. apply IH.
  - unfold pt_root in *. simpl. apply IH.
Qed.

(* off μ, cpt is injective *)
Lemma cnm_inj p o p' o' :
  pn_root p ≠ NConst mu → pn_root p' ≠ NConst mu → cnm p o = cnm p' o' → p = p' ∧ o = o'.
Proof.
  revert o p' o'. induction p as [a|a|q IH oq i|q IH oq i]; intros o p' o' Hr Hr' E;
    destruct p' as [a'|a'|q' oq' i'|q' oq' i']; simpl in *;
    repeat case_decide; simplify_eq/=; try done; try (split; congruence).
  - destruct (IH oq q' oq' Hr Hr') as [-> ->]; [|done].
    destruct (cnm q oq) eqn:E1, (cnm q' oq') eqn:E2. simpl in *. by subst.
  - destruct (IH oq q' oq' Hr Hr') as [-> ->]; [|done].
    destruct (cnm q oq) eqn:E1, (cnm q' oq') eqn:E2. simpl in *. by subst.
Qed.

(* the inverse of cnm on the μ line: μ-points move back onto b, one earlier *)
Fixpoint cinvn (p : pname) (o : nat) : point :=
  match p with
  | NConst a => if decide (a = mu) then Pt (NConst b0) (o - 1) else Pt (NConst a) o
  | NVar a => Pt (NVar a) o
  | NSlot q o' i => Pt (NSlot (pt_name (cinvn q o')) (pt_off (cinvn q o')) i) o
  | NBr q o' i => Pt (NBr (pt_name (cinvn q o')) (pt_off (cinvn q o')) i) o
  end.
Definition cinv (x : point) : point := cinvn (pt_name x) (pt_off x).

(* the offset at the root constant of a point *)
Fixpoint pn_boff (p : pname) (o : nat) : nat :=
  match p with
  | NConst _ | NVar _ => o
  | NSlot q o' _ | NBr q o' _ => pn_boff q o'
  end.
Definition cq (x : point) : Prop :=
  pt_root x = NConst mu → 1 ≤ pn_boff (pt_name x) (pt_off x).

Lemma cinv_cpt x : pt_root x ≠ NConst mu → cinv (cpt x) = x.
Proof.
  destruct x as [p o]. unfold cinv, cpt, pt_root. simpl. revert o.
  induction p as [a|a|q IH oq i|q IH oq i]; intros o Hm; simpl in *.
  - destruct (decide (a = b0)) as [->|Hb]; simpl.
    + f_equal. lia.
    + rewrite ?decide_False by (intros ->; done). done.
  - done.
  - rewrite IH by done. done.
  - rewrite IH by done. done.
Qed.

Lemma cq_cpt x : pt_root x ≠ NConst mu → cq (cpt x).
Proof.
  destruct x as [p o]. unfold cq, cpt, pt_root. simpl. revert o.
  induction p as [a|a|q IH oq i|q IH oq i]; intros o Hm; simpl in *.
  - repeat case_decide; simpl; [lia|congruence].
  - discriminate.
  - apply IH, Hm.
  - apply IH, Hm.
Qed.

Lemma cinv_ppo x y : ppo x y → cq x → ppo (cinv x) (cinv y).
Proof.
  assert (∀ z, cq z → cq (pt_shift 1 z)) as Hqs.
  { intros [[| | |] o]; unfold cq, pt_root; simpl; intros H Hr; try (apply H, Hr); lia. }
  assert (∀ z i, cq z → cq (pt_br z i)) as Hqb.
  { intros [p o] i. unfold cq, pt_root. simpl. done. }
  assert (∀ x y, ppo x y → cq x → cq y) as Hq.
  { induction 1; auto. }
  induction 1 as [z|z i|x y z H1 IH1 _ IH2]; intros Hz.
  - destruct z as [[a| | |] o]; unfold cinv, pt_shift; simpl;
      [|apply ppo_po..].
    destruct (decide (a = mu)) as [->|Ha].
    + unfold cq, pt_root in Hz. simpl in Hz. specialize (Hz eq_refl).
      replace (o + 1 - 1) with (o - 1 + 1) by lia. apply (ppo_po (Pt (NConst b0) (o - 1))).
    + apply (ppo_po (Pt (NConst a) o)).
  - apply (ppo_br (cinv z) i).
  - eapply ppo_trans; [by apply IH1|]. apply IH2. by eapply Hq.
Qed.

Definition Wb : world :=
  World {[NConst b0]} (λ x y, x = y) ppo.

Definition Wm : world :=
  World ({[NConst b0]} ∪ {[NConst mu]}) (λ x y, cpt x = cpt y)
    (λ x y, ppo (cpt x) (cpt y)).

Lemma Wb_strict : strict Wb.
Proof.
  split; [split|]; simpl.
  - done.
  - naive_solver.
  - naive_solver.
  - naive_solver.
  - naive_solver.
  - naive_solver.
  - intros x y z ? ?. by eapply ppo_trans.
  - naive_solver.
  - apply ppo_po.
  - apply ppo_br.
  - intros x y ->. by left.
  - intros x y H. by left.
  - intros p Hp. set_solver.
  - apply ppo_irrefl.
Qed.

Lemma cpt_root_in x : pt_root x = NConst b0 ∨ pt_root x = NConst mu →
  pt_root (cpt x) = NConst mu.
Proof.
  unfold cpt. rewrite cnm_root. unfold pt_root. intros [H|H]; case_decide; congruence.
Qed.
Lemma cpt_root_out x : pt_root x ≠ NConst b0 → pt_root (cpt x) = pt_root x.
Proof. unfold cpt. rewrite cnm_root. unfold pt_root. intros H. by case_decide. Qed.

Lemma cpt_out_id x : pt_root x ≠ NConst b0 → pt_root x ≠ NConst mu → cpt x = x.
Proof.
  destruct x as [p o]. unfold cpt, pt_root. simpl. revert o.
  induction p as [a|a|q IH oq i|q IH oq i]; intros o Hb Hm; simpl in *; repeat case_decide; subst; try done;
    rewrite IH by done; done.
Qed.

Lemma Wm_strict : strict Wm.
Proof.
  split; [split|]; simpl.
  - done.
  - naive_solver.
  - intros x y z. congruence.
  - intros x y H. by rewrite !cpt_shift, H.
  - intros x y i H. by rewrite !cpt_slot, H.
  - intros x y i H. by rewrite !cpt_br, H.
  - intros x y z ? ?. by eapply ppo_trans.
  - intros x x' y y' -> ? <-. done.
  - intros x. rewrite cpt_shift. apply ppo_po.
  - intros x i. rewrite cpt_br. apply ppo_br.
  - intros x y H. unfold eq_or_supp.
    destruct (decide (pt_root x = NConst b0 ∨ pt_root x = NConst mu)) as [Hx|Hx];
    destruct (decide (pt_root y = NConst b0 ∨ pt_root y = NConst mu)) as [Hy|Hy].
    + right. set_solver.
    + exfalso. apply cpt_root_in in Hx. rewrite H, cpt_root_out in Hx by naive_solver. naive_solver.
    + exfalso. apply cpt_root_in in Hy. rewrite <-H, cpt_root_out in Hy by naive_solver. naive_solver.
    + left. rewrite cpt_out_id in H by naive_solver. rewrite cpt_out_id in H by naive_solver. done.
  - intros x y Hp. unfold po_or_supp. pose proof (ppo_root _ _ Hp) as Hn.
    destruct (decide (pt_root x = NConst b0 ∨ pt_root x = NConst mu)) as [Hx|Hx];
    destruct (decide (pt_root y = NConst b0 ∨ pt_root y = NConst mu)) as [Hy|Hy].
    + right. set_solver.
    + exfalso. apply cpt_root_in in Hx. rewrite Hn in Hx.
      rewrite cpt_root_out in Hx by naive_solver. naive_solver.
    + exfalso. apply cpt_root_in in Hy. rewrite <-Hn in Hy.
      rewrite cpt_root_out in Hy by naive_solver. naive_solver.
    + left. rewrite !cpt_out_id in Hp by naive_solver. done.
  - intros p Hp. set_solver.
  - intros x H. exact (ppo_irrefl _ H).
Qed.

Lemma Wm_fresh : wext_fresh Wb {[NConst mu]} Wm.
Proof.
  split_and!.
  - split_and!; simpl.
    + set_solver.
    + by intros x y ->.
    + intros x y Hp. apply ppo_map; [apply cpt_shift|apply cpt_br|done].
    + exact Wm_strict.
  - simpl. set_solver.
  - done.
  - intros [p o] [p' o'] Hx Hy. unfold pt_root in Hx, Hy. simpl in *. split.
    + intros H. unfold cpt in H. simpl in H.
      destruct (cnm_inj p o p' o') as [-> ->]; [set_solver|set_solver|done|done].
    + intros Hp. apply cinv_ppo in Hp; [|apply cq_cpt; unfold pt_root; simpl; set_solver].
      rewrite !cinv_cpt in Hp by (unfold pt_root; simpl; set_solver). done.
Qed.

Definition Tb : ty := TSess SEnd (Pt (NVar 0) 1).
Definition Tcex : ty := TLolli None None (TBox 1 0 (BCs [] (λ _, False)) (TLolli None None TUnit Tb)) (TSess SEnd (Pt (NConst b0) 0)).

Lemma Tcex_roots : NConst mu ∉ ty_roots Tcex.
Proof. simpl. unfold pt_root, bcs_roots. simpl. set_solver. Qed.

Lemma force_in_Wm n : Vrel n Wm ∅ Tcex (Konst KForce).
Proof.
  apply Vrel_lolli_iff. right. exists KForce, (TLolli None None (TBox 1 0 (BCs [] (λ _, False)) (TLolli None None TUnit Tb)) (sinst_ty (slist []) (ty_inst [Pt (NConst mu) 0] Tb))).
  split_and!; [done|done| |].
  - apply (KTForce _ _ _ 1 0 (BCs [] (λ _, False)) None Tb [Pt (NConst mu) 0] []); try done.
    + intros g (f & [] & _).
    + constructor; [|constructor]. unfold pt_known. simpl. set_solver.
  - simpl. split_and!; try done.
    + split; intros g (f & [] & _).
    + left. done.
    + apply seq_refl.
    + right. split_and!; [by exists mu|by exists b0|]. done.
    + apply seq_refl.
Qed.

Lemma force_notin_Wb n : ¬ Vrel n Wb ∅ Tcex (Konst KForce).
Proof.
  intros H. apply Vrel_lolli_iff in H as [(eb & ? & _)|(k & T0 & Hk & _ & Hkt & Heq)]; [done|].
  simplify_eq. inversion Hkt; subst.
  simpl in Heq. destruct Heq as (_ & _ & Hbox & Hres).
  destruct ss; [|by destruct Hbox as (_ & ? & _)]. rewrite sinst_slist_nil in Hres.
  destruct T as [| | | | |s y|]; simpl in Hbox; try naive_solver.
  destruct Hbox as (Hn & _ & _ & Hub & _ & _ & Hs & _).
  destruct ub; simpl in Hub; [done|].
  destruct Hs as [->|(_ & Hg & _)]; [|by destruct Hg].
  destruct xs as [|x []]; simpl in *; try lia.
  destruct Hres as [[Hp|(_ & _ & Hp)] _]; unfold pt_inst, pt_shift in Hp;
    destruct x; simpl in Hp; simplify_eq; lia.
Qed.

Lemma force_in_Erel_Wm n F : Erel n Wm ∅ Tcex F (Konst KForce).
Proof. apply Vrel_Erel, force_in_Wm. Qed.

Lemma force_notin_Erel_Wb n F : ¬ Erel (S n) Wb ∅ Tcex F (Konst KForce).
Proof.
  intros H. apply Erel_S_iff in H as (Hv & _).
  apply (force_notin_Wb (S n)). apply Hv. intros e' α Hs. inversion Hs; subst.
  match goal with H : head_step _ _ _ |- _ => inversion H end.
Qed.
