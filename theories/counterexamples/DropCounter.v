(** * Dropping a fresh conservative extension fails (sharp edges 54)

    The claim: if W′ places a fresh constant μ over W and adds nothing
    between old points, then V and E at W′ give V and E at W for
    environments, types and frames without μ. It fails at V-Const. The
    witness T₀ of a constant is existential, and force's instance xs
    may use μ.

    b = 0 and μ = 1. W knows b and has only program order. W′ adds the
    alias (μ,1) ≡ (b,0) and places μ ([Wm_fresh]). force is in V^{W′}
    at □(∀ι. Close@(ι+1)) ⊸ Close@(b,0) with xs = [(μ,0)], and in no
    V^W at that type, because no point x of W has x+1 ≡_W (b,0). *)
From stdpp Require Import base gmap.
From LRGV Require Import Relation.

Definition b0 : nat := 0.
Definition mu : nat := 1.

(* canonical representative: b-points move onto the μ line, one later *)
Fixpoint cnm (p : pname) (o : nat) : point :=
  match p with
  | NConst a => if decide (a = b0) then Pt (NConst mu) (S o) else Pt (NConst a) o
  | NVar a => Pt (NVar a) o
  | NSlot q o' i => Pt (NSlot (pt_name (cnm q o')) (pt_off (cnm q o')) i) o
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

Lemma cnm_root p o :
  pt_root (cnm p o) = if decide (pn_root p = NConst b0) then NConst mu else pn_root p.
Proof.
  revert o. induction p as [a|a|q IH o' i]; intros o; simpl.
  - unfold pt_root. repeat case_decide; simpl; subst; try done; congruence.
  - done.
  - unfold pt_root in *. simpl. apply IH.
Qed.

(* off μ, cpt is injective *)
Lemma cnm_inj p o p' o' :
  pn_root p ≠ NConst mu → pn_root p' ≠ NConst mu → cnm p o = cnm p' o' → p = p' ∧ o = o'.
Proof.
  revert o p' o'. induction p as [a|a|q IH oq i]; intros o p' o' Hr Hr' E;
    destruct p' as [a'|a'|q' oq' i']; simpl in *;
    repeat case_decide; simplify_eq/=; try done; try (split; congruence).
  - destruct (IH oq q' oq' Hr Hr') as [-> ->]; [|done].
    destruct (cnm q oq) eqn:E1, (cnm q' oq') eqn:E2. simpl in *. by subst.
Qed.

Definition Wb : world :=
  World {[NConst b0]} (λ x y, x = y) (λ x y, pt_name x = pt_name y ∧ pt_off x < pt_off y).

Definition Wm : world :=
  World ({[NConst b0]} ∪ {[NConst mu]}) (λ x y, cpt x = cpt y)
    (λ x y, pt_name (cpt x) = pt_name (cpt y) ∧ pt_off (cpt x) < pt_off (cpt y)).

Lemma Wb_strict : strict Wb.
Proof.
  split; [split|]; simpl.
  - done.
  - naive_solver.
  - naive_solver.
  - naive_solver.
  - naive_solver.
  - intros x y z [? ?] [? ?]. split; [congruence|lia].
  - naive_solver.
  - intros x. split; [done|simpl; lia].
  - intros x y ->. by left.
  - intros x y H. by left.
  - intros p Hp. set_solver.
  - intros x [_ H]. lia.
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
  induction p as [a|a|q IH oq i]; intros o Hb Hm; simpl in *; repeat case_decide; subst; try done.
  rewrite IH by done. done.
Qed.

Lemma Wm_strict : strict Wm.
Proof.
  split; [split|]; simpl.
  - done.
  - naive_solver.
  - intros x y z. congruence.
  - intros x y H. by rewrite !cpt_shift, H.
  - intros x y i H. by rewrite !cpt_slot, H.
  - intros x y z [? ?] [? ?]. split; [congruence|lia].
  - intros x x' y y' -> ? <-. done.
  - intros x. rewrite cpt_shift. simpl. split; [done|lia].
  - intros x y H. unfold eq_or_supp.
    destruct (decide (pt_root x = NConst b0 ∨ pt_root x = NConst mu)) as [Hx|Hx];
    destruct (decide (pt_root y = NConst b0 ∨ pt_root y = NConst mu)) as [Hy|Hy].
    + right. set_solver.
    + exfalso. apply cpt_root_in in Hx. rewrite H, cpt_root_out in Hx by naive_solver. naive_solver.
    + exfalso. apply cpt_root_in in Hy. rewrite <-H, cpt_root_out in Hy by naive_solver. naive_solver.
    + left. rewrite cpt_out_id in H by naive_solver. rewrite cpt_out_id in H by naive_solver. done.
  - intros x y [Hn Ho]. unfold po_or_supp.
    destruct (decide (pt_root x = NConst b0 ∨ pt_root x = NConst mu)) as [Hx|Hx];
    destruct (decide (pt_root y = NConst b0 ∨ pt_root y = NConst mu)) as [Hy|Hy].
    + right. set_solver.
    + exfalso. apply cpt_root_in in Hx. unfold pt_root in Hx. rewrite Hn in Hx.
      fold (pt_root (cpt y)) in Hx. rewrite cpt_root_out in Hx by naive_solver. naive_solver.
    + exfalso. apply cpt_root_in in Hy. unfold pt_root in Hy. rewrite <-Hn in Hy.
      fold (pt_root (cpt x)) in Hy. rewrite cpt_root_out in Hy by naive_solver. naive_solver.
    + left. rewrite !cpt_out_id in Hn, Ho by naive_solver. done.
  - intros p Hp. set_solver.
  - intros x [_ H]. lia.
Qed.

Lemma Wm_fresh : wext_fresh Wb {[NConst mu]} Wm.
Proof.
  split_and!.
  - split_and!; simpl.
    + set_solver.
    + by intros x y ->.
    + intros [p o] [p' o'] [Hn Ho]; simpl in *. subst p'. unfold cpt. simpl.
      rewrite (cnm_name p o o'). split; [done|]. rewrite (cnm_off p o), (cnm_off p o'). lia.
    + exact Wm_strict.
  - simpl. set_solver.
  - done.
  - intros [p o] [p' o'] Hx Hy. unfold pt_root in Hx, Hy. simpl in *. split.
    + intros H. unfold cpt in H. simpl in H.
      destruct (cnm_inj p o p' o') as [-> ->]; [set_solver|set_solver|done|done].
    + intros [Hn Ho]. unfold cpt in Hn, Ho. simpl in *.
      assert (p = p') as <-.
      { destruct (cnm_inj p 0 p' 0) as [? _]; [set_solver|set_solver| |done].
        destruct (cnm p 0) eqn:E1, (cnm p' 0) eqn:E2.
        rewrite (cnm_name p o 0), (cnm_name p' o' 0), E1, E2 in Hn. simpl in Hn. subst.
        (* same name; offsets at 0 agree because they depend on the name only *)
        pose proof (cnm_off p 0) as H1. pose proof (cnm_off p' 0) as H2.
        rewrite E1 in H1. rewrite E2 in H2. simpl in *.
        destruct p, p'; simpl in *; repeat case_decide; simplify_eq/=; try done; set_solver. }
      split; [done|]. rewrite (cnm_off p o), (cnm_off p o') in Ho. lia.
Qed.

Definition Tb : ty := TSess SEnd (Pt (NVar 0) 1).
Definition Tcex : ty := TLolli None None (TBox 1 (BCs [] []) None Tb) (TSess SEnd (Pt (NConst b0) 0)).

Lemma Tcex_roots : NConst mu ∉ ty_roots Tcex.
Proof. simpl. unfold pt_root, bcs_roots, steps_roots, pcs_roots. simpl. set_solver. Qed.

Lemma force_in_Wm n : Vrel n Wm ∅ Tcex (Konst KForce).
Proof.
  apply Vrel_lolli_iff. right. exists KForce, (TLolli None None (TBox 1 (BCs [] []) None Tb) (ty_inst [Pt (NConst mu) 0] Tb)).
  split_and!; [done|done| |].
  - apply (KTForce _ _ _ 1 (BCs [] []) None Tb [Pt (NConst mu) 0]); try done.
    + intros w _ p Hp. by apply elem_of_nil in Hp.
    + constructor; [|constructor]. unfold pt_known. simpl. set_solver.
  - simpl. split_and!; try done.
    + split; constructor.
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
  destruct T as [| | | | |s y]; simpl in Hbox; try naive_solver.
  destruct Hbox as (Hn & _ & Hub & Hs & _).
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
