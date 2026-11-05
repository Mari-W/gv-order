(** * The type of sendTree (sharp edges 73, K8, K11)

      TreeC = µX. ⊕(Skip, !∗;X;X)
      C     = {p ≺ ζ, p ≺ p[i] ∣ p ∈ reach(ι), i}
      C′    = {ι ≺ ι′} ∪ {p ≺ ζ, p ≺ p[i] ∣ p ∈ reach(ι′), i}
      sendTree : □(∀ι ζ α. C. ∗ ⊸ ((TreeC;α)@ι ⊸^ζ ∃ι′ ≽ ι. C′. α@ι′))

    reach(ι) holds the points of the walks from ι, ι·w for every walk w.
    A step of a walk is a successor p+1 or the point p[i] where a choice
    at p continues (K11). A select at p moves the channel to p[i] and
    owes p ≺ p[i], and a branch owes both facts, so C states them for
    every reachable p next to the ceiling.

    A smoke test of the type only. The term is stage D. The type is
    closed in points and in session variables, its instance at α :=
    Close is the expected one, and C′ gives the constraint of the next
    call. A recursive call at ι′ meets C[ι′/ι] ([send_C_after]), and the
    point after a choice meets it too ([send_C_br]). The lower point ι
    of the existential is below ι′ by the first fact of C′. That fact
    holds because every path through TreeC makes a choice at least
    once.

    With end points every fact of C and C′ holds between all polarities
    of its two points. A select at p continues at (p[i])‾, a branch at
    p[i], and the lower point of an existential must sit below the
    partner point of ι′. The facts at both polarities cover all three
    without tracking which end holds the channel. *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export examples.ExampleTools.

Set Default Proof Using "All".

Definition TreeC : sty :=
  SMu (SPlus SSkip (SSeq (SSnd 0 TUnit) (SSeq (SVar 0) (SVar 0)))).

(** The facts of a channel at ι with the ceiling ζ. Every point of a
    walk from ι is below ζ and below the two points where a choice at
    it continues. With end points the facts hold at both polarities of
    each point: the selecting end continues at (p[i])‾, the branching
    end at p[i], and a walk from ῑ reaches the same points as a walk
    from ι up to polarity. *)
Definition walk_P (ι ζ : point) (g : fact) : Prop :=
  ∃ w c c', g = FLt (pt_polar c (pwalk ι w)) ζ ∨
            ∃ i, g = FLt (pt_polar c (pwalk ι w)) (pt_polar c' (wstep (pwalk ι w) (Some i))).

(** C with ι = 0 and ζ = 1 under the box binder. *)
Definition send_P (g : fact) : Prop := walk_P (pv 0 0) (pv 1 0) g.
Definition send_C : bcs := BCs [] send_P.

(** C′ under the binder of ι′ = 0, with the outer ι and ζ as 1 and 2. *)
Definition after_P (g : fact) : Prop :=
  (∃ c c', g = FLt (pt_polar c (pv 1 0)) (pt_polar c' (pv 0 0))) ∨ walk_P (pv 0 0) (pv 2 0) g.
Definition after_C : bcs := BCs [pv 0 0; pv 1 0] after_P.

Definition send_after : ty := TEx (LPt (pv 0 0)) 1 after_C (TSess (SVar 0) (pv 0 0)).

Definition send_body : ty :=
  TLolli (Some (pv 1 0)) None (TSess (SSeq TreeC (SVar 0)) (pv 0 0)) send_after.

Definition sendTree_ty : ty := TBox 2 1 send_C (TLolli None None TUnit send_body).

Lemma sendTree_ty_pscoped : pscoped 0 sendTree_ty.
Proof.
  assert (∀ k a o, a < k → pt_scoped k (pv a o)) as Hs.
  { intros k a o Ha b Hb. cbn in Hb. injection Hb as <-. done. }
  cbn. split_and!; try done; try (apply Hs; lia).
  all: unfold bcs_scoped; cbn; rewrite ?Forall_cons, ?Forall_nil; repeat split; apply Hs; lia.
Qed.

Lemma sendTree_ty_sclosed : sclosed_ty 0 sendTree_ty.
Proof. cbn. split_and!; try done; lia. Qed.

(** The instance at α := Close. *)
Lemma sendTree_inst_end x z :
  sinst_ty (slist [SEnd]) (ty_inst [x; z] (TLolli None None TUnit send_body)) =
  TLolli None None TUnit
    (TLolli (Some z) None (TSess (SSeq TreeC SEnd) x)
       (TEx (LPt x) 1 (BCs [x; z] after_P) (TSess SEnd (pv 0 0)))).
Proof.
  destruct x as [p o], z as [q r]. cbn. unfold bcs_inst, pup. cbn.
  unfold pt_inst, pt_shift. cbn. rewrite !Nat.add_0_r. done.
Qed.

Lemma st_inst_polar σ c x : pt_inst σ (pt_polar c x) = pt_polar c (pt_inst σ x).
Proof. destruct c; [done|apply pt_inst_dual]. Qed.

Lemma st_pwalk_polar c x v : ∃ d, pwalk (pt_polar c x) v = pt_polar d (pwalk x v).
Proof.
  revert c x. induction v as [|[i|] v IH]; intros c x; simpl.
  - by exists c.
  - rewrite pt_polar_payload. by exists true.
  - rewrite <-pt_polar_shift. apply IH.
Qed.

Lemma st_polar_polar c d y : ∃ e, pt_polar c (pt_polar d y) = pt_polar e y.
Proof. destruct c, d; simpl; [by exists true|by exists false|by exists false|]. exists true. apply pt_dual_dual. Qed.

(** C′ at ι′ gives C at ι′, so the next call meets its constraint. The
    outer points are the closed ones of a run. *)
Lemma send_C_after (eq lt : point → point → Prop) a o b r x' :
  bcs_hold eq lt (BCs [Pt (NConst a) o; Pt (NConst b) r] after_P) [x'] →
  bcs_hold eq lt send_C [x'; Pt (NConst b) r].
Proof.
  intros H g (f & (w & c & c' & [-> | (i & ->)]) & _ & ->).
  - assert (bcs_open 1 (BCs [Pt (NConst a) o; Pt (NConst b) r] after_P)
              (FLt (pt_polar c (pwalk (pv 0 0) w)) (Pt (NConst b) r))) as Ho.
    { exists (FLt (pt_polar c (pwalk (pv 0 0) w)) (pv 2 0)).
      split_and!; [right; exists w, c, c'; by left|split; [destruct c; apply pwalk_vb; cbn; lia|cbn; lia]|].
      cbn [fact_map]. rewrite st_inst_polar, pwalk_inst. cbn. unfold pup. cbn.
      unfold pt_inst, pt_shift. cbn. by rewrite !Nat.add_0_r. }
    specialize (H _ Ho). revert H. cbn [fact_map]. rewrite !st_inst_polar, !pwalk_inst. cbn. unfold pup. cbn.
    unfold pt_inst, pt_shift. cbn. by rewrite !Nat.add_0_r.
  - assert (bcs_open 1 (BCs [Pt (NConst a) o; Pt (NConst b) r] after_P)
              (FLt (pt_polar c (pwalk (pv 0 0) w)) (pt_polar c' (wstep (pwalk (pv 0 0) w) (Some i))))) as Ho.
    { exists (FLt (pt_polar c (pwalk (pv 0 0) w)) (pt_polar c' (wstep (pwalk (pv 0 0) w) (Some i)))).
      split_and!; [right; exists w, c, c'; right; by exists i|destruct c, c'; fscw|].
      cbn [fact_map]. rewrite ?st_inst_polar, ?wstep_inst, ?pwalk_inst. done. }
    specialize (H _ Ho). revert H. cbn [fact_map]. by rewrite ?st_inst_polar, ?wstep_inst, ?pwalk_inst.
Qed.

(** C[p/ι] ⊆ C for p = ι[i] or (ι[i])‾. The point after a choice
    still meets C, at either end. *)
Lemma send_C_br d i g :
  send_P g → fact_scoped 2 g →
  send_P (fact_map (pt_inst (plist [pt_polar d (wstep (pv 0 0) (Some i)); pv 1 0])) g).
Proof.
  assert (pt_inst (plist [pt_polar d (wstep (pv 0 0) (Some i)); pv 1 0]) (pv 0 0) =
          pt_polar d (wstep (pv 0 0) (Some i))) as E0 by (destruct d; reflexivity).
  assert (pt_inst (plist [pt_polar d (wstep (pv 0 0) (Some i)); pv 1 0]) (pv 1 0) = pv 1 0) as E1
    by reflexivity.
  intros (w & c & c' & [-> | (j & ->)]) _; cbn [fact_map];
    rewrite ?st_inst_polar, ?wstep_inst, ?pwalk_inst, E0, ?E1;
    destruct (st_pwalk_polar d (wstep (pv 0 0) (Some i)) w) as [e ->];
    destruct (st_polar_polar c e (pwalk (wstep (pv 0 0) (Some i)) w)) as [e1 ->].
  - exists (Some i :: w), e1, c'. by left.
  - destruct (st_polar_polar c' e (pwalk (wstep (pv 0 0) (Some i)) w)) as [e2 E2].
    exists (Some i :: w), e1, c'. right. exists j. simpl. f_equal.
    by rewrite pt_polar_payload.
Qed.
