(** * The type of sendTree (sharp edges 73, K8, K11)

      TreeC = µX. ⊕(Skip, !∗;X;X)
      C     = {p ≺ ζ, p ≺ p[i] ∣ p ∈ reach(ι), i}
      C′    = {ι ≺ ι′} ∪ {p ≺ ζ, p ≺ p[i] ∣ p ∈ reach(ι′), i}
      sendTree : □(∀ι ζ α. C. ∗ ⊸^⊥_⊤ ((TreeC;α)@ι ⊸^ζ_⊤ ∃ι′ ≽ ι. C′. α@ι′))

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
    once. *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export examples.ExampleTools.

Set Default Proof Using "All".

Definition TreeC : sty :=
  SMu (SPlus SSkip (SSeq (SSnd 0 TUnit) (SSeq (SVar 0) (SVar 0)))).

(** The facts of a channel at ι with the ceiling ζ. Every point of a
    walk from ι is below ζ and below the two points where a choice at
    it continues. *)
Definition walk_P (ι ζ : point) (g : fact) : Prop :=
  ∃ w, g = FLt (pwalk ι w) ζ ∨ ∃ i, g = FLt (pwalk ι w) (wstep (pwalk ι w) (Some i)).

(** C with ι = 0 and ζ = 1 under the box binder. *)
Definition send_P (g : fact) : Prop := walk_P (pv 0 0) (pv 1 0) g.
Definition send_C : bcs := BCs [] send_P.

(** C′ under the binder of ι′ = 0, with the outer ι and ζ as 1 and 2. *)
Definition after_P (g : fact) : Prop := g = FLt (pv 1 0) (pv 0 0) ∨ walk_P (pv 0 0) (pv 2 0) g.
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

(** C′ at ι′ gives C at ι′, so the next call meets its constraint. The
    outer points are the closed ones of a run. *)
Lemma send_C_after (eq lt : point → point → Prop) a o b r x' :
  bcs_hold eq lt (BCs [Pt (NConst a) o; Pt (NConst b) r] after_P) [x'] →
  bcs_hold eq lt send_C [x'; Pt (NConst b) r].
Proof.
  intros H g (f & (w & [-> | (i & ->)]) & _ & ->).
  - assert (bcs_open 1 (BCs [Pt (NConst a) o; Pt (NConst b) r] after_P)
              (FLt (pwalk (pv 0 0) w) (Pt (NConst b) r))) as Ho.
    { exists (FLt (pwalk (pv 0 0) w) (pv 2 0)).
      split_and!; [right; exists w; by left|split; [apply pwalk_vb; cbn; lia|cbn; lia]|].
      cbn [fact_map]. rewrite pwalk_inst. cbn. unfold pup. cbn.
      unfold pt_inst, pt_shift. cbn. by rewrite !Nat.add_0_r. }
    specialize (H _ Ho). revert H. cbn [fact_map]. rewrite !pwalk_inst. cbn. unfold pup. cbn.
    unfold pt_inst, pt_shift. cbn. by rewrite !Nat.add_0_r.
  - assert (bcs_open 1 (BCs [Pt (NConst a) o; Pt (NConst b) r] after_P)
              (FLt (pwalk (pv 0 0) w) (wstep (pwalk (pv 0 0) w) (Some i)))) as Ho.
    { exists (FLt (pwalk (pv 0 0) w) (wstep (pwalk (pv 0 0) w) (Some i))).
      split_and!; [right; exists w; right; by exists i|fscw|].
      cbn [fact_map]. rewrite ?wstep_inst, ?pwalk_inst. done. }
    specialize (H _ Ho). revert H. cbn [fact_map]. by rewrite ?wstep_inst, ?pwalk_inst.
Qed.

(** C[ι[i]/ι] ⊆ C. The point after a choice still meets C. *)
Lemma send_C_br i g :
  send_P g → fact_scoped 2 g →
  send_P (fact_map (pt_inst (plist [wstep (pv 0 0) (Some i); pv 1 0])) g).
Proof.
  intros (w & [-> | (j & ->)]) _; exists (Some i :: w); [left|right; exists j];
    cbn [fact_map]; by rewrite ?wstep_inst, ?pwalk_inst.
Qed.
