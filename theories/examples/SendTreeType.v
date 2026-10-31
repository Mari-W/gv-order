(** * The type of sendTree (sharp edges 73, K8)

      TreeC = µX. ⊕(Skip, !∗;X;X)
      C     = {ι+k ≺ ζ ∣ k ∈ ℕ}
      C′    = {ι ≺ ι′} ∪ {ι′+k ≺ ζ ∣ k ∈ ℕ}
      sendTree : □(∀ι ζ α. C. ∗ ⊸^⊥_⊤ ((TreeC;α)@ι ⊸^ζ_⊤ ∃ι′ ≽ ι. C′. α@ι′))

    A smoke test of the type only. The term is stage D. The type is
    closed in points and in session variables, its instance at α :=
    Close is the expected one, and C′ gives the constraint of the next
    call: a recursive call at ι′ meets C[ι′/ι], and the instant after
    a select meets it too ([send_C_shift]). The lower point ι of the
    existential is below ι′ by the first fact of C′. That fact holds
    because every path through TreeC selects at least once. *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export examples.ExampleTools.

Set Default Proof Using "All".

Definition TreeC : sty :=
  SMu (SPlus SSkip (SSeq (SSnd 0 TUnit) (SSeq (SVar 0) (SVar 0)))).

(** C = {ι+k ≺ ζ ∣ k}, with ι = 0 and ζ = 1 under the box binder. *)
Definition send_P (g : fact) : Prop := ∃ k, g = FLt (pv 0 k) (pv 1 0).
Definition send_C : bcs := BCs [] send_P.

(** C′ under the binder of ι′ = 0, with the outer ι and ζ as 1 and 2. *)
Definition after_P (g : fact) : Prop :=
  g = FLt (pv 1 0) (pv 0 0) ∨ ∃ k, g = FLt (pv 0 k) (pv 2 0).
Definition after_C : bcs := BCs [pv 0 0; pv 1 0] after_P.

Definition send_after : ty := TEx (Some (pv 0 0)) 1 after_C (TSess (SVar 0) (pv 0 0)).

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
       (TEx (Some x) 1 (BCs [x; z] after_P) (TSess SEnd (pv 0 0)))).
Proof.
  destruct x as [p o], z as [q r]. cbn. unfold bcs_inst, pup. cbn.
  unfold pt_inst, pt_shift. cbn. rewrite !Nat.add_0_r. done.
Qed.

(** C′ at ι′ gives C at ι′: the next call meets its constraint. The
    outer points are the closed ones of a run. *)
Lemma send_C_after (eq lt : point → point → Prop) a o b r x' :
  bcs_hold eq lt (BCs [Pt (NConst a) o; Pt (NConst b) r] after_P) [x'] →
  bcs_hold eq lt send_C [x'; Pt (NConst b) r].
Proof.
  intros H g (f & (k & ->) & _ & ->).
  assert (bcs_open 1 (BCs [Pt (NConst a) o; Pt (NConst b) r] after_P)
            (FLt (pv 0 k) (Pt (NConst b) r))) as Ho.
  { exists (FLt (pv 0 k) (pv 2 0)). split_and!; [right; by exists k|cbn; split; lia|].
    cbn. unfold pup. cbn. unfold pt_inst, pt_shift. cbn. by rewrite !Nat.add_0_r. }
  specialize (H _ Ho). revert H. cbn. unfold pup. cbn.
  unfold pt_inst, pt_shift. cbn. by rewrite !Nat.add_0_r.
Qed.

(** C[ι+1/ι] ⊆ C: the instant after a select stays below ζ. *)
Lemma send_C_shift g :
  send_P g → fact_scoped 2 g → send_P (fact_map (pt_inst (plist [pv 0 1; pv 1 0])) g).
Proof. intros (k & ->) _. by exists (S k). Qed.
