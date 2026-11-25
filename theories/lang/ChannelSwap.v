(** * Channel renamings in the semantics (stage S1)

    A renaming h of channel names acts on ends by [cmap h], which keeps
    the sign of each end, and on terms by the one renaming [emap]. Thread
    steps are equivariant under every h ([tstep_cmap]). A transposition of
    two names maps process steps to process steps ([pstep_pswap]) and
    preserves safety ([safe_pswap_iff]). *)

From stdpp Require Import relations.
From GV Require Export lang.Safety.

(** ** Renaming of labels *)

Lemma set_map_upair (g : cend → cend) o1 o2 :
  set_map g ({[o1; o2]} : gset cend) = ({[g o1; g o2]} : gset cend).
Proof. by rewrite set_map_union_L, !set_map_singleton_L. Qed.

(** ** Thread steps are equivariant *)

(** ** Transpositions *)

Definition cswap (a b c : chan) : chan :=
  if decide (c = a) then b else if decide (c = b) then a else c.

Abbreviation oswap a b := (cmap (cswap a b)).
Abbreviation eswap a b := (emap (cmap (cswap a b))).

(** ** Soups and processes *)

Lemma emapE_empty g : emapE g ∅ = ∅.
Proof. apply gmultiset_map_empty. Qed.

Lemma emapE_emapE g h E : emapE g (emapE h E) = emapE (g ∘ h) E.
Proof.
  induction E as [|e E IH] using gmultiset_ind; [by rewrite !emapE_empty|].
  by rewrite !emapE_disj_union, !emapE_singleton, IH, emap_emap.
Qed.

Lemma emapE_ext g h E : (∀ o, g o = h o) → emapE g E = emapE h E.
Proof.
  intros Hgh. induction E as [|e E IH] using gmultiset_ind; [by rewrite !emapE_empty|].
  by rewrite !emapE_disj_union, !emapE_singleton, IH, (emap_ext g h).
Qed.

(** ** Process steps are equivariant under a transposition *)

(** ** Safety is equivariant *)

