(** * Soundness of the algorithmic judgment

    [algo_sound]: an algorithmic derivation of an annotated term gives a
    declarative derivation of its erasure, at the same contexts, type
    and cost, in both modes. *)

From GV Require Export algorithmic.Algo.

Lemma lenv_sinst_ids Δ : lenv_sinst SVar Δ = Δ.
Proof.
  induction Δ as [|[T|] Δ IH]; simpl; [done| |by rewrite IH].
  rewrite IH. f_equal. f_equal. by apply sinst_id_mut.
Qed.

(** ** One instance of a box body types it at all instances *)

Lemma box_body_all W N Γ Δ F e m k C ub c U c' :
  lenv_contr Δ → tcontr U →
  typed W N ∅ Γ (lenv_pinst (pshift m) (Some (TBox m k C ub c U) :: Δ)) F e
    (sinst_ty (slist (box_inst (box_base k U Δ) k)) U) c' →
  ∀ ss, length ss = k → sinsts N ss →
  typed W N ∅ Γ (lenv_pinst (pshift m) (Some (TBox m k C ub c U) :: Δ)) F e
    (sinst_ty (slist ss) U) c'.
Proof.
  intros HΔ HU H ss Hk Hss.
  set (M := box_base k U Δ).
  set (φ := λ b, if decide (b < M) then SVar b else slist ss (b - M)).
  destruct (sinst_ok_slist N ss Hss) as (Hc & Hs & Hd).
  assert (sinst_ok N φ) as Hok.
  { unfold φ. split_and!.
    - intros a. case_decide; [done|apply Hc].
    - intros a. case_decide; [done|apply Hs].
    - intros HN a. case_decide; [done|by apply Hd]. }
  assert (lenv_contr (lenv_pinst (pshift m) (Some (TBox m k C ub c U) :: Δ))) as Hctx
    by (apply lenv_contr_pinst, lenv_contr_some; done).
  pose proof (typed_sinst _ _ _ _ _ _ _ _ _ H φ Hok tenv_contr_empty Hctx) as H'.
  rewrite tenv_sinst_empty in H'.
  assert (lenv_sinst φ (lenv_pinst (pshift m) (Some (TBox m k C ub c U) :: Δ)) =
          lenv_pinst (pshift m) (Some (TBox m k C ub c U) :: Δ)) as E1.
  { rewrite <-(lenv_sinst_ids (lenv_pinst _ _)) at 2. apply lenv_sinst_fv.
    intros a Ha. rewrite lfv_pinst in Ha. unfold φ. case_decide as Ha'; [done|].
    exfalso. apply Ha'. unfold M, box_base. simpl in Ha. lia. }
  assert (sinst_ty φ (sinst_ty (slist (box_inst M k)) U) = sinst_ty (slist ss) U) as E2.
  { rewrite sinst_ty_sinst. apply sinst_fv_mut. intros a Ha. unfold compose.
    destruct (decide (a < k)) as [Hak|Hak].
    - unfold slist at 1. rewrite box_inst_lookup by done. cbn [sinst]. unfold φ.
      case_decide; [lia|]. f_equal. lia.
    - assert (slist (box_inst M k) a = SVar (a - k)) as ->.
      { unfold slist. rewrite lookup_ge_None_2 by (rewrite box_inst_length; lia).
        rewrite box_inst_length. done. }
      cbn [sinst]. unfold φ. case_decide; [|unfold M, box_base in *; lia].
      unfold slist. rewrite lookup_ge_None_2 by lia. f_equal. lia. }
  change (box_base k U Δ) with M in H'. rewrite E1, E2 in H'. exact H'.
Qed.

(** ** Soundness *)

Section sound.
  Context (W : sworld) (N : fuel).

  Theorem algo_sound :
    (∀ Θ Γ Δ F t T c, syn W N Θ Γ Δ F t T c → typed W N Θ Γ Δ F (erase t) T c) ∧
    (∀ Θ Γ Δ F t T c, chk W N Θ Γ Δ F t T c → typed W N Θ Γ Δ F (erase t) T c).
  Proof.
    apply syn_chk_mut; intros; simpl.
    - by apply e_unit.
    - by apply e_var.
    - by apply e_chan.
    - (* App *)
      eapply e_app; [by eapply tpart_tsplit|by eapply lpart_lsplit|done|exact H|done|done|exact H0|done].
    - (* Pair *)
      eapply e_pair; [by eapply tpart_tsplit|by eapply lpart_lsplit|exact H|done|done|exact H0|done].
    - (* LetU *)
      eapply e_letu; [by eapply tpart_tsplit|by eapply lpart_lsplit|exact H|done|done|exact H0].
    - (* LetP *)
      eapply e_letp; [by eapply tpart_tsplit|by eapply lpart_lsplit|exact H|done|done|exact H0].
    - by eapply e_force.
    - by eapply e_send.
    - by eapply e_recv.
    - by eapply e_close.
    - by eapply e_select.
    - by eapply e_branch.
    - by eapply e_link.
    - by eapply e_spawn.
    - by apply e_new.
    - by apply e_new_fld.
    - (* Asc *)
      eapply e_sub; [exact H|apply tsub_refl|done|done].
    - by eapply e_pack.
    - by eapply e_open.
    - (* Lam *)
      eapply e_abs; [done|done|done|done|].
      eapply e_sub; [exact H|apply tsub_refl|done|done].
    - by apply e_inj.
    - (* Case *)
      eapply e_case; [by eapply tpart_tsplit|by eapply lpart_lsplit|exact H|done|done|exact H0|exact H1].
    - (* Box *)
      apply e_box; [done|done|]. apply box_body_all; [done|done|].
      eapply e_sub; [exact H|apply tsub_refl|done|done].
    - (* LetU, checked *)
      eapply e_letu; [by eapply tpart_tsplit|by eapply lpart_lsplit|exact H|done|done|exact H0].
    - (* LetP, checked *)
      eapply e_letp; [by eapply tpart_tsplit|by eapply lpart_lsplit|exact H|done|done|exact H0].
    - eapply e_sub; [exact H|done|apply fle_refl|done].
  Qed.
End sound.
