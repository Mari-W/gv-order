(** * The cost half of the merged judgment (stage S7, A.3)

      Θ ; Γ ; Δ ⊢^F _{W,N} e : T ▷ c  ⟹  Θ ; Δ ⊨^N e : T ▷ c    [cost_fundamental]

    by induction on the derivation, one rule of cost/CostRules.v per
    case. E-Abs and E-Box take the facts of their term from
    [typed_tfacts]. [fsem_of_cost] turns a closed thread into [fsem],
    the premise LF-Term adds to P-Term: every end starts at its tickets.
    [fw_fsem] is the forwarder of
    S7.1, which now has its [fsem]. *)

From GV Require Export cost.CostRules cost.Forwarder.

Theorem cost_fundamental W N Θ Γ Δ F e T c :
  Θ ; Γ ; Δ ⊢^F _{W,N} e : T ▷ c → Θ ; Δ ⊨^N e : T ▷ c.
Proof.
  induction 1.
  - by apply cost_e_unit.
  - by apply cost_e_var.
  - by apply cost_e_chan.
  - eapply cost_e_abs; [|done|done|done]. eapply (typed_tfacts _ _ _ _ _ (∅, None)). by eapply e_abs.
  - by eapply cost_e_app.
  - by eapply cost_e_pair.
  - by eapply cost_e_letu.
  - by eapply cost_e_letp.
  - by apply cost_e_inj.
  - by eapply cost_e_case.
  - eapply cost_e_box; [|done|done]. eapply (typed_tfacts _ _ _ _ _ (∅, None)). by eapply e_box.
  - by eapply cost_e_force.
  - by eapply cost_e_send.
  - by eapply cost_e_recv.
  - by eapply cost_e_close.
  - by eapply cost_e_select.
  - by eapply cost_e_branch.
  - by eapply cost_e_link.
  - by eapply cost_e_spawn.
  - by eapply cost_e_new.
  - by eapply cost_e_new_fld.
  - by eapply cost_e_sub.
  - by eapply cost_e_pack.
  - by eapply cost_e_open.
Qed.

(** The counters of Θ at the tickets of its ends. *)
Definition tkenv (Θ : tenv) : cenv := (λ te, (te_tk te, te_tk te)) <$> Θ.

Lemma thfuel_id Θ :
  cr_tk Θ →
  thfuel Θ id (te_sty <$> Θ) (tkenv Θ).
Proof.
  intros HN. split_and!.
  - by intros o1 o2 _ _.
  - rewrite dom_fmap_L. apply set_eq. intros o. rewrite elem_of_map. split; [intros; by exists o|by intros (? & -> & ?)].
  - unfold tkenv. by rewrite !dom_fmap_L.
  - intros o te Hte. unfold tkenv. simpl. rewrite !lookup_fmap, Hte. split; [done|]. eexists. split; [done|].
    split; [exact (HN o te Hte)|done].
Qed.

(** A closed thread typed at N, whose ends have credits at most their
    tickets, satisfies [fsem N] with the session types of its ends,
    each end at its tickets. *)
Theorem fsem_of_cost W N Θ e T c :
  Θ ; hc_empty ; [] ⊢^(∅, None) _{W,N} e : T ▷ c → tfree T →
  cr_tk Θ →
  fsem N (te_sty <$> Θ) (tkenv Θ) e.
Proof.
  intros Hty Hp HN n.
  pose proof (cost_fundamental _ _ _ _ _ _ _ _ _ Hty) as Hcs.
  assert (subst Var (emap id e) ∈ F^N _ n⟦RTy T ▷ c⟧((te_sty <$> Θ) ∪ ∅, tkenv Θ ∪ ∅)) as H.
  { apply (Hcs n id Var).
    apply envf_intro; [by apply thfuel_id|done|apply map_disjoint_empty_r]. }
  rewrite !map_union_empty, emap_id, subst_ids in H. eapply FuelE_thread; [exact Hp|exact H].
Qed.

(** The forwarder of S7.1 satisfies [fsem] at every bound. *)
Theorem fw_fsem N o m : fsem N {[o := S_fw]} {[o := (m, m)]} (fw o).
Proof.
  pose proof (fsem_of_cost W_fw N _ _ _ _ (fw_typed N o (pvar 0) m m) tfree_unit) as H.
  unfold tkenv in H. rewrite !map_fmap_singleton in H. apply H.
  intros o' te Hte. apply lookup_singleton_Some in Hte as [_ <-]. apply fle_refl.
Qed.
