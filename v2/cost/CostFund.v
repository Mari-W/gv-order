(** * The cost half of the merged judgment (stage S7, A.3)

      Θ ; Γ ; Δ ⊢^F _{W,N} e : T^a ▷ c ; ϑ  ⟹  Θ ; Δ ⊨^N e : T^a ▷ c ; ϑ    [cost_fundamental]

    by induction on the derivation, one rule of cost/CostRules.v per
    case. E-Abs, E-Box and E-SpawnLam take the facts of their term from
    [typed_tfacts]. [fsem_of_cost] turns a closed thread into [fsem],
    the premise LF-Term adds to P-Term: every end starts at N, at a
    ticket count that meets ϑ at reserve 0. [fw_fsem] is the forwarder of
    S7.1, which now has its [fsem]. *)

From GV Require Export cost.CostRules cost.Forwarder.

Theorem cost_fundamental W N Θ Γ Δ F e T a c ϑ :
  Θ ; Γ ; Δ ⊢^F _{W,N} e : T^a ▷ c ; ϑ → Θ ; Δ ⊨^N e : T^a ▷ c ; ϑ.
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
  - by apply cost_e_inj1.
  - by apply cost_e_inj2.
  - by eapply cost_e_case.
  - eapply cost_e_box; [|done|done]. eapply (typed_tfacts _ _ _ _ _ (∅, None)). by eapply e_box.
  - by eapply cost_e_force.
  - by eapply cost_e_send.
  - by eapply cost_e_recv.
  - by eapply cost_e_close.
  - by eapply cost_e_select.
  - by eapply cost_e_branch.
  - by eapply cost_e_link.
  - eapply cost_e_spawn_lam; [|done|done|done].
    assert (tfacts Θ Δ (ESpawn (Lam e))) as Ht
      by (eapply (typed_tfacts _ _ _ _ _ (∅, None)); eapply e_spawn_lam; eassumption).
    exact Ht.
  - by eapply cost_e_spawn.
  - by apply cost_e_new.
  - by eapply cost_e_new_at.
  - by eapply cost_e_sub.
  - by eapply cost_e_weak.
  - by apply cost_e_contract.
  - by eapply cost_e_pack.
  - by eapply cost_e_open.
Qed.

Lemma thfuel_id N Θ :
  (∀ o te, Θ !! o = Some te → fle (te_cr te) N) →
  thfuel Θ id (te_sty <$> Θ) (const N <$> (te_sty <$> Θ)).
Proof.
  intros HN. split_and!.
  - by intros o1 o2 _ _.
  - rewrite dom_fmap_L. apply set_eq. intros o. rewrite elem_of_map. split; [intros; by exists o|by intros (? & -> & ?)].
  - by rewrite !dom_fmap_L.
  - intros o te Hte. simpl. rewrite !lookup_fmap, Hte. split; [done|]. eexists. split; [done|]. exact (HN o te Hte).
Qed.

(** A closed thread typed at N, whose ends have credits at most N and
    whose transformer some ticket count meets at reserve 0, satisfies
    [fsem N] with the session types of its ends. *)
Theorem fsem_of_cost W N Θ e T a c ϑ tk :
  Θ ; hc_empty ; [] ⊢^(∅, None) _{W,N} e : T^a ▷ c ; ϑ → prim T →
  (∀ o te, Θ !! o = Some te → fle (te_cr te) N) → meets ϑ 0 tk →
  fsem N (te_sty <$> Θ) e.
Proof.
  intros Hty Hp HN Hm. exists tk. intros n.
  pose proof (cost_fundamental _ _ _ _ _ _ _ _ _ _ _ Hty) as Hcs.
  assert (subst Var (emap id e) ∈ F^N _ n⟦RTy T a ▷ c ; 0⟧((te_sty <$> Θ) ∪ ∅,
            (const N <$> (te_sty <$> Θ)) ∪ ∅, tk)) as H.
  { apply (Hcs N n id Var); [apply rle_refl| |exact Hm].
    apply envf_intro; [by apply thfuel_id|done|apply map_disjoint_empty_r]. }
  rewrite !map_union_empty, emap_id, subst_ids in H. eapply FuelE_thread; [exact Hp|exact H].
Qed.

(** The forwarder of S7.1 satisfies [fsem] at every refill. *)
Theorem fw_fsem N o : fsem N {[o := S_fw]} (fw o).
Proof.
  pose proof (fsem_of_cost W_fw N _ _ _ _ _ _ 0 (fw_typed N o (pvar 0)) prim_unit) as H.
  rewrite map_fmap_singleton in H. apply H; [|apply fw_tix_met].
  intros o' te Hte. apply lookup_singleton_Some in Hte as [_ <-]. apply fle_refl.
Qed.
