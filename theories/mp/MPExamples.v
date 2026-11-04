(** * Examples of Mordido and Pérez through the general translation

    Each program is typed in [mtyped], the judgment of Mordido and Pérez
    on our terms, and [mp_deadlock_free] makes its translation deadlock
    free. No derivation in the static system is written by hand. *)

From stdpp Require Import base list numbers sets.
From LRGV Require Export mp.MPTranslate.

(** ** Tactics *)

Ltac msp := repeat (first [apply ms_nil | apply ms_none | apply ms_l | apply ms_r | (apply ms_un; [exact I|])]).

Definition okun (o : option mty) : Prop := match o with Some t => mun t | None => True end.

Fixpoint ouc (Γ : menv) (k : option nat) : Prop :=
  match Γ with
  | [] => True
  | o :: Γ' => (k = Some 0 ∨ okun o) ∧ ouc Γ' (match k with Some (S k') => Some k' | _ => None end)
  end.

Lemma ouc_sound Γ x : ouc Γ (Some x) → ∀ y t', y ≠ x → Γ !! y = Some (Some t') → mun t'.
Proof.
  assert (∀ Γ, ouc Γ None → ∀ y t', Γ !! y = Some (Some t') → mun t') as Hn.
  { intros Γ0. induction Γ0 as [|o Γ0 IH]; intros HH [|y] t' Hy; simpl in *; try done;
      destruct HH as [Ho H].
    - injection Hy as ->. by destruct Ho. 
    - by apply (IH H y). }
  revert x. induction Γ as [|o Γ IH]; intros x HH [|y] t' Hne Hy; simpl in *; try done;
    destruct HH as [Ho H].
  - injection Hy as ->. destruct Ho as [[=->]|Ho]; [done|exact Ho].
  - destruct x as [|x].
    + by apply (Hn Γ H y).
    + apply (IH x H y); [lia|done].
Qed.

Ltac onlyun := split; [reflexivity|]; apply ouc_sound; cbn; tauto.

Ltac allun :=
  let t := fresh "t" in let Ht := fresh "Ht" in
  intros t Ht; repeat (apply elem_of_cons in Ht as [Ht|Ht]; [first [discriminate Ht | injection Ht as ->; exact I]|]);
  by apply elem_of_nil in Ht.

Ltac vals :=
  match goal with
  | Hl : length ?v = _ |- _ =>
      destruct v as [|? [|? [|]]]; simpl in Hl; try discriminate;
      repeat (match goal with H : Forall _ (_ :: _) |- _ => inversion H; clear H; subst end)
  end.

Ltac pl :=
  let v := fresh "v" in let Hl := fresh "Hl" in let Hc := fresh "Hc" in
  let ρ := fresh "ρ" in let Hρ := fresh "Hρ" in
  intros v [Hl Hc] ρ Hρ; cbn in Hl, Hc;
  repeat (apply elem_of_cons in Hρ as [->|Hρ]); try (by apply elem_of_nil in Hρ);
  vals; cbn in *; lia.

Ltac pnt := let v := fresh "v" in let Hm := fresh "Hm" in intros v Hm; cbn; done.

Ltac pok :=
  split; [done|]; split; [repeat constructor|];
  let v := fresh "v" in let Hl := fresh "Hl" in let Hc := fresh "Hc" in
  intros v [Hl Hc]; cbn in Hl, Hc; vals; split; [done|]; repeat constructor; cbn in *; lia.

(** T-PApp with the instance given as equations. *)
Lemma m_app_poly' Θ Γ Γ1 Γ2 e1 e2 e1' e2' nv cs T σ V ef1 ef2 σs V' ef :
  msplit Γ Γ1 Γ2 → mtyped Θ Γ1 e1 (MPoly nv cs T σ V) ef1 e1' → pinst_ok Θ (PCtx nv cs) σs →
  mtyped Θ Γ2 e2 (msub σs T) ef2 e2' → plt Θ ef1 (envp Γ2) → pntop Θ ef2 →
  V' = msub σs V → ef = ef1 ++ ef2 ++ (psub σs <$> σ) →
  mtyped Θ Γ (App e1 e2) V' ef (App (App EForce e1') e2').
Proof. intros ?????? -> ->. by eapply m_app_poly. Qed.

(** ** Two streams in a cycle (Listings 1.1 and 1.2, p. 4)

      Stream    = µβ.∀^S ι. !^ι Unit; β
      client    : ∀p q ∈ (p < q < p + 2). Stream⟨p, 2⟩ →^{⊤,⊥}_un dual Stream⟨q, 2⟩ →^{p,⊤}_lin Unit
      client c1 c2 = let c1 = send () c1 in let (_, c2) = receive c2 in client{p+2, q+2} c1 c2
      newclient : ∀p q ∈ (q < p < q + 2). Stream⟨p, 2⟩ →^{⊤,⊥}_un dual Stream⟨q, 2⟩ →^{p,⊤}_lin Unit
      newclient c1 c2 = let (_, c2) = receive c2 in let c1 = send () c1 in newclient{p+2, q+2} c1 c2
      main = let (w1, r1) = new Stream 1 2 in let (w2, r2) = new Stream 2 2 in
             fork (λ_. client{1, 2} w1 r2); newclient{2, 1} w2 r1

    The paper types client with p only and reads the sequence of c2
    from the caller's Ψ (D3). Here client names the head q of c2 as
    well, with the interval q ∈ (p, p + 2) that its body needs. inst is
    implicit in send and receive, which read the head of the channel
    type. *)

Definition st0 : msty := MSnd (PI 0) MPUnit MVar.
Definition stream : msty := MRec st0.

Abbreviation cl_cs := [(PV 0 0, PV 1 0); (PV 1 0, PV 0 2)].
Abbreviation ncl_cs := [(PV 1 0, PV 0 0); (PV 0 0, PV 1 2)].

Definition cl_ty (cs : list (prio * prio)) : mty :=
  MPoly 2 cs (MChan false stream (PV 0 0) 2) []
    (MArr (MChan true stream (PV 1 0) 2) [PV 0 0] [PTop] MUnit).

Definition client : expr :=
  EBox (Lam (Lam (App (Lam (LetP (App ERecv (Var 1)) (App (App (Var 5) (Var 2)) (Var 0))))
                      (App ESend (Pair EUnit (Var 1)))))).

Definition newclient : expr :=
  EBox (Lam (Lam (LetP (App ERecv (Var 0))
                   (App (Lam (App (App (Var 5) (Var 0)) (Var 1)))
                        (App ESend (Pair EUnit (Var 3))))))).

Definition st_main : expr :=
  App (Lam (App (Lam
    (LetP (App ENew EUnit) (LetP (App ENew EUnit)
      (LetU (App ESpawn (Lam (App (App (Var 6) (Var 4)) (Var 1))))
            (App (App (Var 4) (Var 1)) (Var 2)))))) newclient)) client.

Lemma client_typed Θ : ∃ e', mtyped Θ [] client (cl_ty cl_cs) [] e'.
Proof.
  eexists. unfold client, cl_ty. eapply m_fix; [allun| |left; reflexivity].
  eapply m_lam; [done|].
  eapply m_sub; [|right; left; set_solver].
  (* let c1 = send () c1 in … *)
  eapply (m_let _ _ [None; Some _; Some _] [Some _; None; Some _]); [msp| | |].
  - eapply (m_send _ _ [None; None; Some _] [None; Some _; Some _] _ _ _ _ _ _ _ _ _ MPUnit);
      [msp|apply m_unit; allun|apply m_var; onlyun|reflexivity|done|done|pl|pl|pl|pl].
  - eapply (m_recv _ _ [None; Some _; None; Some _] [Some _; None; None; Some _]);
      [msp|apply m_var; onlyun|reflexivity|done|done| |pl|pl|pl].
    eapply (m_app _ _ [None; Some _; Some _; None; None; Some _] [Some _; None; None; None; None; Some _]);
      [msp| |apply m_var; onlyun| |].
    + eapply (m_app_poly' _ _ [None; None; None; None; None; Some _] [None; Some _; Some _; None; None; None]
                _ _ _ _ _ _ _ _ _ _ _ [PV 0 2; PV 1 2]);
        [msp|apply m_var; onlyun|pok|apply m_var; onlyun|pl|pnt|reflexivity|reflexivity].
    + pl.
    + pl.
  - pl.
Qed.

Lemma newclient_typed Θ : ∃ e', mtyped Θ [] newclient (cl_ty ncl_cs) [] e'.
Proof.
  eexists. unfold newclient, cl_ty. eapply m_fix; [allun| |left; reflexivity].
  eapply m_lam; [done|].
  eapply m_sub; [|right; left; set_solver].
  eapply (m_recv _ _ [Some _; None; None] [None; Some _; Some _]);
    [msp|apply m_var; onlyun|reflexivity|done|done| |pl|pl|pl].
  eapply (m_let _ _ [None; Some _; None; Some _; Some _] [Some _; None; None; None; Some _]); [msp| | |].
  - eapply (m_send _ _ [None; Some _; None; None; None] [None; None; None; Some _; Some _] _ _ _ _ _ _ _ _ _ MPUnit);
      [msp|apply m_unit; allun|apply m_var; onlyun|reflexivity|done|done|pl|pl|pl|pl].
  - eapply (m_app _ _ [Some _; None; None; None; None; Some _] [None; Some _; None; None; None; None]);
      [msp| |apply m_var; onlyun| |].
    + eapply (m_app_poly' _ _ [None; None; None; None; None; Some _] [Some _; None; None; None; None; None]
                _ _ _ _ _ _ _ _ _ _ _ [PV 0 2; PV 1 2]);
        [msp|apply m_var; onlyun|pok|apply m_var; onlyun|pl|pnt|reflexivity|reflexivity].
    + pl.
    + pl.
  - pl.
Qed.

(** Weakening by a spent entry at the end of the environment. *)
Lemma msplit_snoc Γ Γ1 Γ2 : msplit Γ Γ1 Γ2 → msplit (Γ ++ [None]) (Γ1 ++ [None]) (Γ2 ++ [None]).
Proof. induction 1; simpl; constructor; auto. constructor. Qed.

Lemma envp_snoc Γ : envp (Γ ++ [None]) = envp Γ.
Proof. induction Γ as [|[t|] Γ IH]; simpl; by rewrite ?IH. Qed.

Lemma snoc_in (Γ : menv) t : Some t ∈ Γ ++ [None] → Some t ∈ Γ.
Proof. rewrite elem_of_app. intros [H|H]; [done|]. apply list_elem_of_singleton in H. done. Qed.

Lemma mtyped_snoc Θ Γ e T ef e' : mtyped Θ Γ e T ef e' → mtyped Θ (Γ ++ [None]) e T ef e'.
Proof.
  induction 1.
  all: try (econstructor; (eauto using msplit_snoc || (rewrite ?envp_snoc; eauto)); fail).
  all: try (apply m_var; destruct H as [Hx Hu]; split; [by apply lookup_app_l_Some|];
    intros y t' Hy Hl; apply (Hu y); [done|]; apply lookup_app_Some in Hl as [Hl|[_ Hl]]; [done|];
    apply list_lookup_singleton_Some in Hl as [_ [=]]; fail).
  all: try (apply m_unit; intros t Ht; by apply H, snoc_in).
  all: try (rewrite <-envp_snoc; apply m_lam; [by rewrite envp_snoc|done]; fail).
  all: try (eapply m_app; [by apply msplit_snoc|done|done|by rewrite envp_snoc|done]; fail).
  all: try (eapply m_app_poly; [by apply msplit_snoc|done|done|done|by rewrite envp_snoc|done]; fail).
  all: try (eapply m_fix; [intros t Ht; by apply H, snoc_in|exact IHmtyped|done]; fail).
  all: try (eapply m_new; [exact H|exact H0|exact IHmtyped]; fail).
  all: try (eapply m_let; [by apply msplit_snoc|done|done|by rewrite envp_snoc]; fail).
  all: try (eapply m_letu; [by apply msplit_snoc|done|done|by rewrite envp_snoc]; fail).
  all: try (eapply m_send; try done; [by apply msplit_snoc|by rewrite envp_snoc]; fail).
  all: try (eapply m_recv; try done; [by apply msplit_snoc|by rewrite envp_snoc]; fail).
  all: try (eapply m_match; try done; [by apply msplit_snoc|by rewrite envp_snoc]; fail).
Qed.

Lemma st_main_typed : ∃ ef e', mtyped pc0 [] st_main MUnit ef e'.
Proof.
  destruct (client_typed pc0) as [ec Hc]. destruct (newclient_typed pc0) as [en Hn].
  do 2 eexists. unfold st_main.
  eapply (m_let _ _ [] []); [msp|exact Hc| |pl].
  eapply (m_let _ _ [None] [Some _]); [msp|exact (mtyped_snoc _ _ _ _ _ _ Hn)| |pl].
  eapply (m_new _ _ _ _ stream (PZ 1) 2); [done|done|].
  eapply (m_new _ _ _ _ stream (PZ 2) 2); [done|done|].
  eapply (m_letu _ _ [Some _; None; None; Some _; None; Some _] [None; Some _; Some _; None; Some _; None]);
    [msp| | |].
  - eapply m_fork. eapply m_lam; [done|].
    eapply (m_app _ _ [Some _; None; None; None; Some _; None; Some _] [None; Some _; None; None; None; None; None]);
      [msp| |apply m_var; onlyun| |].
    + eapply (m_app_poly' _ _ [Some _; None; None; None; None; None; Some _] [None; None; None; None; Some _; None; None]
                _ _ _ _ _ _ _ _ _ _ _ [PZ 1; PZ 2]);
        [msp|apply m_var; onlyun|pok|apply m_var; onlyun|pl|pnt|reflexivity|reflexivity].
    + pl.
    + pl.
  - eapply (m_app _ _ [None; Some _; None; None; Some _; None] [None; None; Some _; None; None; None]);
      [msp| |apply m_var; onlyun| |].
    + eapply (m_app_poly' _ _ [None; None; None; None; Some _; None] [None; Some _; None; None; None; None]
                _ _ _ _ _ _ _ _ _ _ _ [PZ 2; PZ 1]);
        [msp|apply m_var; onlyun|pok|apply m_var; onlyun|pl|pnt|reflexivity|reflexivity].
    + pl.
    + pl.
  - pl.
Qed.

Theorem st_mp_deadlock_free : ∃ ef e', mtyped pc0 [] st_main MUnit ef e' ∧ deadlock_free (∅, {[+ e' +]}).
Proof.
  destruct st_main_typed as (ef & e' & H). exists ef, e'. split; [done|]. by eapply mp_deadlock_free.
Qed.
