(** * The logical relation (Fig. 5, §7) and semantic typing (§3, §8)

    Three step-indexed layers, indexed by a world W (Worlds.v):
      V^W_n⟦Θ ⊢ T⟧      values      ([Vrel])
      E^W_n⟦Θ ⊢ T ≺ F⟧  terms       ([Erel]), F a frame of points
      P^W_n⟦Σ ⊢ T⟧      processes   ([Prel])
    Values and terms are indexed by term-level environments Θ, which
    may hold both ends of a channel; processes by process-level Σ.

    The step-index recursion is implemented by course-of-values
    recursion on n: [levels n] is (structurally in n) the family of all
    levels below n, [mk_level below n] builds level n from it, and
    [level_at n] projects the actual level n. Later proofs only use the
    equations [level_at_eq] and [levels_at], never the encoding.

    "Σ = Σ1, c : S@k" from the paper is rendered as
    Σ = <[c := (S, k)]> Σ1 together with c ∉ dom Σ1, and at the term
    level as [tenv_ext Θ1 c (S, k) Θ].

    Lemma 3.5 needs the paper's argument "if p is not irreducible then
    it has some transition". That is [proc_progress], proved by
    deciding reducibility rather than by excluded middle, so the
    development is closed under the global context. *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export Semantics Safety Swap Types Coequal Worlds Ready Typing.

(** ** The three relations, level by level *)

(** A world read on type points, through the embedding. *)
Definition tw_eq (W : world) (x y : tpoint) : Prop := w_eq W (emb x) (emb y).
Definition tw_lt (W : world) (x y : tpoint) : Prop := w_lt W (emb x) (emb y).

Record level := Level {
  lV : world → tenv → ty → expr → Prop;
  lE : world → tenv → ty → gset point → expr → Prop;
  lP : world → senv → ty → proc → Prop
}.

(** Value relation at level n, given the family [below] of levels < n.
    Recursive on the type; lower levels are accessed through [below]
    (the ∀ j < n quantification in the ⊸ and □ cases).

    - V-Chan: the channel's current instant c@k is an alias of the
      point the type names.
    - V-Abs: the closure holds only above its lower point
      ({λ} ≼ heads(Θ)); applied in any future world to an argument,
      it is a good term under any frame above its upper point. The
      argument's environment may hold the other ends of channels the
      closure holds ([tenv_comp]).
    - V-Const: the constant's signature is read in W.
    - V-Box / V-All: ∀ appears only under □; a box is good at every
      instance of its point variables, in every future world. *)
Fixpoint Vdef (below : nat → level) (n : nat)
    (W : world) (Θ : tenv) (T : ty) (v : expr) {struct T} : Prop :=
  match T with
  | TUnit => Θ = ∅ ∧ v = EUnit
  | TSess s x =>
      ∃ c s0 k, v = Chan c ∧ Θ = {[c := One (s0, k)]} ∧ seq s0 s ∧
        w_eq W (pt_chan c k) (emb x)
  | TLolli ub lb T1 U =>
      (∃ eb, v = Lam eb ∧ fchans eb = dom Θ ∧ lb_below W (emb <$> lb) (tenv_heads Θ) ∧
         ∀ W' j Θ' Θ'' w F, wext W W' → j < n →
           tenv_comp Θ'' Θ Θ' →
           lV (below j) W' Θ' T1 w →
           ub_below W' (emb <$> ub) F →
           lE (below j) W' Θ'' U F (subst1 w eb))
      ∨ (∃ k T0, v = Konst k ∧ Θ = ∅ ∧ konst_ty (tw_eq W) (tw_lt W) k T0 ∧
           teq T0 (TLolli ub lb T1 U))
  | TProd T1 U =>
      ∃ v1 v2 Θ1 Θ2, v = Pair v1 v2 ∧ tenv_comp Θ Θ1 Θ2 ∧
        Vdef below n W Θ1 T1 v1 ∧ Vdef below n W Θ2 U v2
  | TSum T1 U =>
      (∃ v', v = Inj1 v' ∧ Vdef below n W Θ T1 v')
      ∨ (∃ v', v = Inj2 v' ∧ Vdef below n W Θ U v')
  | TBox m T1 =>
      (* as in the paper's V⟦□T⟧ = {!e | fix x.e ∈ E⟦T ≺ ∅⟧}, at every
         instance of the ∀ and in every future world; forcing always
         takes a β step, so only lower indices are constrained *)
      Θ = ∅ ∧ ∃ eb, v = EBox eb ∧ fchans eb = ∅ ∧
        ∀ W' j xs, wext W W' → j < n → length xs = m →
          lE (below j) W' ∅ (ty_inst xs T1) ∅ (subst1 (EBox eb) eb)
  end.

(** Term relation at level n (n = S n' in the non-trivial case), given
    [below] and the level-n value relation [Vn]. A term that can step
    must be ready and keep its offered entries below the frame F; one
    case per label shape of the transition. The new case is guarded by
    freshness of the new channel: new labels exist for every name c,
    but only fresh ones are process-level enabled. *)
Definition Edef (below : nat → level) (Vn : world → tenv → ty → expr → Prop)
    (n : nat) (W : world) (Θ : tenv) (T : ty) (F : gset point) (e : expr)
    : Prop :=
  match n with
  | 0 => True
  | S n' =>
      (irred e → Vn W Θ T e) ∧                         (* E-Stop *)
      (¬ irred e → ready_t W Θ e ∧ frame_t W Θ e F) ∧  (* E-Step *)
      (∀ α e', tstep e α e' →
        match α with
        | LBeta =>                                     (* O-Beta *)
            lE (below n') W Θ T F e'
        | LNew c =>                                    (* O-New *)
            c ∉ dom Θ → NChan c ∉ w_names W →
            ∃ s s' W', sdual s s' ∧ wext_fresh W {[NChan c]} W' ∧
              lE (below n') W' (<[c := Both (s, 0) (s', 0)]> Θ) T F e'
        | LSpawn w =>                                  (* O-Spawn *)
            ∃ Θ1 Θ2 ub lb, tenv_comp Θ Θ1 Θ2 ∧
              Vn W Θ1 (TLolli ub lb TUnit TUnit) w ∧
              lE (below n') W Θ2 T F e'
        | LSess (SRecv c w) =>                         (* O-Recv *)
            ∃ Θ1 m U s k,
              tenv_hd Θ c (SRcv m U s) k Θ1 ∧
              ∀ W' j Θ2 Θ12 xs, wext W W' → j ≤ n' →
                tenv_comp Θ12 Θ1 Θ2 →
                slot_aliases (w_eq W') xs m (pt_chan c k) →
                lV (below j) W' Θ2 (ty_inst xs U) w →
                ∃ Θ', tenv_ext Θ12 c (s, S k) Θ' ∧
                  lE (below j) W' Θ' T F e'
        | LSess (SSend c w) =>                         (* O-Send *)
            ∃ Θr Θ1 Θ2 m U s k Θ' xs,
              tenv_hd Θ c (SSnd m U s) k Θr ∧ tenv_comp Θr Θ1 Θ2 ∧
              slot_aliases (w_eq W) xs m (pt_chan c k) ∧
              Vn W Θ2 (ty_inst xs U) w ∧
              tenv_ext Θ1 c (s, S k) Θ' ∧
              lE (below n') W Θ' T F e'
        | LSess (SClos c) =>                           (* O-Close *)
            ∃ Θ1 k, tenv_hd Θ c SEnd k Θ1 ∧ lE (below n') W Θ1 T F e'
        | LSess (SLink cd) =>                          (* O-Link *)
            (* c = d is a self-link: Θ holds both ends of c, and both
               entries leave *)
            ∃ c d Θ1 Θm sc sd kc kd,
              cd = {[c; d]} ∧
              tenv_ext Θ1 d (sd, kd) Θm ∧ tenv_ext Θm c (sc, kc) Θ ∧
              sdual sd sc ∧ w_eq W (pt_chan c kc) (pt_chan d kd) ∧
              lE (below n') W Θ1 T F e'
        end)
  end.

(** ** Messages at the process level

    Q-Recv: the payload's environment Θ2 is term-level, so a message
    may carry both ends of one channel. B ([recv_back]) is the set of
    channels the receiver ends up holding both ends of: those whose
    other end it already holds, and those whose both ends arrive in
    one message. They are restricted in the continuation. Every other
    received channel is fresh for the world, so it inherits no facts
    of an old name. *)

Definition tenv_ones (Θ : tenv) : senv :=
  omap (λ o, match o with One e => Some e | Both _ _ => None end) Θ.

Definition recv_back (Σr : senv) (Θ2 : tenv) : gset chan :=
  (dom Θ2 ∩ dom Σr) ∪ (dom Θ2 ∖ dom (tenv_ones Θ2)).

Definition recv_ok (W : world) (Σr : senv) (Θ2 : tenv) : Prop :=
  senv_dual_on Σr (tenv_ones Θ2) ∧ tenv_dual Θ2 ∧
  (dom Θ2 ∖ dom (tenv_ones Θ2)) ## dom Σr ∧
  (∀ c, c ∈ dom (tenv_ones Θ2) → c ∉ dom Σr → NChan c ∉ w_names W).

Definition recv_env (Σr : senv) (Θ2 : tenv) : senv :=
  (Σr ∖ tenv_ones Θ2) ∪ (tenv_ones Θ2 ∖ Σr).

(** Q-Send: the restricted channels a message carries. Θe holds the
    ends that leave with the message (one end, or both), Σe the ends
    that stay, dual at equal counts. *)
Definition send_split (Σe : senv) (Θe : tenv) : Prop :=
  dom Σe ⊆ dom Θe ∧
  ∀ r o, Θe !! r = Some o →
    match o with
    | One e' => ∃ e, Σe !! r = Some e ∧ e.2 = e'.2 ∧ sdual e.1 e'.1
    | Both e1 e2 => Σe !! r = None ∧ e1.2 = e2.2 ∧ sdual e1.1 e2.1
    end.

(** ** α-variants

    Restricted names are bound. An α-variant of a process renames its
    restricted names, one at a time, to names that capture nothing:
    absent from the process, outside the interface Σ, and unknown to
    the world before the step (decisions I1, J1): the world after the
    step may then carry facts about them, e.g. about a renamed new
    channel. *)

Definition wfresh (W : world) (c : chan) : Prop :=
  ∀ p, p ∈ w_names W → pn_root p ≠ NChan c.

Inductive walpha (W : world) (Σ : senv) : proc → proc → Prop :=
  | walpha_refl p : walpha W Σ p p
  | walpha_step p q a b :
      a ∈ p.1 → b ∉ p.1 → b ∉ echans p.2 → b ∉ dom Σ → wfresh W b →
      walpha W Σ (pswap a b p) q → walpha W Σ p q.

Lemma walpha_alpha W Σ p q : walpha W Σ p q → alpha p q.
Proof. induction 1; econstructor; eauto. Qed.

(** Process relation at level n. Differences from the term relation:

    - Restricted names are bound: every step obligation is stated for
      some α-variant of the successor ([walpha]), so facts a world
      states about restricted names never pin the process, and the two
      orientations of an internal link are the same obligation.
    - Q-Tau: the world may grow, but only invisibly: W ⊑ W′ adds facts
      only about names restricted before the step or in the chosen
      α-variant ([wext_inv]). Only successors whose restricted
      channels stay clear of Σ are constrained (the paper's implicit
      "Σ and C do not share channels"). The paper's Q-Tau is W′ = W
      with the successor itself.
    - Q-Recv: the received channels are fresh for the restricted set
      ([dom Θ2 ## p.1]). Channels B the receiver ends up holding both
      ends of ("migration", or both ends in one message) come back:
      the obligation is stated for the successor with B restricted,
      and their entries leave both environments. If the carrier c is
      in B, its continuation entry leaves as well. The other received
      channels are fresh for W ([recv_ok]). The obligation holds for an
      α-variant of the successor ([walpha]): restricted names are
      bound, so facts the environment's W′ states about them do not
      pin the process.
    - Q-Send: the restricted channels the message carries,
      dom Θe = fchans w ∩ C, split into the ends that leave with the
      message (Θe, possibly both ends) and the ends that stay (Σe). *)
Definition Pdef (below : nat → level) (Vn : world → tenv → ty → expr → Prop)
    (n : nat) (W : world) (Σ : senv) (T : ty) (p : proc) : Prop :=
  match n with
  | 0 => True
  | S n' =>
      (pirred p →                                      (* P-Stop *)
        ∃ v E, p = (∅, {[+ v +]} ⊎ E) ∧ is_val v ∧ Vn W (tenv_of Σ) T v ∧
               (∀ e, e ∈ E → e = EUnit)) ∧
      (¬ pirred p → ready_p W Σ p) ∧                   (* P-Step *)
      (∀ π p', proc_step p π p' →
        match π with
        | PTau =>                                      (* Q-Tau *)
            p'.1 ## dom Σ →
            ∃ W' q, walpha W Σ p' q ∧ wext_inv W (set_map NChan (p.1 ∪ q.1)) W' ∧
              lP (below n') W' Σ T q
        | PSess (SRecv c w) =>                         (* Q-Recv *)
            ∃ Σ1 m U s k,
              senv_hd Σ c (SRcv m U s) k Σ1 ∧ c ∉ dom Σ1 ∧
              ∀ W' j Θ2 xs, wext W W' → j ≤ n' → dom Θ2 ## p.1 →
                recv_ok W (<[c := (s, S k)]> Σ1) Θ2 →
                slot_aliases (w_eq W') xs m (pt_chan c k) →
                lV (below j) W' Θ2 (ty_inst xs U) w →
                ∃ q, walpha W (recv_env (<[c := (s, S k)]> Σ1) Θ2)
                 (p'.1 ∪ recv_back (<[c := (s, S k)]> Σ1) Θ2, p'.2) q ∧
                  lP (below j) W' (recv_env (<[c := (s, S k)]> Σ1) Θ2) T q
        | PSess (SSend c w) =>                         (* Q-Send *)
            ∃ Σ0 Σv m U s k (Σe : senv) (Θe : tenv) xs,
              senv_hd Σ c (SSnd m U s) k (Σ0 ∪ Σv) ∧
              Σ0 ##ₘ Σv ∧ c ∉ dom Σ0 ∧ c ∉ dom Σv ∧
              dom Θe = fchans w ∩ p.1 ∧ send_split Σe Θe ∧
              dom Θe ## dom Σ ∧
              slot_aliases (w_eq W) xs m (pt_chan c k) ∧
              Vn W (tenv_of Σv ∪ Θe) (ty_inst xs U) w ∧
              ∃ q, walpha W (<[c := (s, S k)]> (Σ0 ∪ Σe)) p' q ∧
                lP (below n') W (<[c := (s, S k)]> (Σ0 ∪ Σe)) T q
        | PSess (SClos c) =>                           (* Q-Close *)
            ∃ Σ1 k, senv_hd Σ c SEnd k Σ1 ∧ c ∉ dom Σ1 ∧
              ∃ q, walpha W Σ1 p' q ∧ lP (below n') W Σ1 T q
        | PSess (SLink cd) =>                          (* Q-Link *)
            (* c = d cannot reach the interface: Σ holds one end per
               channel *)
            ∃ c d Σ1 sc sd kc kd,
              cd = {[c; d]} ∧ c ≠ d ∧
              Σ = <[c := (sc, kc)]> (<[d := (sd, kd)]> Σ1) ∧
              c ∉ dom Σ1 ∧ d ∉ dom Σ1 ∧
              sdual sd sc ∧ w_eq W (pt_chan c kc) (pt_chan d kd) ∧
              ∃ q, walpha W Σ1 p' q ∧ lP (below n') W Σ1 T q
        end)
  end.

Definition mk_level (below : nat → level) (n : nat) : level :=
  {| lV := Vdef below n;
     lE := Edef below (Vdef below n) n;
     lP := Pdef below (Vdef below n) n |}.

Definition dummy_level : level :=
  {| lV := λ _ _ _ _, False; lE := λ _ _ _ _ _, False;
     lP := λ _ _ _ _, False |}.

(** [levels n j] is level j, for every j < n (garbage above). *)
Fixpoint levels (n : nat) : nat → level :=
  match n with
  | 0 => λ _, dummy_level
  | S n' => λ j, if decide (j < n') then levels n' j else mk_level (levels n') n'
  end.

Definition level_at (n : nat) : level := levels (S n) n.

Definition Vrel (n : nat) : world → tenv → ty → expr → Prop := lV (level_at n).
Definition Erel (n : nat) : world → tenv → ty → gset point → expr → Prop :=
  lE (level_at n).
Definition Prel (n : nat) : world → senv → ty → proc → Prop := lP (level_at n).

(** ** Interface to the encoding *)

Lemma level_at_eq n : level_at n = mk_level (levels n) n.
Proof. unfold level_at. simpl. by destruct (decide (n < n)); [lia|]. Qed.

Lemma levels_at n j : j < n → levels n j = level_at j.
Proof.
  revert j. induction n as [|n' IH]; intros j Hj; [lia|].
  simpl. destruct (decide (j < n')) as [H|H].
  - by apply IH.
  - assert (j = n') as -> by lia. by rewrite level_at_eq.
Qed.

Lemma Erel_0 W Θ T F e : Erel 0 W Θ T F e.
Proof. unfold Erel. rewrite level_at_eq. simpl. exact I. Qed.

Lemma Prel_0 W Σ T p : Prel 0 W Σ T p.
Proof. unfold Prel. rewrite level_at_eq. simpl. exact I. Qed.

(** Members of the value relation are values. *)
Lemma Vdef_val below n W Θ T v : Vdef below n W Θ T v → is_val v.
Proof.
  induction T in Θ, v |- *; simpl.
  - by intros [_ ->].
  - by intros [(eb & -> & _ & _)|(k & T0 & -> & _)].
  - intros (v1 & v2 & Θ1 & Θ2 & -> & _ & H1 & H2).
    simpl. apply andb_True. eauto.
  - intros [(v' & -> & H)|(v' & -> & H)]; simpl; eauto.
  - by intros (-> & eb & -> & _).
  - by intros (c & s0 & k & -> & _).
Qed.

Lemma Vrel_val n W Θ T v : Vrel n W Θ T v → is_val v.
Proof. unfold Vrel. rewrite level_at_eq. apply Vdef_val. Qed.

(** Values in the relation mention exactly the channels of Θ: the
    linear discipline has no weakening, so a value owns precisely the
    channels occurring in it. Tightness (⊇) is essential for the
    compositionality of outputs — a component's decomposition may not
    park a restricted channel inside a value that never mentions it,
    or the channel's end would leak out of the composite unaccounted. *)
Lemma Vdef_fchans below n W Θ T v :
  Vdef below n W Θ T v → fchans v = dom Θ.
Proof.
  induction T in Θ, v |- *; simpl.
  - intros [-> ->]. simpl. by rewrite dom_empty_L.
  - intros [(eb & -> & Hsup & _)|(k & T0 & -> & -> & _)]; simpl;
      [done|by rewrite dom_empty_L].
  - intros (v1 & v2 & Θ1 & Θ2 & -> & [Hj _] & H1 & H2). simpl.
    rewrite (IHT1 _ _ H1), (IHT2 _ _ H2). by rewrite (tenv_join_dom _ _ _ Hj).
  - intros [(v' & -> & H)|(v' & -> & H)]; simpl; eauto.
  - intros (-> & eb & -> & Hfc & _). simpl.
    rewrite Hfc. by rewrite dom_empty_L.
  - intros (c & s0 & k & -> & -> & _). simpl. by rewrite dom_singleton_L.
Qed.

Lemma Vrel_fchans n W Θ T v : Vrel n W Θ T v → fchans v = dom Θ.
Proof. unfold Vrel. rewrite level_at_eq. apply Vdef_fchans. Qed.

(** Values of primitive type own no channels. *)
Lemma Vdef_prim_empty below n W Θ T v :
  prim T → Vdef below n W Θ T v → Θ = ∅.
Proof.
  intros Hp. revert Θ v. induction Hp; simpl.
  - by intros ? ? [-> _].
  - intros Θ v (v1 & v2 & Θ1 & Θ2 & -> & [Hj _] & H1 & H2).
    rewrite (IHHp1 _ _ H1), (IHHp2 _ _ H2) in Hj.
    by apply tenv_join_empty.
  - intros Θ v [(v' & -> & H)|(v' & -> & H)]; eauto.
  - by intros Θ v (-> & _).
Qed.

Lemma Vrel_prim_empty n W Θ T v : prim T → Vrel n W Θ T v → Θ = ∅.
Proof. unfold Vrel. rewrite level_at_eq. apply Vdef_prim_empty. Qed.

(** TLR-VAL: values in V are in E, under any frame: a value does not
    step, so neither readiness nor the frame is asked of it. *)
Lemma Vrel_Erel n W Θ T F v : Vrel n W Θ T v → Erel n W Θ T F v.
Proof.
  intros HV. assert (is_val v) by eauto using Vrel_val.
  destruct n as [|n']; [apply Erel_0|].
  unfold Erel. rewrite level_at_eq. simpl. split_and!.
  - intros _. unfold Vrel in HV. rewrite level_at_eq in HV. exact HV.
  - intros Hirr. exfalso. by apply Hirr, val_irred.
  - intros α e' Hst. exfalso. eauto using val_no_tstep.
Qed.

(** Terminated shape of irreducible related processes. *)
Lemma Prel_S_irred n W Σ T p :
  Prel (S n) W Σ T p → pirred p →
  ∃ v E, p = (∅, {[+ v +]} ⊎ E) ∧ is_val v ∧ Vrel (S n) W (tenv_of Σ) T v ∧
         (∀ e, e ∈ E → e = EUnit).
Proof.
  unfold Prel, Vrel. rewrite level_at_eq. simpl.
  intros (H1 & _) Hirr. exact (H1 Hirr).
Qed.

(** τ steps decrease the index by one, may grow the world invisibly,
    and relate an α-variant of the successor (for τ successors whose
    restricted channels stay clear of Σ). *)
Lemma Prel_S_tau n W Σ T p p' :
  Prel (S n) W Σ T p → preduction p p' → p'.1 ## dom Σ →
  ∃ W' q, walpha W Σ p' q ∧ wext_inv W (set_map NChan (p.1 ∪ q.1)) W' ∧
    Prel n W' Σ T q.
Proof.
  unfold Prel at 1. rewrite level_at_eq. simpl.
  intros (_ & _ & Hstep) Hred Hdisj.
  specialize (Hstep _ _ Hred). simpl in Hstep. specialize (Hstep Hdisj).
  destruct (decide (n < n)); [lia|].
  unfold Prel. rewrite level_at_eq. exact Hstep.
Qed.

(** With an empty session environment, no session-labelled transition
    is allowed by the relation. *)
Lemma Prel_S_empty_no_sess n W T p σ p' :
  Prel (S n) W ∅ T p → proc_step p (PSess σ) p' → False.
Proof.
  unfold Prel. rewrite level_at_eq. simpl.
  intros (_ & _ & Hstep) Hp. specialize (Hstep _ _ Hp).
  destruct σ as [c w|c w|c|cd]; simpl in Hstep.
  - destruct Hstep as (Σ1 & m & U & s & k & Heq & _).
    exact (senv_hd_not_empty _ _ _ _ Heq).
  - destruct Hstep as (?&?&?&?&?&?&?&?&?&Heq&_).
    exact (senv_hd_not_empty _ _ _ _ Heq).
  - destruct Hstep as (Σ1 & k & Heq & _).
    exact (senv_hd_not_empty _ _ _ _ Heq).
  - (* forwarding: both ends must be in Σ *)
    destruct Hstep as (c & d & Σ1 & sc & sd & kc & kd & _ & _ & Heq & _).
    exact (insert_non_empty _ _ _ (eq_sym Heq)).
Qed.


(** ** Characteristic equations

    Encoding-free unfoldings of the three relations: [Vrel_*_iff] per
    type constructor, [Erel_S_iff] / [Prel_S_iff] per positive step
    index (via the case predicates [Ecase] / [Pcase]). All later
    proofs go through these and never touch [levels]/[level_at]. *)

Lemma Vrel_unit_iff n W Θ v : Vrel n W Θ TUnit v ↔ Θ = ∅ ∧ v = EUnit.
Proof. unfold Vrel. rewrite (level_at_eq n). cbn [mk_level lV Vdef]. done. Qed.

Lemma Vrel_sess_iff n W Θ s x v :
  Vrel n W Θ (TSess s x) v ↔
  ∃ c s0 k, v = Chan c ∧ Θ = {[c := One (s0, k)]} ∧ seq s0 s ∧
    w_eq W (pt_chan c k) (emb x).
Proof. unfold Vrel. rewrite (level_at_eq n). cbn [mk_level lV Vdef]. done. Qed.

Lemma Vrel_prod_iff n W Θ T U v :
  Vrel n W Θ (TProd T U) v ↔
  ∃ v1 v2 Θ1 Θ2, v = Pair v1 v2 ∧ tenv_comp Θ Θ1 Θ2 ∧
    Vrel n W Θ1 T v1 ∧ Vrel n W Θ2 U v2.
Proof. unfold Vrel. rewrite (level_at_eq n). cbn [mk_level lV Vdef]. done. Qed.

Lemma Vrel_sum_iff n W Θ T U v :
  Vrel n W Θ (TSum T U) v ↔
  (∃ v', v = Inj1 v' ∧ Vrel n W Θ T v')
  ∨ (∃ v', v = Inj2 v' ∧ Vrel n W Θ U v').
Proof. unfold Vrel. rewrite (level_at_eq n). cbn [mk_level lV Vdef]. done. Qed.

Lemma Vrel_box_iff n W Θ m T v :
  Vrel n W Θ (TBox m T) v ↔
  Θ = ∅ ∧ ∃ eb, v = EBox eb ∧ fchans eb = ∅ ∧
    ∀ W' j xs, wext W W' → j < n → length xs = m →
      Erel j W' ∅ (ty_inst xs T) ∅ (subst1 (EBox eb) eb).
Proof.
  unfold Vrel, Erel. rewrite (level_at_eq n). cbn [mk_level lV Vdef].
  apply and_iff_compat_l.
  split; intros (eb & -> & Hfc & H); exists eb; (split_and!; [done..|]);
    intros W' j xs HW Hj Hxs.
  - rewrite <-(levels_at n j Hj). by apply H.
  - rewrite (levels_at n j Hj). by apply H.
Qed.

Lemma Vrel_box_empty n W Θ m T v : Vrel n W Θ (TBox m T) v → Θ = ∅.
Proof. intros [-> _]%Vrel_box_iff. done. Qed.

(** Values at an unlimited type own no channels. One case per
    modality; the structural rules only ever need this much. *)
Lemma Vrel_unl_empty n W Θ T v : unlimited T → Vrel n W Θ T v → Θ = ∅.
Proof. destruct T; try done. intros _. apply Vrel_box_empty. Qed.

Lemma Vrel_lolli_iff n W Θ ub lb T U v :
  Vrel n W Θ (TLolli ub lb T U) v ↔
  (∃ eb, v = Lam eb ∧ fchans eb = dom Θ ∧ lb_below W (emb <$> lb) (tenv_heads Θ) ∧
     ∀ W' j Θ' Θ'' w F, wext W W' → j < n →
       tenv_comp Θ'' Θ Θ' →
       Vrel j W' Θ' T w →
       ub_below W' (emb <$> ub) F →
       Erel j W' Θ'' U F (subst1 w eb))
  ∨ (∃ k T0, v = Konst k ∧ Θ = ∅ ∧ konst_ty (tw_eq W) (tw_lt W) k T0 ∧
       teq T0 (TLolli ub lb T U)).
Proof.
  unfold Vrel, Erel. rewrite (level_at_eq n). cbn [mk_level lV Vdef].
  apply or_iff_compat_r.
  split; intros (eb & -> & Hsup & Hlb & H); exists eb; (split_and!; [done..|]);
    intros W' j Θ' Θ'' w F HW Hj Hc HV Hub.
  - rewrite <-(levels_at n j Hj). apply (H W' j Θ' Θ'' w F); auto.
    rewrite (levels_at n j Hj). exact HV.
  - rewrite (levels_at n j Hj). apply (H W' j Θ' Θ'' w F); auto.
    rewrite <-(levels_at n j Hj). exact HV.
Qed.

(** The step-clause cases of the term relation at index S n'. *)
Definition Ecase (n' : nat) (W : world) (Θ : tenv) (T : ty) (F : gset point)
    (α : tlabel) (e' : expr) : Prop :=
  match α with
  | LBeta =>
      Erel n' W Θ T F e'
  | LNew c =>
      c ∉ dom Θ → NChan c ∉ w_names W →
      ∃ s s' W', sdual s s' ∧ wext_fresh W {[NChan c]} W' ∧
        Erel n' W' (<[c := Both (s, 0) (s', 0)]> Θ) T F e'
  | LSpawn w =>
      ∃ Θ1 Θ2 ub lb, tenv_comp Θ Θ1 Θ2 ∧
        Vrel (S n') W Θ1 (TLolli ub lb TUnit TUnit) w ∧
        Erel n' W Θ2 T F e'
  | LSess (SRecv c w) =>
      ∃ Θ1 m U s k,
        tenv_hd Θ c (SRcv m U s) k Θ1 ∧
        ∀ W' j Θ2 Θ12 xs, wext W W' → j ≤ n' →
          tenv_comp Θ12 Θ1 Θ2 →
          slot_aliases (w_eq W') xs m (pt_chan c k) →
          Vrel j W' Θ2 (ty_inst xs U) w →
          ∃ Θ', tenv_ext Θ12 c (s, S k) Θ' ∧ Erel j W' Θ' T F e'
  | LSess (SSend c w) =>
      ∃ Θr Θ1 Θ2 m U s k Θ' xs,
        tenv_hd Θ c (SSnd m U s) k Θr ∧ tenv_comp Θr Θ1 Θ2 ∧
        slot_aliases (w_eq W) xs m (pt_chan c k) ∧
        Vrel (S n') W Θ2 (ty_inst xs U) w ∧
        tenv_ext Θ1 c (s, S k) Θ' ∧
        Erel n' W Θ' T F e'
  | LSess (SClos c) =>
      ∃ Θ1 k, tenv_hd Θ c SEnd k Θ1 ∧ Erel n' W Θ1 T F e'
  | LSess (SLink cd) =>
      ∃ c d Θ1 Θm sc sd kc kd,
        cd = {[c; d]} ∧
        tenv_ext Θ1 d (sd, kd) Θm ∧ tenv_ext Θm c (sc, kc) Θ ∧
        sdual sd sc ∧ w_eq W (pt_chan c kc) (pt_chan d kd) ∧
        Erel n' W Θ1 T F e'
  end.

Lemma Erel_S_iff n W Θ T F e :
  Erel (S n) W Θ T F e ↔
    (irred e → Vrel (S n) W Θ T e) ∧
    (¬ irred e → ready_t W Θ e ∧ frame_t W Θ e F) ∧
    (∀ α e', tstep e α e' → Ecase n W Θ T F α e').
Proof.
  unfold Ecase, Erel, Vrel. rewrite (level_at_eq (S n)).
  cbn [mk_level lV lE Edef].
  rewrite (levels_at (S n) n (Nat.lt_succ_diag_r n)).
  do 2 apply and_iff_compat_l.
  split; intros H α e' Hst; specialize (H α e' Hst);
    destruct α as [|[c w|c w|c|cd]|c|w]; try exact H.
  - (* recv, → *)
    destruct H as (Θ1 & m & U & s & k & Hhd & H).
    exists Θ1, m, U, s, k. split; [done|].
    intros W' j Θ2 Θ12 xs HW Hj Hc Hxs HV.
    rewrite <-(levels_at (S n) j) in HV by lia.
    destruct (H W' j Θ2 Θ12 xs HW Hj Hc Hxs HV) as (Θ' & Hext & HE).
    exists Θ'. split; [done|]. by rewrite (levels_at (S n) j) in HE by lia.
  - (* recv, ← *)
    destruct H as (Θ1 & m & U & s & k & Hhd & H).
    exists Θ1, m, U, s, k. split; [done|].
    intros W' j Θ2 Θ12 xs HW Hj Hc Hxs HV.
    rewrite (levels_at (S n) j) in HV by lia.
    destruct (H W' j Θ2 Θ12 xs HW Hj Hc Hxs HV) as (Θ' & Hext & HE).
    exists Θ'. split; [done|]. by rewrite <-(levels_at (S n) j) in HE by lia.
Qed.

(** The step-clause cases of the process relation at index S n'. *)
Definition Pcase (n' : nat) (W : world) (Σ : senv) (T : ty) (p : proc)
    (π : plabel) (p' : proc) : Prop :=
  match π with
  | PTau =>
      p'.1 ## dom Σ →
      ∃ W' q, walpha W Σ p' q ∧ wext_inv W (set_map NChan (p.1 ∪ q.1)) W' ∧
        Prel n' W' Σ T q
  | PSess (SRecv c w) =>
      ∃ Σ1 m U s k,
        senv_hd Σ c (SRcv m U s) k Σ1 ∧ c ∉ dom Σ1 ∧
        ∀ W' j Θ2 xs, wext W W' → j ≤ n' → dom Θ2 ## p.1 →
          recv_ok W (<[c := (s, S k)]> Σ1) Θ2 →
          slot_aliases (w_eq W') xs m (pt_chan c k) →
          Vrel j W' Θ2 (ty_inst xs U) w →
          ∃ q, walpha W (recv_env (<[c := (s, S k)]> Σ1) Θ2)
                 (p'.1 ∪ recv_back (<[c := (s, S k)]> Σ1) Θ2, p'.2) q ∧
            Prel j W' (recv_env (<[c := (s, S k)]> Σ1) Θ2) T q
  | PSess (SSend c w) =>
      ∃ Σ0 Σv m U s k (Σe : senv) (Θe : tenv) xs,
        senv_hd Σ c (SSnd m U s) k (Σ0 ∪ Σv) ∧
        Σ0 ##ₘ Σv ∧ c ∉ dom Σ0 ∧ c ∉ dom Σv ∧
        dom Θe = fchans w ∩ p.1 ∧ send_split Σe Θe ∧
        dom Θe ## dom Σ ∧
        slot_aliases (w_eq W) xs m (pt_chan c k) ∧
        Vrel (S n') W (tenv_of Σv ∪ Θe) (ty_inst xs U) w ∧
        ∃ q, walpha W (<[c := (s, S k)]> (Σ0 ∪ Σe)) p' q ∧
          Prel n' W (<[c := (s, S k)]> (Σ0 ∪ Σe)) T q
  | PSess (SClos c) =>
      ∃ Σ1 k, senv_hd Σ c SEnd k Σ1 ∧ c ∉ dom Σ1 ∧
        ∃ q, walpha W Σ1 p' q ∧ Prel n' W Σ1 T q
  | PSess (SLink cd) =>
      ∃ c d Σ1 sc sd kc kd,
        cd = {[c; d]} ∧ c ≠ d ∧
        Σ = <[c := (sc, kc)]> (<[d := (sd, kd)]> Σ1) ∧
        c ∉ dom Σ1 ∧ d ∉ dom Σ1 ∧
        sdual sd sc ∧ w_eq W (pt_chan c kc) (pt_chan d kd) ∧
        ∃ q, walpha W Σ1 p' q ∧ Prel n' W Σ1 T q
  end.

Lemma Prel_S_iff n W Σ T p :
  Prel (S n) W Σ T p ↔
    (pirred p →
      ∃ v E, p = (∅, {[+ v +]} ⊎ E) ∧ is_val v ∧ Vrel (S n) W (tenv_of Σ) T v ∧
             (∀ e, e ∈ E → e = EUnit)) ∧
    (¬ pirred p → ready_p W Σ p) ∧
    (∀ π p', proc_step p π p' → Pcase n W Σ T p π p').
Proof.
  unfold Pcase, Prel, Vrel. rewrite (level_at_eq (S n)).
  cbn [mk_level lV lP Pdef].
  rewrite (levels_at (S n) n (Nat.lt_succ_diag_r n)).
  do 2 apply and_iff_compat_l.
  split; intros H π p' Hst; specialize (H π p' Hst);
    destruct π as [|[c w|c w|c|cd]]; try exact H.
  - (* recv, → *)
    destruct H as (Σ1 & m & U & s & k & Hhd & Hc & H).
    exists Σ1, m, U, s, k. split_and!; [done|done|].
    intros W' j Θ2 xs HW Hj Hfr Hdu Hxs HV.
    rewrite <-(levels_at (S n) j) in HV by lia.
    specialize (H W' j Θ2 xs HW Hj Hfr Hdu Hxs HV).
    rewrite (levels_at (S n) j) in H by lia. exact H.
  - (* recv, ← *)
    destruct H as (Σ1 & m & U & s & k & Hhd & Hc & H).
    exists Σ1, m, U, s, k. split_and!; [done|done|].
    intros W' j Θ2 xs HW Hj Hfr Hdu Hxs HV.
    rewrite (levels_at (S n) j) in HV by lia.
    specialize (H W' j Θ2 xs HW Hj Hfr Hdu Hxs HV).
    rewrite <-(levels_at (S n) j) in H by lia. exact H.
Qed.

(** Convenient corollaries of the characteristic equations. *)
Lemma Prel_S_intro n W Σ T p :
  (pirred p →
    ∃ v E, p = (∅, {[+ v +]} ⊎ E) ∧ is_val v ∧ Vrel (S n) W (tenv_of Σ) T v ∧
           (∀ e, e ∈ E → e = EUnit)) →
  (¬ pirred p → ready_p W Σ p) →
  (∀ π p', proc_step p π p' → Pcase n W Σ T p π p') →
  Prel (S n) W Σ T p.
Proof. intros. apply Prel_S_iff. done. Qed.

Lemma Prel_S_step n W Σ T p π p' :
  Prel (S n) W Σ T p → proc_step p π p' → Pcase n W Σ T p π p'.
Proof. intros HP Hst. apply Prel_S_iff in HP as (_ & _ & H). auto. Qed.

Lemma Erel_S_step n W Θ T F e α e' :
  Erel (S n) W Θ T F e → tstep e α e' → Ecase n W Θ T F α e'.
Proof. intros HE Hst. apply Erel_S_iff in HE as (_ & _ & H). auto. Qed.

(** ** Semantic judgments (Defs. 3.2 and 3.3) *)

(** Grounding substitutions G^W_n⟦Θ; Δ⟧: substitutions assigning to
    each available variable of Δ a value in the value relation,
    splitting Θ among them. *)
Fixpoint grounding (n : nat) (W : world) (Θ : tenv) (Δ : lenv)
    (γ : nat → expr) : Prop :=
  match Δ with
  | [] => Θ = ∅
  | None :: Δ' => grounding n W Θ Δ' (γ ∘ S)
  | Some T :: Δ' =>
      ∃ Θ1 Θ2, tenv_comp Θ Θ1 Θ2 ∧ Vrel n W Θ1 T (γ 0) ∧
               grounding n W Θ2 Δ' (γ ∘ S)
  end.

(** Free variables available in Δ: x is bound to a [Some] entry. *)
Definition lenv_avail (Δ : lenv) (x : nat) : Prop :=
  ∃ T, Δ !! x = Some (Some T).

(** Availability at a linear (non-unlimited) type: the variables
    constrained by relevance — unlimited variables may be discarded
    (weakening), so only linear availability forces occurrence. *)
Definition lenv_avail_lin (Δ : lenv) (x : nat) : Prop :=
  ∃ T, Δ !! x = Some (Some T) ∧ ¬ unlimited T.

Lemma lenv_avail_lin_avail Δ x :
  lenv_avail_lin Δ x → lenv_avail Δ x.
Proof. intros (T & ? & _). by exists T. Qed.

(** Syntactic well-formedness of e against Θ; Δ: the channels of e are
    exactly dom Θ, the free variables of e are available in Δ, and —
    relevance, i.e. absence of weakening — every linearly available
    variable of Δ occurs in e.

    None of this is part of the semantic judgment below. It is a
    separate, purely syntactic predicate, established once and for all
    for syntactically typed terms ([Terms.typed_term_wf]) and consumed
    as an explicit premise by exactly the two rules that build a
    suspended computation, whose V-clauses demand channel ownership:
    E-Abs needs all three (the ⊸-clause asks for [fchans eb = dom Θ],
    ⊆ from the first two, ⊇ from relevance) and E-Box needs the first
    two (the □-clause asks for [fchans eb = ∅]; relevance is vacuous
    there, the environment being unlimited). The elimination rules
    need none of it: E constrains environments, not term channels. *)
Definition term_wf (Θ : tenv) (Δ : lenv) (e : expr) : Prop :=
  fchans e = dom Θ ∧
  allfv (lenv_avail Δ) e ∧
  (∀ x, lenv_avail_lin Δ x → freevar x e).

(** Θ; Δ ⊨^F_W e : T.  In every future world, the channels of e itself
    are covered by Θ; the grounding substitution brings its own
    (disjoint) Θ'. F is the frame (§8; F = ∅ is the paper's judgment,
    plus ready). (Def. 3.3;
    the draft's phrasing conflates the two environments — this is the
    reading under which the rules of Fig. 4, e.g. E-Ch, are
    non-vacuous.)

    The judgment is purely semantic: it says nothing about the syntax
    of e beyond what Erel says about its behaviour. The syntactic
    side conditions live in [term_wf] and enter as premises exactly
    where Fig. 4's proofs consume them. *)
Definition sem_typed (W : world) (Θ : tenv) (Δ : lenv) (F : gset point)
    (e : expr) (T : ty) : Prop :=
  ∀ n W' Θ' γ, wext W W' → Θ' ##ₘ Θ → grounding n W' Θ' Δ γ →
    Erel n W' (Θ ∪ Θ') T F (subst γ e).

(** Σ ⊨_W p : T *)
Definition sem_ptyped (W : world) (Σ : senv) (p : proc) (T : ty) : Prop :=
  ∀ n, Prel n W Σ T p.

(** ** The adequacy chain (Lemmas 3.4, 3.5 and Theorem 3.6) *)

(** Lemma 3.4, for the closed environment: along a run, an α-variant
    of the last state is related in some world, and its safety implies
    the safety of the last state ([Swap.alpha_nsteps]). *)
Lemma Prel_steps m : ∀ W n T p p',
  nsteps preduction m p p' → Prel (m + n) W ∅ T p →
  ∃ W' r, Prel n W' ∅ T r ∧ (safe r → safe p').
Proof.
  induction m as [|m IH]; intros W n T p p' Hrun HP.
  { inversion Hrun; subst. by exists W, p'. }
  inversion Hrun as [|? ? q ? Hpq Hqr]; subst. simpl in HP.
  destruct (Prel_S_tau _ _ _ _ _ _ HP Hpq) as (W' & q' & Hal & _ & HP').
  { rewrite dom_empty_L. apply disjoint_empty_r. }
  destruct (alpha_nsteps _ _ _ _ (walpha_alpha _ _ _ _ Hal) Hqr) as (r' & Hr' & Hs').
  destruct (IH W' n T q' r' Hr' HP') as (W'' & r & HPr & Hs).
  exists W'', r. split; [done|]. intros H. by apply Hs', Hs.
Qed.

(** Lemma 3.5 *)
Lemma Prel_safe n W T p : Prel (S n) W ∅ T p → safe p.
Proof.
  intros HP. destruct (proc_progress p) as [Hirr|(π & p' & Hst)].
  - left. destruct (Prel_S_irred _ _ _ _ _ HP Hirr) as (v & E & -> & Hv & _ & HE).
    exists v, E. auto.
  - right. destruct π as [|σ].
    + by exists p'.
    + exfalso. by eapply Prel_S_empty_no_sess.
Qed.

(** Theorem 3.6 (Adequacy). Runs relate α-variants of their states,
    and safety transports along renamings ([Swap.safe_pswap_iff]). *)
Theorem adequacy W T p : sem_ptyped W ∅ p T → deadlock_free p.
Proof.
  intros HP p' Hsteps. apply rtc_nsteps_1 in Hsteps as [m Hm].
  destruct (Prel_steps m W 1 T p p' Hm) as (W' & r & HPr & Hs);
    [by rewrite Nat.add_1_r|].
  apply Hs. by eapply (Prel_safe 0).
Qed.

(** ** Downward closure (Lemma 3.7) *)

Lemma Vrel_down n m W Θ T v : m ≤ n → Vrel n W Θ T v → Vrel m W Θ T v.
Proof.
  intros Hle. induction T in Θ, v |- *.
  - rewrite !Vrel_unit_iff. done.
  - rewrite !Vrel_lolli_iff.
    intros [(eb & -> & Hsup & Hlb & H)|Hk]; [left|by right].
    exists eb. split_and!; [done..|].
    intros W' j Θ' Θ'' w F HW Hj Hc HV Hub.
    apply (H W' j Θ' Θ'' w F); auto. lia.
  - rewrite !Vrel_prod_iff.
    intros (v1 & v2 & Θ1 & Θ2 & -> & Hc & H1 & H2).
    eexists _, _, _, _. split_and!; eauto.
  - rewrite !Vrel_sum_iff.
    intros [(v' & -> & H)|(v' & -> & H)]; [left|right]; eauto.
  - rewrite !Vrel_box_iff.
    intros (-> & eb & -> & Hfc & H). split; [done|].
    exists eb. split_and!; [done|done|]. intros W' j xs HW Hj Hxs.
    apply H; auto. lia.
  - rewrite !Vrel_sess_iff. done.
Qed.

Lemma Erel_down n m W Θ T F e :
  m ≤ n → Erel n W Θ T F e → Erel m W Θ T F e.
Proof.
  revert n W Θ T F e. induction m as [|m' IH]; intros n W Θ T F e Hle HE;
    [apply Erel_0|].
  destruct n as [|n']; [lia|].
  apply Erel_S_iff in HE as (H1 & Hr & H2).
  apply Erel_S_iff. split_and!.
  - intros He. eapply Vrel_down; [|by apply H1]. lia.
  - done.
  - intros α e' Hst. specialize (H2 α e' Hst).
    destruct α as [|[c w|c w|c|cd]|c|w]; simpl in H2 |- *.
    + eapply IH; [|exact H2]. lia.
    + destruct H2 as (Θ1 & m & U & s & k & Hhd & H2).
      eexists _, _, _, _, _. split; [done|].
      intros W' j Θ2 Θ12 xs HW Hj Hc Hxs HV. apply (H2 W' j Θ2 Θ12 xs); auto. lia.
    + destruct H2 as (Θr & Θ1 & Θ2 & m & U & s & k & Θ' & xs &
                      Hhd & Hc & Hxs & HV & Hext & HE').
      eexists _, _, _, _, _, _, _, _, _. split_and!; eauto.
      * eapply Vrel_down; [|exact HV]. lia.
      * eapply IH; [|exact HE']. lia.
    + destruct H2 as (Θ1 & k & Hhd & HE').
      eexists _, _. split; [done|]. eapply IH; [|done]. lia.
    + destruct H2 as (c & d & Θ1 & Θm & sc & sd & kc & kd &
                      -> & ? & ? & ? & ? & HE').
      eexists _, _, _, _, _, _, _, _. split_and!; [done..|].
      eapply IH; [|done]. lia.
    + intros Hc Hn. destruct (H2 Hc Hn) as (s & s' & W' & ? & ? & HE').
      eexists _, _, _. split_and!; [done|done|]. eapply IH; [|done]. lia.
    + destruct H2 as (Θ1 & Θ2 & ub & lb & ? & HV & HE').
      eexists _, _, _, _. split_and!; eauto.
      * eapply Vrel_down; [|exact HV]. lia.
      * eapply IH; [|done]. lia.
Qed.

Lemma Prel_down n m W Σ T p : m ≤ n → Prel n W Σ T p → Prel m W Σ T p.
Proof.
  revert n W Σ T p. induction m as [|m' IH]; intros n W Σ T p Hle HP;
    [apply Prel_0|].
  destruct n as [|n']; [lia|].
  apply Prel_S_iff in HP as (H1 & Hr & H2).
  apply Prel_S_iff. split_and!.
  - intros Hirr. destruct (H1 Hirr) as (v & E & -> & ? & HV & ?).
    eexists _, _. split_and!; eauto. eapply Vrel_down; [|exact HV]. lia.
  - done.
  - intros π p' Hst. specialize (H2 π p' Hst).
    destruct π as [|[c w|c w|c|cd]]; simpl in H2 |- *.
    + intros Hd. destruct (H2 Hd) as (W' & q & ? & ? & ?).
      exists W', q. split_and!; [done|done|]. eapply IH; [|done]. lia.
    + destruct H2 as (Σ1 & m & U & s & k & Hhd & Hc & H2).
      eexists _, _, _, _, _. split_and!; [done|done|].
      intros W' j Θ2 xs HW Hj Hfr Hdu Hxs HV. apply (H2 W' j Θ2 xs); auto. lia.
    + destruct H2 as (Σ0 & Σv & m & U & s & k & Σe & Θe & xs & Hhd &
                      ? & ? & ? & ? & ? & ? & ? & HV & HP0).
      destruct HP0 as (q & Hal & HP0).
      eexists _, _, _, _, _, _, _, _, _. split_and!; eauto.
      * eapply Vrel_down; [|exact HV]. lia.
      * exists q. split; [done|]. eapply IH; [|exact HP0]. lia.
    + destruct H2 as (Σ1 & k & Hhd & ? & q & Hal & HP').
      eexists _, _. split_and!; eauto. exists q. split; [done|].
      eapply IH; [|done]. lia.
    + destruct H2 as (c & d & Σ1 & sc & sd & kc & kd &
                      -> & ? & -> & ? & ? & ? & ? & q & Hal & HP').
      eexists _, _, _, _, _, _, _. split_and!; [done..|].
      exists q. split; [done|]. eapply IH; [|done]. lia.
Qed.
