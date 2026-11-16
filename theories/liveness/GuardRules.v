(** * The guard as rules (lock-freedom plan §19, T1)

    [glive L e] is the guard of Guard.v written as a rule system, one
    rule per term form. The mark context L holds the later variables.
    [L y = Some true] lets y be forced and applied, [Some false] does
    not. A later variable is never used as such. A term that acts
    before it returns ([acts], the rules of [gd]) clears the marks for
    what follows it, so the continuation is checked under [noL]. A
    closure may not capture a later variable ([nolater]). A box body
    gets its self as a later variable, forceable under the λs of the
    body ([gbody]).

    [okM_iff] says [glive L e] holds exactly when [okM L e] does and
    every box of e is guarded. At the root [guarded_iff] gives
    [guarded e ↔ glive noL e], so [gtyped], [gptyped] and the live
    theorems keep their text and read the rules ([gtyped_iff]). *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export liveness.GuardMarks.

Set Default Proof Using "All".

(** ** The rules *)

(** The session primitives. *)
Inductive sprim : konst → Prop :=
  | sprim_recv : sprim KRecv
  | sprim_send : sprim KSend
  | sprim_clos : sprim KClos
  | sprim_sel1 : sprim KSel1
  | sprim_sel2 : sprim KSel2
  | sprim_bra : sprim KBra.

(** e performs a session primitive before it returns. *)
Inductive acts : expr → Prop :=
  | acts_konst k e2 : sprim k → acts (App (Konst k) e2)
  | acts_app1 e1 e2 : acts e1 → acts (App e1 e2)
  | acts_app2 e1 e2 : acts e2 → acts (App e1 e2)
  | acts_let b e2 : acts b → acts (App (Lam b) e2)
  | acts_pair1 e1 e2 : acts e1 → acts (Pair e1 e2)
  | acts_pair2 e1 e2 : acts e2 → acts (Pair e1 e2)
  | acts_letu1 e1 e2 : acts e1 → acts (LetU e1 e2)
  | acts_letu2 e1 e2 : acts e2 → acts (LetU e1 e2)
  | acts_letp1 e1 e2 : acts e1 → acts (LetP e1 e2)
  | acts_letp2 e1 e2 : acts e2 → acts (LetP e1 e2)
  | acts_inj1 e : acts e → acts (Inj1 e)
  | acts_inj2 e : acts e → acts (Inj2 e)
  | acts_case e e1 e2 : acts e → acts (Case e e1 e2)
  | acts_branches e e1 e2 : acts e1 → acts e2 → acts (Case e e1 e2).

(** No later variable occurs in e. *)
Inductive nolater : lmark → expr → Prop :=
  | nolater_var L y : L y = None → nolater L (Var y)
  | nolater_unit L : nolater L EUnit
  | nolater_konst L k : nolater L (Konst k)
  | nolater_chan L c b : nolater L (Chan c b)
  | nolater_pt L x : nolater L (EPt x)
  | nolater_lam L b : nolater (None .: L) b → nolater L (Lam b)
  | nolater_app L e1 e2 : nolater L e1 → nolater L e2 → nolater L (App e1 e2)
  | nolater_pair L e1 e2 : nolater L e1 → nolater L e2 → nolater L (Pair e1 e2)
  | nolater_letu L e1 e2 : nolater L e1 → nolater L e2 → nolater L (LetU e1 e2)
  | nolater_letp L e1 e2 : nolater L e1 → nolater (None .: None .: L) e2 → nolater L (LetP e1 e2)
  | nolater_inj1 L e : nolater L e → nolater L (Inj1 e)
  | nolater_inj2 L e : nolater L e → nolater L (Inj2 e)
  | nolater_case L e e1 e2 : nolater L e → nolater (None .: L) e1 → nolater (None .: L) e2 →
      nolater L (Case e e1 e2)
  | nolater_box L b : nolater (None .: L) b → nolater L (EBox b).

(** Under the λs of a box body its self may be forced and applied. *)
Definition forceable (L : lmark) : lmark := λ i, (λ _, true) <$> L i.

Inductive glive : lmark → expr → Prop :=
  | glive_var L y : L y = None → glive L (Var y)
  | glive_unit L : glive L EUnit
  | glive_konst L k : glive L (Konst k)
  | glive_chan L c b : glive L (Chan c b)
  | glive_pt L x : glive L (EPt x)
  | glive_lam L b : nolater (None .: L) b → glive noL b → glive L (Lam b)
  | glive_box L b : nolater (None .: L) b → gbody (Some false .: noL) b → glive L (EBox b)
  | glive_app L e1 e2 : glive L e1 → glive L e2 → glive L (App e1 e2)
  | glive_app_acts L e1 e2 : glive L e1 → acts e1 → glive noL e2 → glive L (App e1 e2)
  | glive_let L b e2 : glive L e2 → glive (None .: L) b → glive L (App (Lam b) e2)
  | glive_let_acts L b e2 : glive L e2 → acts e2 → glive noL b → glive L (App (Lam b) e2)
  | glive_force L y e2 : L y = Some true → acts e2 → glive L e2 →
      glive L (App (App (Konst KForce) (Var y)) e2)
  | glive_pair L e1 e2 : glive L e1 → glive L e2 → glive L (Pair e1 e2)
  | glive_pair_acts L e1 e2 : glive L e1 → acts e1 → glive noL e2 → glive L (Pair e1 e2)
  | glive_letu L e1 e2 : glive L e1 → glive L e2 → glive L (LetU e1 e2)
  | glive_letu_acts L e1 e2 : glive L e1 → acts e1 → glive noL e2 → glive L (LetU e1 e2)
  | glive_letp L e1 e2 : glive L e1 → glive (None .: None .: L) e2 → glive L (LetP e1 e2)
  | glive_letp_acts L e1 e2 : glive L e1 → acts e1 → glive noL e2 → glive L (LetP e1 e2)
  | glive_inj1 L e : glive L e → glive L (Inj1 e)
  | glive_inj2 L e : glive L e → glive L (Inj2 e)
  | glive_case L e e1 e2 : glive L e → glive (None .: L) e1 → glive (None .: L) e2 →
      glive L (Case e e1 e2)
  | glive_case_acts L e e1 e2 : glive L e → acts e → glive noL e1 → glive noL e2 →
      glive L (Case e e1 e2)
with gbody : lmark → expr → Prop :=
  | gbody_lam L b : gbody (None .: forceable L) b → gbody L (Lam b)
  | gbody_now L e : glive L e → gbody L e.

Scheme glive_mut := Induction for glive Sort Prop
  with gbody_mut := Induction for gbody Sort Prop.
Combined Scheme glive_gbody_mut from glive_mut, gbody_mut.

(** ** The rules of [acts] and [nolater] are [gd] and [occursM] *)

Lemma gd_app e1 e2 : gd (App e1 e2) =
  match e1 with Konst k => prim_konst k | Lam b => gd b | _ => gd e1 end || gd e2.
Proof. destruct e1; simpl; try done. apply orb_comm. Qed.

Lemma sprim_iff k : sprim k ↔ prim_konst k = true.
Proof. split; [by destruct 1|destruct k; done || constructor]. Qed.

Lemma gd_acts_aux e :
  (gd e = true → acts e) ∧ match e with Lam b => gd b = true → acts b | _ => True end.
Proof.
  induction e as [y| |k|c cb|cx|e IH|e1 IH1 e2 IH2|e1 IH1 e2 IH2|e1 IH1 e2 IH2|e1 IH1 e2 IH2
                 |e IH|e IH|e IH e1 IH1 e2 IH2|e IH]; (split; [intros H|try done]); try done.
  - exact (proj1 IH).
  - rewrite gd_app, orb_true_iff in H. destruct H as [H|H]; [|by apply acts_app2, IH2].
    destruct e1; try (by apply acts_app1, IH1); [constructor; by apply sprim_iff|by apply acts_let, IH1].
  - apply orb_true_iff in H as [H|H]; [by apply acts_pair1, IH1|by apply acts_pair2, IH2].
  - apply orb_true_iff in H as [H|H]; [by apply acts_letu1, IH1|by apply acts_letu2, IH2].
  - apply orb_true_iff in H as [H|H]; [by apply acts_letp1, IH1|by apply acts_letp2, IH2].
  - by apply acts_inj1, IH.
  - by apply acts_inj2, IH.
  - apply orb_true_iff in H as [H|[H1 H2]%andb_true_iff];
      [by apply acts_case, IH|by apply acts_branches; [apply IH1|apply IH2]].
Qed.

Lemma acts_iff e : acts e ↔ gd e = true.
Proof.
  split; [|apply gd_acts_aux].
  induction 1; rewrite ?gd_app; simpl; rewrite ?orb_true_iff, ?andb_true_iff; try tauto.
  - left. by apply sprim_iff.
  - left. by destruct e1.
Qed.

Lemma nolater_iff L e : nolater L e ↔ occursM L e = false.
Proof.
  split.
  - induction 1; simpl; rewrite ?orb_false_iff; try done. unfold marked. by rewrite H.
  - revert L. induction e; intros L; simpl; rewrite ?orb_false_iff; intros H;
      repeat match goal with H : _ ∧ _ |- _ => destruct H end; constructor; auto.
    unfold marked in H. by destruct (L x).
Qed.

(** ** Soundness: the rules imply the guard *)

Lemma okM_app L e1 e2 : okM L e1 = true → gd e1 = true ∨ okM L e2 = true → okM L (App e1 e2) = true.
Proof.
  intros H1 H2. destruct (force_var e1) as [y|] eqn:Hf.
  - apply force_var_some in Hf as ->. simpl in *. unfold marked in H1. destruct (L y); [done|]. by destruct H2.
  - destruct (is_lam e1) eqn:Hl.
    + destruct e1 as [| | | | |b| | | | | | | |]; try done. simpl in *. apply negb_true_iff in H1.
      destruct H2 as [H2|H2]; [done|]. by rewrite H2, (occursM_false_okM _ _ H1), orb_true_r.
    + rewrite okM_app_gen; [|done|done]. rewrite H1. destruct H2 as [->| ->]; [done|apply orb_true_r].
Qed.

Definition ok_eq_P (e : expr) : Prop := ∀ L x f, only_mark L x f → ok f x e = okM L e.

Lemma ok_eq_aux e : ok_eq_P e ∧ match e with Lam b => ok_eq_P b | _ => True end.
Proof.
  induction e as [y| |k|c cb|cx|e IH|e1 IH1 e2 IH2|e1 IH1 e2 IH2|e1 IH1 e2 IH2|e1 IH1 e2 IH2
                 |e IH|e IH|e IH e1 IH1 e2 IH2|e IH];
    (split; [intros L x f HL|try done]); try done.
  - simpl. destruct HL as [Hx Hy]. unfold marked. destruct (Nat.eq_dec x y) as [->|Hne].
    + by rewrite Hx, Nat.eqb_refl.
    + rewrite Hy; [|done]. by rewrite (proj2 (Nat.eqb_neq x y) Hne).
  - simpl. by erewrite occursM_single; [|apply only_mark_up; exact HL].
  - exact (proj1 IH).
  - destruct (force_var e1) as [y|] eqn:Hf.
    + apply force_var_some in Hf as ->. simpl. pose proof HL as [Hx Hy].
      rewrite (proj1 IH2 L x f HL). destruct (Nat.eq_dec x y) as [->|Hne].
      * by rewrite Nat.eqb_refl, Hx.
      * rewrite (proj2 (Nat.eqb_neq x y) Hne), Hy; done.
    + destruct (is_lam e1) eqn:Hl.
      * destruct e1 as [| | | | |b| | | | | | | |]; try done. simpl.
        by rewrite (proj1 IH2 L x f HL), (proj2 IH1 (None .: L) (S x) f (only_mark_up _ _ _ HL)).
      * rewrite okM_app_gen, ok_app_gen; [|done..]. by rewrite (proj1 IH1 L x f HL), (proj1 IH2 L x f HL).
  - simpl. by rewrite (proj1 IH1 L x f HL), (proj1 IH2 L x f HL).
  - simpl. by rewrite (proj1 IH1 L x f HL), (proj1 IH2 L x f HL).
  - simpl. by rewrite (proj1 IH1 L x f HL), (proj1 IH2 _ (S (S x)) f (only_mark_up _ _ _ (only_mark_up _ _ _ HL))).
  - simpl. by rewrite (proj1 IH L x f HL).
  - simpl. by rewrite (proj1 IH L x f HL).
  - simpl. by rewrite (proj1 IH L x f HL), (proj1 IH1 _ (S x) f (only_mark_up _ _ _ HL)),
      (proj1 IH2 _ (S x) f (only_mark_up _ _ _ HL)).
  - simpl. by erewrite occursM_single; [|apply only_mark_up; exact HL].
Qed.

Lemma ok_eq e L x f : only_mark L x f → ok f x e = okM L e.
Proof. apply ok_eq_aux. Qed.

Lemma okv_eq e x f : is_lam e = false → okv f x e = ok f x e.
Proof. by destruct e. Qed.

Lemma only_mark_one x f : only_mark (λ i, if Nat.eqb i x then Some f else None) x f.
Proof.
  split; [by rewrite Nat.eqb_refl|]. intros y Hne. by rewrite (proj2 (Nat.eqb_neq y x) Hne).
Qed.

Lemma only_mark_forceable L x f : only_mark L x f → only_mark (None .: forceable L) (S x) true.
Proof.
  intros [Hx Hy]. split; [simpl; unfold forceable; by rewrite Hx|].
  intros [|y] Hne; simpl; [done|]. unfold forceable. rewrite Hy; [done|lia].
Qed.

Lemma okv_nooc e : ∀ x f, occurs x e = false → okv f x e = true.
Proof.
  induction e as [y| | | | |b IH| | | | | | | |]; intros z f H; try (rewrite okv_eq; [|done];
    rewrite (ok_eq _ _ z f (only_mark_one z f)); apply occursM_false_okM;
    by rewrite (occursM_single _ _ z f (only_mark_one z f))).
  simpl in *. by apply IH.
Qed.

Lemma okM_okv e L x f : only_mark L x f → okM L e = true → okv f x e = true.
Proof.
  intros HL H. destruct (is_lam e) eqn:Hl.
  - destruct e as [| | | | |b| | | | | | | |]; try done. simpl in *. apply okv_nooc.
    apply negb_true_iff in H. by rewrite <-(occursM_single _ _ _ f (only_mark_up _ _ _ HL)).
  - by rewrite okv_eq, (ok_eq _ L x f HL).
Qed.

(** Rewrite with every hypothesis that fixes a boolean or a mark. *)
Ltac fin := unfold marked;
  repeat match goal with
  | H : ?a = true |- context [?a] => rewrite H
  | H : ?a = false |- context [?a] => rewrite H
  | H : ?a = None |- context [?a] => rewrite H
  | H : ?a = Some true |- context [?a] => rewrite H
  end; rewrite ?orb_true_r, ?andb_true_r; first [done|by left|by right].

Ltac destr :=
  repeat match goal with
  | H : _ ∧ _ |- _ => destruct H
  | H : nolater _ _ |- _ => apply nolater_iff in H
  | H : acts _ |- _ => apply acts_iff in H
  end.

Lemma glive_sound :
  (∀ L e, glive L e → okM L e = true ∧ gall e = true) ∧
  (∀ L e, gbody L e → ∀ x f, only_mark L x f → okv f x e = true ∧ gall e = true).
Proof.
  apply glive_gbody_mut; intros; simpl; destr; try (split; [|by fin]).
  all: try (by fin).
  all: try (by apply okM_app; fin).
  - match goal with H : ∀ x f, only_mark _ x f → _ |- _ => destruct (H 0 false) as [Hv Ha] end;
      [split; [done|by intros [|y]]|].
    split; [by fin|]. by rewrite Hv, Ha.
  - match goal with H : ∀ x f, only_mark _ x f → _, Hm : only_mark _ _ _ |- _ =>
      apply (H _ _ (only_mark_forceable _ _ _ Hm)) end.
  - by eapply okM_okv.
Qed.

(** ** Completeness: the guard implies the rules *)

Lemma okM_noL e : okM noL e = true.
Proof. by apply occursM_false_okM, occursM_noL. Qed.

Definition glive_complete_P (e : expr) : Prop :=
  (∀ L, okM L e = true → gall e = true → glive L e) ∧
  (∀ L x f, only_mark L x f → okv f x e = true → gall e = true → gbody L e).

Lemma glive_complete_aux e :
  glive_complete_P e ∧ match e with Lam b => glive_complete_P b | _ => True end.
Proof.
  induction e as [y| |k|c cb|cx|e IH|e1 IH1 e2 IH2|e1 IH1 e2 IH2|e1 IH1 e2 IH2|e1 IH1 e2 IH2
                 |e IH|e IH|e IH e1 IH1 e2 IH2|e IH].
  (* the second half of [glive_complete_P] for a term that is not a λ *)
  all: try match goal with |- glive_complete_P ?e ∧ _ =>
    enough (∀ L, okM L e = true → gall e = true → glive L e) as Hg;
      [split; [split; [exact Hg|]|done];
       intros L x f HL Hv Ha; apply gbody_now, Hg; [|done];
       by rewrite <-(ok_eq _ L x f HL), <-okv_eq|] end.
  all: try (intros L H Ha; simpl in Ha; rewrite ?andb_true_iff in Ha;
    lazymatch goal with
    | |- glive _ (App _ _) => idtac
    | _ => simpl in H; rewrite ?andb_true_iff, ?orb_true_iff in H
    end).
  - constructor. unfold marked in H. by destruct (L y).
  - constructor.
  - constructor.
  - constructor.
  - constructor.
  - destruct IH as [[IHg IHb] _]. split; [split|exact (conj IHg IHb)].
    + intros L H Ha. simpl in H, Ha. apply negb_true_iff in H.
      apply glive_lam; [by apply nolater_iff|by apply IHg; [apply okM_noL|]].
    + intros L x f HL Hv Ha. simpl in Hv, Ha. apply gbody_lam.
      apply (IHb _ (S x) true); [by apply (only_mark_forceable _ _ f)|done|done].
  - destruct IH1 as [[IH1g _] IH1l], IH2 as [[IH2g _] _]. destruct Ha as [Ha1 Ha2].
    destruct (force_var e1) as [y|] eqn:Hf.
    + apply force_var_some in Hf as ->. simpl in H. destruct (L y) as [[]|] eqn:Hy.
      * rewrite !andb_true_iff in H. destruct H as [[_ ?] ?].
        by apply glive_force; [|apply acts_iff|apply IH2g].
      * done.
      * apply glive_app; [|by apply IH2g]. apply glive_app; constructor; done.
    + destruct (is_lam e1) eqn:Hl.
      * destruct e1 as [| | | | |b| | | | | | | |]; try done. destruct IH1l as [IHb _].
        simpl in H, Ha1. rewrite andb_true_iff, orb_true_iff in H. destruct H as [H [H'|H']].
        { apply glive_let_acts; [by apply IH2g|by apply acts_iff|by apply IHb; [apply okM_noL|]]. }
        { apply glive_let; [by apply IH2g|by apply IHb]. }
      * rewrite okM_app_gen in H; [|done|done]. rewrite andb_true_iff, orb_true_iff in H.
        destruct H as [H [H'|H']].
        { apply glive_app_acts; [by apply IH1g|by apply acts_iff|by apply IH2g; [apply okM_noL|]]. }
        { apply glive_app; [by apply IH1g|by apply IH2g]. }
  - destruct IH1 as [[IH1g _] _], IH2 as [[IH2g _] _]. destruct Ha as [Ha1 Ha2], H as [H [H'|H']].
    + apply glive_pair_acts; [by apply IH1g|by apply acts_iff|by apply IH2g; [apply okM_noL|]].
    + apply glive_pair; [by apply IH1g|by apply IH2g].
  - destruct IH1 as [[IH1g _] _], IH2 as [[IH2g _] _]. destruct Ha as [Ha1 Ha2], H as [H [H'|H']].
    + apply glive_letu_acts; [by apply IH1g|by apply acts_iff|by apply IH2g; [apply okM_noL|]].
    + apply glive_letu; [by apply IH1g|by apply IH2g].
  - destruct IH1 as [[IH1g _] _], IH2 as [[IH2g _] _]. destruct Ha as [Ha1 Ha2], H as [H [H'|H']].
    + apply glive_letp_acts; [by apply IH1g|by apply acts_iff|by apply IH2g; [apply okM_noL|]].
    + apply glive_letp; [by apply IH1g|by apply IH2g].
  - destruct IH as [[IHg _] _]. by apply glive_inj1, IHg.
  - destruct IH as [[IHg _] _]. by apply glive_inj2, IHg.
  - destruct IH as [[IHg _] _], IH1 as [[IH1g _] _], IH2 as [[IH2g _] _].
    destruct Ha as [[Ha Ha1] Ha2], H as [H [H'|[H1 H2]%andb_true_iff]].
    + apply glive_case_acts; [by apply IHg|by apply acts_iff|by apply IH1g; [apply okM_noL|]
      |by apply IH2g; [apply okM_noL|]].
    + apply glive_case; [by apply IHg|by apply IH1g|by apply IH2g].
  - destruct IH as [[_ IHb] _]. destruct Ha as [Hv Ha]. apply negb_true_iff in H.
    apply glive_box; [by apply nolater_iff|]. apply (IHb _ 0 false); [|done|done].
    split; [done|by intros [|y]].
Qed.

(** ** The equivalence *)

Theorem okM_iff L e : glive L e ↔ okM L e = true ∧ gall e = true.
Proof.
  split; [apply glive_sound|]. intros [H Ha]. by apply glive_complete_aux.
Qed.

Theorem gbody_iff L x f e : only_mark L x f → gbody L e ↔ okv f x e = true ∧ gall e = true.
Proof.
  intros HL. split; [intros H; by apply (proj2 glive_sound L)|].
  intros [H Ha]. by apply (proj2 (proj1 (glive_complete_aux e)) L x f).
Qed.

Theorem guarded_iff e : guarded e ↔ glive noL e.
Proof. rewrite okM_iff. unfold guarded. pose proof (okM_noL e). tauto. Qed.

Corollary gtyped_iff W Φ Ψ Θ Δ F e T :
  gtyped W Φ Ψ Θ Δ F e T ↔ typed W Φ Ψ Θ Δ F e T ∧ glive noL e.
Proof. unfold gtyped. by rewrite guarded_iff. Qed.

Corollary gptyped_iff W Σ p T :
  gptyped W Σ p T ↔ ptyped W Σ p T ∧ ∀ e, e ∈ p.2 → glive noL e.
Proof. unfold gptyped. by setoid_rewrite guarded_iff. Qed.
