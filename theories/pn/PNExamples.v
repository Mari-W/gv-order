(** * Examples of Padovani and Novara

    Example 1 (parallel Fibonacci, pdf p. 5, typed in Example 3, p. 11)
    and Example 2 (the signal pipe, p. 5, with wrap and unwrap in
    Example 4, p. 13), each typed in the judgment of PNTyping.v and
    deadlock free through [pn_deadlock_free]. *)

From stdpp Require Import base gmap numbers.
From LRGV Require Export pn.PNTranslate.

Set Default Proof Using "All".

(** ** Splitting by occurrence

    [pl e x Γ] keeps the unlimited bindings of Γ and the linear ones
    that occur in e, with x the index of Γ's head inside e. [psok]
    checks that every linear binding goes to exactly one side. *)

Fixpoint pl (e : expr) (x : nat) (Γ : penv) : penv :=
  match Γ with
  | [] => []
  | None :: Γ' => None :: pl e (S x) Γ'
  | Some t :: Γ' => (if un_b t || occ x e then Some t else None) :: pl e (S x) Γ'
  end.

Fixpoint psok (e1 : expr) (x1 : nat) (e2 : expr) (x2 : nat) (Γ : penv) : bool :=
  match Γ with
  | [] => true
  | None :: Γ' => psok e1 (S x1) e2 (S x2) Γ'
  | Some t :: Γ' => (un_b t || xorb (occ x1 e1) (occ x2 e2)) && psok e1 (S x1) e2 (S x2) Γ'
  end.

Lemma pl_split e1 x1 e2 x2 Γ :
  psok e1 x1 e2 x2 Γ = true → pn_split Γ (pl e1 x1 Γ) (pl e2 x2 Γ).
Proof.
  revert x1 x2. induction Γ as [|[t|] Γ IH]; intros x1 x2 H; simpl in *; [constructor| |].
  - apply andb_true_iff in H as [H1 H2].
    destruct (un_b t) eqn:Hu; simpl.
    + apply ps_un; [by apply un_b_un|by apply IH].
    + destruct (occ x1 e1), (occ x2 e2); simpl in *; try done; [apply ps_l|apply ps_r]; by apply IH.
  - apply ps_none. by apply IH.
Qed.

Fixpoint allun (Γ : penv) : bool :=
  match Γ with
  | [] => true
  | None :: Γ' => allun Γ'
  | Some t :: Γ' => un_b t && allun Γ'
  end.

Lemma allun_un Γ : allun Γ = true → penv_un Γ.
Proof.
  induction Γ as [|[t|] Γ IH]; simpl; intros H t' Ht'; [by apply elem_of_nil in Ht'| |].
  - apply andb_true_iff in H as [H1 H2]. apply elem_of_cons in Ht' as [[=<-]|Ht'].
    + by apply un_b_un.
    + by apply IH.
  - apply elem_of_cons in Ht' as [[=]|Ht']. by apply IH.
Qed.

Fixpoint okun (x : nat) (Γ : penv) : bool :=
  match Γ, x with
  | [], _ => true
  | _ :: Γ', 0 => allun Γ'
  | o :: Γ', S x' => match o with Some t => un_b t | None => true end && okun x' Γ'
  end.

Lemma okun_only x Γ t : Γ !! x = Some (Some t) → okun x Γ = true → penv_only_un Γ x t.
Proof.
  intros Hx Hok. split; [done|]. revert x Hx Hok. induction Γ as [|o Γ IH]; intros [|x] Hx Hok y t' Hy Hyt;
    simpl in *; try done.
  - destruct y; [done|]. simpl in Hyt. apply (allun_un Γ Hok). by eapply list_elem_of_lookup_2.
  - apply andb_true_iff in Hok as [H1 H2]. destruct y as [|y]; simpl in Hyt.
    + injection Hyt as ->. by apply un_b_un.
    + eapply (IH x Hx H2 y); [lia|done].
Qed.

(** One step of a derivation, by the head of the term. *)
Lemma pn_var Γ x t : Γ !! x = Some (Some t) → okun x Γ = true → pn_typed Γ (Var x) t LBot (Var x).
Proof. intros. by apply pn_name, okun_only. Qed.

Lemma pn_unit' Γ : allun Γ = true → pn_typed Γ EUnit PUnit LBot unitv.
Proof. intros. by apply pn_unit, allun_un. Qed.

(** Rule instances with the split by occurrence. The effect and the type
    of the conclusion are equations at the end, solved once the
    premises have fixed them. *)
Lemma pn_app' Γ e1 e2 e1' e2' t r σ s τ1 τ2 τ :
  psok e1 0 e2 0 Γ = true →
  pn_typed (pl e1 0 Γ) e1 (PArr t (Some r) σ s) τ1 e1' →
  pn_typed (pl e2 0 Γ) e2 t τ2 e2' →
  lvl_lt τ1 (olvl (env_lev (pl e2 0 Γ))) → lvl_lt τ2 (LZ r) →
  τ = lvl_max σ (lvl_max τ1 τ2) →
  pn_typed Γ (App e1 e2) s τ (App e1' e2').
Proof. intros Hs ? ? ? ? ->. eapply pn_app; [by apply pl_split|eassumption..]. Qed.

Lemma pn_poly' Γ e1 e2 e1' e2' t σ s s' τ1 τ2 τ n :
  psok e1 0 e2 0 Γ = true →
  pn_typed (pl e1 0 Γ) e1 (PArr t None σ s) τ1 e1' →
  pn_typed (pl e2 0 Γ) e2 (lshift n t) τ2 e2' →
  lvl_lt τ1 (olvl (env_lev (pl e2 0 Γ))) → lvl_lt τ2 LTop →
  s' = lshift n s → τ = lvl_max (lvl_sh n σ) (lvl_max τ1 τ2) →
  pn_typed Γ (App e1 e2) s' τ (App (App EForce e1') e2').
Proof. intros Hs ? ? ? ? -> ->. eapply pn_app_poly; [by apply pl_split|eassumption..]. Qed.

Lemma pn_send' Γ e1 e2 e1' e2' t n τ1 τ2 τ :
  psok e1 0 e2 0 Γ = true →
  pn_typed (pl e1 0 Γ) e1 (PChan false t n) τ1 e1' →
  pn_typed (pl e2 0 Γ) e2 t τ2 e2' →
  lvl_lt (LZ n) (olvl (tlev t)) → payok t →
  lvl_lt τ1 (olvl (env_lev (pl e2 0 Γ))) → lvl_lt τ2 (LZ n) →
  τ = lvl_max (LZ n) (lvl_max τ1 τ2) →
  pn_typed Γ (App (App ESend e1) e2) PUnit τ (App (App send_tr e1') e2').
Proof. intros Hs ? ? ? ? ? ? ->. eapply pn_send; [by apply pl_split|eassumption..]. Qed.

Lemma pn_recv' Γ e e' t n τ0 τ :
  pn_typed Γ e (PChan true t n) τ0 e' →
  lvl_lt (LZ n) (olvl (tlev t)) → payok t → τ = lvl_max (LZ n) τ0 →
  pn_typed Γ (App ERecv e) t τ (App recv_tr e').
Proof. intros ? ? ? ->. by apply pn_recv. Qed.

Lemma pn_case' Γ e e1 e2 e' e1' e2' t s u τ1 τ2 τ :
  psok e 0 (Lam (App e1 e2)) 0 Γ = true →
  pn_typed (pl e 0 Γ) e (PSum t s) τ1 e' → un t → un s →
  pn_typed (Some t :: pl (Lam (App e1 e2)) 0 Γ) e1 u τ2 e1' →
  pn_typed (Some s :: pl (Lam (App e1 e2)) 0 Γ) e2 u τ2 e2' →
  lvl_lt τ1 (olvl (env_lev (pl (Lam (App e1 e2)) 0 Γ))) →
  τ = lvl_max τ1 τ2 →
  pn_typed Γ (Case e e1 e2) u τ (Case (App EForce e') e1' e2').
Proof. intros Hs ? ? ? ? ? ? ->. eapply pn_case; [by apply pl_split|eassumption..]. Qed.

Lemma pn_fun' Γ e e' e'' t s ρ r τ :
  pn_typed (Some t :: Γ) e s ρ e' → r = env_lev Γ → τ = LBot → e'' = lam_tr r e' →
  pn_typed Γ (Lam e) (PArr t r ρ s) τ e''.
Proof. intros ? -> -> ->. by apply pn_fun. Qed.

Ltac pfun := eapply pn_fun'; [|reflexivity|reflexivity|reflexivity].
Ltac pfunu := eapply (pn_fun' _ _ _ _ PUnit); [|reflexivity|reflexivity|reflexivity].

Lemma pn_eff Γ e t τ τ' e' : pn_typed Γ e t τ e' → τ = τ' → pn_typed Γ e t τ' e'.
Proof. by intros ? ->. Qed.

Ltac lv := simpl; try done; try lia.

(** One step, by the head of the term or the side condition. Side
    conditions on levels are solved once their effects are known. *)
Ltac pstep :=
  match goal with
  | |- pn_typed _ (Var _) _ _ _ => apply pn_var; [reflexivity|reflexivity]
  | |- pn_typed _ EUnit _ _ _ => apply pn_unit'; reflexivity
  | |- pn_typed _ (Inj1 _) _ _ _ => apply pn_inj1
  | |- pn_typed _ (Inj2 _) _ _ _ => apply pn_inj2
  | |- pn_typed _ (App ESpawn _) _ _ _ => eapply pn_fork
  | |- pn_typed _ (App ERecv _) _ _ _ => eapply pn_recv'
  | |- pn_typed _ (App (App ESend _) _) _ _ _ => eapply pn_send'; [reflexivity|..]
  | |- psok _ _ _ _ _ = true => reflexivity
  | |- payok _ => by right
  | |- un _ => done
  end.

Ltac lvs := match goal with
  | |- lvl_lt _ _ => simpl; lia
  | |- lvl_lt _ _ => simpl; done
  | |- @eq lvl _ _ => reflexivity
  | |- @eq pty _ _ => reflexivity
  end.

Ltac pfin := repeat pstep; try lvs.

(** ** Example 1, parallel Fibonacci, with unit only

    fix λfibo.λd.λc. case d of
      inj₁ _ ⇒ send c ()
      inj₂ _ ⇒ let a = new() in let b = new() in
               (fork λ_.fibo (inj₁ ()) a); (fork λ_.fibo (inj₂ ()) b);
               send c (plus (recv a) (recv b))

    The test n ≤ 1 is a case on d : unit + unit. fibo (n − 1) and
    fibo (n − 2) become fibo (inj₁ ()) and fibo (inj₂ ()), so the left
    spine ends and the right spine recurses forever. plus = λx.λy.() is
    the addition of unit values. a has level −2 and b level −1 (p. 11),
    because recv a comes before recv b and both come before send c. *)

Definition plus_pn : expr := Lam (Lam EUnit).

(** Inside the second branch: 0 = b!, 1 = b?, 2 = a!, 3 = a?, 4 = x,
    5 = c, 6 = d, 7 = fibo. Each e₁; e₂ is (λ_.e₂) e₁. *)
Definition fibo_rest : expr :=
  App (Lam
    (App (Lam
      (App (App ESend (Var 7)) (App (App plus_pn (App ERecv (Var 5))) (App ERecv (Var 3)))))
      (App ESpawn (Lam (App (App (Var 9) (Inj2 EUnit)) (Var 2))))))
    (App ESpawn (Lam (App (App (Var 8) (Inj1 EUnit)) (Var 3)))).

Definition fibo_pn : expr :=
  EBox (Lam (Lam (Case (Var 1)
    (App (App ESend (Var 1)) EUnit)
    (LetP (App ENew EUnit) (LetP (App ENew EUnit) fibo_rest))))).

(** let fibo = … in let c = new() in (fork λ_.fibo (inj₂ ()) c); recv c *)
Definition fibo_main : expr :=
  App (Lam (LetP (App ENew EUnit)
    (App (Lam (App ERecv (Var 2)))
         (App ESpawn (Lam (App (App (Var 3) (Inj2 EUnit)) (Var 1)))))))
    fibo_pn.

Definition SUM : pty := PSum PUnit PUnit.
Definition C0t : pty := PChan false PUnit 0.

(** fibo : unit + unit → ![unit]⁰ →^{⊤,0} unit (Example 3 with unit). *)
Definition fibo_ty : pty := PArr SUM None LBot (PArr C0t None (LZ 0) PUnit).

Lemma fibo_pn_typed : ∃ e', pn_typed [] fibo_pn fibo_ty LBot e'.
Proof.
  eexists. apply pn_fix; [by apply allun_un|].
  pfun. pfun.
  eapply pn_case'; [reflexivity|pfin|done|done| | | |].
  - (* inj₁ _ ⇒ send c () *)
    simpl. pfin.
  - (* inj₂ _ *)
    simpl. eapply (pn_new _ _ _ PUnit (-2)); [lv|by right|].
    eapply (pn_new _ _ _ PUnit (-1)); [lv|by right|]. unfold fibo_rest.
    eapply pn_app'; [reflexivity| | | | |].
    + simpl. pfunu.
      eapply pn_app'; [reflexivity| | | | |].
      * simpl. pfunu. eapply pn_send'; [reflexivity|pfin| | | | | |].
        -- simpl. eapply (pn_poly' _ _ _ _ _ _ _ _ _ _ _ _ 0); [reflexivity| | | | | |].
           ++ simpl. eapply (pn_poly' _ _ _ _ _ _ _ _ _ _ _ _ 0); [reflexivity| | | | | |].
              ** simpl. pfunu. pfunu. pfin.
              ** simpl. pfin.
              ** lvs.
              ** lvs.
              ** lvs.
              ** lvs.
           ++ simpl. pfin.
           ++ lvs.
           ++ lvs.
           ++ lvs.
           ++ lvs.
        -- lvs.
        -- by right.
        -- lvs.
        -- lvs.
        -- lvs.
      * simpl. pstep. pfun.
        eapply (pn_poly' _ _ _ _ _ _ _ _ _ _ _ _ (-1)); [reflexivity| | | | | |].
        -- simpl. eapply (pn_poly' _ _ _ _ _ _ _ _ _ _ _ _ 0); [reflexivity|pfin|simpl; pfin|lvs|lvs|lvs|lvs].
        -- simpl. pfin.
        -- lvs.
        -- lvs.
        -- lvs.
        -- lvs.
      * lvs.
      * lvs.
      * lvs.
    + simpl. pstep. pfun.
      eapply (pn_poly' _ _ _ _ _ _ _ _ _ _ _ _ (-2)); [reflexivity| | | | | |].
      * simpl. eapply (pn_poly' _ _ _ _ _ _ _ _ _ _ _ _ 0); [reflexivity|pfin|simpl; pfin|lvs|lvs|lvs|lvs].
      * simpl. pfin.
      * lvs.
      * lvs.
      * lvs.
      * lvs.
    + lvs.
    + lvs.
    + lvs.
  - lvs.
  - lvs.
Qed.

Lemma fibo_typed : ∃ τ e', pn_typed [] fibo_main PUnit τ e'.
Proof.
  destruct fibo_pn_typed as [fe Hf].
  eexists _, _. eapply (pn_poly' _ _ _ _ _ _ _ _ _ _ _ _ 0); [reflexivity| | | | | |].
  - simpl. eapply (pn_fun' _ _ _ _ fibo_ty); [|reflexivity|reflexivity|reflexivity].
    eapply (pn_new _ _ _ PUnit 0); [lv|by right|].
    eapply pn_app'; [reflexivity| | | | |].
    + simpl. pfunu. pfin.
    + simpl. pstep. pfun.
      eapply (pn_poly' _ _ _ _ _ _ _ _ _ _ _ _ 0); [reflexivity| | | | | |].
      * simpl. eapply (pn_poly' _ _ _ _ _ _ _ _ _ _ _ _ 0); [reflexivity|pfin|simpl; pfin|lvs|lvs|lvs|lvs].
      * simpl. pfin.
      * lvs.
      * lvs.
      * lvs.
      * lvs.
    + lvs.
    + lvs.
    + lvs.
  - simpl. exact Hf.
  - lvs.
  - lvs.
  - lvs.
  - lvs.
Qed.

(** Example 1 is deadlock free: its translation is a typed closed
    thread in the empty world under the top-level constraint [Crel]. *)
Theorem fibo_deadlock_free :
  ∃ τ e', pn_typed [] fibo_main PUnit τ e' ∧ deadlock_free (∅, {[+ e' +]}).
Proof.
  destruct fibo_typed as (τ & e' & H). exists τ, e'. split; [done|].
  by apply (pn_deadlock_free fibo_main τ).
Qed.

(** ** Example 2, the signal pipe, with the types of Example 4

    let cont = λx. let c = new() in (fork λ_.send x (wrap c)); c in
    let pipe = fix λpipe.λx.λy. pipe (unwrap (recv x)) (cont y) in
    let a = new() in let b = new() in
    (fork λ_.pipe a b); (fork λ_.pipe b (cont a))

    wrap and unwrap are erased, and [T-Conv] folds, unfolds, wraps and
    unwraps at the top of a type. tⁿ = μα.?[⌈α⌉²]ⁿ and
    sⁿ = ![⌈tⁿ⁺¹⌉²]ⁿ⁺¹ (p. 12). cont : s⁰ → s² and
    pipe : t⁰ → s⁰ →^{0,⊤} unit (p. 13). In the main program a has
    level 0 and b level 1, pipe a b is [T-App-Poly] at the shift 0,
    pipe b (cont a) at the shift 1 and cont a at the shift −1. *)

Definition tt (n : Z) : pty := PRec true 2 n.
Definition st (n : Z) : pty := PChan false (PDisp 2 (tt (n + 1))) (n + 1).

(** Under λx: 0 = c!, 1 = c?, 2 = x after the new. *)
Definition cont_pn : expr :=
  Lam (LetP (App ENew EUnit)
    (App (Lam (Var 1)) (App ESpawn (Lam (App (App ESend (Var 3)) (Var 2)))))).

(** Under λy: 0 = y, 1 = x, 2 = pipe, 3 = cont. *)
Definition pipe_pn : expr :=
  EBox (Lam (Lam (App (App (Var 2) (App ERecv (Var 1))) (App (Var 3) (Var 0))))).

(** After the two news: 0 = b!, 1 = b?, 2 = a!, 3 = a?, 4 = pipe, 5 = cont. *)
Definition pipe_main : expr :=
  App (Lam (App (Lam
    (LetP (App ENew EUnit) (LetP (App ENew EUnit)
      (App (Lam (App ESpawn (Lam (App (App (Var 6) (Var 3)) (App (Var 7) (Var 4))))))
           (App ESpawn (Lam (App (App (Var 5) (Var 4)) (Var 1))))))))
    pipe_pn))
    cont_pn.

Definition cont_ty : pty := PArr (st 0) None LBot (st 2).
Definition pipe_ty : pty := PArr (tt 0) None LBot (PArr (st 0) (Some 0%Z) LTop PUnit).

(** Fold a fresh ? end into tⁿ, and wrap tⁿ⁺² as ⌈tⁿ⌉². *)
Lemma fold_t p m n : pconv (PChan p (PDisp m (PRec p m n)) n) (PRec p m n).
Proof. eapply pconv_bw; [apply pc_unfold|apply pconv_refl]. Qed.

Lemma cont_typed : ∃ e', pn_typed [] cont_pn cont_ty LBot e'.
Proof.
  eexists. unfold cont_pn, cont_ty.
  eapply (pn_fun' _ _ _ _ (st 0)); [|reflexivity|reflexivity|reflexivity].
  eapply (pn_new _ _ _ (PDisp 2 (tt 3)) 3); [lv|by left|].
  eapply pn_app'; [reflexivity| | | | |].
  - simpl. pfunu. pfin.
  - simpl. pstep. pfun. eapply pn_send'; [reflexivity|pfin| | | | | |].
    + simpl. eapply pn_conv; [pfin|].
      eapply pconv_bw; [apply pc_unfold|].
      apply (pconv_bw _ (PDisp 2 (tt 1))); [apply pc_wrap|apply pconv_refl].
    + lvs.
    + by left.
    + lvs.
    + lvs.
    + lvs.
  - lvs.
  - lvs.
  - lvs.
Qed.

Lemma pipe_typed : ∃ e', pn_typed [Some cont_ty] pipe_pn pipe_ty LBot e'.
Proof.
  eexists. unfold pipe_pn, pipe_ty. apply pn_fix; [by apply allun_un|].
  eapply (pn_fun' _ _ _ _ (tt 0)); [|reflexivity|reflexivity|reflexivity].
  eapply (pn_fun' _ _ _ _ (st 0)); [|reflexivity|reflexivity|reflexivity].
  eapply pn_app'; [reflexivity| | | | |].
  - simpl. eapply (pn_poly' _ _ _ _ _ _ _ _ _ _ _ _ 2); [reflexivity| | | | | |].
    + simpl. pfin.
    + simpl. eapply pn_conv.
      * eapply pn_recv'; [eapply pn_conv; [pfin|]| | |].
        -- eapply pconv_fw; [apply pc_unfold|apply pconv_refl].
        -- lvs.
        -- by left.
        -- reflexivity.
      * eapply pconv_fw; [apply pc_wrap|apply pconv_refl].
    + lvs.
    + lvs.
    + reflexivity.
    + reflexivity.
  - simpl. eapply (pn_poly' _ _ _ _ _ _ _ _ _ _ _ _ 0); [reflexivity|pfin|simpl; pfin|lvs|lvs|lvs|lvs].
  - lvs.
  - lvs.
  - lvs.
Qed.

Lemma pipe_main_typed : ∃ τ e', pn_typed [] pipe_main PUnit τ e'.
Proof.
  destruct cont_typed as [ce Hc]. destruct pipe_typed as [pe Hp].
  eexists _, _. unfold pipe_main.
  eapply (pn_poly' _ _ _ _ _ _ _ _ _ _ _ _ 0); [reflexivity| | | | | |].
  - simpl. eapply (pn_fun' _ _ _ _ cont_ty); [|reflexivity|reflexivity|reflexivity].
    eapply (pn_poly' _ _ _ _ _ _ _ _ _ _ _ _ 0); [reflexivity| | | | | |].
    + simpl. eapply (pn_fun' _ _ _ _ pipe_ty); [|reflexivity|reflexivity|reflexivity].
      eapply (pn_new _ _ _ (PDisp 2 (tt 0)) 0); [lv|by left|].
      eapply (pn_new _ _ _ (PDisp 2 (tt 1)) 1); [lv|by left|].
      eapply pn_app'; [reflexivity| | | | |].
      * (* λ_. fork λ_.pipe b (cont a) *)
        simpl. pfunu. pstep. pfun.
        eapply pn_app'; [reflexivity| | | | |].
        -- simpl. eapply (pn_poly' _ _ _ _ _ _ _ _ _ _ _ _ 1); [reflexivity|pfin| | | | |].
           ++ simpl. eapply pn_conv; [pfin|apply fold_t].
           ++ lvs.
           ++ lvs.
           ++ reflexivity.
           ++ reflexivity.
        -- simpl. eapply (pn_poly' _ _ _ _ _ _ _ _ _ _ _ _ (-1)); [reflexivity|pfin|simpl; pfin|lvs|lvs|lvs|lvs].
        -- lvs.
        -- lvs.
        -- lvs.
      * (* fork λ_.pipe a b *)
        simpl. pstep. pfun.
        eapply pn_app'; [reflexivity| | | | |].
        -- simpl. eapply (pn_poly' _ _ _ _ _ _ _ _ _ _ _ _ 0); [reflexivity|pfin| | | | |].
           ++ simpl. eapply pn_conv; [pfin|apply fold_t].
           ++ lvs.
           ++ lvs.
           ++ reflexivity.
           ++ reflexivity.
        -- simpl. pfin.
        -- lvs.
        -- lvs.
        -- lvs.
      * lvs.
      * lvs.
      * lvs.
    + simpl. exact Hp.
    + lvs.
    + lvs.
    + lvs.
    + lvs.
  - simpl. exact Hc.
  - lvs.
  - lvs.
  - lvs.
  - lvs.
Qed.

(** Example 2 is deadlock free, although its two pipes form a cycle. *)
Theorem pipe_deadlock_free :
  ∃ τ e', pn_typed [] pipe_main PUnit τ e' ∧ deadlock_free (∅, {[+ e' +]}).
Proof.
  destruct pipe_main_typed as (τ & e' & H). exists τ, e'. split; [done|].
  by apply (pn_deadlock_free pipe_main τ).
Qed.

(** ** Fixes whose body is no abstraction

    The chapter uses two such fixes after Theorem 2 (pdf p. 14): the
    diverging thread ⟨fix λx.x⟩ and the thread ⟨send a (fix λx.x)⟩,
    which never uses a because the evaluation of the message diverges.
    Both fixes have type unit. [fixfork_main] adds a fix of arrow type
    whose body forks a thread before it returns a λ, and calls the fix
    twice. The source runs that body once, when the fix is evaluated,
    and so does the translation. *)

(** ⟨fix λx.x⟩ *)
Definition div_main : expr := EBox (Var 0).

Lemma div_typed : ∃ τ e', pn_typed [] div_main PUnit τ e'.
Proof. eexists _, _. apply pn_fix; [by apply allun_un|]. pfin. Qed.

(** let a = new() in (fork λ_.recv a); send a (fix λx.x)

    Under the λ of the sequence: 0 = _, 1 = a!, 2 = a?. *)
Definition divsend_main : expr :=
  LetP (App ENew EUnit)
    (App (Lam (App (App ESend (Var 1)) (EBox (Var 0))))
         (App ESpawn (Lam (App ERecv (Var 2))))).

Lemma divsend_typed : ∃ τ e', pn_typed [] divsend_main PUnit τ e'.
Proof.
  eexists _, _. eapply (pn_new _ _ _ PUnit 0); [lv|by right|].
  eapply pn_app'; [reflexivity| | | | |].
  - simpl. pfunu. eapply pn_send'; [reflexivity|pfin| | | | | |].
    + simpl. apply pn_fix; [by apply allun_un|]. pfin.
    + lvs.
    + by right.
    + lvs.
    + lvs.
    + lvs.
  - simpl. pstep. pfunu. pfin.
  - lvs.
  - lvs.
  - lvs.
Qed.

(** let g = fix λf.(λ_.λx.x) (fork λ_.()) in (g ()); (g ())

    g : unit → unit. The body of the fix is an application, so the fix
    is no λ. *)
Definition fixfork_pn : expr :=
  EBox (App (Lam (Lam (Var 0))) (App ESpawn (Lam EUnit))).

Definition fixfork_main : expr :=
  App (Lam (App (Lam (App (Var 1) EUnit)) (App (Var 0) EUnit))) fixfork_pn.

Definition uu : pty := PArr PUnit None LBot PUnit.

Lemma fixfork_pn_typed : ∃ e', pn_typed [] fixfork_pn uu LBot e'.
Proof.
  eexists. apply pn_fix; [by apply allun_un|].
  eapply (pn_poly' _ _ _ _ _ PUnit LBot uu _ _ _ _ 0); [reflexivity| | | | | |].
  - simpl. pfunu. pfunu. pfin.
  - simpl. pstep. pfunu. pfin.
  - lvs.
  - lvs.
  - reflexivity.
  - reflexivity.
Qed.

Lemma fixfork_typed : ∃ τ e', pn_typed [] fixfork_main PUnit τ e'.
Proof.
  destruct fixfork_pn_typed as [fe Hf].
  eexists _, _. eapply (pn_poly' _ _ _ _ _ uu LBot PUnit _ _ _ _ 0); [reflexivity| | | | | |].
  - simpl. eapply (pn_fun' _ _ _ _ uu); [|reflexivity|reflexivity|reflexivity].
    eapply (pn_poly' _ _ _ _ _ PUnit LBot PUnit _ _ _ _ 0); [reflexivity| | | | | |].
    + simpl. pfunu.
      eapply (pn_poly' _ _ _ _ _ PUnit LBot PUnit _ _ _ _ 0); [reflexivity|pfin|simpl; pfin|lvs|lvs|lvs|lvs].
    + simpl. eapply (pn_poly' _ _ _ _ _ PUnit LBot PUnit _ _ _ _ 0); [reflexivity|pfin|simpl; pfin|lvs|lvs|lvs|lvs].
    + lvs.
    + lvs.
    + lvs.
    + lvs.
  - simpl. exact Hf.
  - lvs.
  - lvs.
  - lvs.
  - lvs.
Qed.
