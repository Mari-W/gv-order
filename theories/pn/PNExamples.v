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

Lemma pn_app' Γ e1 e2 e1' e2' t r σ s τ1 τ2 :
  psok e1 0 e2 0 Γ = true →
  pn_typed (pl e1 0 Γ) e1 (PArr t (Some r) σ s) τ1 e1' →
  pn_typed (pl e2 0 Γ) e2 t τ2 e2' →
  lvl_lt τ1 (olvl (env_lev (pl e2 0 Γ))) → lvl_lt τ2 (LZ r) →
  pn_typed Γ (App e1 e2) s (lvl_max σ (lvl_max τ1 τ2)) (App e1' e2').
Proof. intros Hs. apply pn_app. by apply pl_split. Qed.

Lemma pn_poly' Γ e1 e2 e1' e2' t σ s τ1 τ2 n :
  psok e1 0 e2 0 Γ = true →
  pn_typed (pl e1 0 Γ) e1 (PArr t None σ s) τ1 e1' →
  pn_typed (pl e2 0 Γ) e2 (lshift n t) τ2 e2' →
  lvl_lt τ1 (olvl (env_lev (pl e2 0 Γ))) → lvl_lt τ2 LTop →
  pn_typed Γ (App e1 e2) (lshift n s) (lvl_max (lvl_sh n σ) (lvl_max τ1 τ2))
    (App (App EForce e1') e2').
Proof. intros Hs. apply pn_app_poly. by apply pl_split. Qed.

Lemma pn_send' Γ e1 e2 e1' e2' t n τ1 τ2 :
  psok e1 0 e2 0 Γ = true →
  pn_typed (pl e1 0 Γ) e1 (PChan false t n) τ1 e1' →
  pn_typed (pl e2 0 Γ) e2 t τ2 e2' →
  lvl_lt (LZ n) (olvl (tlev t)) → payok t →
  lvl_lt τ1 (olvl (env_lev (pl e2 0 Γ))) → lvl_lt τ2 (LZ n) →
  pn_typed Γ (App (App ESend e1) e2) PUnit (lvl_max (LZ n) (lvl_max τ1 τ2))
    (App (App send_tr e1') e2').
Proof. intros Hs. apply pn_send. by apply pl_split. Qed.

Lemma pn_case' Γ e e1 e2 e' e1' e2' t s u τ1 τ2 :
  psok e 0 (Lam (Lam (App e1 e2))) 0 Γ = true →
  pn_typed (pl e 0 Γ) e (PSum t s) τ1 e' → un t → un s →
  pn_typed (Some t :: pl (Lam (Lam (App e1 e2))) 0 Γ) e1 u τ2 e1' →
  pn_typed (Some s :: pl (Lam (Lam (App e1 e2))) 0 Γ) e2 u τ2 e2' →
  lvl_lt τ1 (olvl (env_lev (pl (Lam (Lam (App e1 e2))) 0 Γ))) →
  pn_typed Γ (Case e e1 e2) u (lvl_max τ1 τ2) (Case (App EForce e') e1' e2').
Proof. intros Hs. apply pn_case. by apply pl_split. Qed.

Lemma pn_eff Γ e t τ τ' e' : pn_typed Γ e t τ e' → τ = τ' → pn_typed Γ e t τ' e'.
Proof. by intros ? ->. Qed.

Ltac lv := simpl; try done; try lia.

(** One step, by the head of the term. *)
Ltac pstep :=
  match goal with
  | |- pn_typed _ (Var _) _ _ _ => apply pn_var; [reflexivity|reflexivity]
  | |- pn_typed _ EUnit _ _ _ => apply pn_unit'; reflexivity
  | |- pn_typed _ (Lam _) _ _ _ => apply pn_fun
  | |- pn_typed _ (Inj1 _) _ _ _ => apply pn_inj1; [|done|done]
  | |- pn_typed _ (Inj2 _) _ _ _ => apply pn_inj2; [|done|done]
  | |- pn_typed _ (LetP (App ENew EUnit) _) _ _ _ => apply pn_new; [lv|by right|]
  | |- pn_typed _ (App ESpawn _) _ _ _ => apply pn_fork
  | |- pn_typed _ (App ERecv _) _ _ _ => apply pn_recv; [|lv|by right]
  | |- pn_typed _ (App (App ESend _) _) _ _ _ => eapply pn_send'; [reflexivity| | |lv|by right|lv|lv]
  end.

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

Lemma fibo_pn_typed Γ :
  allun Γ = true → ∃ e', pn_typed Γ fibo_pn fibo_ty LBot e'.
Proof.
  intros HΓ. eexists. apply pn_fix; [by apply allun_un|].
  eapply pn_conv; [|apply pconv_refl].
Abort.
