(** * alternating bit protocol: typable, lock-free fragment (Padovani 2014, Example III.8)

    Padovani's protocol (padovani2014deadlock p9), in the linear
    π-calculus with continuation passing:

      Bob    = *bob?(x, y).(νa b) x?(x̄).(x̄!⟨a⟩ | y?(ȳ).(ȳ!⟨b⟩ | bob!⟨a, b⟩))
      Alice0 = *alice0?(x, z).(νa c) x!⟨a⟩ | z!⟨c⟩ | a?(x̄).c?(z̄).alice0!⟨x̄, z̄⟩
      Alice1 = *alice1?(y, z).(νb c) z?(z̄).(y!⟨b⟩ | z̄!⟨c⟩ | b?(ȳ).alice1!⟨ȳ, c⟩)

    Alice sends M0 on x and M1 on y, Bob acknowledges each, and the two
    Alice threads alternate through z, which Bob does not know. The
    translation replaces each continuation channel by the continuation
    of one session end and the parallel sends by sequential ones.

      AB = μX. !∗.?∗.X
      bob    : □(∀ι₁ ι₂ ζ. C_B. ∗ ⊸ (AB‾@ι₁ ⊗ AB‾@ι₂ ⊸^ζ ∗))
      bob    = !(f = λp. let (x, y) = p in let (u, x) = recv x in let () = u in
                  let x = send ⟨∗, x⟩ in let (v, y) = recv y in let () = v in
                  (force f) ⟨x, send ⟨∗, y⟩⟩)
      alice0 : □(∀ι₁ ι₂ ζ. C_A. ∗ ⊸ (AB@ι₁ ⊗ AB@ι₂ ⊸^ζ ∗))
      alice0 = !(g = λp. let (x, z) = p in let x = send ⟨∗, x⟩ in let z = send ⟨∗, z⟩ in
                  let (u, x) = recv x in let () = u in let (v, z) = recv z in let () = v in
                  (force g) ⟨x, z⟩)
      alice1 : □(∀ι₁ ι₂ ζ. C_C. ∗ ⊸ (AB@ι₁ ⊗ AB‾@ι₂ ⊸^ζ ∗))
      alice1 = !(h = λp. let (y, z) = p in let (u, z) = recv z in let () = u in
                  let y = send ⟨∗, y⟩ in let z = send ⟨∗, z⟩ in
                  let (v, y) = recv y in let () = v in (force h) ⟨y, z⟩)
      abp_main = let (b, q) = ⟨bob, ⟨alice0, alice1⟩⟩ in let (a0, a1) = q in
                 let (x, x′) = new@χ ∗ in let (y, y′) = new@υ ∗ in let (z, z′) = new@ζ ∗ in
                 let () = spawn (λw. let () = w in (force b) ⟨x′, y′⟩) in
                 let () = spawn (λw. let () = w in (force a1) ⟨y, z′⟩) in
                 (force a0) ⟨x, z⟩

    All three recursions are tail calls under the ceiling ζ, as in
    TailCall.v. A round acts twice on each end, so the call goes to
    (ι₁+2, ι₂+2, ζ). Each box constraint is a round template
    ([abp_P]): a tuple (a, i, b, j) stands for ι_a+2k+i ≺ (ι_b+2k+j)‾ at
    every k, and every point of ι₁ and ι₂ lies below ζ.

    main runs at the top-level points χ = 0, υ = 1, ζ = 2 and the
    ceiling θ = 3. The instants of the three channels interleave as
    X₀ Z₀ X₁ Y₀ Z₁ Y₁ X₂ Z₂ … ([rk]), below θ. *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export examples.ExampleTools.
From LRGV Require Import examples.cfst.CfstTools.
From LRGV Require examples.cfst.CfstScheduler.

Set Default Proof Using "All".

Definition AB : sty := SMu (SSeq (SSnd 0 TUnit) (SSeq (SRcv 0 TUnit) (SVar 0))).

(** ** Box constraints from a round template *)

Definition abp_P (fs : list (nat * nat * nat * nat)) (g : fact) : Prop :=
  (∃ k a i b j, (a, i, b, j) ∈ fs ∧ a < 2 ∧ b < 2 ∧
     g = FLt (pv a (2 * k + i)) (pt_dual (pv b (2 * k + j)))) ∨
  (∃ n a, a < 2 ∧ g = FLt (pv a n) (pv 2 0)).
Definition abp_C fs : bcs := BCs [] (abp_P fs).

Lemma abp_inst_v a m : a < 2 → pt_inst (plist [pv 0 2; pv 1 2; pv 2 0]) (pv a m) = pv a (2 + m).
Proof. intros Ha. destruct a as [|[|]]; [reflexivity|reflexivity|lia]. Qed.

Lemma abp_sub fs g : abp_P fs g → fact_scoped 3 g → abp_P fs (fact_map (pt_inst (plist [pv 0 2; pv 1 2; pv 2 0])) g).
Proof.
  intros [(k & a & i & b & j & Hin & Ha & Hb & ->)|(n & a & Ha & ->)] _; cbn [fact_map];
    rewrite ?pt_inst_dual, !abp_inst_v by done.
  - left. exists (S k), a, i, b, j. split_and!; [done|done|done|].
    replace (2 * S k + i) with (2 + (2 * k + i)) by lia.
    replace (2 * S k + j) with (2 + (2 * k + j)) by lia. reflexivity.
  - right. exists (2 + n), a. split; [done|reflexivity].
Qed.

Lemma abp_call W Ψ fs : (abp_C fs, ids 3) ∈ Ψ → bcs_hold (seqs W Ψ) (slt W Ψ) (abp_C fs) [pv 0 2; pv 1 2; pv 2 0].
Proof. intros Hg. apply bcs_hold_self; [done|vb_list|apply abp_sub]. Qed.

Lemma abp_hyp W Ψ fs x y :
  (abp_C fs, ids 3) ∈ Ψ → abp_P fs (FLt x y) → fact_scoped 3 (FLt x y) → slt W Ψ x y.
Proof.
  intros Hg HP Hs. eapply (sl_hyp0 _ _ (abp_P fs) (ids 3) x y); [done|done|done| |].
  all: by destruct Hs; apply pt_inst_ids.
Qed.

Lemma abp_kn W Ψ fs a k : (abp_C fs, ids 3) ∈ Ψ → a < 3 → skn W Ψ (pv a k).
Proof.
  intros Hg Ha. apply (skn_in W Ψ (abp_C fs) (ids 3) (pvar a)); [done| |done].
  destruct a as [|[|[|]]]; [inlist|inlist|inlist|lia].
Qed.

Lemma abp_kn3 W Ψ fs : (abp_C fs, ids 3) ∈ Ψ → Forall (skn W Ψ) [pv 0 2; pv 1 2; pv 2 0].
Proof.
  intros Hg. constructor; [|constructor; [|constructor; [|constructor]]]; apply (abp_kn W Ψ fs); first [done|lia].
Qed.

(** ι_a+i ≺ (ι_b+j)‾ at k = 0, and ι_a+n ≺ ζ. *)
Ltac abf a i b j :=
  eapply abp_hyp; [by left|left; exists 0, a, i, b, j; split_and!; [inlist|lia|lia|reflexivity]|cbn; lia].
Ltac abz a n :=
  eapply abp_hyp; [by left|right; exists n, a; split; [lia|reflexivity]|cbn; lia].

(** ** The three boxes *)

Definition fsB : list (nat * nat * nat * nat) := [(0, 0, 1, 0); (0, 1, 1, 0); (1, 0, 0, 2); (1, 1, 0, 2)].
Definition fsA : list (nat * nat * nat * nat) := [(0, 0, 1, 0); (1, 0, 0, 1); (0, 1, 1, 1); (1, 1, 0, 2)].
Definition fsC : list (nat * nat * nat * nat) := [(1, 0, 0, 0); (0, 0, 1, 1); (1, 1, 0, 1); (0, 1, 1, 2)].

Definition bob_body : ty :=
  TLolli (Some (pv 2 0)) None (TProd (TSess (dual AB) (pv 0 0)) (TSess (dual AB) (pv 1 0))) TUnit.
Definition al0_body : ty :=
  TLolli (Some (pv 2 0)) None (TProd (TSess AB (pv 0 0)) (TSess AB (pv 1 0))) TUnit.
Definition al1_body : ty :=
  TLolli (Some (pv 2 0)) None (TProd (TSess AB (pv 0 0)) (TSess (dual AB) (pv 1 0))) TUnit.

Definition bob_ty : ty := TBox 3 0 (abp_C fsB) (TLolli None None TUnit bob_body).
Definition al0_ty : ty := TBox 3 0 (abp_C fsA) (TLolli None None TUnit al0_body).
Definition al1_ty : ty := TBox 3 0 (abp_C fsC) (TLolli None None TUnit al1_body).

Definition bob : expr :=
  EBox (Lam (LetP (Var 0)
    (LetP (App ERecv (Var 1)) (LetU (Var 1)
    (LetP (Pair (App ESend (Pair EUnit (Var 0))) EUnit) (LetU (Var 0)
    (LetP (App ERecv (Var 4)) (LetU (Var 1)
    (App (App EForce (Var 9)) (Pair (Var 3) (App ESend (Pair EUnit (Var 0))))))))))))).

Definition alice0 : expr :=
  EBox (Lam (LetP (Var 0)
    (LetP (Pair (App ESend (Pair EUnit (Var 1))) EUnit) (LetU (Var 0)
    (LetP (Pair (App ESend (Pair EUnit (Var 2))) EUnit) (LetU (Var 0)
    (LetP (App ERecv (Var 3)) (LetU (Var 1)
    (LetP (App ERecv (Var 3)) (LetU (Var 1)
    (App (App EForce (Var 11)) (Pair (Var 2) (Var 0))))))))))))).

Definition alice1 : expr :=
  EBox (Lam (LetP (Var 0)
    (LetP (App ERecv (Var 0)) (LetU (Var 1)
    (LetP (Pair (App ESend (Pair EUnit (Var 3))) EUnit) (LetU (Var 0)
    (LetP (Pair (App ESend (Pair EUnit (Var 2))) EUnit) (LetU (Var 0)
    (LetP (App ERecv (Var 3)) (LetU (Var 1)
    (App (App EForce (Var 11)) (Pair (Var 0) (Var 3))))))))))))).

Ltac box_open3 C T :=
  try change (bcs_inst (pshift 3) C) with C;
  change (lenv_pinst (pshift 3) [Some (TBox 3 0 C (TLolli None None TUnit T))])
    with [Some (pinst_ty (pshift 3) (TBox 3 0 C (TLolli None None TUnit T)))];
  rewrite (pinst_closed _ (TBox 3 0 C (TLolli None None TUnit T))) by (split; [constructor|]; unfold T; body_scope).

Lemma bob_typed W F : world_wf W → typed W ∅ [] ∅ [] F bob bob_ty.
Proof.
  intros HW. unfold bob, bob_ty.
  apply (t_exp W _ _ _ _ _ _ _ _ _ _ 0); [by intros o Ho; apply elem_of_nil in Ho|set_solver|box_k0].
  box_open3 (abp_C fsB) bob_body. cbn. unfold bob_body.
  eapply (tv_lam W HW _ _ _ _ _ _ _ _ None 1); [set_solver|cbn; set_solver|].
  cbn. tstep; [tstep|]. cbn.
  (* recv M0 on x at ι₁ *)
  tstep.
  { eapply (tv_appk W HW _ _ _ _ KRecv _ (Some (pv 0 0))
              (TSess (SSeq (SRcv 0 TUnit) (SSeq (SSnd 0 TUnit) (dual AB))) (pv 0 0))).
    - eapply t_conv; [|tstep]. conv_sess.
    - apply KTRecv.
    - kscope.
    - apply ubs_intro; [intros y Hy; mem_cases Hy; abf 0 0 1 0|].
      exists (pv 2 0). split; [done|]. right. abz 0 0. }
  cbn. tstep; [tstep|]. cbn.
  (* send A0 on x at ι₁+1 *)
  tstep.
  { tstep; [tstep|].
    eapply (tv_appk W HW _ _ _ _ KSend _ (Some (pv 0 1)) (TProd TUnit (TSess (SSeq (SSnd 0 TUnit) (dual AB)) (pv 0 1)))).
    - tstep; tstep.
    - apply (KTSend _ _ _ 0 TUnit (dual AB) (pv 0 1)). cbn. set_solver.
    - kscope.
    - apply ubs_intro; [intros y Hy; mem_cases Hy; abf 0 1 1 0|].
      exists (pv 2 0). split; [done|]. right. abz 0 1. }
  cbn. tstep; [tstep|]. cbn.
  (* recv M1 on y at ι₂ *)
  tstep.
  { eapply (tv_appk W HW _ _ _ _ KRecv _ (Some (pv 1 0))
              (TSess (SSeq (SRcv 0 TUnit) (SSeq (SSnd 0 TUnit) (dual AB))) (pv 1 0))).
    - eapply t_conv; [|tstep]. conv_sess.
    - apply KTRecv.
    - kscope.
    - apply ubs_intro; [intros y Hy; mem_cases Hy; abf 1 0 0 2|].
      exists (pv 2 0). split; [done|]. right. abz 1 0. }
  cbn. tstep; [tstep|]. cbn.
  (* send A1 on y at ι₂+1 inside the argument, then the tail call *)
  eapply tv_app; [exact HW|reflexivity| | |].
  - apply (typed_force0 W _ _ _ _ _ _ 3 (abp_C fsB) None bob_body [pv 0 2; pv 1 2; pv 2 0]);
      [done|done|apply abp_call; by left|apply (abp_kn3 W _ fsB); by left|apply ubs_none|tstep].
  - eapply (tv_pair W HW _ _ _ _ _ _ (TSess (dual AB) (pv 0 2))); [reflexivity| |tstep].
    eapply (tv_appk W HW _ _ _ _ KSend _ (Some (pv 1 1)) (TProd TUnit (TSess (SSeq (SSnd 0 TUnit) (dual AB)) (pv 1 1)))).
    + tstep; tstep.
    + apply (KTSend _ _ _ 0 TUnit (dual AB) (pv 1 1)). cbn. set_solver.
    + kscope.
    + apply ubs_intro; [intros y Hy; mem_cases Hy; abf 1 1 0 2|].
      exists (pv 2 0). split; [done|]. right. abz 1 1.
  - apply ubs_intro; [intros y Hy; mem_cases Hy|].
    exists (pv 2 0). split; [done|]. apply sle_refl, HW.
Qed.

Lemma alice0_typed W F : world_wf W → typed W ∅ [] ∅ [] F alice0 al0_ty.
Proof.
  intros HW. unfold alice0, al0_ty.
  apply (t_exp W _ _ _ _ _ _ _ _ _ _ 0); [by intros o Ho; apply elem_of_nil in Ho|set_solver|box_k0].
  box_open3 (abp_C fsA) al0_body. cbn. unfold al0_body.
  eapply (tv_lam W HW _ _ _ _ _ _ _ _ None 1); [set_solver|cbn; set_solver|].
  cbn. tstep; [tstep|]. cbn.
  (* send M0 on x at ι₁ *)
  tstep.
  { tstep; [tstep|].
    eapply (tv_appk W HW _ _ _ _ KSend _ (Some (pv 0 0))
              (TProd TUnit (TSess (SSeq (SSnd 0 TUnit) (SSeq (SRcv 0 TUnit) AB)) (pv 0 0)))).
    - tstep; [|tstep]. eapply t_conv; [|tstep]. conv_sess.
    - apply (KTSend _ _ _ 0 TUnit (SSeq (SRcv 0 TUnit) AB) (pv 0 0)). cbn. set_solver.
    - kscope.
    - apply ubs_intro; [intros y Hy; mem_cases Hy; abf 0 0 1 0|].
      exists (pv 2 0). split; [done|]. right. abz 0 0. }
  cbn. tstep; [tstep|]. cbn.
  (* send the turn on z at ι₂ *)
  tstep.
  { tstep; [tstep|].
    eapply (tv_appk W HW _ _ _ _ KSend _ (Some (pv 1 0))
              (TProd TUnit (TSess (SSeq (SSnd 0 TUnit) (SSeq (SRcv 0 TUnit) AB)) (pv 1 0)))).
    - tstep; [|tstep]. eapply t_conv; [|tstep]. conv_sess.
    - apply (KTSend _ _ _ 0 TUnit (SSeq (SRcv 0 TUnit) AB) (pv 1 0)). cbn. set_solver.
    - kscope.
    - apply ubs_intro; [intros y Hy; mem_cases Hy; abf 1 0 0 1|].
      exists (pv 2 0). split; [done|]. right. abz 1 0. }
  cbn. tstep; [tstep|]. cbn.
  (* recv A0 on x at ι₁+1 *)
  tstep.
  { eapply (tv_appk W HW _ _ _ _ KRecv _ (Some (pv 0 1)) (TSess (SSeq (SRcv 0 TUnit) AB) (pv 0 1)));
      [tstep|apply KTRecv|kscope|].
    apply ubs_intro; [intros y Hy; mem_cases Hy; abf 0 1 1 1|].
    exists (pv 2 0). split; [done|]. right. abz 0 1. }
  cbn. tstep; [tstep|]. cbn.
  (* recv the turn on z at ι₂+1 *)
  tstep.
  { eapply (tv_appk W HW _ _ _ _ KRecv _ (Some (pv 1 1)) (TSess (SSeq (SRcv 0 TUnit) AB) (pv 1 1)));
      [tstep|apply KTRecv|kscope|].
    apply ubs_intro; [intros y Hy; mem_cases Hy; abf 1 1 0 2|].
    exists (pv 2 0). split; [done|]. right. abz 1 1. }
  cbn. tstep; [tstep|]. cbn.
  eapply tv_app; [exact HW|reflexivity| | |].
  - apply (typed_force0 W _ _ _ _ _ _ 3 (abp_C fsA) None al0_body [pv 0 2; pv 1 2; pv 2 0]);
      [done|done|apply abp_call; by left|apply (abp_kn3 W _ fsA); by left|apply ubs_none|tstep].
  - tstep; tstep.
  - apply ubs_intro; [intros y Hy; mem_cases Hy|].
    exists (pv 2 0). split; [done|]. apply sle_refl, HW.
Qed.

Lemma alice1_typed W F : world_wf W → typed W ∅ [] ∅ [] F alice1 al1_ty.
Proof.
  intros HW. unfold alice1, al1_ty.
  apply (t_exp W _ _ _ _ _ _ _ _ _ _ 0); [by intros o Ho; apply elem_of_nil in Ho|set_solver|box_k0].
  box_open3 (abp_C fsC) al1_body. cbn. unfold al1_body.
  eapply (tv_lam W HW _ _ _ _ _ _ _ _ None 1); [set_solver|cbn; set_solver|].
  cbn. tstep; [tstep|]. cbn.
  (* recv the turn on z at ι₂ *)
  tstep.
  { eapply (tv_appk W HW _ _ _ _ KRecv _ (Some (pv 1 0))
              (TSess (SSeq (SRcv 0 TUnit) (SSeq (SSnd 0 TUnit) (dual AB))) (pv 1 0))).
    - eapply t_conv; [|tstep]. conv_sess.
    - apply KTRecv.
    - kscope.
    - apply ubs_intro; [intros y Hy; mem_cases Hy; abf 1 0 0 0|].
      exists (pv 2 0). split; [done|]. right. abz 1 0. }
  cbn. tstep; [tstep|]. cbn.
  (* send M1 on y at ι₁ *)
  tstep.
  { tstep; [tstep|].
    eapply (tv_appk W HW _ _ _ _ KSend _ (Some (pv 0 0))
              (TProd TUnit (TSess (SSeq (SSnd 0 TUnit) (SSeq (SRcv 0 TUnit) AB)) (pv 0 0)))).
    - tstep; [|tstep]. eapply t_conv; [|tstep]. conv_sess.
    - apply (KTSend _ _ _ 0 TUnit (SSeq (SRcv 0 TUnit) AB) (pv 0 0)). cbn. set_solver.
    - kscope.
    - apply ubs_intro; [intros y Hy; mem_cases Hy; abf 0 0 1 1|].
      exists (pv 2 0). split; [done|]. right. abz 0 0. }
  cbn. tstep; [tstep|]. cbn.
  (* hand the turn back on z at ι₂+1 *)
  tstep.
  { tstep; [tstep|].
    eapply (tv_appk W HW _ _ _ _ KSend _ (Some (pv 1 1)) (TProd TUnit (TSess (SSeq (SSnd 0 TUnit) (dual AB)) (pv 1 1)))).
    - tstep; tstep.
    - apply (KTSend _ _ _ 0 TUnit (dual AB) (pv 1 1)). cbn. set_solver.
    - kscope.
    - apply ubs_intro; [intros y Hy; mem_cases Hy; abf 1 1 0 1|].
      exists (pv 2 0). split; [done|]. right. abz 1 1. }
  cbn. tstep; [tstep|]. cbn.
  (* recv A1 on y at ι₁+1 *)
  tstep.
  { eapply (tv_appk W HW _ _ _ _ KRecv _ (Some (pv 0 1)) (TSess (SSeq (SRcv 0 TUnit) AB) (pv 0 1)));
      [tstep|apply KTRecv|kscope|].
    apply ubs_intro; [intros y Hy; mem_cases Hy; abf 0 1 1 2|].
    exists (pv 2 0). split; [done|]. right. abz 0 1. }
  cbn. tstep; [tstep|]. cbn.
  eapply tv_app; [exact HW|reflexivity| | |].
  - apply (typed_force0 W _ _ _ _ _ _ 3 (abp_C fsC) None al1_body [pv 0 2; pv 1 2; pv 2 0]);
      [done|done|apply abp_call; by left|apply (abp_kn3 W _ fsC); by left|apply ubs_none|tstep].
  - tstep; tstep.
  - apply ubs_intro; [intros y Hy; mem_cases Hy|].
    exists (pv 2 0). split; [done|]. apply sle_refl, HW.
Qed.

(** ** main, under the top-level constraint over χ, υ, ζ, θ *)

Definition abp_main : expr :=
  LetP (Pair bob (Pair alice0 alice1)) (LetP (Var 0)
    (let_new_pair (let_new_pair (let_new_pair
      (LetU (App ESpawn (Lam (LetU (Var 0) (App (App EForce (Var 10)) (Pair (Var 5) (Var 3))))))
      (LetU (App ESpawn (Lam (LetU (Var 0) (App (App EForce (Var 7)) (Pair (Var 4) (Var 1))))))
        (App (App EForce (Var 7)) (Pair (Var 5) (Var 1))))))))).

(** Bob holds x′ at χ̄ and y′ at ῡ, Alice0 x at χ and z at ζ, Alice1 y at
    υ and z′ at ζ̄. *)
Definition abp_inst : list (list (nat * nat * nat * nat) * list point) :=
  [(fsB, [pt_dual (pv 0 0); pt_dual (pv 1 0); pv 3 0]);
   (fsA, [pv 0 0; pv 2 0; pv 3 0]);
   (fsC, [pv 1 0; pt_dual (pv 2 0); pv 3 0])].

(** Besides the box facts at their instances, C₀ puts χ ≺ υ and ζ ≺ ῡ,
    so that the two spawned threads of main have a lower point. *)
Definition abp0_P (g : fact) : Prop :=
  (∃ fs xs g0, (fs, xs) ∈ abp_inst ∧ abp_P fs g0 ∧ g = fact_map (pt_inst (plist xs)) g0) ∨
  g = FLt (pv 0 0) (pv 1 0) ∨ g = FLt (pv 2 0) (pt_dual (pv 1 0)).
Definition abp0_C : bcs := BCs [] abp0_P.

Lemma abp0_hyp W x y : abp0_P (FLt x y) → fact_scoped 4 (FLt x y) → slt W [(abp0_C, ids 4)] x y.
Proof.
  intros H Hs. eapply (sl_hyp0 _ _ abp0_P (ids 4) x y); [by left|done|done| |].
  all: by destruct Hs; apply pt_inst_ids.
Qed.

Lemma abp_force W fs xs :
  (fs, xs) ∈ abp_inst → bcs_hold (seqs W [(abp0_C, ids 4)]) (slt W [(abp0_C, ids 4)]) (abp_C fs) xs.
Proof.
  intros Hin. apply bcs_hold_intro. intros g HP Hs.
  assert (Forall (λ y, pn_vb 4 (pt_name y)) xs) as Hvb.
  { repeat (apply elem_of_cons in Hin as [Hin|Hin]; [injection Hin as -> ->; vb_list|]).
    by apply elem_of_nil in Hin. }
  pose proof (fact_scoped_inst 4 xs g Hvb Hs) as Hs4.
  assert (abp0_P (fact_map (pt_inst (plist xs)) g)) as H0 by (left; exists fs, xs, g; done).
  revert H0 Hs4. destruct (fact_map (pt_inst (plist xs)) g) as [x y]. intros H0 Hs4.
  cbn [fact_holds]. by apply abp0_hyp.
Qed.

Lemma abp_typed : styped ∅ [(abp0_C, ids 4)] [] (∅, None) abp_main TUnit.
Proof.
  apply styped_Wpo. pose proof Wpo_nil_strict' as HWs.
  pose proof (proj1 HWs) as HW. set (W := Wpo []) in *. unfold abp_main.
  assert (∀ a, a < 4 → skn W [(abp0_C, ids 4)] (pv a 0)) as Hkn.
  { intros a Ha. apply (skn_in W _ abp0_C (ids 4) (pvar a)); [by left| |done].
    destruct a as [|[|[|[|]]]]; [inlist|inlist|inlist|inlist|lia]. }
  tstep.
  { tstep; [tstep; apply typed_hyps_wk; [exact HWs|apply alice1_typed, HW|exact HWs|apply alice0_typed, HW]|].
    apply typed_hyps_wk; [exact HWs|apply bob_typed, HW]. }
  cbn. tstep; [tstep|]. cbn.
  apply (t_new_at W _ _ _ _ _ _ _ AB (pv 0 0) HWs); [apply Hkn; lia|].
  apply (t_new_at W _ _ _ _ _ _ _ AB (pv 1 0) HWs); [apply Hkn; lia|].
  apply (t_new_at W _ _ _ _ _ _ _ AB (pv 2 0) HWs); [apply Hkn; lia|].
  cbn. tstep.
  { (* Bob at (χ̄, ῡ, θ) *)
    tstep; [|apply KTSpawn|done|apply ubs_none].
    eapply (tv_lam W HW _ _ _ _ _ TUnit TUnit (Some (pv 3 0)) (Some (pv 0 0)) 0); [set_solver| |].
    { intros y Hy. mem_cases Hy;
        first [apply sle_refl, HW|right; apply abp0_hyp; [right; left; reflexivity|cbn; lia]]. }
    cbn. tstep; [tstep|]. cbn.
    eapply tv_app; [exact HW|reflexivity| | |].
    - apply (typed_force0 W _ _ _ _ _ _ 3 (abp_C fsB) None bob_body [pt_dual (pv 0 0); pt_dual (pv 1 0); pv 3 0]);
        [done|done|apply abp_force; by left|constructor; [|constructor; [|constructor; [|constructor]]]; apply Hkn; lia|apply ubs_none|tstep].
    - tstep; tstep.
    - apply ubs_intro; [intros y Hy; mem_cases Hy|].
      exists (pv 3 0). split; [done|]. apply sle_refl, HW. }
  cbn. tstep.
  { (* Alice1 at (υ, ζ̄, θ) *)
    tstep; [|apply KTSpawn|done|apply ubs_none].
    eapply (tv_lam W HW _ _ _ _ _ TUnit TUnit (Some (pv 3 0)) (Some (pv 2 0)) 0); [set_solver| |].
    { intros y Hy. mem_cases Hy;
        first [apply sle_refl, HW|right; apply abp0_hyp; [right; right; reflexivity|cbn; lia]]. }
    cbn. tstep; [tstep|]. cbn.
    eapply tv_app; [exact HW|reflexivity| | |].
    - apply (typed_force0 W _ _ _ _ _ _ 3 (abp_C fsC) None al1_body [pv 1 0; pt_dual (pv 2 0); pv 3 0]);
        [done|done|apply abp_force; by right; right; left|constructor; [|constructor; [|constructor; [|constructor]]]; apply Hkn; lia|apply ubs_none|tstep].
    - tstep; tstep.
    - apply ubs_intro; [intros y Hy; mem_cases Hy|].
      exists (pv 3 0). split; [done|]. apply sle_refl, HW. }
  (* Alice0 at (χ, ζ, θ) *)
  cbn. eapply tv_app; [exact HW|reflexivity| | |].
  - apply (typed_force0 W _ _ _ _ _ _ 3 (abp_C fsA) None al0_body [pv 0 0; pv 2 0; pv 3 0]);
      [done|done|apply abp_force; by right; left|constructor; [|constructor; [|constructor; [|constructor]]]; apply Hkn; lia|apply ubs_none|tstep].
  - tstep; tstep.
  - apply ubs_intro; [intros y Hy; mem_cases Hy|done].
Qed.

(** ** The rank of the top-level constraint *)

(** rk c k = 6⌊k/2⌋ + b(c, k mod 2): χ at (0, 2), υ at (3, 5), ζ at
    (1, 4). *)
Definition abp_b0 (c : nat) : nat := match c with 0 => 0 | 1 => 3 | 2 => 1 | _ => 0 end.
Definition abp_b1 (c : nat) : nat := match c with 0 => 2 | 1 => 5 | 2 => 4 | _ => 1 end.

Definition rk (c k : nat) : nat := 6 * Nat.div2 k + (if Nat.even k then abp_b0 c else abp_b1 c).

Lemma rk_S c k : rk c k < rk c (S k).
Proof.
  unfold rk. assert (abp_b0 c < abp_b1 c ∧ abp_b1 c < abp_b0 c + 6) as [Hb1 Hb2]
    by (destruct c as [|[|[|]]]; cbn; lia).
  destruct (CfstScheduler.div2_even_S k) as [(H1 & H2 & H3)|(H1 & H2 & H3)]; rewrite H1, H2, H3; lia.
Qed.

Lemma rk_2k c k i : rk c (2 * k + i) = 6 * k + rk c i.
Proof.
  induction k as [|k IH]; [done|].
  replace (2 * S k + i) with (S (S (2 * k + i))) by lia.
  unfold rk in *. cbn [Nat.div2 Nat.even]. lia.
Qed.

(** The name index of a top-level point, constant or variable. *)
Definition pidx (p : pname) : option nat :=
  match p with NVar c | NConst c => Some c | _ => None end.

Definition abp_rank (x : point) : nat * nat :=
  match pidx (pt_name x) with
  | Some 3 => (1, pt_off x)
  | Some c => (0, rk c (pt_off x))
  | None => (0, pt_off x)
  end.

Lemma abp_rank_shift x : lexlt (abp_rank x) (abp_rank (pt_shift 1 x)).
Proof.
  unfold abp_rank, pt_shift, lexlt. cbn -[rk].
  destruct (pidx (pt_name x)) as [[|[|[|[|c]]]]|]; cbn -[rk]; try lia;
    (right; refine (conj eq_refl _); rewrite Nat.add_1_r; apply rk_S).
Qed.

Lemma abp_rank_facts x y : abp0_P (FLt x y) → lexlt (abp_rank x) (abp_rank y).
Proof.
  intros [(fs & xs & g0 & Hin & HP & E)|[E|E]];
    [|injection E as -> ->; unfold lexlt, abp_rank; cbn; lia|injection E as -> ->; unfold lexlt, abp_rank; cbn; lia].
  unfold abp_inst in Hin. apply list_elem_of_In in Hin. cbn in Hin.
  repeat destruct Hin as [Hin|Hin]; try contradiction; simplify_eq;
    (destruct HP as [(k & a & i & b & j & Hm & Ha & Hb & ->)|(n & a & Ha & ->)];
     [ apply list_elem_of_In in Hm; cbn in Hm; repeat destruct Hm as [Hm|Hm]; try contradiction;
       simplify_eq; injection E as -> ->; unfold lexlt, abp_rank; cbn -[rk Nat.mul];
       right; refine (conj eq_refl _); replace (k + (k + 0)) with (2 * k) by lia; rewrite !rk_2k; cbn; lia
     | assert (a = 0 ∨ a = 1) as [-> | ->] by lia; injection E as -> ->; unfold lexlt, abp_rank;
       cbn -[rk Nat.mul]; lia ]).
Qed.

Lemma abp0_acyclic : c0_acyclic 4 abp0_C.
Proof.
  apply (c0_acyclic_den lexlt 4 abp0_P (λ x, MkPt (pt_name x) true (pt_off x)) (pt_shift 1)
           (λ x i, pt_payload x i) abp_rank).
  - intros a. unfold lexlt. lia.
  - intros a b c. unfold lexlt. lia.
  - done.
  - done.
  - intros d. apply abp_rank_shift.
  - intros x y H. exact (abp_rank_facts x y H).
  - done.
Qed.

Lemma abp_rank_c0 x : abp_rank (c0_pt 4 x) = abp_rank x.
Proof.
  destruct x as [[c|c|q b i] pb o]; unfold abp_rank, c0_pt; cbn -[rk]; [done| |done].
  destruct (decide (c < 4)); done.
Qed.

Lemma abp_deadlock_free : deadlock_free (∅, {[+ abp_main +]}).
Proof.
  apply (soundness_source 4 abp0_C _ TUnit (c0_acyclic_creation _ _ abp0_acyclic));
    [constructor|apply abp_typed].
Qed.
