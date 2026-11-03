(** * The protocol-point world of PGV

    docs/extensions/adequacy/pgv-adequacy.md §6. One root constant a.
    The protocol point of a session type S is the carried root
    a.(code S), with one code for S and its dual. The bound points are
    ℓ_n = (a+1).n and u_n = (a+2).n, with ℓ_⊥ = (a+3).0 and
    u_⊤ = (a+4).0.

    Points are read through a denotation [den] that commutes with
    successor and carried roots. On a protocol point it is the session
    type up to duality, and the successor of a monotone !ᵒT.S or ?ᵒT.S is the
    point of S. The rank [drank] of a denotation is 3·pr(S)+2 for a
    protocol, 3n+1 for ℓ_n, 3n+3 for u_n, below everything for ℓ_⊥ and
    above everything for u_⊤. The world identifies two points of the
    root a with the same denotation and orders two with rising rank. It
    is strict, because the rank rises along program order and along
    every generated fact ([Wpgv_strict]). *)

From stdpp Require Import base gmap countable.
From LRGV Require Export examples.ExampleTools pgv.PGVTyping.

Set Default Proof Using "All".

(** ** Session types up to duality *)

Definition canon (s : psty) : psty :=
  match s with PRcv _ _ _ | PEndR _ => pdual s | _ => s end.

Lemma canon_dual s : canon (pdual s) = canon s.
Proof. destruct s; simpl; by rewrite ?pdual_involutive. Qed.

Lemma spr_canon s : spr (canon s) = spr s.
Proof. by destruct s. Qed.

(** The condition of [pgv_mono] at the top connective. *)
Definition top_mono (s : psty) : Prop :=
  match s with PSnd o _ s' | PRcv o _ s' => o < spr s' | _ => True end.

Lemma pgv_mono_top s : pgv_mono s → top_mono s.
Proof. destruct s; simpl; naive_solver. Qed.

(** ** Points *)

Definition proot : point := Pt (NConst 0) 0.
Definition ppt (s : psty) : point := pt_slot proot (encode_nat (canon s)).
Definition lpt (n : nat) : point := pt_slot (pt_shift 1 proot) n.
Definition upt (n : nat) : point := pt_slot (pt_shift 2 proot) n.
Definition lbot : point := pt_slot (pt_shift 3 proot) 0.
Definition utop : point := pt_slot (pt_shift 4 proot) 0.

(** The lower point of a lower bound (⊤ is none) and the upper point of
    an upper bound (⊥ is none). *)
Definition lbp (p : prio) : option point :=
  match p with PTop => None | PBot => Some lbot | PNat n => Some (lpt n) end.
Definition ubp (q : prio) : option point :=
  match q with PBot => None | PNat n => Some (upt n) | PTop => Some utop end.

Lemma ppt_dual s : ppt (pdual s) = ppt s.
Proof. unfold ppt. by rewrite canon_dual. Qed.

(** ** Denotation of points *)

Inductive dn :=
  | DC (a b : nat)                (* the constant a at offset b *)
  | DV (a b : nat)                (* the variable a at offset b *)
  | DP (s : psty) (k : nat)       (* a protocol point, k steps on *)
  | DS (b i k : nat)              (* (a+b).i at offset k, b ≠ 0 *)
  | DJ (d : dn) (i k : nat).      (* any other carried root *)

Definition dsh (d : dn) : dn :=
  match d with
  | DC a b => DC a (S b)
  | DV a b => DV a (S b)
  | DP s k =>
      match k, s with
      | 0, PSnd o _ s' | 0, PRcv o _ s' =>
          if decide (o < spr s') then DP (canon s') 0 else DP s 1
      | _, _ => DP s (S k)
      end
  | DS b i k => DS b i (S k)
  | DJ d i k => DJ d i (S k)
  end.

Definition dsl (d : dn) (i : nat) : dn :=
  match d with
  | DC 0 0 => match decode_nat i with Some s => DP s 0 | None => DJ d i 0 end
  | DC 0 (S b) => DS (S b) i 0
  | _ => DJ d i 0
  end.

Fixpoint dshN (k : nat) (d : dn) : dn :=
  match k with 0 => d | S k => dsh (dshN k d) end.

Fixpoint denN (p : pname) : dn :=
  match p with
  | NConst a => DC a 0
  | NVar a => DV a 0
  | NSlot p b i => dsl (dshN b (denN p)) i
  end.

Definition den (x : point) : dn := dshN (pt_off x) (denN (pt_name x)).

Lemma den_shift x : den (pt_shift 1 x) = dsh (den x).
Proof. destruct x as [p k]. unfold den, pt_shift. simpl. by rewrite Nat.add_1_r. Qed.

Lemma den_slot x i : den (pt_slot x i) = dsl (den x) i.
Proof. done. Qed.

Lemma dshN_DC k a b : dshN k (DC a b) = DC a (k + b).
Proof. induction k; simpl; [done|]. by rewrite IHk. Qed.

Lemma den_ppt s : den (ppt s) = DP (canon s) 0.
Proof. unfold ppt, den. simpl. by rewrite decode_encode_nat. Qed.

Lemma den_lpt n : den (lpt n) = DS 1 n 0.
Proof. done. Qed.
Lemma den_upt n : den (upt n) = DS 2 n 0.
Proof. done. Qed.
Lemma den_lbot : den lbot = DS 3 0 0.
Proof. done. Qed.
Lemma den_utop : den utop = DS 4 0 0.
Proof. done. Qed.

(** The successor of a monotone protocol point is the point of its
    continuation. *)
Lemma den_ppt_next o T s :
  o < spr s → den (pt_shift 1 (ppt (PSnd o T s))) = den (ppt s).
Proof.
  intros Ho. rewrite den_shift, !den_ppt. simpl. by rewrite decide_True.
Qed.

Lemma den_ppt_next_rcv o T s :
  o < spr s → den (pt_shift 1 (ppt (PRcv o T s))) = den (ppt s).
Proof.
  intros Ho. rewrite den_shift, !den_ppt. simpl. rewrite spr_dual, decide_True by done.
  by rewrite canon_dual.
Qed.

(** ** Rank *)

Definition drank (d : dn) : nat * nat :=
  match d with
  | DC _ b | DV _ b => (0, b)
  | DP s k => (0, 3 * spr s + 2 + k)
  | DS b i k =>
      match b with
      | 1 => (0, 3 * i + 1 + k)
      | 2 => (0, 3 * i + 3 + k)
      | 4 => (1, k)
      | _ => (0, k)
      end
  | DJ _ _ k => (0, k)
  end.

Lemma drank_dsh d : lexlt (drank d) (drank (dsh d)).
Proof.
  unfold lexlt. destruct d as [a b|a b|s [|k]|b i k|d i k]; simpl; try lia.
  - destruct s as [o T s'|o T s'|o|o]; simpl; try lia;
      case_decide; simpl; rewrite ?spr_canon; lia.
  - destruct b as [|[|[|[|[|b]]]]]; simpl; lia.
Qed.

(** ** The world *)

Definition rooted0 (x : point) : Prop := pt_root x = NConst 0.

Definition Wpgv : world :=
  wgen {[NConst 0]}
    (λ x y, rooted0 x ∧ rooted0 y ∧ den x = den y)
    (λ x y, rooted0 x ∧ rooted0 y ∧ lexlt (drank (den x)) (drank (den y))).

Lemma lexlt_trans a b c : lexlt a b → lexlt b c → lexlt a c.
Proof. unfold lexlt. lia. Qed.

Lemma Wpgv_strict : strict Wpgv.
Proof.
  set (E := λ x y, rooted0 x ∧ rooted0 y ∧ den x = den y).
  set (L := λ x y, rooted0 x ∧ rooted0 y ∧ lexlt (drank (den x)) (drank (den y))).
  assert (∀ x y, geq E x y → den x = den y) as Heq.
  { induction 1 as [x y (_ & _ & H)| | | | x y _ IH | x y i _ IH]; try congruence.
    - by rewrite !den_shift, IH.
    - by rewrite !den_slot, IH. }
  split.
  - apply wgen_wf.
    + intros p ->%elem_of_singleton. by exists 0.
    + intros x y (Hx & Hy & _). right. unfold rooted0 in *. rewrite Hx, Hy. set_solver.
    + intros x y (Hx & Hy & _). right. unfold rooted0 in *. rewrite Hx, Hy. set_solver.
  - assert (∀ x y, glt E L x y → lexlt (drank (den x)) (drank (den y))) as Hlt.
    { induction 1 as [x y (_ & _ & H)|x|x x' y y' Hx _ IH Hy|x y z _ IH1 _ IH2].
      - done.
      - rewrite den_shift. apply drank_dsh.
      - apply Heq in Hx, Hy. by rewrite Hx, <-Hy.
      - by eapply lexlt_trans. }
    intros x H. apply Hlt in H. unfold lexlt in H. lia.
Qed.

Lemma Wpgv_wf : world_wf Wpgv.
Proof. apply Wpgv_strict. Qed.

Lemma pgv_lt x y :
  rooted0 x → rooted0 y → lexlt (drank (den x)) (drank (den y)) → w_lt Wpgv x y.
Proof. intros Hx Hy H. by apply glt_base. Qed.

Lemma pgv_eq x y : rooted0 x → rooted0 y → den x = den y → w_eq Wpgv x y.
Proof. intros Hx Hy H. by apply geq_base. Qed.

Lemma rooted0_ppt s : rooted0 (ppt s).
Proof. done. Qed.
Lemma rooted0_shift n x : rooted0 x → rooted0 (pt_shift n x).
Proof. done. Qed.

Lemma pgv_known x : rooted0 x → pt_known Wpgv x.
Proof. intros Hx. unfold pt_known, rooted0 in *. rewrite Hx. simpl. set_solver. Qed.

Lemma lbp_rooted p l : lbp p = Some l → rooted0 l.
Proof. destruct p; simpl; intros [=<-]; done. Qed.
Lemma ubp_rooted q u : ubp q = Some u → rooted0 u.
Proof. destruct q; simpl; intros [=<-]; done. Qed.

(** ** Translation of types *)

Fixpoint tr_ty (T : pty) : ty :=
  match T with
  | PUnit => TUnit
  | PProd T U => TProd (tr_ty T) (tr_ty U)
  | PSum T U => TSum (tr_ty T) (tr_ty U)
  | PLolli p q T U => TLolli (ubp q) (lbp p) (tr_ty T) (tr_ty U)
  | PSess s => TSess (tr_sty s) (ppt s)
  end
with tr_sty (s : psty) : sty :=
  match s with
  | PSnd _ T s' => SSnd (tr_ty T) (tr_sty s')
  | PRcv _ T s' => SRcv (tr_ty T) (tr_sty s')
  | PEndS _ | PEndR _ => SEnd
  end.

Lemma tr_sty_dual s : tr_sty (pdual s) = dual (tr_sty s).
Proof. induction s; simpl; by f_equal. Qed.

Definition tr_env (Γ : penv) : lenv := fmap (M:=option) tr_ty <$> Γ.

(** A translated type holds no existential, so it has no ⊥ flag
    (sharp edges 103). *)
Lemma hbot_tr T : hbot (tr_ty T) = false.
Proof. induction T; simpl; try done. by rewrite IHT1, IHT2. by rewrite IHT1, IHT2. Qed.

Lemma lenv_bot_tr Γ : lenv_bot (tr_env Γ) = false.
Proof. induction Γ as [|[T|] Γ IH]; simpl; [done| |done]. by rewrite hbot_tr, IH. Qed.

(** Every point of a translated type is a constant, so a payload of
    send and recv needs no binder and is its own instance. *)
Lemma tr_pscoped T : pscoped 0 (tr_ty T).
Proof.
  induction T as [|T IH1 U IH2|T IH1 U IH2|p q T IH1 U IH2|s]; simpl; try done.
  split_and!; try done.
  - destruct q; simpl; try done; intros a Ha; done.
  - destruct p; simpl; try done; intros a Ha; done.
Qed.

Lemma payload_tr T x : payload_at (tr_ty T) x = tr_ty T.
Proof.
  unfold payload_at. rewrite (pinst_closed _ _ (tr_pscoped T)). done.
Qed.

(** ** Heads of translated types

    A head of a translated type is a protocol point or a lower point,
    at a priority no smaller than pr(T). *)

Definition hd_ok (P : prio) (h : point) : Prop :=
  (∃ s, h = ppt s ∧ prio_le P (PNat (spr s))) ∨ (∃ p, lbp p = Some h ∧ prio_le P p).

Lemma prio_le_min_l a b c : prio_le a c → prio_le (prio_min a b) c.
Proof. destruct a, b, c; simpl; lia. Qed.
Lemma prio_le_min_r a b c : prio_le b c → prio_le (prio_min a b) c.
Proof. destruct a, b, c; simpl; lia. Qed.

Lemma hd_ok_min_l a b h : hd_ok a h → hd_ok (prio_min a b) h.
Proof. intros [(s&?&?)|(p&?&?)]; [left; exists s|right; exists p]; eauto using prio_le_min_l. Qed.
Lemma hd_ok_min_r a b h : hd_ok b h → hd_ok (prio_min a b) h.
Proof. intros [(s&?&?)|(p&?&?)]; [left; exists s|right; exists p]; eauto using prio_le_min_r. Qed.

Lemma heads_tr T h : h ∈ heads (tr_ty T) → hd_ok (pr T) h.
Proof.
  induction T as [| T IH1 U IH2|T IH1 U IH2|p q T IH1 U IH2|s]; simpl; intros Hh.
  - set_solver.
  - apply elem_of_union in Hh as [Hh|Hh]; [apply hd_ok_min_l|apply hd_ok_min_r]; auto.
  - apply elem_of_union in Hh as [Hh|Hh]; [apply hd_ok_min_l|apply hd_ok_min_r]; auto.
  - right. exists p. destruct (lbp p) eqn:E; simpl in Hh; [|set_solver].
    apply elem_of_singleton in Hh as ->. split; [done|]. destruct p; simpl; lia.
  - left. exists s. apply elem_of_singleton in Hh as ->. simpl. split; [done|lia].
Qed.

Lemma heads_tr_env Γ h : h ∈ lenv_heads (tr_env Γ) → hd_ok (pr_env Γ) h.
Proof.
  induction Γ as [|[T|] Γ IH]; simpl; intros Hh.
  - set_solver.
  - apply elem_of_union in Hh as [Hh|Hh];
      [apply hd_ok_min_l, heads_tr|apply hd_ok_min_r, IH]; done.
  - by apply IH.
Qed.

Lemma lenv_heads_tr_empty Γ : penv_empty Γ → lenv_heads (tr_env Γ) = ∅.
Proof.
  induction Γ as [|o Γ IH]; simpl; intros H; [done|].
  rewrite (H o) by set_solver. apply IH. intros o' Ho'. apply H. set_solver.
Qed.

(** ** Facts between the points *)

(** A head at priority above n lies above u_n and above every protocol
    point at n. *)
Lemma hd_above (x : point) n P h :
  rooted0 x → (∃ k, drank (den x) = (0, k) ∧ k ≤ 3 * n + 3) →
  prio_lt (PNat n) P → hd_ok P h → w_lt Wpgv x h.
Proof.
  intros Hx (k & Ek & Hk) Hn [(s & -> & Hs)|(p & Hp & Hle)].
  - apply pgv_lt; [done|done|]. rewrite Ek, den_ppt. simpl. rewrite spr_canon.
    unfold lexlt. simpl. destruct P; simpl in *; lia.
  - apply pgv_lt; [done|by eapply lbp_rooted|]. rewrite Ek.
    destruct p; simpl in Hp; simplify_eq; destruct P; simpl in *; try done;
      unfold lexlt; simpl; lia.
Qed.

Lemma upt_below_hd n P h : prio_lt (PNat n) P → hd_ok P h → w_lt Wpgv (upt n) h.
Proof. intros. eapply hd_above; [done| |done..]. exists (3 * n + 3). simpl. split; [f_equal; lia|lia]. Qed.

Lemma ppt_below_hd s P h : prio_lt (PNat (spr s)) P → hd_ok P h → w_lt Wpgv (ppt s) h.
Proof.
  intros. eapply hd_above; [done| |done..]. exists (3 * spr s + 2). rewrite den_ppt. simpl.
  rewrite spr_canon. split; [f_equal; lia|lia].
Qed.

(** The lower point of P lies at or below every head at priority P. *)
Lemma lbp_below_hd P l h : lbp P = Some l → hd_ok P h → l = h ∨ w_lt Wpgv l h.
Proof.
  intros Hl [(s & -> & Hs)|(p & Hp & Hle)].
  - right. apply pgv_lt; [by eapply lbp_rooted|done|]. rewrite den_ppt.
    destruct P; simpl in Hl; simplify_eq; simpl in *; rewrite ?spr_canon;
      unfold lexlt; simpl; lia.
  - destruct P as [|n|], p as [|m|]; simpl in Hl, Hp, Hle; try done;
      injection Hl as <-; injection Hp as <-; try by left.
    + right. apply pgv_lt; [done|done|]. unfold lexlt. simpl. lia.
    + destruct (decide (n = m)) as [->|]; [by left|]. right.
      apply pgv_lt; [done|done|]. unfold lexlt. simpl. lia.
Qed.

Lemma hd_ok_top h : ¬ hd_ok PTop h.
Proof. intros [(s & _ & H)|(p & Hp & H)]; [done|]. by destruct p. Qed.

(** Upper points rise with the bound. *)
Lemma ubp_mono a b x :
  prio_le a b → ubp a = Some x → ∃ y, ubp b = Some y ∧ (x = y ∨ w_lt Wpgv x y).
Proof.
  intros Hab Ha. destruct a as [|n|], b as [|m|]; simpl in *; try done; injection Ha as <-.
  - eexists. split; [done|]. destruct (decide (n = m)) as [->|]; [by left|].
    right. apply pgv_lt; [done|done|]. unfold lexlt. simpl. lia.
  - eexists. split; [done|]. right. apply pgv_lt; [done|done|]. unfold lexlt. simpl. lia.
  - eexists. split; [done|]. by left.
Qed.

(** q < p′ puts u_q below ℓ_p′. *)
Lemma ubp_below_lbp q p u l : prio_lt q p → ubp q = Some u → lbp p = Some l → w_lt Wpgv u l.
Proof.
  intros Hqp Hu Hl. destruct q as [|n|], p as [|m|]; simpl in *; try done;
    injection Hu as <-; injection Hl as <-.
  apply pgv_lt; [done|done|]. unfold lexlt. simpl. lia.
Qed.

(** An action at priority o lies below u_o. *)
Lemma ppt_below_upt s : w_lt Wpgv (ppt s) (upt (spr s)).
Proof.
  apply pgv_lt; [done|done|]. rewrite den_ppt, den_upt. simpl. rewrite spr_canon.
  unfold lexlt. simpl. lia.
Qed.
