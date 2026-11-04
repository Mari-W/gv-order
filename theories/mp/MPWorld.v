(** * The priority world of Mordido and Pérez

    docs/extensions/adequacy/mordido-perez.md, mechanization. Priorities
    become points relative to an anchor, as levels do for Padovani and
    Novara (pn/PNWorld.v on branch orders-lr). An anchor stands for a
    valuation of the priority variables of the enclosing abstraction,
    and its carried points are

    - B[RAnc σs], the anchor of the valuation σs read in B's valuation,
      the instance at which a priority abstraction is forced;
    - B[RCh Q h d], the channel of type Q with priority sequence
      h + k·d, at its current instant;
    - B[RLo ρs], the lower point of a closure whose lower bound is
      min ρs;
    - B[RHi σs], the upper point of a latent effect max σs.

    The root constant (NConst 0, 0) is the anchor of the empty
    valuation. Inside a box the anchor is its one point variable.

    A point denotes ([den]) the valuation of an anchor, a channel in
    head form, a lower or upper level, or junk. A successor of a
    channel denotes the continuation after its head action. The point
    x[0] of a message denotes the payload it carries, and the points
    x[0] and x[1] of a choice its two branches (K11). The rank is the priority of the head, with lower points
    below and upper points above it. Two channels with the same
    denotation share a point. A continuation whose priority does not
    rise denotes junk ranked on top, so the rank rises along the program
    order of every point and from a choice to each of its branches. The
    world [Wmp] identifies root points with one denotation and orders
    root points of rising rank, so it states x ≺ x[i] at every choice.

    A box has the constraint [Crel Θ], every fact between points of its
    anchor that holds at every valuation of Θ. A force at B[RAnc σs]
    meets it when σs instantiates Θ ([crel_hold]). *)

From stdpp Require Import base gmap countable numbers.
From LRGV Require Export examples.ExampleTools mp.MPTyping.

Set Default Proof Using "All".

(** ** Items *)

Inductive ritem :=
  | RAnc (σ : list prio)
  | RCh (Q : msty) (h : prio) (d : Z)
  | RLo (l : list prio)
  | RHi (l : list prio).

Global Instance ritem_eq_dec : EqDecision ritem.
Proof. solve_decision. Defined.

Global Instance ritem_countable : Countable ritem.
Proof.
  apply (inj_countable'
    (λ r, match r with
          | RAnc σ => inl (inl σ) | RCh Q h d => inl (inr (Q, h, d))
          | RLo l => inr (inl l) | RHi l => inr (inr l)
          end : (list prio + msty * prio * Z) + (list prio + list prio))
    (λ s, match s with
          | inl (inl σ) => RAnc σ | inl (inr (Q, h, d)) => RCh Q h d
          | inr (inl l) => RLo l | inr (inr l) => RHi l
          end)).
  by intros [].
Qed.

Definition proot : point := Pt (NConst 0) 0.
Definition rpt (B : point) (r : ritem) : point := pt_slot B (encode_nat r).

(** ** Ranks

    ⊥, an integer or ⊤, each with a subrank in ℤ. A lower point of
    min ρs has the subrank −|ρs|, a channel 1 and an upper point 3, so a
    closure that captures another one with more entries lies strictly
    below it, and its captured channels strictly above it. *)

Inductive rk := KB (j : Z) | KZ (z j : Z) | KH | KT (j : Z).

Definition rlt (a b : rk) : Prop :=
  match a, b with
  | KB j, KB j' => (j < j')%Z
  | KB _, _ => True
  | KZ z j, KZ z' j' => (z < z')%Z ∨ (z = z' ∧ (j < j')%Z)
  | KZ _ _, (KH | KT _) => True
  | KH, KT _ => True
  | KT j, KT j' => (j < j')%Z
  | _, _ => False
  end.

Lemma rlt_irrefl a : ¬ rlt a a.
Proof. destruct a; simpl; lia. Qed.

Lemma rlt_trans a b c : rlt a b → rlt b c → rlt a c.
Proof. destruct a, b, c; simpl; lia. Qed.

Global Instance rlt_dec a b : Decision (rlt a b).
Proof. destruct a, b; simpl; apply _. Defined.

Definition rtop (a : rk) : Z := match a with KT j => (j + 1)%Z | _ => 0%Z end.

Lemma rlt_rtop a : rlt a (KT (rtop a)).
Proof. destruct a; simpl; lia. Qed.

(** ** Denotations *)

Inductive dn :=
  | DAnc (v : val)
  | DCh (Q : msty) (h : prio) (d : Z)       (* Q in head form *)
  | DLo (x : ext) (n : nat)
  | DHi (x : ext) (n : nat)
  | DJ (j : Z).

Definition xrk (x : ext) (j : Z) (t : rk) : rk :=
  match x with XB => KB j | XZ z => KZ z j | XT => t end.

Definition rank (d : dn) : rk :=
  match d with
  | DAnc _ => KT 0
  | DCh Q _ _ => xrk (evalp [] (hprio Q)) 1 (KT 1)
  | DLo x n => xrk x (- Z.of_nat n) (KT (- Z.of_nat n))
  | DHi x n => xrk x (3 + Z.of_nat n) KH
  | DJ j => KT j
  end.

(** The subrank of an upper point: the length of its list, or 0 when ⊤
    is in it, so that every effect that contains ⊤ has one point. *)
Definition hlen (l : list prio) : nat := if bool_decide (PTop ∈ l) then 0 else length l.

(** A channel in head form. *)
Definition dch (Q : msty) (h : prio) (d : Z) : dn := DCh (mhd Q h d).1 (mhd Q h d).2 d.

(** The move to d′ from d, junk when the rank would not rise. *)
Definition guard (d d' : dn) : dn := if decide (rlt (rank d) (rank d')) then d' else DJ (rtop (rank d)).

Lemma guard_rise d d' : rlt (rank d) (rank (guard d d')).
Proof. unfold guard. case_decide; [done|]. apply rlt_rtop. Qed.

Definition dnext (d : dn) : dn :=
  match d with
  | DCh (MSnd _ _ K) h dd | DCh (MRcv _ _ K) h dd => dch K h dd
  | _ => DJ 0
  end.

Definition dsh (d : dn) : dn := guard d (dnext d).

Definition dbr (d : dn) (b : bool) : dn :=
  guard d (match d with
           | DCh (MSel _ K1 K2) h dd | DCh (MBra _ K1 K2) h dd => dch (if b then K2 else K1) h dd
           | _ => DJ 0
           end).

(** The points x[0] and x[1] of a choice are its branches (K11). *)
Definition dsl (d : dn) (i : nat) : dn :=
  match d with
  | DCh (MSel _ _ _) _ _ | DCh (MBra _ _ _) _ _ =>
      match i with 0 => dbr d false | 1 => dbr d true | _ => DJ 0 end
  | DAnc v =>
      match decode_nat i with
      | Some (RAnc σ) => DAnc (evalZ v <$> σ)
      | Some (RCh Q h dd) => dch (mmap (pclose v) Q) (pclose v h) dd
      | Some (RLo l) => DLo (xminl v l) (length l)
      | Some (RHi l) => DHi (xmaxl v l) (hlen l)
      | None => DJ 0
      end
  | DCh (MSnd _ (MPChan _ Q h dd) _) _ _ | DCh (MRcv _ (MPChan _ Q h dd) _) _ _ =>
      match i with 0 => dch Q h dd | _ => DJ 0 end
  | _ => DJ 0
  end.

Lemma rank_dsh d : rlt (rank d) (rank (dsh d)).
Proof. apply guard_rise. Qed.

Lemma rank_dbr d b : rlt (rank d) (rank (dbr d b)).
Proof. apply guard_rise. Qed.

Fixpoint dshN (n : nat) (d : dn) : dn :=
  match n with 0 => d | S n => dsh (dshN n d) end.

(** The denotation of a name under the valuation v of the box variable. *)
Fixpoint denN (v : val) (p : pname) : dn :=
  match p with
  | NConst 0 => DAnc []
  | NVar 0 => DAnc v
  | NConst _ | NVar _ => DJ 0
  | NSlot q b i => dsl (dshN b (denN v q)) i
  end.

Definition den (v : val) (x : point) : dn := dshN (pt_off x) (denN v (pt_name x)).

Lemma dshN_add n m d : dshN n (dshN m d) = dshN (n + m) d.
Proof. induction n; simpl; congruence. Qed.

Lemma den_shift v x : den v (pt_shift 1 x) = dsh (den v x).
Proof. destruct x as [p k]. unfold den, pt_shift. simpl. by rewrite Nat.add_1_r. Qed.

Lemma den_shiftN v n x : den v (pt_shift n x) = dshN n (den v x).
Proof. destruct x as [p k]. unfold den, pt_shift. simpl. by rewrite dshN_add, Nat.add_comm. Qed.

Lemma den_slot v x i : den v (pt_slot x i) = dsl (den v x) i.
Proof. done. Qed.

Definition dchoice (d : dn) : Prop :=
  match d with DCh (MSel _ _ _) _ _ | DCh (MBra _ _ _) _ _ => True | _ => False end.

Lemma den_br v x i : dchoice (den v x) → den v (pt_slot x (bidx i)) = dbr (den v x) i.
Proof.
  intros H. rewrite den_slot. destruct (den v x) as [|[]| | |]; simpl in H; try done; by destruct i.
Qed.

Lemma den_proot v : den v proot = DAnc [].
Proof. done. Qed.

Lemma den_pvar0 v : den v (pvar 0) = DAnc v.
Proof. done. Qed.

(** Root points do not depend on the valuation. *)
Lemma denN_const v v' p : pn_root p = NConst 0 → denN v p = denN v' p.
Proof. induction p as [[|a]|a|q IH b i]; simpl; try done; intros Hp; by rewrite IH. Qed.

Lemma den_const v v' x : pt_root x = NConst 0 → den v x = den v' x.
Proof. intros H. unfold den. by rewrite (denN_const v v'). Qed.

(** ** Strictness through a denotation *)

Lemma wgen_strict_dn {D A} (R : A → A → Prop) N E L (dnt : point → D)
    (dS : D → D) (dL : D → nat → D) (r : D → A) :
  (∀ a, ¬ R a a) → (∀ a b c, R a b → R b c → R a c) →
  (∀ p, p ∈ N → ∃ a, p = NConst a) →
  (∀ x y, E x y → eq_or_supp N x y) →
  (∀ x y, L x y → po_or_supp N x y) →
  (∀ x, dnt (pt_shift 1 x) = dS (dnt x)) →
  (∀ x i, dnt (pt_slot x i) = dL (dnt x) i) →
  (∀ x y, E x y → dnt x = dnt y) →
  (∀ d, R (r d) (r (dS d))) →
  (∀ x y, L x y → R (r (dnt x)) (r (dnt y))) →
  strict (wgen N E L).
Proof.
  intros Hirr Htr HN HE HL Hs Hl Hc Hr HLr. split; [by apply wgen_wf|].
  assert (∀ x y, geq E x y → dnt x = dnt y) as Heq.
  { induction 1; try congruence; auto; rewrite ?Hs, ?Hl; congruence. }
  assert (∀ x y, glt E L x y → R (r (dnt x)) (r (dnt y))) as Hlt.
  { induction 1 as [x y H|x|x x' y y' Hx _ IH Hy|x y z _ IH1 _ IH2].
    - by apply HLr.
    - rewrite Hs. apply Hr.
    - apply Heq in Hx, Hy. by rewrite Hx, <-Hy.
    - by eapply Htr. }
  intros x H. apply Hlt in H. exact (Hirr _ H).
Qed.

(** ** The world *)

Definition rooted0 (x : point) : Prop := pt_root x = NConst 0.

Definition Wmp : world :=
  wgen {[NConst 0]}
    (λ x y, rooted0 x ∧ rooted0 y ∧ den [] x = den [] y)
    (λ x y, rooted0 x ∧ rooted0 y ∧ rlt (rank (den [] x)) (rank (den [] y))).

Lemma Wmp_strict : strict Wmp.
Proof.
  apply (wgen_strict_dn rlt _ _ _ (den []) dsh dsl rank).
  - apply rlt_irrefl.
  - apply rlt_trans.
  - intros p ->%elem_of_singleton. by exists 0.
  - intros x y (Hx & Hy & _). right. unfold rooted0 in *. rewrite Hx, Hy. set_solver.
  - intros x y (Hx & Hy & _). right. unfold rooted0 in *. rewrite Hx, Hy. set_solver.
  - apply den_shift.
  - apply den_slot.
  - by intros x y (_ & _ & H).
  - apply rank_dsh.
  - by intros x y (_ & _ & H).
Qed.

Lemma Wmp_wf : world_wf Wmp.
Proof. apply Wmp_strict. Qed.

(** ** Instantiating the anchor

    Forcing a box at an anchor X of valuation w reads every point of
    the box variable at w. *)

Lemma den_inst_pn v w X p :
  den v X = DAnc w → pn_root p = NVar 0 → den v (pn_inst (plist [X]) p) = denN w p.
Proof.
  intros HX. induction p as [c|[|c]|q IH b i]; intros Hp; simpl in Hp; try discriminate.
  - exact HX.
  - change (pn_inst (plist [X]) (NSlot q b i)) with (pt_slot (pt_shift b (pn_inst (plist [X]) q)) i).
    rewrite den_slot, den_shiftN, IH by done. done.
Qed.

Lemma den_inst v w X x :
  den v X = DAnc w → pt_root x = NVar 0 → den v (pt_inst (plist [X]) x) = den w x.
Proof.
  intros HX Hx. destruct x as [p o]. unfold pt_inst, pt_root in *. simpl in *.
  rewrite den_shiftN, (den_inst_pn v w X) by done. done.
Qed.

(** ** Priorities under valuations and substitutions *)

Lemma evalp_pclose v ρ : evalp [] (pclose v ρ) = evalp v ρ.
Proof. by destruct ρ. Qed.

Lemma pclose_padd v ρ n : pclose v (padd ρ n) = padd (pclose v ρ) n.
Proof. destruct ρ; simpl; f_equal; lia. Qed.

Lemma mmap_comp f g : (∀ Q, mmap f (mmap g Q) = mmap (f ∘ g) Q) ∧
                      (∀ P, mmapp f (mmapp g P) = mmapp (f ∘ g) P).
Proof. apply msty_mpay_mut; intros; simpl; congruence. Qed.

Lemma mmap_ext f g : (∀ ρ, f ρ = g ρ) →
  (∀ Q, mmap f Q = mmap g Q) ∧ (∀ P, mmapp f P = mmapp g P).
Proof. intros H. apply msty_mpay_mut; intros; simpl; congruence. Qed.

Lemma mmap_subV f X Q : mmap f (msubV X Q) = msubV (mmap f X) (mmap f Q).
Proof. induction Q; simpl; congruence. Qed.

(** A map of priorities that commutes with displacement and with the
    binder of ∀^S commutes with inst. *)
Lemma mhd_mmap f Q h d :
  (∀ x n, f (padd x n) = padd (f x) n) →
  (∀ x ρ, f (pinI x ρ) = pinI (f x) (f ρ)) →
  mhd (mmap f Q) (f h) d = (mmap f (mhd Q h d).1, f (mhd Q h d).2).
Proof.
  intros Ha Hi. destruct Q as [| | | | |S0|]; simpl; try done.
  unfold munf. rewrite mmap_subV. simpl. f_equal; [|by rewrite Ha].
  f_equal. rewrite !(proj1 (mmap_comp _ _)). apply mmap_ext. intros ρ. simpl. by rewrite Hi.
Qed.

Lemma pclose_pinI v x ρ : pclose v (pinI x ρ) = pinI (pclose v x) (pclose v ρ).
Proof. destruct ρ; simpl; try done. apply pclose_padd. Qed.

Lemma mhd_pclose v Q h d :
  mhd (mmap (pclose v) Q) (pclose v h) d = (mmap (pclose v) (mhd Q h d).1, pclose v (mhd Q h d).2).
Proof. apply mhd_mmap; [apply pclose_padd|apply pclose_pinI]. Qed.

Lemma hprio_mmap f Q : f PTop = PTop → hprio (mmap f Q) = f (hprio Q).
Proof. intros H. destruct Q; simpl; done. Qed.

(** The head of a channel point, read at v. *)
Lemma dch_rank v Q h d :
  rank (dch (mmap (pclose v) Q) (pclose v h) d) = xrk (evalp v (chead Q h d)) 1 (KT 1).
Proof.
  unfold dch, chead. rewrite mhd_pclose. simpl.
  rewrite hprio_mmap by done. by rewrite evalp_pclose.
Qed.

(** ** The box constraint *)

Definition crel_fact (Θ : pctx) (g : fact) : Prop :=
  match g with
  | FEq x y => pt_root x = NVar 0 ∧ pt_root y = NVar 0 ∧ ∀ v, models Θ v → den v x = den v y
  | FLt x y => pt_root x = NVar 0 ∧ pt_root y = NVar 0 ∧
               ∀ v, models Θ v → rlt (rank (den v x)) (rank (den v y))
  end.

Definition Crel (Θ : pctx) : bcs := BCs [] (crel_fact Θ).
Definition C0 : bcs := BCs [] (λ _, False).

(** ** Translation of types *)

Definition hiz (B : point) (ef : list prio) : option point :=
  match ef with [] => None | _ => Some (rpt B (RHi ef)) end.

Fixpoint tr (B : point) (T : mty) : ty :=
  match T with
  | MUnit => U
  | MChan p Q h d => TSess (polS p (ers Q)) (rpt B (RCh Q h d))
  | MArr T lo ef V => TLolli (hiz B ef) (Some (rpt B (RLo lo))) (tr B T) (tr B V)
  | MPoly nv cs T ef V =>
      TBox 1 0 (Crel (PCtx nv cs))
        (TLolli None None TUnit (TLolli (hiz (pvar 0) ef) None (tr (pvar 0) T) (tr (pvar 0) V)))
  end.

Lemma pt_inst_rpt σ B r : pt_inst σ (rpt B r) = rpt (pt_inst σ B) r.
Proof. apply pt_inst_slot. Qed.

Lemma hiz_pinst σ B ef : pt_inst σ <$> hiz B ef = hiz (pt_inst σ B) ef.
Proof. destruct ef; simpl; [done|]. by rewrite pt_inst_rpt. Qed.

Lemma pup1_0 σ : pt_inst (pup 1 σ) (pvar 0) = pvar 0.
Proof. rewrite pt_inst_pvar_at. unfold pup. by rewrite decide_True by lia. Qed.

Lemma tr_pinst σ B T : pinst_ty σ (tr B T) = tr (pt_inst σ B) T.
Proof.
  revert σ B. induction T as [|p Q h d|T IH1 lo ef V IH2|nv cs T IH1 ef V IH2]; intros σ B; simpl.
  - done.
  - by rewrite pt_inst_rpt.
  - by rewrite IH1, IH2, hiz_pinst, pt_inst_rpt.
  - by rewrite IH1, IH2, hiz_pinst, pup1_0.
Qed.

Definition tun (T : mty) : Prop := match T with MUnit | MPoly _ _ _ _ _ => True | _ => False end.

(** Units and priority abstractions do not see the anchor. *)
Lemma tr_un B B' T : mun T → tr B T = tr B' T.
Proof. destruct T; simpl; done. Qed.

Lemma tr_unlimited B T : mun T → unlimited (tr B T).
Proof. destruct T; simpl; done. Qed.

Lemma heads_un B T : mun T → heads (tr B T) = ∅.
Proof. destruct T; simpl; done. Qed.

(** ** The static context of an anchor

    [good Ψ Θ B]: B is the anchor of every valuation of Θ, and Γ ⊢ ≡
    and Γ ⊢ ≺ hold between two points of B's root whenever they hold at
    every valuation. *)

Record good (Ψ : hyps) (Θ : pctx) (B : point) : Prop := {
  gd_den v : models Θ v → den v B = DAnc v;
  gd_eq x y : pt_root x = pt_root B → pt_root y = pt_root B →
    (∀ v, models Θ v → den v x = den v y) → seqs Wmp Ψ x y;
  gd_lt x y : pt_root x = pt_root B → pt_root y = pt_root B →
    (∀ v, models Θ v → rlt (rank (den v x)) (rank (den v y))) → slt Wmp Ψ x y;
  gd_kn x : pt_root x = pt_root B → skn Wmp Ψ x
}.

Definition pc0 : pctx := PCtx 0 [].

Lemma models_pc0 v : models pc0 v ↔ v = [].
Proof.
  unfold models. simpl. split; [intros [H _]; by destruct v|intros ->; split; [done|constructor]].
Qed.

Lemma good_root Ψ : good Ψ pc0 proot.
Proof.
  split.
  - intros v ->%models_pc0. done.
  - intros x y Hx Hy E. apply se_w, geq_base. split_and!; [done|done|]. apply E, models_pc0. done.
  - intros x y Hx Hy E. apply sl_w, glt_base. split_and!; [done|done|]. apply E, models_pc0. done.
  - intros x Hx. left. unfold pt_known. simpl. rewrite Hx. set_solver.
Qed.

Lemma pn_vb_var0 p : pn_root p = NVar 0 → pn_vb 1 p.
Proof. induction p as [a|a|q IH b i]; simpl; [done|intros [=->]; lia|exact IH]. Qed.

Lemma good_box Ψ Θ : (Crel Θ, ids 1) ∈ Ψ → good Ψ Θ (pvar 0).
Proof.
  intros HΨ. split.
  - done.
  - intros x y Hx Hy E. eapply (se_hyp0 _ _ _ (ids 1) x y); [exact HΨ|by split_and!| | |].
    + split; by apply pn_vb_var0.
    + apply pt_inst_ids. by apply pn_vb_var0.
    + apply pt_inst_ids. by apply pn_vb_var0.
  - intros x y Hx Hy E. eapply (sl_hyp0 _ _ _ (ids 1) x y); [exact HΨ|by split_and!| | |].
    + split; by apply pn_vb_var0.
    + apply pt_inst_ids. by apply pn_vb_var0.
    + apply pt_inst_ids. by apply pn_vb_var0.
  - intros x Hx. right. exists (Crel Θ), (ids 1), (pvar 0). split_and!; [done|by left|done].
Qed.

(** ** Comparisons of ranks *)

Lemma xminl_app v l1 l2 : xminl v (l1 ++ l2) = xmin (xminl v l1) (xminl v l2).
Proof.
  induction l1 as [|ρ l1 IH]; simpl; [by destruct (xminl v l2)|].
  rewrite IH. destruct (evalp v ρ), (xminl v l1), (xminl v l2); simpl; f_equal; lia.
Qed.

Lemma xmin_le_l a b : xle (xmin a b) a.
Proof. destruct a, b; simpl; lia. Qed.
Lemma xmin_le_r a b : xle (xmin a b) b.
Proof. destruct a, b; simpl; lia. Qed.
Lemma xle_trans a b c : xle a b → xle b c → xle a c.
Proof. destruct a, b, c; simpl; lia. Qed.

Lemma xminl_le v l ρ : ρ ∈ l → xle (xminl v l) (evalp v ρ).
Proof.
  induction l as [|ρ' l IH]; intros Hρ; [by apply elem_of_nil in Hρ|].
  apply elem_of_cons in Hρ as [->|Hρ]; simpl; [apply xmin_le_l|].
  eapply xle_trans; [apply xmin_le_r|by apply IH].
Qed.

Lemma xlt_minl v a l : (∀ ρ, ρ ∈ l → xlt a (evalp v ρ)) → l = [] ∨ xlt a (xminl v l).
Proof.
  induction l as [|ρ l IH]; intros H; [by left|right]. simpl.
  assert (xlt a (evalp v ρ)) as H1 by (apply H; by left).
  destruct (IH (λ ρ' Hρ', H ρ' (list_elem_of_further _ _ _ Hρ'))) as [->|H2].
  - simpl. by destruct (evalp v ρ).
  - destruct a, (evalp v ρ), (xminl v l); simpl in *; lia.
Qed.

(** An upper point below a channel head of higher priority. *)
Lemma hi_chan a n e : xlt a e → rlt (rank (DHi a n)) (xrk e 1 (KT 1)).
Proof. destruct a, e; simpl; lia. Qed.

(** An upper point below a lower point of higher priority. *)
Lemma hi_lo v a n l : (∀ ρ, ρ ∈ l → xlt a (evalp v ρ)) →
  rlt (rank (DHi a n)) (rank (DLo (xminl v l) (length l))).
Proof.
  intros H. destruct (xlt_minl v a l H) as [->|H2]; [destruct a; simpl; lia|].
  destruct a, (xminl v l); simpl in *; lia.
Qed.

(** A lower point below a channel of at least its priority. *)
Lemma lo_chan m n e : xle m e → rlt (rank (DLo m n)) (xrk e 1 (KT 1)).
Proof. destruct m, e; simpl; lia. Qed.

(** A lower point below the lower point of a shorter list it contains. *)
Lemma lo_lo m m' n n' : xle m m' → n' < n → rlt (rank (DLo m n)) (rank (DLo m' n')).
Proof. destruct m, m'; simpl; lia. Qed.

(** ** Points relative to a good anchor *)

Section facts.
  Context (Ψ : hyps) (Θ : pctx) (B : point) (HB : good Ψ Θ B).

  Lemma den_anc v σ : models Θ v → den v (rpt B (RAnc σ)) = DAnc (evalZ v <$> σ).
  Proof. intros Hv. unfold rpt. rewrite den_slot, (gd_den _ _ _ HB v Hv). simpl. by rewrite decode_encode_nat. Qed.
  Lemma den_ch v Q h d : models Θ v → den v (rpt B (RCh Q h d)) = dch (mmap (pclose v) Q) (pclose v h) d.
  Proof. intros Hv. unfold rpt. rewrite den_slot, (gd_den _ _ _ HB v Hv). simpl. by rewrite decode_encode_nat. Qed.
  Lemma den_lo v l : models Θ v → den v (rpt B (RLo l)) = DLo (xminl v l) (length l).
  Proof. intros Hv. unfold rpt. rewrite den_slot, (gd_den _ _ _ HB v Hv). simpl. by rewrite decode_encode_nat. Qed.
  Lemma den_hi v l : models Θ v → den v (rpt B (RHi l)) = DHi (xmaxl v l) (hlen l).
  Proof. intros Hv. unfold rpt. rewrite den_slot, (gd_den _ _ _ HB v Hv). simpl. by rewrite decode_encode_nat. Qed.

  Lemma rank_ch v Q h d : models Θ v →
    rank (den v (rpt B (RCh Q h d))) = xrk (evalp v (chead Q h d)) 1 (KT 1).
  Proof. intros Hv. rewrite den_ch by done. apply dch_rank. Qed.

  (** A box forced at B[RAnc σs] meets its constraint. *)
  Lemma crel_hold Θ' σ : pinst_ok Θ Θ' σ →
    bcs_hold (seqs Wmp Ψ) (slt Wmp Ψ) (Crel Θ') [rpt B (RAnc σ)].
  Proof.
    intros (_ & _ & Hm) g Hg. apply bcs_open_nil in Hg as [Hg _].
    assert (∀ x, pt_root x = NVar 0 → pt_root (pt_inst (plist [rpt B (RAnc σ)]) x) = pt_root B)
      as Hr by (intros x Hx; rewrite pt_root_inst, Hx; done).
    destruct g as [x y|x y]; simpl in *; destruct Hg as (Hx & Hy & E).
    - apply (gd_lt _ _ _ HB); [by apply Hr|by apply Hr|]. intros v Hv.
      rewrite !(den_inst v (evalZ v <$> σ)) by (done || by apply den_anc). by apply E, Hm.
    - apply (gd_eq _ _ _ HB); [by apply Hr|by apply Hr|]. intros v Hv.
      rewrite !(den_inst v (evalZ v <$> σ)) by (done || by apply den_anc). by apply E, Hm.
  Qed.

  Lemma anc_known σ : Forall (skn Wmp Ψ) [rpt B (RAnc σ)].
  Proof. apply Forall_singleton. by apply (gd_kn _ _ _ HB). Qed.

  Lemma rpt_known r : skn Wmp Ψ (rpt B r).
  Proof. by apply (gd_kn _ _ _ HB). Qed.
End facts.
