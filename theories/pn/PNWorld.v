(** * The level anchors of Padovani and Novara

    docs/extensions/adequacy/padovani-novara.md §7. Levels become points
    relative to a level anchor. An anchor B stands for a shift, and its
    slots B[r] are the points of one level relative to it.

    - B[RAnc a] is the anchor shifted by a.
    - B[RCh c] is the point of a channel with code c (PNTypes.chres). The
      message is at offset 0 and the close at offset 1.
    - B[RLo z] lies at or below every head of level z, B[RHi z] above
      every action of level z, and B[RTop] above every level. They are
      the lower point of an arrow of level z, the upper point of a latent
      effect z and the ceiling for the latent effect ⊤.

    At the top level the anchor is the program's one top-level point
    variable, under the constraint [Crel]. Inside a box the anchor is
    the box's one point variable, which the force instantiates with an
    anchor of the caller. The constant [proot] only fills the anchor
    of unlimited types, whose translation names no point.

    Points are read through a denotation [den] that commutes with
    successor and slots and adds the shift of the anchor to every level.
    The rank [rank] of a denotation is the level and the instant, in ℤ
    with a top element. The constraint [Crel] identifies two points of
    the anchor with the same denotation and orders two with rising rank.
    It is acyclic ([Crel_acyclic]).

    A box has the constraint [Crel], the same facts read relative to its
    variable. A force at the anchor B[RAnc a] meets it, because
    instantiation adds a to every level ([den_inst]). *)

From stdpp Require Import base gmap countable numbers.
From LRGV Require Export examples.ExampleTools pn.PNTyping.

Set Default Proof Using "All".

(** ** Items *)

Inductive ritem := RAnc (a : Z) | RCh (c : pty) | RLo (z : Z) | RHi (z : Z) | RTop.

Global Instance ritem_eq_dec : EqDecision ritem.
Proof. solve_decision. Defined.

Global Instance ritem_countable : Countable ritem.
Proof.
  apply (inj_countable'
    (λ r, match r with
          | RAnc a => inl (inl a) | RCh c => inl (inr c)
          | RLo z => inr (inl z) | RHi z => inr (inr (inl z)) | RTop => inr (inr (inr ()))
          end : (Z + pty) + (Z + (Z + unit)))
    (λ s, match s with
          | inl (inl a) => RAnc a | inl (inr c) => RCh c
          | inr (inl z) => RLo z | inr (inr (inl z)) => RHi z | inr (inr (inr _)) => RTop
          end)).
  by intros [].
Qed.

Definition proot : point := Pt (NConst 0) 0.
Definition rpt (B : point) (r : ritem) : point := pt_slot B (encode_nat r).

Lemma pt_root_rpt B r : pt_root (rpt B r) = pt_root B.
Proof. done. Qed.

(** ** Denotation of points *)

Inductive dn :=
  | DC (a o : nat)             (* another constant *)
  | DV (a o : nat)             (* another variable *)
  | DAnc (k : Z) (o : nat)     (* an anchor of shift k *)
  | DCh (c : pty) (o : nat)    (* a channel with code c *)
  | DLo (z : Z) (o : nat)
  | DHi (z : Z) (o : nat)
  | DTop (o : nat)
  | DJ (d : dn) (i o : nat).   (* any other slot *)

Definition dsh (d : dn) : dn :=
  match d with
  | DC a o => DC a (S o)
  | DV a o => DV a (S o)
  | DAnc k o => DAnc k (S o)
  | DCh c o => DCh c (S o)
  | DLo z o => DLo z (S o)
  | DHi z o => DHi z (S o)
  | DTop o => DTop (S o)
  | DJ d i o => DJ d i (S o)
  end.

Definition dsl (d : dn) (i : nat) : dn :=
  match d with
  | DAnc k 0 =>
      match decode_nat i with
      | Some (RAnc a) => DAnc (k + a) 0
      | Some (RCh c) => DCh (lshift k c) 0
      | Some (RLo z) => DLo (z + k) 0
      | Some (RHi z) => DHi (z + k) 0
      | Some RTop => DTop 0
      | None => DJ d i 0
      end
  | DCh c 0 =>
      match i, cpay c with 0, Some c' => DCh c' 0 | _, _ => DJ d i 0 end
  | _ => DJ d i 0
  end.

Fixpoint dshN (n : nat) (d : dn) : dn :=
  match n with 0 => d | S n => dsh (dshN n d) end.

Fixpoint denN (p : pname) : dn :=
  match p with
  | NConst 0 | NVar 0 => DAnc 0 0
  | NConst a => DC a 0
  | NVar a => DV a 0
  | NSlot p b i => dsl (dshN b (denN p)) i
  end.

Definition den (x : point) : dn := dshN (pt_off x) (denN (pt_name x)).

Lemma den_shift x : den (pt_shift 1 x) = dsh (den x).
Proof. destruct x as [p k]. unfold den, pt_shift. simpl. by rewrite Nat.add_1_r. Qed.

Lemma dshN_add n m d : dshN n (dshN m d) = dshN (n + m) d.
Proof. induction n; simpl; congruence. Qed.

Lemma den_shiftN n x : den (pt_shift n x) = dshN n (den x).
Proof. destruct x as [p k]. unfold den, pt_shift. simpl. by rewrite dshN_add, Nat.add_comm. Qed.

Lemma den_slot x i : den (pt_slot x i) = dsl (den x) i.
Proof. done. Qed.

Lemma den_proot : den proot = DAnc 0 0.
Proof. done. Qed.

Lemma den_pvar0 : den (pvar 0) = DAnc 0 0.
Proof. done. Qed.

Section den_rpt.
  Context (B : point) (a : Z) (HB : den B = DAnc a 0).

  Lemma den_anc b : den (rpt B (RAnc b)) = DAnc (a + b) 0.
  Proof. unfold rpt. rewrite den_slot, HB. simpl. by rewrite decode_encode_nat. Qed.
  Lemma den_ch c : den (rpt B (RCh c)) = DCh (lshift a c) 0.
  Proof. unfold rpt. rewrite den_slot, HB. simpl. by rewrite decode_encode_nat. Qed.
  Lemma den_lo z : den (rpt B (RLo z)) = DLo (z + a) 0.
  Proof. unfold rpt. rewrite den_slot, HB. simpl. by rewrite decode_encode_nat. Qed.
  Lemma den_hi z : den (rpt B (RHi z)) = DHi (z + a) 0.
  Proof. unfold rpt. rewrite den_slot, HB. simpl. by rewrite decode_encode_nat. Qed.
  Lemma den_top : den (rpt B RTop) = DTop 0.
  Proof. unfold rpt. rewrite den_slot, HB. simpl. by rewrite decode_encode_nat. Qed.
End den_rpt.

(** ** Shifting a denotation *)

Fixpoint dshift (a : Z) (d : dn) : dn :=
  match d with
  | DAnc k o => DAnc (k + a) o
  | DCh c o => DCh (lshift a c) o
  | DLo z o => DLo (z + a) o
  | DHi z o => DHi (z + a) o
  | DJ d i o => DJ (dshift a d) i o
  | _ => d
  end.

Lemma dshift_dsh a d : dshift a (dsh d) = dsh (dshift a d).
Proof. by destruct d. Qed.

Lemma dshift_dshN a n d : dshift a (dshN n d) = dshN n (dshift a d).
Proof. induction n; simpl; [done|]. by rewrite dshift_dsh, IHn. Qed.

Lemma dshift_dsl a d i : dshift a (dsl d i) = dsl (dshift a d) i.
Proof.
  destruct d as [| |k [|o]|c [|o]| | | |]; simpl; try done.
  - destruct (decode_nat i) as [[b|c|z|z|]|]; simpl; try done;
      [zeq|by rewrite lshift_lshift|zeq|zeq].
  - destruct i; [|done]. rewrite cpay_lshift. by destruct (cpay c).
Qed.

(** Instantiating the variable of a box at an anchor of shift a adds a
    to every level. *)
Lemma den_inst_pn X a p :
  den X = DAnc a 0 → pn_root p = NVar 0 →
  den (pn_inst (plist [X]) p) = dshift a (denN p).
Proof.
  intros HX. induction p as [c|[|c]|p IH b i]; intros Hp; simpl in Hp; try discriminate.
  - change (pn_inst (plist [X]) (NVar 0)) with X. rewrite HX. simpl. zeq.
  - change (pn_inst (plist [X]) (NSlot p b i)) with (pt_slot (pt_shift b (pn_inst (plist [X]) p)) i).
    rewrite den_slot, den_shiftN, IH by done. simpl. by rewrite dshift_dsl, dshift_dshN.
Qed.

Lemma den_inst X a x :
  den X = DAnc a 0 → pt_root x = NVar 0 →
  den (pt_inst (plist [X]) x) = dshift a (den x).
Proof.
  intros HX Hx. destruct x as [p o]. unfold pt_inst, pt_root in *. simpl in *.
  rewrite den_shiftN, (den_inst_pn X a) by done. unfold den. simpl. by rewrite dshift_dshN.
Qed.

(** ** Rank *)

Definition zshift (a : Z) (r : zrank) : zrank :=
  match r with ZR z k => ZR (z + a) k | ZT k => ZT k end.

Fixpoint rank (d : dn) : zrank :=
  match d with
  | DC _ o | DV _ o | DTop o => ZT o
  | DAnc k o => ZR k o
  | DCh c o => match clev c with Some n => ZR n (S o) | None => ZT o end
  | DLo z o => ZR z o
  | DHi z o => ZR z (3 + o)
  | DJ d _ o => match rank d with ZR z _ => ZR z o | ZT _ => ZT o end
  end.

Lemma rank_dsh d : zlt (rank d) (rank (dsh d)).
Proof.
  destruct d as [| | | c o| | | | d i o]; simpl; try lia.
  - destruct (clev c); simpl; lia.
  - destruct (rank d); simpl; lia.
Qed.

Lemma rank_dshift a d : rank (dshift a d) = zshift a (rank d).
Proof.
  induction d as [| | |c o| | | |d IH i o]; simpl; try done.
  - rewrite clev_lshift. by destruct (clev c).
  - rewrite IH. by destruct (rank d).
Qed.

Lemma zlt_shift a x y : zlt (zshift a x) (zshift a y) ↔ zlt x y.
Proof. destruct x, y; simpl; lia. Qed.

(** ** Box constraints

    [Crel] holds every fact between points of the box's variable that
    the denotation and the rank give. [C0] is empty, the constraint of
    the boxes of unit and of sums. *)

Definition crel_fact (g : fact) : Prop :=
  match g with
  | FEq x y => pt_root x = NVar 0 ∧ pt_root y = NVar 0 ∧ den x = den y
  | FLt x y => pt_root x = NVar 0 ∧ pt_root y = NVar 0 ∧ zlt (rank (den x)) (rank (den y))
  end.

Definition Crel : bcs := BCs [] crel_fact.
Definition C0 : bcs := BCs [] (λ _, False).

(** [Crel] is acyclic as the top-level constraint of a program over one
    variable, because the rank rises along program order and along its
    ≺ facts (sharp edges 110). *)
Lemma Crel_acyclic : c0_acyclic 1 Crel.
Proof.
  apply (c0_acyclic_den zlt 1 crel_fact den dsh dsl rank).
  - apply zlt_irrefl.
  - apply zlt_trans.
  - apply den_shift.
  - apply den_slot.
  - by intros x y (_ & _ & H).

  - apply rank_dsh.
  - by intros x y (_ & _ & H).
Qed.

(** ** Translation of types

    [trz B k t] is the translation of ⇑ᵏ t at the anchor B.

    - unit is the box □(∗ ⊸ ∗), and a sum of unlimited types the box of
      the sum of their translations, read at the root anchor.
    - p[t]ⁿ is (p(∃ιs. P).Close)@B[RCh c] with c the code of the channel.
      A channel payload sits at the first slot of the channel's point
      (one binder), an unlimited payload needs no binder.
    - μα.p[⌈α⌉ᵐ]ⁿ is (µα. p(∃ι. α@ι).Close)@B[RCh c].
    - ⌈t⌉ᵐ is ⇑ᵐ t. wrap and unwrap are erased.
    - t →^{ρ,σ} s with ρ ∈ ℤ is T ⊸^{B[RHi σ]}_{B[RLo ρ]} U.
    - t →^{⊤,σ} s is □(∀ι. Crel. ∗ ⊸^⊥_⊤ (T ⊸^{ι[RHi σ]}_⊤ U)) with T, U
      read at the anchor ι, shifted down by the first finite level of the
      arrow. Shifted copies of one arrow get one box. *)

Definition loz (B : point) (k z : Z) : point := rpt B (RLo (z + k)).

Definition hiz (B : point) (k : Z) (σ : lvl) : option point :=
  match σ with
  | LBot => None
  | LZ z => Some (rpt B (RHi (z + k)))
  | LTop => Some (rpt B RTop)
  end.

Definition Ubox (T : ty) : ty := TBox 0 C0 (TLolli None None TUnit T).
Definition U : ty := Ubox TUnit.

Definition pol (p : bool) (m : nat) (T : ty) (s : sty) : sty :=
  if p then SSeq (SRcv m T) s else SSeq (SSnd m T) s.

(** The offset of the body of a box: minus the first finite level. *)
Definition mneg (t : pty) : Z := (- default 0 (mlev t))%Z.

Definition pbind (t : pty) : nat := if chanlike t then 1 else 0.

Fixpoint trz (B : point) (k : Z) (t : pty) {struct t} : ty :=
  match t with
  | PUnit => U
  | PSum t1 t2 => Ubox (TSum (trz proot 0 t1) (trz proot 0 t2))
  | PChan p t1 n =>
      TSess (pol p (pbind t1)
               (if chanlike t1 then TSess (sess t1) (pvar 0)
                else if un_b t1 then trz proot 0 t1 else TUnit) SEnd)
        (rpt B (RCh (PChan true (lshift k t1) (n + k))))
  | PRec p m n =>
      TSess (SMu (pol p 1 (TSess (SVar 0) (pvar 0)) SEnd))
        (rpt B (RCh (PChan true (PDisp m (PRec p m (n + k))) (n + k))))
  | PDisp m t1 => trz B (k + m) t1
  | PArr t1 (Some r) σ t2 => TLolli (hiz B k σ) (Some (loz B k r)) (trz B k t1) (trz B k t2)
  | PArr t1 None σ t2 =>
      TBox 1 Crel (TLolli None None TUnit
        (TLolli (hiz (pvar 0) (mneg t) σ) None
           (trz (pvar 0) (mneg t) t1) (trz (pvar 0) (mneg t) t2)))
  end
with sess (t : pty) {struct t} : sty :=
  match t with
  | PChan p t1 _ =>
      pol p (pbind t1)
        (if chanlike t1 then TSess (sess t1) (pvar 0)
         else if un_b t1 then trz proot 0 t1 else TUnit) SEnd
  | PRec p _ _ => SMu (pol p 1 (TSess (SVar 0) (pvar 0)) SEnd)
  | PDisp _ t1 => sess t1
  | _ => SEnd
  end.

(** The payload of a channel type. *)
Definition ppay (t : pty) : ty :=
  if chanlike t then TSess (sess t) (pvar 0) else if un_b t then trz proot 0 t else TUnit.

Lemma sess_chan p t n : sess (PChan p t n) = pol p (pbind t) (ppay t) SEnd.
Proof. done. Qed.

(** A channel type is a session at the point of its code. *)
Lemma trz_chanlike B k t c :
  chres k t = Some c → trz B k t = TSess (sess t) (rpt B (RCh c)).
Proof.
  revert k. induction t as [| | p t IH n|p m n|m t IH|t IH1 r σ s IH2]; intros k Hc;
    simpl in *; try done; try (by injection Hc as <-).
  by apply IH.
Qed.

(** The translation of an unlimited type is a closed box. *)
Lemma trz_un B B' k k' t : un t → trz B k t = trz B' k' t.
Proof.
  revert k k'. unfold un.
  induction t as [| | p t IH n|p m n|m t IH|t IH1 r σ s IH2]; intros k k' Ht; simpl in *; try done.
  - apply IH. by destruct (tlev t).
  - by subst r.
Qed.

Lemma trz_unlimited B k t : un t → unlimited (trz B k t).
Proof.
  unfold un. revert k.
  induction t as [| | p t IH n|p m n|m t IH|t IH1 r σ s IH2]; intros k Ht; simpl in *; try done.
  - apply IH. by destruct (tlev t).
  - by subst r.
Qed.

Lemma heads_un B k t : un t → heads (trz B k t) = ∅.
Proof.
  unfold un. revert k.
  induction t as [| | p t IH n|p m n|m t IH|t IH1 r σ s IH2]; intros k Ht; simpl in *; try done.
  - apply IH. by destruct (tlev t).
  - by subst r.
Qed.

(** Shifting the type is shifting the anchor's offset. Sessions do not
    see levels. *)
Lemma trz_sess_lshift t :
  (∀ B k j, trz B k (lshift j t) = trz B (k + j) t) ∧ (∀ j, sess (lshift j t) = sess t).
Proof.
  induction t as [| | p t IH n|p m n|m t IH|t IH1 r σ s IH2]; simpl.
  - done.
  - done.
  - destruct IH as [IH1 IH2].
    assert (∀ j, (if chanlike (lshift j t) then TSess (sess (lshift j t)) (pvar 0)
              else if un_b (lshift j t) then trz proot 0 (lshift j t) else TUnit) = ppay t) as Ej.
    { intros j. rewrite chanlike_lshift, un_b_lshift, IH2, IH1. unfold ppay.
      destruct (chanlike t); [done|]. destruct (un_b t) eqn:E; [|done].
      apply trz_un. by apply un_b_un. }
    split.
    + intros B k j. rewrite Ej, lshift_lshift. unfold pbind. rewrite chanlike_lshift. fold (ppay t).
      do 3 f_equal. zeq.
    + intros j. rewrite Ej. unfold pbind. by rewrite chanlike_lshift.
  - split; [|done]. intros B k j. do 4 f_equal; zeq.
  - destruct IH as [IH1 IH2]. split; [|done]. intros B k j. rewrite IH1. f_equal. lia.
  - destruct IH1 as [IH1 _], IH2 as [IH2 _]. split; [|by destruct r].
    intros B k j. destruct r as [r|]; simpl.
    + rewrite IH1, IH2. f_equal.
      * destruct σ; simpl; zeq.
      * unfold loz. zeq.
    + destruct (mlev (PArr t None σ s)) as [m0|] eqn:Em.
      * assert (mlev (PArr (lshift j t) None (lvl_sh j σ) (lshift j s)) = Some (m0 + j)%Z) as Em'.
        { change (PArr (lshift j t) None (lvl_sh j σ) (lshift j s)) with (lshift j (PArr t None σ s)).
          by rewrite mlev_lshift, Em. }
        unfold mneg. rewrite Em', Em. simpl. rewrite !IH1, !IH2.
        replace (- (m0 + j) + j)%Z with (- m0)%Z by lia.
        do 3 f_equal. destruct σ; simpl; zeq.
      * assert (lshift j (PArr t None σ s) = PArr t None σ s) as E by by apply mlev_none.
        pose proof E as E'. simpl in E'. injection E' as Et Eσ Es.
        rewrite Et, Eσ, Es. done.
Qed.

Lemma trz_lshift B k j t : trz B k (lshift j t) = trz B (k + j) t.
Proof. apply trz_sess_lshift. Qed.

Lemma sess_lshift j t : sess (lshift j t) = sess t.
Proof. apply trz_sess_lshift. Qed.

(** ** Substitution of points

    Every point of [trz B k t] is a slot of B, a slot of the variable of
    an inner box, or a slot of the root. *)

Lemma pt_inst_rpt σ B r : pt_inst σ (rpt B r) = rpt (pt_inst σ B) r.
Proof. apply pt_inst_slot. Qed.

Lemma hiz_pinst σ B k s : pt_inst σ <$> hiz B k s = hiz (pt_inst σ B) k s.
Proof. destruct s; simpl; try done; by rewrite pt_inst_rpt. Qed.

Lemma pup1_0 σ : pt_inst (pup 1 σ) (pvar 0) = pvar 0.
Proof. rewrite pt_inst_pvar_at. unfold pup. by rewrite decide_True by lia. Qed.

Lemma trz_pinst σ B k t : pinst_ty σ (trz B k t) = trz (pt_inst σ B) k t.
Proof.
  revert σ B k. induction t as [| t1 IH1 t2 IH2 | p t IH n|p m n|m t IH|t IH1 r s t2 IH2];
    intros σ B k.
  - done.
  - simpl. rewrite IH1, IH2. by rewrite (pt_inst_const _ proot 0).
  - simpl. by rewrite pt_inst_rpt.
  - simpl. by rewrite pt_inst_rpt.
  - simpl. apply IH.
  - destruct r as [r|]; simpl.
    + rewrite IH1, IH2, hiz_pinst. unfold loz. by rewrite pt_inst_rpt.
    + rewrite IH1, IH2, hiz_pinst, pup1_0. done.
Qed.

(** ** The static context of an anchor

    [good Ψ B]: B is an anchor of shift 0, and Γ ⊢ ≡ and Γ ⊢ ≺ hold
    between two points of B's root whenever the denotation and the rank
    say so. The variable of a box is good in its body ([good_box]), and
    so is the top-level variable of a program, which starts under the
    same constraint [Crel] (sharp edges 110). *)

Record good (Ψ : hyps) (B : point) : Prop := {
  gd_den : den B = DAnc 0 0;
  gd_eq x y : pt_root x = pt_root B → pt_root y = pt_root B → den x = den y → seqs wnil Ψ x y;
  gd_lt x y : pt_root x = pt_root B → pt_root y = pt_root B →
    zlt (rank (den x)) (rank (den y)) → slt wnil Ψ x y;
  gd_kn x : pt_root x = pt_root B → skn wnil Ψ x
}.

Lemma pn_vb_var0 p : pn_root p = NVar 0 → pn_vb 1 p.
Proof. induction p as [a|a|q IH b i]; simpl; [done|intros [=->]; lia|exact IH]. Qed.

Lemma good_box Ψ : (Crel, ids 1) ∈ Ψ → good Ψ (pvar 0).
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
  - intros x Hx. right. exists Crel, (ids 1), (pvar 0). split_and!; [done|by left|done].
Qed.

Section facts.
  Context (Ψ : hyps) (B : point) (HB : good Ψ B).

  Lemma gden : den B = DAnc 0 0.
  Proof. apply HB. Qed.

  Lemma den_ch0 c : den (rpt B (RCh c)) = DCh c 0.
  Proof. rewrite (den_ch B 0 gden). by rewrite lshift_0. Qed.
  Lemma den_lo0 z : den (rpt B (RLo z)) = DLo z 0.
  Proof. rewrite (den_lo B 0 gden). zeq. Qed.
  Lemma den_hi0 z : den (rpt B (RHi z)) = DHi z 0.
  Proof. rewrite (den_hi B 0 gden). zeq. Qed.
  Lemma den_anc0 a : den (rpt B (RAnc a)) = DAnc a 0.
  Proof. rewrite (den_anc B 0 gden). zeq. Qed.

  (** A head at level z: a lower point of level z, or a point ranked
      above it. *)
  Definition hd_at (z : Z) (h : point) : Prop :=
    pt_root h = pt_root B ∧ (den h = DLo z 0 ∨ zlt (ZR z 0) (rank (den h))).

  Lemma heads_trz k t z h :
    tlev t = Some z → h ∈ heads (trz B k t) → hd_at (z + k) h.
  Proof.
    revert k z. induction t as [| | p t IH n|p m n|m t IH|t IH1 r σ s IH2]; intros k z Hz Hh;
      simpl in *; try done.
    - injection Hz as <-. apply elem_of_singleton in Hh as ->. split; [done|right].
      rewrite den_ch0. simpl. lia.
    - injection Hz as <-. apply elem_of_singleton in Hh as ->. split; [done|right].
      rewrite den_ch0. simpl. lia.
    - destruct (tlev t) as [z'|] eqn:E; simpl in Hz; [|done]. injection Hz as <-.
      destruct (IH (k + m)%Z z' eq_refl Hh) as [H1 H2]. split; [done|].
      replace (z' + m + k)%Z with (z' + (k + m))%Z by lia. done.
    - subst r. simpl in Hh. apply elem_of_singleton in Hh as ->. split; [done|left].
      unfold loz. rewrite den_lo0. done.
  Qed.

  Lemma hd_at_mono z z' h : (z' ≤ z)%Z → hd_at z h → hd_at z' h.
  Proof.
    intros Hz [Hr [Hd|Hd]]; split; [done| |done|].
    - destruct (decide (z = z')) as [->|]; [by left|]. right. rewrite Hd. simpl. lia.
    - right. destruct (rank (den h)); simpl in *; lia.
  Qed.

  (** {B[RLo z]} ≼ every head at level z. *)
  Lemma lo_below z h : hd_at z h → sle wnil Ψ (rpt B (RLo z)) h.
  Proof.
    intros [Hr [Hd|Hd]].
    - left. apply (gd_eq _ _ HB); [done|done|]. by rewrite den_lo0.
    - right. apply (gd_lt _ _ HB); [done|done|]. by rewrite den_lo0.
  Qed.

  (** τ < z puts the upper point of τ below every head at level z. *)
  Lemma hi_below k τ z h u :
    lvl_lt τ (LZ (z - k)) → hiz B k τ = Some u → hd_at z h → slt wnil Ψ u h.
  Proof.
    intros Hτ Hu [Hr Hd]. destruct τ as [|t|]; simpl in *; try done. injection Hu as <-.
    apply (gd_lt _ _ HB); [done|done|]. rewrite den_hi0.
    destruct Hd as [->|Hd]; simpl; [lia|]. destruct (rank (den h)); simpl in *; lia.
  Qed.

  Lemma hi_below_lo k τ r u :
    lvl_lt τ (LZ r) → hiz B k τ = Some u → slt wnil Ψ u (loz B k r).
  Proof.
    intros Hτ Hu. eapply (hi_below k τ (r + k)); [|done|].
    - by replace (r + k - k)%Z with r by lia.
    - split; [done|left]. unfold loz. by rewrite den_lo0.
  Qed.

  (** Upper points rise with the effect. *)
  Lemma hiz_mono k a b u :
    lvl_le a b → hiz B k a = Some u → ∃ v, hiz B k b = Some v ∧ sle wnil Ψ u v.
  Proof.
    intros Hab Hu. destruct a as [|x|], b as [|y|]; simpl in *; try done; injection Hu as <-;
      eexists; (split; [done|]).
    - destruct (decide (x = y)) as [->|]; [left; apply se_refl|]. right.
      apply (gd_lt _ _ HB); [done|done|]. rewrite !den_hi0. simpl. lia.
    - right. apply (gd_lt _ _ HB); [done|done|]. rewrite den_hi0, (den_top B 0 gden). done.
    - left. apply se_refl.
  Qed.

  (** The two instants of a channel of level n lie below the upper point
      of n. *)
  Lemma ch_below_hi c n :
    clev c = Some n → slt wnil Ψ (rpt B (RCh c)) (rpt B (RHi n)).
  Proof.
    intros Hc. apply (gd_lt _ _ HB); [done|done|]. rewrite den_ch0, den_hi0. simpl.
    rewrite Hc. simpl. lia.
  Qed.

  Lemma ch1_below_hi c n :
    clev c = Some n → slt wnil Ψ (pt_shift 1 (rpt B (RCh c))) (rpt B (RHi n)).
  Proof.
    intros Hc. apply (gd_lt _ _ HB); [done|done|]. rewrite den_shift, den_ch0, den_hi0. simpl.
    rewrite Hc. simpl. lia.
  Qed.

  (** The payload of a channel sits at the first slot of its point. *)
  Lemma den_pay c c' : cpay c = Some c' → den (pt_slot (rpt B (RCh c)) 0) = DCh c' 0.
  Proof. intros Hc. rewrite den_slot, den_ch0. simpl. by rewrite Hc. Qed.

  Lemma ch_below_pay c c' n n' :
    cpay c = Some c' → clev c = Some n → clev c' = Some n' → (n < n')%Z →
    slt wnil Ψ (rpt B (RCh c)) (pt_slot (rpt B (RCh c)) 0) ∧
    slt wnil Ψ (pt_shift 1 (rpt B (RCh c))) (pt_slot (rpt B (RCh c)) 0).
  Proof.
    intros Hp Hc Hc' Hn. split; apply (gd_lt _ _ HB); try done;
      rewrite ?den_shift, (den_pay _ _ Hp), den_ch0; simpl; rewrite Hc, Hc'; simpl; lia.
  Qed.

  Lemma pay_eq c c' : cpay c = Some c' → seqs wnil Ψ (pt_slot (rpt B (RCh c)) 0) (rpt B (RCh c')).
  Proof.
    intros Hc. apply (gd_eq _ _ HB); [done|done|]. by rewrite (den_pay _ _ Hc), den_ch0.
  Qed.

  (** A box at the anchor B[RAnc a] meets its constraint. *)
  Lemma crel_hold a : bcs_hold (seqs wnil Ψ) (slt wnil Ψ) Crel [rpt B (RAnc a)].
  Proof.
    intros g Hg. apply bcs_open_nil in Hg as [Hg _]. pose proof (den_anc0 a) as HX.
    assert (∀ x, pt_root x = NVar 0 → pt_root (pt_inst (plist [rpt B (RAnc a)]) x) = pt_root B)
      as Hr by (intros x Hx; rewrite pt_root_inst, Hx; done).
    destruct g as [x y|x y]; simpl in *; destruct Hg as (Hx & Hy & E).
    - apply (gd_lt _ _ HB); [by apply Hr|by apply Hr|].
      rewrite !(den_inst _ a) by done. rewrite !rank_dshift. by apply zlt_shift.
    - apply (gd_eq _ _ HB); [by apply Hr|by apply Hr|].
      rewrite !(den_inst _ a) by done. by rewrite E.
  Qed.

  Lemma anc_known a : Forall (skn wnil Ψ) [rpt B (RAnc a)].
  Proof. apply Forall_singleton. by apply (gd_kn _ _ HB). Qed.

  (** The type at the anchor B[RAnc a] and offset k₁ is the type at B and
      offset k₁ + a, up to Γ ⊢ ≡. *)
  Lemma trz_anc a k1 k2 t :
    (k1 + a = k2)%Z → steq wnil Ψ (trz (rpt B (RAnc a)) k1 t) (trz B k2 t).
  Proof.
    pose proof (den_anc0 a) as HX.
    assert (∀ c, seqs wnil Ψ (rpt (rpt B (RAnc a)) (RCh c)) (rpt B (RCh (lshift a c)))) as Hch.
    { intros c. apply (gd_eq _ _ HB); [done|done|]. by rewrite (den_ch _ a HX), den_ch0. }
    revert k1 k2. induction t as [| | p t IH n|p m n|m t IH|t IH1 r σ s IH2]; intros k1 k2 Hk;
      try (apply teq_steq, teq_refl; fail); simpl.
    - split; [|apply seq_refl]. eapply se_trans; [apply Hch|]. simpl.
      rewrite lshift_lshift. replace (k1 + a)%Z with k2 by lia.
      replace (n + k1 + a)%Z with (n + k2)%Z by lia. apply se_refl.
    - split; [|apply seq_refl]. eapply se_trans; [apply Hch|]. simpl.
      replace (n + k1 + a)%Z with (n + k2)%Z by lia. apply se_refl.
    - apply IH. lia.
    - destruct r as [r|]; [|split_and!; [done|done|apply teq_refl]]. simpl. split_and!; try (apply IH1 || apply IH2; lia).
      + destruct σ as [|z|]; simpl; try done.
        * apply (gd_eq _ _ HB); [done|done|]. rewrite (den_hi _ a HX), den_hi0. zeq.
        * apply (gd_eq _ _ HB); [done|done|]. by rewrite (den_top _ a HX), (den_top B 0 gden).
      + unfold loz. apply (gd_eq _ _ HB); [done|done|]. rewrite (den_lo _ a HX), den_lo0. zeq.
  Qed.

  Lemma hiz_anc a k1 k2 σ :
    (k1 + a = k2)%Z → opt_rel (seqs wnil Ψ) (hiz (rpt B (RAnc a)) k1 σ) (hiz B k2 σ).
  Proof.
    pose proof (den_anc0 a) as HX. intros Hk. destruct σ as [|z|]; simpl; try done.
    - apply (gd_eq _ _ HB); [done|done|]. rewrite (den_hi _ a HX), den_hi0. zeq.
    - apply (gd_eq _ _ HB); [done|done|]. by rewrite (den_top _ a HX), (den_top B 0 gden).
  Qed.
End facts.
