(** * The soup and the lock-free judgment (stage S8, proposal §2.12)

      a ∈ S^{N,W} _ n⟦Σ ⊢ T⟧      [Soup N W n Σ T a]
      Σ ⊪^N _ W p : T              [lf_sem N W Σ p T]

    A soup state a fixes the configuration q (threads with identifiers)
    and the ownership K. K maps every held end to its holder, its point,
    its counter and its tickets ([hold]). The lock-free judgment chooses
    a state at each index α. One state for every index follows by the
    existential property of the step index (soup/SoupRun.v,
    relation/ExProp.v). The bound N on the tickets of a channel is
    finite.

    At each index n the soup chooses an environment A of the relation
    (an end to S@x), a protocol map Π of the fuel layer (an end to a
    session type) and a result type per thread. Every thread t is in the
    live relation E[live] at its part of A and in FuelE^N at its part of
    Π and its counters with their tickets. The points of A are those of K, the
    ends of A and Π are those of K, the two ends of an internal channel
    are both held, at dual points, at dual session types up to
    annotations in A, and at dual protocols up to ≈ in Π. An end of the
    interface Σ is held at its entry of Σ. Every counter is finite and at
    most the tickets of its end, and the tickets of the two ends of an
    internal channel sum to at most N. The soup reads no term but
    through E[live] and FuelE.

    Π is chosen per index next to A and is not read off A. The fuel layer
    and the relation pick the session type of a new channel each by an
    existential of its own (O-New, F-New), so no soup can take one from
    the other (docs/redesign/progress.md, S8).

    Along a run the state follows the events by one index-free update
    ([lf_next]): a new end starts at the point the creation chose, in the
    world it grew to, with the tickets m1 and m2 it chose, each end with counter equal to its tickets. An action moves the end to x⁺ (or to the point of its
    branch) and sets its counter back to its tickets, every other end of
    an actor ticks, the ends of a sent or spawned value move to the
    receiver or the child with their counters minus one, a close removes
    both ends, and a link removes its two ends and renames the partner of
    the removed channel ([csub]). No counter changes at a link.

    The lock-free judgment is the soup alone (Q12, decided 2026-11-18).
    [soup_no_tau_divergence] (soup/SoupTau.v) gives what the live process
    conjunct of the proposal was kept for. *)

From stdpp Require Import relations.
From GV Require Export soup.State soup.Idle relation.Adequacy lockfree.ThreadProgress.


(** ** The soup at one index

    The clauses are the generic record [soup_gen] of soup/State.v at the
    live relation and at FuelE^N. *)

Definition soup_inv (N : nat) (n : Ix) (W : world) (Σ : senv) (T : ty) (a : lfstate)
    (A : senv) (Π : penv) (U : nat → ty) : Prop :=
  soup_gen (Some N) (λ Θ U e, e ∈ E[live]^W _ n⟦Θ ⊢ U⟧^∅)
    (λ Π φ e, e ∈ F^(Some N) _ n⟦RThread ▷ None⟧(Π, φ)) Σ T a A Π U.

(** The soup reads its threads at the world of the state, which extends
    the world W of the judgment. *)
Definition Soup (N : nat) (W : world) (n : Ix) (Σ : senv) (T : ty) (a : lfstate) : Prop :=
  wext W (s_W a) ∧ ∃ A Π U, soup_inv N n (s_W a) Σ T a A Π U.

Notation "a ∈ S^{ N , W } '_' n ⟦ Σ ⊢ T ⟧" := (Soup N W n Σ T a)
  (at level 70, N at level 0, W at level 0, n at level 0, Σ at level 60,
   format "a  ∈  S^{ N , W }  '_'  n ⟦ Σ  ⊢  T ⟧").

(** The soup at one index is monotone in the world it reads its threads at. *)
Lemma soup_inv_mono N n V V' Σ T a A Π U :
  wext V V' → soup_inv N n V Σ T a A Π U → soup_inv N n V' Σ T a A Π U.
Proof.
  intros HV Hs. constructor; try apply Hs.
  intros t e He. eapply Erel_mono; [exact HV|]. by apply (sp_rel _ _ _ _ _ _ _ _ _ Hs).
Qed.

(** ** The lock-free judgment *)

(** A state of the judgment starts at any ranked world that extends W
    ([Soup]). Two components of P-Connect are read at every ranked world
    that models their static worlds (soup/LFCompose.v, [lf_sems]). *)
Definition lf_sem (N : nat) (W : world) (Σ : senv) (p : proc) (T : ty) : Prop :=
  ∀ n, ∃ a, erase (s_q a) = p ∧ a ∈ S^{N,W} _ n⟦Σ ⊢ T⟧.

Notation "Σ ⊪^ N '_' W p : T" := (lf_sem N W Σ p T)
  (at level 74, N at level 0, W at level 0, p at level 60, T at level 60,
   format "Σ  ⊪^ N  '_' W  p  :  T").

(** ** The index-free update *)

(** The tickets of an end. *)
Definition kcap (K : own) (o : cend) : fuel := default (Some 0) (h_cap <$> K !! o).

(** The two ends of a new channel c of thread i at x and x‾, with m1 and
    m2 tickets, each at a counter equal to its tickets. *)
Definition knew (m1 m2 : fuel) (i : nat) (c : chan) (x : point) (K : own) : own :=
  <[EPos c := Hold i x m1 m1]> (<[ENeg c := Hold i x‾ m2 m2]> K).

(** Change every entry by f. *)
Definition kmod (f : cend → hold → hold) (K : own) : own := map_imap (λ o h, Some (f o h)) K.

Definition htick (h : hold) : hold := Hold h.(h_th) h.(h_pt) (ftick h.(h_ctr)) h.(h_cap).

(** Every entry of the actors i and j outside the moved ends M ticks. *)
Definition ktick (i j : nat) (M : gset cend) (K : own) : own :=
  kmod (λ o h, if decide ((h.(h_th) = i ∨ h.(h_th) = j) ∧ o ∉ M) then htick h else h) K.

(** The ends M move to thread j with one unit less. *)
Definition khand (M : gset cend) (j : nat) (K : own) : own :=
  kmod (λ o h, if decide (o ∈ M) then Hold j h.(h_pt) (ftick h.(h_ctr)) h.(h_cap) else h) K.

(** An action of thread i on o moves o to y and sets its counter back to
    its tickets. *)
Definition kact (o : cend) (i : nat) (y : point) (K : own) : own :=
  <[o := Hold i y (kcap K o) (kcap K o)]> K.

Definition kpt (K : own) (o : cend) : point := default (pvar 0) (h_pt <$> K !! o).

(** A map of ends renames the keys. *)
Definition kmapr {Y : Type} (g : cend → cend) (m : gmap cend Y) : gmap cend Y :=
  list_to_map ((λ p : cend * Y, (g p.1, p.2)) <$> map_to_list m).

(** A synchronization of thread i on o with thread j on o‾: the actors
    tick their other ends, the ends M of the moved value go to j, and the two
    ends move to y and y′ and go back to their tickets. *)
Definition ksync (i j : nat) (o : cend) (y y' : point) (M : gset cend) (K : own) : own :=
  kact o i y (kact (edual o) j y' (khand M j (ktick i j M K))).

(** The ownership after an event. The actors of a message, a close and
    a choice tick their other ends first, then the acted ends refill and
    the ends of the moved value move. *)
Definition own_next (tc : tchoice) (ev : event) (K : own) : own :=
  match ev with
  | EvSolo i α k =>
      let kn := match α with
                | LNew c => knew (tc_m1 tc) (tc_m2 tc) i c (tc_pt tc) K
                | _ => K
                end in
      match k with
      | PickLink o1 o2 => kmapr (csub o1 o2) (delete o1 (delete o2 K))
      | PickChild j => match α with LSpawn v => khand (fends v) j K | _ => kn end
      | PickNone => kn
      end
  | EvSync i j (SSend o v) => ksync i j o (pt_shift 1 (kpt K o)) (pt_shift 1 (kpt K (edual o))) (fends v) K
  | EvSync i j (SClose o) => ktick i j ∅ (delete o (delete o‾ K))
  | EvSync i j (SSel o b) => ksync i j o (sel_pt (kpt K o) b) (bra_pt (kpt K (edual o)) b) ∅ K
  | _ => K
  end.

(** The world after an event: a creation takes the world it chose. *)
Definition world_next (tc : tchoice) (ev : event) (W : world) : world :=
  match ev with EvSolo _ (LNew _) _ => tc_W tc | _ => W end.

(** The update takes the choice tc of a creation. Every other event
    ignores tc. *)
Definition lf_next (tc : tchoice) (a : lfstate) (ev : event) (q' : config) : lfstate :=
  LFState q' (own_next tc ev (s_K a)) (world_next tc ev (s_W a)).

(** Along a run, a stutter keeps the state. *)
Definition lf_upd (tc : tchoice) (a : lfstate) (l : option event) (q' : config) : lfstate :=
  match l with Some ev => lf_next tc a ev q' | None => LFState q' (s_K a) (s_W a) end.

Fixpoint lf_run_state (tcs : nat → tchoice) (a0 : lfstate) (r : nat → config)
    (l : nat → option event) (k : nat) : lfstate :=
  match k with
  | 0 => a0
  | S k' => lf_upd (tcs k') (lf_run_state tcs a0 r l k') (l k') (r k)
  end.
