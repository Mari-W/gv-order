(** * The soup and the lock-free judgment (stage S8, proposal §2.12)

      a ∈ S^{N,W} _ n⟦Σ ⊢ T⟧      [Soup N W n Σ T a]
      Σ ⊪_W p : T                 [lf_sem W Σ p T]

    A soup state a fixes, outside the index, the configuration q (threads
    with identifiers), the ownership K and the tickets tk. K maps every
    held end to its holder, its point and its counter ([hold]). So the
    ends a thread holds, their points and their counters are the same at
    every index ("∃ before ∀ n", F20). The refill N is finite.

    At each index n the soup chooses an environment A of the relation
    (an end to S@x), a protocol map Π of the fuel layer (an end to a
    session type) and a result type per thread. Every thread t is in the
    live relation E[live] at its part of A and in FuelE^N at its part of
    Π, its counters and its tickets. The points of A are those of K, the
    ends of A and Π are those of K, the two ends of an internal channel
    are both held, at dual points, at dual session types up to
    annotations in A, and at dual protocols up to ≈ in Π. An end of the
    interface Σ is held at its entry of Σ. The soup reads no term but
    through E[live] and FuelE.

    Π is chosen per index next to A and is not read off A. The fuel layer
    and the relation pick the session type of a new channel each by an
    existential of its own (O-New, F-New), so no soup can take one from
    the other (docs/redesign/progress.md, S8).

    Along a run the state follows the events by one index-free update
    ([lf_next]): a new end starts at a fresh generated root of its family
    or at the field of its anchor with counter N, an action moves the end
    to x⁺ (or to the point of its branch) and refills it to N, every other
    end of an actor ticks, a transfer set moves to the receiver or the
    child with its counters minus one, a close removes both ends, a link
    removes its two ends, spends a ticket and renames the partner of the
    removed channel ([csub]), and a spawn splits the tickets ⌈tk/2⌉ for
    the child and ⌊tk/2⌋ for the parent.

    The lock-free judgment keeps the live process conjunct of the
    proposal (Q12, F21). [soup_no_tau_divergence] (soup/SoupTau.v) shows
    that adequacy does not need it. *)

From stdpp Require Import relations.
From GV Require Export soup.State soup.Idle relation.Adequacy lockfree.ThreadProgress.

(** ** The soup at one index

    The clauses are the generic record [soup_gen] of soup/State.v at the
    live relation and at FuelE^N. *)

Definition soup_inv (N n : nat) (W : world) (Σ : senv) (T : ty) (a : lfstate)
    (A : senv) (Π : penv) (U : nat → ty) : Prop :=
  soup_gen (λ Θ U e, e ∈ E[live]^W _ n⟦Θ ⊢ U⟧^∅)
    (λ Π φ tk e, e ∈ F^(Some N) _ n⟦RThread ▷ None ; 0⟧(Π, φ, tk)) Σ T a A Π U.

Definition Soup (N : nat) (W : world) (n : nat) (Σ : senv) (T : ty) (a : lfstate) : Prop :=
  ∃ A Π U, soup_inv N n W Σ T a A Π U.

Notation "a ∈ S^{ N , W } '_' n ⟦ Σ ⊢ T ⟧" := (Soup N W n Σ T a)
  (at level 70, N at level 0, W at level 0, n at level 0, Σ at level 60,
   format "a  ∈  S^{ N ,  W }  '_'  n ⟦ Σ  ⊢  T ⟧").

(** ** The lock-free judgment *)

Definition lf_sem (W : world) (Σ : senv) (p : proc) (T : ty) : Prop :=
  (∀ n, p ∈ P[live]^W _ n⟦Σ ⊢ T⟧) ∧
  ∃ N a, erase (s_q a) = p ∧ ∀ n, a ∈ S^{N,W} _ n⟦Σ ⊢ T⟧.

Notation "Σ ⊪_ W p : T" := (lf_sem W Σ p T)
  (at level 74, W at level 0, p at level 60, T at level 60,
   format "Σ  ⊪_ W  p  :  T").

(** ** The index-free update *)

(** A generated root of family ℓ that is the root of no point of K. *)
Definition kgens (ℓ : family) (K : own) : gset nat :=
  list_to_set (omap (λ h : hold,
    match pt_root h.(h_pt) with NGen ℓ' g => if decide (ℓ' = ℓ) then Some g else None | _ => None end)
    (map_to_list K).*2).

Definition kfresh (ℓ : family) (K : own) : nat := fresh (kgens ℓ K).

(** The two ends of a new channel c of thread i at x and x‾. *)
Definition knew (N : nat) (i : nat) (c : chan) (x : point) (K : own) : own :=
  <[EPos c := Hold i x (Some N)]> (<[ENeg c := Hold i x‾ (Some N)]> K).

(** Change every entry by f. *)
Definition kmod (f : cend → hold → hold) (K : own) : own := map_imap (λ o h, Some (f o h)) K.

Definition htick (h : hold) : hold := Hold h.(h_th) h.(h_pt) (ftick h.(h_ctr)).

(** Every entry of the actors i and j outside the transfer set M ticks. *)
Definition ktick (i j : nat) (M : gset cend) (K : own) : own :=
  kmod (λ o h, if decide ((h.(h_th) = i ∨ h.(h_th) = j) ∧ o ∉ M) then htick h else h) K.

(** The ends M move to thread j with one unit less. *)
Definition khand (M : gset cend) (j : nat) (K : own) : own :=
  kmod (λ o h, if decide (o ∈ M) then Hold j h.(h_pt) (ftick h.(h_ctr)) else h) K.

(** An action of thread i on o moves o to y and refills it. *)
Definition kact (N : nat) (o : cend) (i : nat) (y : point) (K : own) : own :=
  <[o := Hold i y (Some N)]> K.

Definition kpt (K : own) (o : cend) : point := default (pvar 0) (h_pt <$> K !! o).

(** A map of ends renames the keys. *)
Definition kmapr {Y : Type} (g : cend → cend) (m : gmap cend Y) : gmap cend Y :=
  list_to_map ((λ p : cend * Y, (g p.1, p.2)) <$> map_to_list m).

Definition tupd (tk : nat → nat) (i : nat) (k : nat) : nat → nat :=
  λ t, if decide (t = i) then k else tk t.

(** A synchronization of thread i on o with thread j on o‾: the actors
    tick their other ends, the transfer set M moves to j, and the two
    ends move to y and y′ and refill. *)
Definition ksync (N i j : nat) (o : cend) (y y' : point) (M : gset cend) (K : own) : own :=
  kact N o i y (kact N (edual o) j y' (khand M j (ktick i j M K))).

(** The ownership after an event. The actors of a message, a close and
    a choice tick their other ends first, then the acted ends refill and
    the transfer set moves. *)
Definition own_next (N : nat) (ev : event) (K : own) : own :=
  match ev with
  | EvBeta _ | EvSess _ _ => K
  | EvNew i ℓ c => knew N i c (pgen ℓ (kfresh ℓ K)) K
  | EvNewAt i κ o c => knew N i c ((kpt K o)·κ) K
  | EvSpawn i j M => khand M j K
  | EvMsg i j o M => ksync N i j o (pt_shift 1 (kpt K o)) (pt_shift 1 (kpt K (edual o))) M K
  | EvClose i j o => ktick i j ∅ (delete o (delete o‾ K))
  | EvChoice i j o b => ksync N i j o (sel_pt (kpt K o) b) (bra_pt (kpt K (edual o)) b) ∅ K
  | EvLink i o1 o2 => kmapr (csub o1 o2) (delete o1 (delete o2 K))
  end.

Definition tk_next (ev : event) (tk : nat → nat) : nat → nat :=
  match ev with
  | EvSpawn i j _ => tupd (tupd tk i (Nat.div2 (tk i))) j (Nat.div2 (S (tk i)))
  | EvLink i _ _ => tupd tk i (tk i - 1)
  | _ => tk
  end.

Definition lf_next (N : nat) (a : lfstate) (ev : event) (q' : config) : lfstate :=
  LFState q' (own_next N ev (s_K a)) (tk_next ev (s_tk a)).

(** Along a run, a stutter keeps the state. *)
Definition lf_upd (N : nat) (a : lfstate) (l : option event) (q' : config) : lfstate :=
  match l with Some ev => lf_next N a ev q' | None => LFState q' (s_K a) (s_tk a) end.

Fixpoint lf_run_state (N : nat) (a0 : lfstate) (r : nat → config) (l : nat → option event)
    (k : nat) : lfstate :=
  match k with
  | 0 => a0
  | S k' => lf_upd N (lf_run_state N a0 r l k') (l k') (r k)
  end.
