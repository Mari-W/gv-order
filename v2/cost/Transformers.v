(** * Ticket transformers under sequencing (stage S7)

    [seq_sound]: when t1 ∘ t2 is sound ([tok]), a ticket count that meets
    t1 ∘ t2 at the reserve r splits into a reserve r′ that meets t2 at r
    and a count that meets t1 at r′. Offsets range over ℕ ∪ {∞}. A
    transformer with offset ∞ is met nowhere, so its cases are vacuous.
    Stage S2 states the lemma in §2.17 and defers it, and so does S6. *)

From GV Require Export types.Costs.

Lemma seq_sound t1 t2 r tk :
  tok t1 t2 → meets (tseq t1 t2) r tk → ∃ r', meets t1 r' tk ∧ meets t2 r r'.
Proof.
  destruct t1 as [[s1|] [b1|]], t2 as [[s2|] [[|b2]|]];
    unfold tok, meets, tseq, tapp, fmul; simpl; intros Hok H.
  all: try (destruct (Nat.eqb r 0) eqn:E; [apply Nat.eqb_eq in E as ->|done]).
  all: try done.
  all: try (destruct Hok as [Hok|[Hok|Hok]]; done).
  all: first [ exists 0; simpl; split; nia
             | exists (2 ^ s2 * r + 0); rewrite Nat.pow_add_r in H; split; nia
             | exists (2 ^ s2 * r + S b2); rewrite Nat.pow_add_r in H; split; nia
             | exists (S b2); split; nia ].
Qed.

(** Facts about [meets] that the compatibility lemmas read. *)
Lemma meets_mono t r tk tk' : tk ≤ tk' → meets t r tk → meets t r tk'.
Proof. unfold meets. destruct (tapp t r); lia. Qed.

Lemma meets_tid r tk : meets tid r tk ↔ r ≤ tk.
Proof. unfold meets, tid, tapp. simpl. lia. Qed.
