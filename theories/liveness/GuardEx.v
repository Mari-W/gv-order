(** * The examples against the guard (liveness.md §6, sharp edges 160) *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export liveness.Guard liveness.LiveKob.
From LRGV Require examples.Forwarder examples.TailCall examples.cfst.FirstAction
  examples.SemRounds examples.cfst.CfstTools.
(* NO-EQ: translation pending  From LRGV Require pn.PNExamples mp.MP2Examples. *)

(** The forwarder, with its producer and consumer. *)
Theorem fw_gstyped : gstyped ∅ [] [] (∅, None) Forwarder.fw_main TUnit.
Proof. split; [apply Forwarder.fw_typed|vm_compute; reflexivity]. Qed.

(** The tail call forces the self before the send and applies it after. *)
Theorem tc_gstyped : gstyped ∅ [] [] (∅, None) TailCall.tc_main TUnit.
Proof. split; [apply TailCall.tc_typed|vm_compute; reflexivity]. Qed.

Theorem fa_gstyped : gstyped ∅ [(CfstTools.top_C0, ids 1)] [] (∅, None) FirstAction.fa_go TUnit.
Proof. split; [apply FirstAction.fa_go_typed|vm_compute; reflexivity]. Qed.

Theorem fac_gstyped : gstyped ∅ [(CfstTools.top_C0, ids 1)] [] (∅, None) FirstAction.fac_go TUnit.
Proof. split; [apply FirstAction.fac_go_typed|vm_compute; reflexivity]. Qed.

(** The rounds box of the semantic example is guarded by its two sends. *)
Theorem rounds_guarded : guarded SemRounds.rK.
Proof. vm_compute. reflexivity. Qed.

(* NO-EQ: translation pending
(** MP2 source terms in the style of the translation: the recursive call
    sits under an applied λ whose argument sends (newclient) or after a
    receive (client). Their translations are existential in
    [mtyped], so only the source terms are checked here. *)
Theorem mp2_client_guarded : guarded MP2Examples.client ∧ guarded MP2Examples.newclient.
Proof. split; vm_compute; reflexivity. Qed.
*)

(** Kobayashi's server spawns its self call before any channel step. *)
Theorem kob_not_guarded : ¬ guarded fw_main.
Proof. unfold guarded. vm_compute. discriminate. Qed.

(* NO-EQ: translation pending
(** ⟨fix λx.x⟩ of PN uses its self at once. *)
Theorem pn_div_not_guarded : ¬ guarded PNExamples.div_main.
Proof. unfold guarded. vm_compute. discriminate. Qed.
*)
