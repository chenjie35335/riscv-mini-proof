Require Import CoreSocModel FormalLocalHistory ObservedFrontPCTransfer ObservedCommitPCTransfer ObservedLegalNoTrap FormalResetPreparation.
From Coq Require Import ZArith Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
(* Adjacent instruction addresses, including wraparound at 2^32. *)
Definition pc_adjacent (older younger : bits) : Prop :=
 size older = 32%nat /\ size younger = 32%nat /\
 to_N younger = (to_N older + 4) mod 2 ^ 32.
Definition pipeline_front_fetch_adjacent env : Prop :=
 exists front fetch, size fetch = 33%nat /\
 VM.find 7749 env = Some (Gval (Fuint 32) front) /\
 VM.find 7768 env = Some (Gval (Fuint 33) fetch) /\
 pc_adjacent front (take 32 fetch).
Definition pipeline_commit_front_adjacent env : Prop :=
 exists commit front,
 VM.find 7751 env = Some (Gval (Fuint 32) commit) /\
 VM.find 7749 env = Some (Gval (Fuint 32) front) /\
 pc_adjacent commit front.
Lemma adjacent_transfer_observed_reset memory inputs k observed :
 generated_observe memory inputs k = Some observed ->
 generated_legal_trace memory inputs k ->
 VM.find 1 (formal_external_inputs (generated_observation_input inputs k)) = Some (Gval (Fuint 1) [::false]) ->
 VM.find 1 (top_environment observed) = Some (Gval (Fuint 1) [::false]).
Proof.
 intros Observe Legal Reset.
 destruct (observed_legal_no_trap_history memory inputs k observed Observe Legal Reset)
 as [committed [initial [history [Run [Prepare [First [Last [Steps NoTrap]]]]]]]].
 destruct (top_reset_prepared (Some committed) _ initial _ Reset Prepare) as [env [Env InitialReset]].
 assert (Reset0 : VM.find 1 (history 0%nat) = Some (Gval (Fuint 1) [::false])).
 { rewrite First. unfold top_environment. rewrite Env. exact InitialReset. }
 rewrite <- Last. apply (legal_local_reset_history _ history 9259 false Steps Reset0). vm_compute;lia.
Qed.
Theorem pipeline_pc_adjacent_transfer memory inputs k observed next :
 generated_observe memory inputs k = Some observed ->
 generated_legal_trace memory inputs k ->
 generated_run memory inputs (S k) = Some next ->
 VM.find 1 (formal_external_inputs (generated_observation_input inputs k)) = Some (Gval (Fuint 1) [::false]) ->
 pipeline_front_fetch_adjacent (top_environment observed) ->
 pipeline_commit_front_adjacent (top_environment next).
Proof.
 intros Observe Legal Next Reset [front [fetch [FetchSize [Front [Fetch Adjacent]]]]].
 destruct Adjacent as [FrontSize Rest].
 pose proof (adjacent_transfer_observed_reset memory inputs k observed Observe Legal Reset) as Root.
 pose proof (observed_front_pc_transfer memory inputs k observed next fetch Observe Legal Next Root FetchSize Fetch) as NewFront.
 pose proof (observed_commit_pc_transfer memory inputs k observed next front Observe Legal Next Reset FrontSize Front) as NewCommit.
 exists front, (take 32 fetch). split; [exact NewCommit|]. split; [exact NewFront|].
 split; assumption.
Qed.
