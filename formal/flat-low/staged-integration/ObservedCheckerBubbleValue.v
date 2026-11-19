Require Import CoreSocModel FormalLocalHistory ObservedLegalNoTrap FormalResetPreparation CheckerValidBubbleValue.
From Coq Require Import ZArith Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque generated_modules generated_top generated_run generated_observe.
Theorem observed_checker_bubble_value memory inputs k observed bubble :
 generated_observe memory inputs k = Some observed ->
 generated_legal_trace memory inputs k ->
 VM.find 1 (formal_external_inputs (generated_observation_input inputs k)) = Some (Gval (Fuint 1) [::false]) ->
 VM.find 7947 (top_environment observed) = Some (Gval (Fuint 1) [::bubble]) ->
 VM.find 1 (top_environment observed) = Some (Gval (Fuint 1) [::false]) /\
 VM.find 1395 (top_environment observed) = Some (Gval (Fuint 1) [::~~ bubble]).
Proof.
 intros Observe Legal Reset Bubble.
 destruct (observed_legal_no_trap_history memory inputs k observed Observe Legal Reset)
 as [committed [initial [history [Run [Prepare [First [Last [Steps NoTrap]]]]]]]].
 destruct (top_reset_prepared (Some committed) _ initial _ Reset Prepare) as [env [Env InitialReset]].
 assert (Reset0 : VM.find 1 (history 0%nat) = Some (Gval (Fuint 1) [::false])).
 { rewrite First. unfold top_environment. rewrite Env. exact InitialReset. }
 pose proof (legal_local_reset_history _ history 9259 false Steps Reset0) as Resets.
 split.
 - rewrite <- Last. apply Resets. vm_compute;lia.
 - rewrite <- Last. apply (checker_valid_history_from_bubble _ history bubble Steps Resets).
   rewrite Last. exact Bubble.
Qed.
Print Assumptions observed_checker_bubble_value.
