Require Import CoreSocModel FormalLocalHistory FormalObservedHistory FormalInstructionResetConstants NopKillHistory.
From Coq Require Import ZArith Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Theorem observed_nop_kill_false memory inputs k observed :
 generated_observe memory inputs k = Some observed ->
 generated_legal_trace memory inputs k ->
 VM.find 7748 (top_environment observed) = Some (Gval (Fuint 32) instruction_nop) ->
 VM.find 85 (top_environment observed) = Some (Gval (Fuint 1) [::false]).
Proof.
 intros Observe Legal Nop.
 destruct (observed_history memory inputs k observed Observe Legal) as [bit [history [Last [Steps Resets]]]].
 rewrite <- Last.
 apply (nop_kill_false_history_from_final (formal_invalid_policy (generated_observation_input inputs k) nil) history 9259);
 try exact Steps; try (vm_compute;lia). rewrite Last. exact Nop.
Qed.
Print Assumptions observed_nop_kill_false.
