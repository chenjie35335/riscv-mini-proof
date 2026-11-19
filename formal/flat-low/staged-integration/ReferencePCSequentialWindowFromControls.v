Require Import CoreSocModel FormalLocalHistory FormalObservedHistory ReferencePCSequentialObserved ReferenceControlStabilityHistory.
From Coq Require Import ZArith Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque generated_modules generated_top generated_run.
Theorem reference_pc_window_from_observed_controls memory inputs k observed :
 generated_observe memory inputs k = Some observed ->
 generated_legal_trace memory inputs k ->
 VM.find 1 (top_environment observed) = Some (Gval (Fuint 1) [::false]) ->
 VM.find 6507 (top_environment observed) = Some (Gval (Fuint 1) [::false]) ->
 VM.find 6780 (top_environment observed) = Some (Gval (Fuint 1) [::false]) ->
 reference_pc_sequential_control_window (formal_invalid_policy (generated_observation_input inputs k) nil) (top_environment observed).
Proof.
 intros Observe Legal Reset Redirect Exception.
 destruct (observed_history memory inputs k observed Observe Legal) as [bit [history [Last [Steps Resets]]]].
 assert (FalseBit : bit = false).
 { pose proof (Resets 9259%nat ltac:(vm_compute;lia)) as R. rewrite Last Reset in R.
   destruct bit; [discriminate R|reflexivity]. }
 subst bit. exists history. split; [exact Last|]. split; [exact Steps|]. split; [exact Resets|].
 split.
 - rewrite (reference_control_stable_6507_history (generated_observation_input inputs k) nil history 9259 false Resets Steps 9250 9259 ltac:(vm_compute;lia) ltac:(vm_compute;lia) ltac:(vm_compute;lia) ltac:(vm_compute;lia)). rewrite Last. exact Redirect.
 - split.
   + rewrite (reference_control_stable_6780_history (generated_observation_input inputs k) nil history 9259 false Resets Steps 9250 9259 ltac:(vm_compute;lia) ltac:(vm_compute;lia) ltac:(vm_compute;lia) ltac:(vm_compute;lia)). rewrite Last. exact Exception.
   + rewrite (reference_control_stable_6780_history (generated_observation_input inputs k) nil history 9259 false Resets Steps 9255 9259 ltac:(vm_compute;lia) ltac:(vm_compute;lia) ltac:(vm_compute;lia) ltac:(vm_compute;lia)). rewrite Last. exact Exception.
Qed.
