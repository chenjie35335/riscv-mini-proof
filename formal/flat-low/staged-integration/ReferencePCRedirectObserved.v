Require Import CoreSocModel ComparisonNodes FormalLocalHistory FormalObservationCommit StagedFlatCircuitIteration ReferencePCRedirectFullHistory ReferencePCTargetHistory ReferenceControlStabilityHistory FormalObservedHistory.
From Coq Require Import ZArith Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque generated_modules generated_top flat_statements flat_memories.
Theorem reference_pc_redirect_observed memory inputs k observed next pc target :
 generated_observe memory inputs k = Some observed ->
 generated_legal_trace memory inputs k ->
 generated_run memory inputs (S k) = Some next ->
 VM.find 1 (top_environment observed) = Some (Gval (Fuint 1) [::false]) ->
 size target = 32%nat ->
 VM.find 7331 (top_environment observed) = Some (Gval (Fuint 32) pc) ->
 VM.find 1395 (top_environment observed) = Some (Gval (Fuint 1) [::true]) ->
 VM.find 6507 (top_environment observed) = Some (Gval (Fuint 1) [::true]) ->
 VM.find 6780 (top_environment observed) = Some (Gval (Fuint 1) [::false]) ->
 VM.find 6508 (top_environment observed) = Some (Gval (Fuint 32) target) ->
 VM.find 7331 (top_environment next) = Some (Gval (Fuint 32) target).
Proof.
 intros Observe Legal Next Reset Size PC Valid Redirect Exception Target.
 destruct (observed_history memory inputs k observed Observe Legal) as [bit [history [Last [Steps Resets]]]].
 assert (FalseBit : bit = false).
 { pose proof (Resets 9259%nat ltac:(vm_compute;lia)) as R. rewrite Last Reset in R.
   destruct bit; [discriminate R|reflexivity]. }
 subst bit.
 rewrite (observation_then_commit memory inputs k observed Observe) in Next.
 destruct (flat_iteration_projection _ observed true next Next) as [before [after [Before [Step After]]]].
 assert (Top : top_environment observed = before) by (unfold top_environment; rewrite Before; reflexivity).
 unfold top_environment. rewrite After.
 rewrite <- Top in Step. rewrite <- Last in Step.
 apply (reference_pc_redirect_full_history (formal_invalid_policy (generated_observation_input inputs k) nil) history after pc target Steps Resets Size).
 - rewrite (reference_pc_target_6508_stable (generated_observation_input inputs k) nil history 9259 false Resets Steps 9254 9259 ltac:(vm_compute;lia) ltac:(vm_compute;lia) ltac:(vm_compute;lia) ltac:(vm_compute;lia)). rewrite Last. exact Target.
 - rewrite Last. exact PC.
 - rewrite Last. exact Valid.
 - rewrite (reference_control_stable_6507_history (generated_observation_input inputs k) nil history 9259 false Resets Steps 9250 9259 ltac:(vm_compute;lia) ltac:(vm_compute;lia) ltac:(vm_compute;lia) ltac:(vm_compute;lia)). rewrite Last. exact Redirect.
 - rewrite (reference_control_stable_6780_history (generated_observation_input inputs k) nil history 9259 false Resets Steps 9250 9259 ltac:(vm_compute;lia) ltac:(vm_compute;lia) ltac:(vm_compute;lia) ltac:(vm_compute;lia)). rewrite Last. exact Exception.
 - rewrite (reference_control_stable_6780_history (generated_observation_input inputs k) nil history 9259 false Resets Steps 9255 9259 ltac:(vm_compute;lia) ltac:(vm_compute;lia) ltac:(vm_compute;lia) ltac:(vm_compute;lia)). rewrite Last. exact Exception.
 - exact Step.
Qed.
