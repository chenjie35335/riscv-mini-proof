Require Import CoreSocModel ComparisonNodes FormalLocalHistory FormalObservedHistory FormalObservationCommit StagedFlatCircuitIteration ReferencePCSequentialFullHistory ReferencePCSequentialValues ReferenceControlStabilityHistory.
From Coq Require Import ZArith Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque generated_modules generated_top flat_statements flat_memories.
Theorem reference_pc_sequential_stable_full_history inputs path history result pc :
 (forall i, (i < 9259)%coq_nat -> formal_flat_local_step (formal_invalid_policy inputs path) (history i) (history (S i))) ->
 (forall i, (i <= 9259)%coq_nat -> VM.find 1 (history i) = Some (Gval (Fuint 1) [::false])) ->
 size pc = 32%nat ->
 VM.find 7331 (history 9259%nat) = Some (Gval (Fuint 32) pc) ->
 VM.find 1395 (history 9259%nat) = Some (Gval (Fuint 1) [::true]) ->
 VM.find 6507 (history 9259%nat) = Some (Gval (Fuint 1) [::false]) ->
 VM.find 6780 (history 9259%nat) = Some (Gval (Fuint 1) [::false]) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories (history 9259%nat) true (history 9259%nat) flat_statements = Some result ->
 VM.find 7331 result = Some (Gval (Fuint 32) (reference_pc_plus_four pc)).
Proof.
 intros Steps Resets Size PC Valid Redirect Exception Commit.
 apply (reference_pc_sequential_full_history (formal_invalid_policy inputs path) history result pc Steps Resets Size PC Valid).
 - rewrite (reference_control_stable_6507_history inputs path history 9259 false Resets Steps 9250 9259 ltac:(vm_compute;lia) ltac:(vm_compute;lia) ltac:(vm_compute;lia) ltac:(vm_compute;lia)). exact Redirect.
 - rewrite (reference_control_stable_6780_history inputs path history 9259 false Resets Steps 9250 9259 ltac:(vm_compute;lia) ltac:(vm_compute;lia) ltac:(vm_compute;lia) ltac:(vm_compute;lia)). exact Exception.
 - rewrite (reference_control_stable_6780_history inputs path history 9259 false Resets Steps 9255 9259 ltac:(vm_compute;lia) ltac:(vm_compute;lia) ltac:(vm_compute;lia) ltac:(vm_compute;lia)). exact Exception.
 - exact Commit.
Qed.
Theorem reference_pc_sequential_observed memory inputs k observed next pc :
 generated_observe memory inputs k = Some observed ->
 generated_legal_trace memory inputs k ->
 generated_run memory inputs (S k) = Some next ->
 VM.find 1 (top_environment observed) = Some (Gval (Fuint 1) [::false]) ->
 size pc = 32%nat ->
 VM.find 7331 (top_environment observed) = Some (Gval (Fuint 32) pc) ->
 VM.find 1395 (top_environment observed) = Some (Gval (Fuint 1) [::true]) ->
 VM.find 6507 (top_environment observed) = Some (Gval (Fuint 1) [::false]) ->
 VM.find 6780 (top_environment observed) = Some (Gval (Fuint 1) [::false]) ->
 VM.find 7331 (top_environment next) = Some (Gval (Fuint 32) (reference_pc_plus_four pc)).
Proof.
 intros Observe Legal Next Reset Size PC Valid Redirect Exception.
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
 apply (reference_pc_sequential_stable_full_history (generated_observation_input inputs k) nil history after pc Steps Resets Size).
 - rewrite Last. exact PC.
 - rewrite Last. exact Valid.
 - rewrite Last. exact Redirect.
 - rewrite Last. exact Exception.
 - exact Step.
Qed.
