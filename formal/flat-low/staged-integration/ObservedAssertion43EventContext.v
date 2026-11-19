Require Import Assertion43Enable.
From nbits Require Import NBits.
Require Import CoreSocModel ComparisonNodes FormalObservedHistory FormalLocalHistory FormalLegalObservation FormalAssertionDischarge AssertionInstances StagedFlatObservation Assertion44Enable JointBoundaryReachable JointBoundaryInitialization JointBoundaryRegisters JointBoundaryPreparation JointUpdateBoundaryHistory FormalFetchType LegalNoTrapWindow ExceptionEventAlignment ReferenceEventInversion ReferenceValidStability ExceptionInstructionNonzeroWindow ExceptionInstructionAgreement ConcreteRegisterInitialization.
From Coq Require Import ZArith List Lia PeanoNat.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque generated_modules generated_top flat_statements flat_memories.
Theorem observed_assertion43_event_context memory inputs k states :
 generated_observe memory inputs k = Some states ->
 generated_legal_trace memory inputs k ->
 generated_expr_true assertion43_enable (top_environment states) ->
 exists history,
 history 9259%nat = top_environment states /\
 (forall i, (i < 9259)%coq_nat -> formal_flat_local_step
   (formal_invalid_policy (generated_observation_input inputs k) nil) (history i) (history (S i))) /\
 (forall i, (i <= 9259)%coq_nat -> VM.find 1 (history i) = Some (Gval (Fuint 1) [::false])) /\
 (forall node width, List.In (node,width) joint_boundary_registers ->
   map_uint_concrete (N.of_nat node) width (history 0%nat)) /\
 VM.find 1469 (history 9258%nat) = Some (Gval (Fuint 1) [::false]) /\
 VM.find 1667 (history 9258%nat) = Some (Gval (Fuint 1) [::true]) /\
 VM.find 1707 (history 9254%nat) = Some (Gval (Fuint 1) [::true]) /\
 (exists cw cb, VM.find 6780 (history 9253%nat) = Some (Gval (Fuint cw) cb) /\ is_zero cb = false).
Proof.
 intros Observe Legal Enabled.
 destruct (observed_history memory inputs k states Observe Legal) as [bit [history [Last [Steps Resets]]]].
 destruct (observed_last_iteration memory inputs k states Observe)
 as [committed [initial [previous [old [next [Run [Prepare [Prefix [Old [Step State]]]]]]]]]].
 assert (EnabledHistory : generated_expr_true assertion43_enable (history 9259%nat)).
 { rewrite Last. exact Enabled. }
 pose proof (assertion44_checker_reset_after_three _ (history 9254%nat) (history 9255%nat)
 (history 9256%nat) (history 9257%nat) bit (Resets 9254%nat ltac:(vm_compute; lia))
 (Steps 9254%nat ltac:(vm_compute; lia)) (Steps 9255%nat ltac:(vm_compute; lia))
 (Steps 9256%nat ltac:(vm_compute; lia))) as CheckerReset.
 destruct (assertion43_enabled_reset_and_or _ (history 9257%nat) (history 9258%nat) (history 9259%nat) bit
 CheckerReset (Steps 9257%nat ltac:(vm_compute; lia)) (Steps 9258%nat ltac:(vm_compute; lia)) EnabledHistory)
 as [ResetFalse OrTrue]. subst bit.
 destruct (fetch9220_run_type memory inputs k committed Run) as [committed_env [value [Committed Rest]]].
 destruct (joint_boundary_reachable memory inputs k committed Run Legal) as [Registers Storage].
 unfold top_environment in Registers. rewrite Committed in Registers.
 assert (Boundary : forall node width, List.In (node,width) joint_boundary_registers ->
 map_uint_concrete (N.of_nat node) width (history 0%nat)).
 { intros node width Member.
   destruct (joint_boundary_observed_concrete memory inputs k committed committed_env states node width
   Member (Registers node width Member) Run Committed Observe) as [bits [Size Lookup]].
   exists bits. split; [exact Size|].
   rewrite <- (joint_update_register_history_same _ history 9259 node width Member Steps 9259 (Nat.le_refl _)).
   rewrite Last. exact Lookup. }
 assert (LocalAssume : generated_assume_m0_0_local (history 9259%nat)).
 { rewrite Last. unfold top_environment. rewrite State.
   exact (legal_observation_local_assumption memory inputs k states next Legal Observe State). }
 assert (NoTrap : VM.find 45 (history 9254%nat) = Some (Gval (Fuint 1) [::false])).
 { apply (legal_no_trap_history_window _ history 9259 9254 Steps).
   - vm_compute; lia.
   - vm_compute; lia.
   - apply Resets. vm_compute; lia.
   - exact LocalAssume. }
 pose proof (exception_event_false_at_penultimate (generated_observation_input inputs k) nil history Boundary Steps NoTrap) as Implementation.
 pose proof (assertion44_or_true_reference _ (history 9257%nat) (history 9258%nat) (history 9259%nat)
 (Steps 9257%nat ltac:(vm_compute; lia)) (Steps 9258%nat ltac:(vm_compute; lia)) Implementation OrTrue) as Reference.
 destruct (reference_event_true_after_five _ (history 9253%nat) (history 9254%nat) (history 9255%nat)
 (history 9256%nat) (history 9257%nat) (history 9258%nat)
 (Steps 9253%nat ltac:(vm_compute; lia)) (Steps 9254%nat ltac:(vm_compute; lia))
 (Steps 9255%nat ltac:(vm_compute; lia)) (Steps 9256%nat ltac:(vm_compute; lia))
 (Steps 9257%nat ltac:(vm_compute; lia)) Reference) as [ValidLater Raise].
 exists history. split; [exact Last|]. split; [exact Steps|]. split; [exact Resets|].
 split; [exact Boundary|]. split; [exact Implementation|]. split; [exact Reference|].
 split; [exact ValidLater|exact Raise].
Qed.
Print Assumptions observed_assertion43_event_context.
