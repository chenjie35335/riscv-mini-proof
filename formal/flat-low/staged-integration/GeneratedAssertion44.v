Require Import CoreSocModel ComparisonNodes FormalObservedHistory FormalLocalHistory FormalLegalObservation FormalAssertionDischarge AssertionInstances StagedFlatObservation Assertion44Enable JointBoundaryReachable JointBoundaryInitialization JointBoundaryRegisters JointBoundaryPreparation JointUpdateBoundaryHistory FormalFetchType LegalNoTrapWindow ExceptionEventAlignment ReferenceEventInversion ReferenceValidStability ExceptionInstructionNonzeroWindow ExceptionInstructionAgreement ConcreteRegisterInitialization.
From Coq Require Import ZArith List Lia PeanoNat.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque generated_modules generated_top flat_statements flat_memories.
Theorem generated_assert_44 : forall memory_init inputs (k : nat) states,
 generated_observe memory_init inputs k = Some states ->
 generated_legal_trace memory_init inputs k -> generated_assert_m0_44_all states.
Proof.
 intros memory inputs k states Observe Legal.
 destruct (observed_history memory inputs k states Observe Legal) as [bit [history [Last [Steps Resets]]]].
 destruct (observed_last_iteration memory inputs k states Observe)
 as [committed [initial [previous [old [next [Run [Prepare [Prefix [Old [Step State]]]]]]]]]].
 assert (Top : top_environment states = next) by (unfold top_environment; rewrite State; reflexivity).
 apply (proj2 (assertion_44_at_top states)). rewrite State. rewrite <- Top.
 pose proof (Steps 9258%nat ltac:(vm_compute; lia)) as FinalStep.
 change (formal_value_iter (formal_invalid_policy (generated_observation_input inputs k) nil) flat_memories
 (history 9258%nat) false (history 9258%nat) flat_statements = Some (history 9259%nat)) in FinalStep.
 rewrite Last in FinalStep.
 apply (assertion_44_from_enabled_agreement _ _ _ _ FinalStep).
 intro Enabled.
 assert (EnabledHistory : generated_expr_true assertion44_enable (history 9259%nat)).
 { rewrite Last. exact Enabled. }
 pose proof (assertion44_checker_reset_after_three _ (history 9254%nat) (history 9255%nat)
 (history 9256%nat) (history 9257%nat) bit (Resets 9254%nat ltac:(vm_compute; lia))
 (Steps 9254%nat ltac:(vm_compute; lia)) (Steps 9255%nat ltac:(vm_compute; lia))
 (Steps 9256%nat ltac:(vm_compute; lia))) as CheckerReset.
 destruct (assertion44_enabled_reset_and_or _ (history 9257%nat) (history 9258%nat) (history 9259%nat) bit
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
 assert (ValidEarlier : VM.find 1707 (history 9250%nat) = Some (Gval (Fuint 1) [::true])).
 { pose proof (reference_valid_history_stable _ history 9259 9236 9240 false Steps Resets
   ltac:(vm_compute; lia) ltac:(vm_compute; lia)) as Same.
   change (VM.find 1707 (history 9250%nat) = VM.find 1707 (history 9254%nat)) in Same.
   rewrite Same. exact ValidLater. }
 destruct (Boundary 7750%nat 32%nat exception_instruction_register_member) as [bits [Size Source]].
 apply (exception_instruction_nonzero_window_agreement (formal_invalid_policy (generated_observation_input inputs k) nil)
 history 9259 9247 bits Steps).
 - vm_compute; lia.
 - exact Size.
 - exact Source.
 - exact ValidEarlier.
 - exact Raise.
 - exact ValidLater.
Qed.
Print Assumptions generated_assert_44.
