Require Import EarlyBubbleNopControlKnown PipelineBubbleNormalCommit FormalCheckerResetConnections Bubble7945Type CoreSocModel ComparisonNodes FormalLocalHistory FormalObservationCommit StagedFlatCircuitIteration LateBubbleNormalHistory ObservedLegalNoTrap JointBoundaryReachable JointBoundaryInitialization JointBoundaryPreparation JointBoundaryRegisters FormalFetchType FormalResetPreparation ConcreteRegisterInitialization.
From Coq Require Import ZArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque generated_modules generated_top flat_statements flat_memories generated_run.
Theorem early_bubble_known_normal_successor memory inputs k observed next :
 generated_observe memory inputs k = Some observed ->
 generated_legal_trace memory inputs k ->
 generated_run memory inputs (S k) = Some next ->
 VM.find 1 (formal_external_inputs (generated_observation_input inputs k)) = Some (Gval (Fuint 1) [::false]) ->
 exists bit, VM.find 7945 (top_environment next) = Some (Gval (Fuint 1) [::bit]).
Proof.
 intros Observe Legal Next Reset.
 destruct (bubble7945_observe_type memory inputs k observed Observe) as [old_value [Old Typed]].
 destruct (observed_legal_no_trap_history memory inputs k observed Observe Legal Reset)
 as [committed [initial [history [Run [Prepare [First [Last [Steps NoTrap]]]]]]]].
 destruct (fetch9220_run_type memory inputs k committed Run) as [env [value [Env Rest]]].
 destruct (joint_boundary_reachable memory inputs k committed Run Legal) as [Registers Storage].
 unfold top_environment in Registers. rewrite Env in Registers.
 assert (Boundary : forall node width, List.In (node,width) joint_boundary_registers ->
 map_uint_concrete (N.of_nat node) width (history 0%nat)).
 { intros node width Member. rewrite First.
   exact (joint_boundary_prepared_concrete committed env _ initial node width
    Member (Registers node width Member) Env Prepare). }
 destruct (top_reset_prepared (Some committed) _ initial _ Reset Prepare) as [initial_env [InitialEnv InitialReset]].
 assert (Reset0 : VM.find 1 (history 0%nat) = Some (Gval (Fuint 1) [::false])).
 { rewrite First. unfold top_environment. rewrite InitialEnv. exact InitialReset. }
 pose proof (legal_local_reset_history _ history 9259 false Steps Reset0) as Resets.
 rewrite (observation_then_commit memory inputs k observed Observe) in Next.
 destruct (flat_iteration_projection _ observed true next Next) as [before [after [Before [Step After]]]].
 assert (Top : top_environment observed = before) by (unfold top_environment; rewrite Before; reflexivity).
 unfold top_environment. rewrite After.
 rewrite <- Top in Step. rewrite <- Last in Step.
 destruct (early_bubble_nop_control_known (generated_observation_input inputs k) nil history Boundary Steps) as [bit Source].
 exists bit.
 assert (Reset65 : VM.find 65 (history 9259%nat) = Some (Gval (Fuint 1) [::false])).
 { apply (reset_connection_65_transfer (formal_invalid_policy (generated_observation_input inputs k) nil) (history 9258%nat) (history 9258%nat) (history 9259%nat) false).
 - apply (reset_connection_24_transfer (formal_invalid_policy (generated_observation_input inputs k) nil) (history 9257%nat) (history 9257%nat) (history 9258%nat) false); [apply Resets|apply Steps];vm_compute;lia.
 - apply Steps;vm_compute;lia. }
 apply (pipeline_bubble_7945_normal_commit (formal_invalid_policy (generated_observation_input inputs k) nil) (history 9259%nat) (history 9259%nat) after old_value bit).
 - rewrite Last. exact Old.
 - exact Typed.
 - exact Reset65.
 - exact Source.
 - exact Step.
Qed.
Require Import PipelineBubbleInitialization PipelineBubbleResetCommit PipelineBubbleResetBase BooleanRegisterResetCycle JointBoundaryInduction ExternalReset StagedObservedRegister StagedCircuitRegisterHold.
Theorem early_bubble_known_run memory inputs k states :
 generated_run memory inputs k = Some states ->
 generated_legal_trace memory inputs k ->
 exists bit, VM.find 7945 (top_environment states) = Some (Gval (Fuint 1) [::bit]).
Proof.
 destruct k as [|k]; intros Run Legal.
 - destruct (pipeline_bubbles_run_zero memory inputs states Run) as [env [Env [Early Late]]].
   exists true. unfold top_environment. rewrite Env. exact Early.
 - assert (PriorLegal : generated_legal_trace memory inputs k).
   { apply (joint_legal_trace_prefix memory inputs (S k) k Legal). lia. }
   destruct (legal_observation_reset memory inputs k PriorLegal) as [reset Reset].
   destruct reset.
   + pose proof Run as Next. rewrite generated_run_successor in Next.
     destruct (generated_run memory inputs k) as [previous|] eqn:Previous; [|discriminate Next].
     destruct (bubble7945_run_type memory inputs k previous Previous) as [old [value [Old [Value Typed]]]].
     destruct (boolean_register_reset_cycle 7945 bubble7945_present (Logic.eq_refl true) (Logic.eq_refl true)
      bubble7945_initial_safe pipeline_bubble_7945_reset_commit (generated_observation_input inputs k) previous old states value Old Value Typed Reset Next)
      as [env [Env Known]].
     exists true. unfold top_environment. rewrite Env. exact Known.
   + destruct (generated_successful_commit memory inputs k states Run) as [observed [Observe Commit]].
     exact (early_bubble_known_normal_successor memory inputs k observed states Observe PriorLegal Run Reset).
Qed.
Theorem early_bubble_known_observation memory inputs k observed :
 generated_observe memory inputs k = Some observed ->
 generated_legal_trace memory inputs k ->
 exists bit, VM.find 7945 (top_environment observed) = Some (Gval (Fuint 1) [::bit]).
Proof.
 intros Observe Legal. pose proof Observe as Expanded. unfold generated_observe in Expanded.
 destruct (generated_run memory inputs k) as [previous|] eqn:Run; [|discriminate Expanded].
 destruct (bubble7945_run_type memory inputs k previous Run) as [old [value [Old [Value Typed]]]].
 destruct (early_bubble_known_run memory inputs k previous Run Legal) as [bit Known].
 unfold top_environment in Known. rewrite Old in Known.
 pose proof (staged_observed_register_copies memory inputs k previous old observed 7945
 (Logic.eq_refl true) (Logic.eq_refl true) bubble7945_initial_safe bubble7945_present Run Old Observe) as Copy.
 rewrite Known in Copy. unfold staged_register_lookup in Copy.
 exists bit. unfold top_environment. destruct (SVM.find nil observed); [exact Copy|discriminate Copy].
Qed.
