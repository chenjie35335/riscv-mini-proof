Require Import CoreSocModel ComparisonNodes FormalLocalHistory FormalObservationCommit StagedFlatCircuitIteration EarlyBubbleNormalHistory ObservedLegalNoTrap JointBoundaryReachable JointBoundaryInitialization JointBoundaryPreparation JointBoundaryRegisters FormalFetchType FormalResetPreparation ConcreteRegisterInitialization.
From Coq Require Import ZArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque generated_modules generated_top flat_statements flat_memories generated_run generated_observe.
Theorem observed_early_bubble_clear_step memory inputs k observed next old_value :
 generated_observe memory inputs k = Some observed ->
 generated_legal_trace memory inputs k ->
 generated_run memory inputs (S k) = Some next ->
 VM.find 1 (formal_external_inputs (generated_observation_input inputs k)) = Some (Gval (Fuint 1) [::false]) ->
 VM.find 7762 (top_environment observed) = Some (Gval (Fuint 1) [::false]) ->
 VM.find 85 (top_environment observed) = Some (Gval (Fuint 1) [::false]) ->
 VM.find 1360 (top_environment observed) = Some (Gval (Fuint 1) [::false]) ->
 VM.find 7945 (top_environment observed) = Some old_value ->
 type_of_val old_value = Gtyp (Fuint 1) ->
 VM.find 7945 (top_environment next) = Some (Gval (Fuint 1) [::false]).
Proof.
 intros Observe Legal Next Reset Started Kill Branch Old Typed.
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
 apply (early_bubble_clear_history (generated_observation_input inputs k) nil history after old_value
 Boundary Steps Resets NoTrap).
 - rewrite Last. exact Started.
 - rewrite Last. exact Kill.
 - rewrite Last. exact Branch.
 - rewrite Last. exact Old.
 - exact Typed.
 - exact Step.
Qed.
(* Transitive assumptions are audited separately to keep incremental compilation fast. *)
