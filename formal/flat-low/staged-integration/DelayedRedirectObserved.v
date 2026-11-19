Require Import FetchPCSelectorStability EarlyControlStabilityHistory FormalPCControlNodes CoreSocModel ComparisonNodes FormalLocalHistory FormalObservationCommit StagedFlatCircuitIteration DelayedRedirectHistory ObservedLegalNoTrap JointBoundaryReachable JointBoundaryInitialization JointBoundaryPreparation JointBoundaryRegisters FormalFetchType FormalResetPreparation ConcreteRegisterInitialization.
From Coq Require Import ZArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque generated_modules generated_top flat_statements flat_memories generated_run generated_observe.
Theorem delayed_redirect_observed_step memory inputs k observed next bit :
 generated_observe memory inputs k = Some observed ->
 generated_legal_trace memory inputs k ->
 generated_run memory inputs (S k) = Some next ->
 VM.find 1 (formal_external_inputs (generated_observation_input inputs k)) = Some (Gval (Fuint 1) [::false]) ->
 VM.find 7773 (top_environment observed) = Some (Gval (Fuint 1) [::bit]) ->
 VM.find 7760 (top_environment next) = Some (Gval (Fuint 1) [::bit]).
Proof.
 intros Observe Legal Next Reset Source.
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
 apply (delayed_redirect_full_history (generated_observation_input inputs k) nil history after bit Boundary Steps Resets NoTrap).
 - rewrite Last. exact Source.
 - exact Step.
Qed.

Theorem delayed_redirect_observed_value memory inputs k observed next low high branch :
 generated_observe memory inputs k = Some observed ->
 generated_legal_trace memory inputs k ->
 generated_run memory inputs (S k) = Some next ->
 VM.find 1 (formal_external_inputs (generated_observation_input inputs k)) = Some (Gval (Fuint 1) [::false]) ->
 VM.find 84 (top_environment observed) = Some (Gval (Fuint 2) [::low;high]) ->
 VM.find 1360 (top_environment observed) = Some (Gval (Fuint 1) [::branch]) ->
 VM.find 7760 (top_environment next) = Some (Gval (Fuint 1) [::(low && ~~high) || branch]).
Proof.
 intros Observe Legal Next Reset Selector Branch.
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
 assert (OldSelector : VM.find 84 (history 9257%nat) = Some (Gval (Fuint 2) [::low;high])).
 { destruct (fetch_pc_decode_same_history (generated_observation_input inputs k) nil history 9259 Boundary Steps 9257 9259 ltac:(vm_compute;lia) ltac:(vm_compute;lia) ltac:(vm_compute;lia) ltac:(vm_compute;lia)) as [word [W O]].
 rewrite Last Selector in O. inversion O; subst word. exact W. }
 assert (OldBranch : VM.find 1360 (history 9258%nat) = Some (Gval (Fuint 1) [::branch])).
 { rewrite (early_control_stable_1360_history (generated_observation_input inputs k) nil history 9259 Boundary Steps 9258 9259 ltac:(vm_compute;lia) ltac:(vm_compute;lia) ltac:(vm_compute;lia) ltac:(vm_compute;lia)). rewrite Last. exact Branch. }
 assert (Decode : VM.find 7772 (history 9258%nat) = Some (Gval (Fuint 1) [::low && ~~high])).
 { apply (pc_control_node_7772 (formal_invalid_policy (generated_observation_input inputs k) nil) (history 9257%nat) (history 9257%nat) (history 9258%nat)); [|reflexivity|apply Steps;vm_compute;lia].
 cbn [pc_control_expr_7772 eval_hfexpr_with_memory eval_href_with_memory]. rewrite OldSelector. destruct low,high;reflexivity. }
 assert (Source : VM.find 7773 (history 9259%nat) = Some (Gval (Fuint 1) [::(low && ~~high) || branch])).
 { apply (pc_control_node_7773 (formal_invalid_policy (generated_observation_input inputs k) nil) (history 9258%nat) (history 9258%nat) (history 9259%nat)); [|reflexivity|apply Steps;vm_compute;lia].
 cbn [pc_control_expr_7773 eval_hfexpr_with_memory eval_href_with_memory]. rewrite Decode OldBranch. destruct low,high,branch;reflexivity. }
 rewrite (observation_then_commit memory inputs k observed Observe) in Next.
 destruct (flat_iteration_projection _ observed true next Next) as [before [after [Before [Step After]]]].
 assert (Top : top_environment observed = before) by (unfold top_environment; rewrite Before; reflexivity).
 unfold top_environment. rewrite After.
 rewrite <- Top in Step. rewrite <- Last in Step.
 apply (delayed_redirect_full_history (generated_observation_input inputs k) nil history after ((low && ~~high) || branch) Boundary Steps Resets NoTrap).
 - exact Source.
 - exact Step.
Qed.
