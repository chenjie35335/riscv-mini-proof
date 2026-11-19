Require Import CoreSocModel ComparisonNodes EarlyBubbleValues EarlyControlWireBitNormalization EarlyControlStabilityHistory ExceptionStabilityHistory ExceptionEventHistory JointBoundaryRegisters JointUpdateBoundaryHistory ConcreteRegisterInitialization StartupFlagInitialization NormalizedBit EarlyBubbleNopControlKnown ExceptionPCSourceRegisters.
From Coq Require Import ZArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Theorem startup_bubble_source_true inputs path history :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < 9259)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 VM.find 7762 (history 9259%nat) = Some (Gval (Fuint 1) [::true]) ->
 VM.find 7944 (history 9259%nat) = Some (Gval (Fuint 1) [::true]).
Proof.
 intros Boundary Steps StartedFinal.
 assert (Started : VM.find 7762 (history 9256%nat) = Some (Gval (Fuint 1) [::true])).
 { rewrite (flat_register_history_same _ history 9259 7762 startup_register_present Steps 9256 ltac:(vm_compute;lia)).
   rewrite (flat_register_history_same _ history 9259 7762 startup_register_present Steps 9259 ltac:(vm_compute;lia)) in StartedFinal. exact StartedFinal. }
 destruct (early_control_wire_85_normalized _ (history 9255%nat) (history 9255%nat) (history 9256%nat)
 (Steps 9255%nat ltac:(vm_compute;lia))) as [killValue [KillValue KillNormal]].
 destruct (early_bubble_normalized_concrete _ 85 killValue KillValue KillNormal
 (early_control_concrete_85_history inputs path history 9259 Boundary Steps 9256 ltac:(vm_compute;lia) ltac:(vm_compute;lia))) as [kill Kill].
 destruct (early_control_wire_1360_normalized _ (history 9256%nat) (history 9256%nat) (history 9257%nat)
 (Steps 9256%nat ltac:(vm_compute;lia))) as [branchValue [BranchValue BranchNormal]].
 destruct (early_bubble_normalized_concrete _ 1360 branchValue BranchValue BranchNormal
 (early_control_concrete_1360_history inputs path history 9259 Boundary Steps 9257 ltac:(vm_compute;lia) ltac:(vm_compute;lia))) as [branch Branch].
 destruct (exception_source128_normalized _ (history 9257%nat) (history 9257%nat) (history 9258%nat)
 (Steps 9257%nat ltac:(vm_compute;lia))) as [exceptionValue [ExceptionValue ExceptionNormal]].
 destruct (early_bubble_normalized_concrete _ 128 exceptionValue ExceptionValue ExceptionNormal
 (exception_concrete_128_history inputs path history 9259 Boundary Steps 9258 ltac:(vm_compute;lia) ltac:(vm_compute;lia))) as [exception Exception].
 exact (early_bubble_value_after_three (formal_invalid_policy inputs path)
 (history 9256%nat) (history 9257%nat) (history 9258%nat) (history 9259%nat)
 true kill branch exception Started Kill Branch Exception
 (Steps 9256%nat ltac:(vm_compute;lia)) (Steps 9257%nat ltac:(vm_compute;lia))
 (Steps 9258%nat ltac:(vm_compute;lia))).
Qed.


Require Import PipelineBubbleNormalCommit FormalCheckerResetConnections CoreSocModel ComparisonNodes FormalLocalHistory FormalObservationCommit StagedFlatCircuitIteration EarlyBubbleNopFullHistory FormalInstructionResetConstants ObservedLegalNoTrap JointBoundaryReachable JointBoundaryInitialization JointBoundaryPreparation JointBoundaryRegisters FormalFetchType FormalResetPreparation ConcreteRegisterInitialization.
From Coq Require Import ZArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque generated_modules generated_top flat_statements flat_memories generated_run generated_observe.
Theorem startup_bubble_observed_step memory inputs k observed next old_value :
 generated_observe memory inputs k = Some observed ->
 generated_legal_trace memory inputs k ->
 generated_run memory inputs (S k) = Some next ->
 VM.find 1 (formal_external_inputs (generated_observation_input inputs k)) = Some (Gval (Fuint 1) [::false]) ->
 VM.find 7945 (top_environment observed) = Some old_value ->
 type_of_val old_value = Gtyp (Fuint 1) ->
 VM.find 7762 (top_environment observed) = Some (Gval (Fuint 1) [::true]) ->
 VM.find 7945 (top_environment next) = Some (Gval (Fuint 1) [::true]).
Proof.
 intros Observe Legal Next Reset Old Typed Started.
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
 assert (Source : VM.find 7944 (history 9259%nat) = Some (Gval (Fuint 1) [::true])).
 { apply (startup_bubble_source_true _ _ history Boundary Steps). rewrite Last. exact Started. }
 assert (Reset65 : VM.find 65 (history 9259%nat) = Some (Gval (Fuint 1) [::false])).
 { apply (reset_connection_65_transfer (formal_invalid_policy (generated_observation_input inputs k) nil) (history 9258%nat) (history 9258%nat) (history 9259%nat) false).
 - apply (reset_connection_24_transfer (formal_invalid_policy (generated_observation_input inputs k) nil) (history 9257%nat) (history 9257%nat) (history 9258%nat) false); [apply Resets|apply Steps]; vm_compute;lia.
 - apply Steps. vm_compute;lia. }
 apply (pipeline_bubble_7945_normal_commit (formal_invalid_policy (generated_observation_input inputs k) nil) (history 9259%nat) (history 9259%nat) after old_value true).
 - rewrite Last. exact Old.
 - exact Typed.
 - exact Reset65.
 - exact Source.
 - exact Step.
Qed.

Require Import PipelinePCRelation EarlyBubbleNopReachable PipelineBubbleInstructionInvariant FetchPCNopObserved FetchPCSequentialExact ObservedCheckerBubbleValue ObservedReferencePCStutter ObservedLateBubbleTransfer StartupFlagReachable Bubble7947Type.
Theorem pipeline_pc_startup_transition_exact memory inputs k observed next bits fetch :
 generated_observe memory inputs k = Some observed ->
 generated_legal_trace memory inputs k ->
 generated_run memory inputs (S k) = Some next ->
 VM.find 1 (formal_external_inputs (generated_observation_input inputs k)) = Some (Gval (Fuint 1) [::false]) ->
 size bits = 32%nat -> take 2 bits = [::false;false] ->
 VM.find 7331 (top_environment observed) = Some (Gval (Fuint 32) bits) ->
 VM.find 7947 (top_environment observed) = Some (Gval (Fuint 1) [::true]) ->
 VM.find 7945 (top_environment observed) = Some (Gval (Fuint 1) [::true]) ->
 VM.find 7762 (top_environment observed) = Some (Gval (Fuint 1) [::true]) ->
 VM.find 7768 (top_environment observed) = Some (Gval (Fuint 33) fetch) ->
 take 32 (fetch_pc_plus_four fetch) = bits ->
 pipeline_pc_relation (top_environment next).
Proof.
 intros Observe Legal Next Reset Size Aligned Reference Late Early Started Fetch Match.
 destruct (observed_checker_bubble_value memory inputs k observed true Observe Legal Reset Late) as [Root Disabled].
 pose proof (early_bubble_nop_all_observations memory inputs k observed Observe Legal Early) as Nop.
 pose proof (fetch_pc_nop_observed memory inputs k observed next fetch Observe Legal Next Root Nop Fetch) as NewFetch.
 pose proof (observed_reference_pc_disabled_step memory inputs k observed next bits Observe Legal Next Root Disabled Size Reference) as NewReference.
 pose proof (startup_bubble_observed_step memory inputs k observed next (Gval (Fuint 1) [::true]) Observe Legal Next Reset Early (Logic.eq_refl _) Started) as NewEarly.
 pose proof (observed_late_bubble_normal_step memory inputs k observed next true (Gval (Fuint 1) [::true]) Observe Legal Next Reset Early Late (Logic.eq_refl _)) as NewLate.
 destruct (startup_flag_normal_successor memory inputs k next Legal Reset Next) as [env [Env NewStarted]].
 assert (StartedNext : VM.find 7762 (top_environment next) = Some (Gval (Fuint 1) [::false])).
 { unfold top_environment. rewrite Env. exact NewStarted. }
 exists bits. split; [exact Size|]. split; [exact Aligned|]. split; [exact NewReference|].
 right. right. split; [exact NewLate|]. split; [exact NewEarly|].
 exists (fetch_pc_plus_four fetch). split; [apply fetch_pc_plus_four_size|].
 split; [exact NewFetch|]. left. split; [exact StartedNext|]. symmetry. exact Match.
Qed.

Require Import FetchPCArithmetic.
From nbits Require Import NBits.
Theorem pipeline_pc_startup_transition memory inputs k observed next :
 generated_observe memory inputs k = Some observed ->
 generated_legal_trace memory inputs k ->
 generated_run memory inputs (S k) = Some next ->
 VM.find 1 (formal_external_inputs (generated_observation_input inputs k)) = Some (Gval (Fuint 1) [::false]) ->
 pipeline_pc_relation (top_environment observed) ->
 VM.find 7947 (top_environment observed) = Some (Gval (Fuint 1) [::true]) ->
 VM.find 7945 (top_environment observed) = Some (Gval (Fuint 1) [::true]) ->
 VM.find 7762 (top_environment observed) = Some (Gval (Fuint 1) [::true]) ->
 pipeline_pc_relation (top_environment next).
Proof.
 intros Observe Legal Next Reset [bits [Size [Aligned [Reference Phase]]]] Late Early Started.
 destruct Phase as [[L C]|[[L [E F]]|[L [E [fetch [FetchSize [Fetch State]]]]]]].
 - rewrite Late in L. discriminate L.
 - rewrite Early in E. discriminate E.
 - destruct State as [[S Eq]|[S Numeric]].
   + rewrite Started in S. discriminate S.
   + apply (pipeline_pc_startup_transition_exact memory inputs k observed next bits fetch Observe Legal Next Reset Size Aligned Reference Late Early Started Fetch).
     exact (fetch_pc_plus_four_matches_reference fetch bits Size Numeric).
Qed.
