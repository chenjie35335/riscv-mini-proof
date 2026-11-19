Require Import PipelineRedirectPhase PipelineRedirectPhaseReachable CoreSocModel ComparisonNodes DUTRedirectDecode ReferenceRedirectSpine JointBoundaryRegisters JointUpdateBoundaryHistory ConcreteRegisterInitialization EarlyBubbleValues EarlyBubbleNopControlKnown EarlyControlWireBitNormalization EarlyControlStabilityHistory ExceptionStabilityHistory ExceptionEventHistory StartupFlagInitialization FormalPCControlNodes ALUOutputTransfer FormalLocalHistory FormalObservationCommit StagedFlatCircuitIteration PipelineBubbleNormalCommit Bubble7945Type FormalCheckerResetConnections.
From Coq Require Import NArith ZArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Lemma pipeline_no_kill_selector_row n : (n < 49)%coq_nat ->
 nth false pipeline_kill_rows n = false ->
 from_N 2 (dut_decode_output false (dut_decode_row n)) = [::false;false].
Proof. intro Bound;do 49 (destruct n as [|n];[vm_compute;intro H;first[reflexivity|discriminate H]|]);lia. Qed.
Lemma pipeline_no_kill_selector instruction count : (count <= 49)%coq_nat ->
 pipeline_kill_decode instruction count = false ->
 dut_decode_mux_value false instruction count = [::false;false].
Proof.
 induction count as [|count IH];intros Bound Kill;[reflexivity|].
 rewrite pipeline_kill_decode_S in Kill.
 unfold dut_decode_mux_value;fold dut_decode_mux_value.
 destruct (dut_decode_test instruction (Nat.sub 48 count)) eqn:Guard.
 - apply pipeline_no_kill_selector_row;[lia|exact Kill].
 - apply IH;[lia|exact Kill].
Qed.
Theorem pipeline_bubble_value_history inputs path history instruction :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < 9259)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 VM.find 7748 (history 9259%nat) = Some (Gval (Fuint 32) instruction) -> size instruction = 32%nat ->
 exists start branch exception,
 VM.find 1360 (history 9259%nat) = Some (Gval (Fuint 1) [::branch]) /\
 VM.find 7944 (history 9259%nat) = Some (Gval (Fuint 1) [::((start || pipeline_kill_decode (to_N instruction) 49) || branch) || exception]).
Proof.
 intros Boundary Steps Front Size.
 destruct (joint_update_register_history_concrete _ history 9259 7762 1 startup_register_member
 (Boundary _ _ startup_register_member) Steps 9256 ltac:(vm_compute;lia)) as [started [StartedSize Started]].
 destruct started as [|start tail];[discriminate StartedSize|]. destruct tail as [|extra tail];[|discriminate StartedSize].
 pose proof (pipeline_kill_history inputs path history 9259 instruction Steps Front Size 9256 ltac:(vm_compute;lia) ltac:(vm_compute;lia)) as Kill.
 destruct (early_control_wire_1360_normalized _ (history 9256%nat) (history 9256%nat) (history 9257%nat)
 (Steps 9256%nat ltac:(vm_compute;lia))) as [branchValue [BranchValue BranchNormal]].
 destruct (early_bubble_normalized_concrete _ 1360 branchValue BranchValue BranchNormal
 (early_control_concrete_1360_history inputs path history 9259 Boundary Steps 9257 ltac:(vm_compute;lia) ltac:(vm_compute;lia))) as [branch Branch].
 destruct (exception_source128_normalized _ (history 9257%nat) (history 9257%nat) (history 9258%nat)
 (Steps 9257%nat ltac:(vm_compute;lia))) as [exceptionValue [ExceptionValue ExceptionNormal]].
 destruct (early_bubble_normalized_concrete _ 128 exceptionValue ExceptionValue ExceptionNormal
 (exception_concrete_128_history inputs path history 9259 Boundary Steps 9258 ltac:(vm_compute;lia) ltac:(vm_compute;lia))) as [exception Exception].
 pose proof (early_bubble_value_after_three (formal_invalid_policy inputs path) (history 9256%nat) (history 9257%nat) (history 9258%nat) (history 9259%nat)
 start (pipeline_kill_decode (to_N instruction) 49) branch exception Started Kill Branch Exception
 (Steps 9256%nat ltac:(vm_compute;lia)) (Steps 9257%nat ltac:(vm_compute;lia)) (Steps 9258%nat ltac:(vm_compute;lia))) as Source.
 exists start,branch,exception. split;[|exact Source].
 rewrite (early_control_stable_1360_history inputs path history 9259 Boundary Steps 9259 9257 ltac:(vm_compute;lia) ltac:(vm_compute;lia) ltac:(vm_compute;lia) ltac:(vm_compute;lia));exact Branch.
Qed.
Lemma pipeline_or_clear (a b c d : bool) : false = (((a || b) || c) || d) -> b = false /\ c = false.
Proof. destruct a,b,c,d;cbn;intro H;try discriminate;auto. Qed.
Theorem pipeline_early_clear_sequential_controls memory inputs k observed next :
 generated_observe memory inputs k = Some observed -> generated_legal_trace memory inputs k ->
 generated_run memory inputs (S k) = Some next ->
 VM.find 1 (formal_external_inputs (generated_observation_input inputs k)) = Some (Gval (Fuint 1) [::false]) ->
 VM.find 7945 (top_environment next) = Some (Gval (Fuint 1) [::false]) ->
 VM.find 7776 (top_environment observed) = Some (Gval (Fuint 1) [::false]) /\
 VM.find 7773 (top_environment observed) = Some (Gval (Fuint 1) [::false]) /\
 VM.find 7771 (top_environment observed) = Some (Gval (Fuint 1) [::false]).
Proof.
 intros Observe Legal Next Reset Clear.
 destruct (alu_output_observed_transfer_context memory inputs k observed next Observe Legal Next Reset)
 as [history [Last [Boundary [Steps [Resets ALU]]]]].
 assert (Member : List.In (7748%nat,32%nat) joint_boundary_registers).
 { apply (List.nth_error_In joint_boundary_registers 53%nat);vm_compute;reflexivity. }
 destruct (joint_update_register_history_concrete _ history 9259 7748 32 Member (Boundary _ _ Member) Steps 9259 (le_n _)) as [instruction [Size Front]].
 destruct (pipeline_bubble_value_history _ _ history instruction Boundary Steps Front Size) as [start [branch [exception [Branch Source]]]].
 destruct (bubble7945_observe_type memory inputs k observed Observe) as [old [Old Typed]].
 assert (Root : VM.find 65 (history 9259%nat) = Some (Gval (Fuint 1) [::false])).
 { apply (reset_connection_65_transfer (formal_invalid_policy (generated_observation_input inputs k) nil) (history 9258%nat) (history 9258%nat) (history 9259%nat) false).
   - apply (reset_connection_24_transfer (formal_invalid_policy (generated_observation_input inputs k) nil) (history 9257%nat) (history 9257%nat) (history 9258%nat) false);[apply Resets|apply Steps];vm_compute;lia.
   - apply Steps;vm_compute;lia. }
 pose proof Next as Commit. rewrite (observation_then_commit memory inputs k observed Observe) in Commit.
 destruct (flat_iteration_projection _ observed true next Commit) as [before [after [Before [Step After]]]].
 assert (Top : top_environment observed = before) by (unfold top_environment;rewrite Before;reflexivity).
 rewrite <- Top in Step;rewrite <- Last in Step.
 pose proof (pipeline_bubble_7945_normal_commit (formal_invalid_policy (generated_observation_input inputs k) nil) (history 9259%nat) (history 9259%nat) after old (((start || pipeline_kill_decode (to_N instruction) 49) || branch) || exception) ltac:(rewrite Last;exact Old) Typed Root Source Step) as Bubble.
 unfold top_environment in Clear;rewrite After in Clear. rewrite Clear in Bubble.
 pose proof (f_equal (fun value => match value with Some (Gval _ (bit::_)) => bit | _ => false end) Bubble) as Decision.
 change (false = (((start || pipeline_kill_decode (to_N instruction) 49) || branch) || exception)) in Decision.
 assert (NoKill : pipeline_kill_decode (to_N instruction) 49 = false /\ branch = false).
 { exact (pipeline_or_clear start (pipeline_kill_decode (to_N instruction) 49) branch exception Decision). }
 destruct NoKill as [NoKill NoBranch];subst branch.
 assert (Selectors : forall time, (56 <= time)%coq_nat -> (time <= 9259)%coq_nat -> VM.find 84 (history time) = Some (Gval (Fuint 2) [::false;false])).
 { intros time Lower Upper. destruct (dut_decode_history _ _ history 9259 instruction Steps Front Size time Lower Upper) as [Selector Kind].
   rewrite (pipeline_no_kill_selector (to_N instruction) 49 ltac:(lia) NoKill) in Selector;exact Selector. }
 assert (Jump : VM.find 7772 (history 9258%nat) = Some (Gval (Fuint 1) [::false])).
 { eapply (pc_control_node_7772 _ (history 9257%nat) (history 9257%nat));[|reflexivity|apply Steps;vm_compute;lia].
   cbn [pc_control_expr_7772 eval_hfexpr_with_memory eval_href_with_memory];rewrite (Selectors 9257 ltac:(vm_compute;lia) ltac:(vm_compute;lia));reflexivity. }
 assert (Branch8 : VM.find 1360 (history 9258%nat) = Some (Gval (Fuint 1) [::false])).
 { rewrite (early_control_stable_1360_history _ _ history 9259 Boundary Steps 9258 9259 ltac:(vm_compute;lia) ltac:(vm_compute;lia) ltac:(vm_compute;lia) ltac:(vm_compute;lia));exact Branch. }
 rewrite <- Last. repeat split.
 - eapply (pc_control_node_7776 _ (history 9258%nat) (history 9258%nat));[|reflexivity|apply Steps;vm_compute;lia].
   cbn [pc_control_expr_7776 eval_hfexpr_with_memory eval_href_with_memory];rewrite (Selectors 9258 ltac:(vm_compute;lia) ltac:(vm_compute;lia));reflexivity.
 - eapply (pc_control_node_7773 _ (history 9258%nat) (history 9258%nat));[|reflexivity|apply Steps;vm_compute;lia].
   cbn [pc_control_expr_7773 eval_hfexpr_with_memory eval_href_with_memory];rewrite Jump Branch8;reflexivity.
 - eapply (pc_control_node_7771 _ (history 9258%nat) (history 9258%nat));[|reflexivity|apply Steps;vm_compute;lia].
   cbn [pc_control_expr_7771 eval_hfexpr_with_memory eval_href_with_memory];rewrite (Selectors 9258 ltac:(vm_compute;lia) ltac:(vm_compute;lia));reflexivity.
Qed.
Require Import PipelinePCSequentialAdjacency PipelinePCAdjacentTransfer ObservedJointRegisterConcrete PipelineBubbleResetBase BooleanRegisterResetCycle PipelineBubbleInitialization PipelineBubbleResetCommit JointBoundaryInduction ExternalReset.
Theorem pipeline_front_fetch_adjacent_normal memory inputs k observed next :
 generated_observe memory inputs k = Some observed -> generated_legal_trace memory inputs k ->
 generated_run memory inputs (S k) = Some next ->
 VM.find 1 (formal_external_inputs (generated_observation_input inputs k)) = Some (Gval (Fuint 1) [::false]) ->
 VM.find 7945 (top_environment next) = Some (Gval (Fuint 1) [::false]) ->
 pipeline_front_fetch_adjacent (top_environment next).
Proof.
 intros Observe Legal Next Reset Early.
 destruct (pipeline_early_clear_sequential_controls memory inputs k observed next Observe Legal Next Reset Early) as [S2 [S3 S4]].
 destruct (observed_joint_register_concrete memory inputs k observed 7768 33 Observe Legal
 ltac:(apply (List.nth_error_In joint_boundary_registers 67%nat);vm_compute;reflexivity)) as [fetch [Size Fetch]].
 exact (pipeline_pc_sequential_front_fetch_adjacent memory inputs k observed next fetch Observe Legal Next Reset S2 S3 S4 Size Fetch).
Qed.
Theorem pipeline_front_fetch_adjacent_reachable memory inputs k states :
 generated_run memory inputs k = Some states -> generated_legal_trace memory inputs k ->
 VM.find 7945 (top_environment states) = Some (Gval (Fuint 1) [::false]) ->
 pipeline_front_fetch_adjacent (top_environment states).
Proof.
 destruct k as [|k];intros Run Legal Early.
 - destruct (pipeline_bubbles_run_zero memory inputs states Run) as [env [Env [Bubble Late]]].
   unfold top_environment in Early;rewrite Env Bubble in Early;discriminate.
 - assert (PriorLegal : generated_legal_trace memory inputs k).
   { apply (joint_legal_trace_prefix memory inputs (S k) k Legal);lia. }
   destruct (legal_observation_reset memory inputs k PriorLegal) as [reset Reset]. destruct reset.
   + pose proof Run as Next;rewrite generated_run_successor in Next.
     destruct (generated_run memory inputs k) as [previous|] eqn:Previous;[|discriminate Next].
     destruct (bubble7945_run_type memory inputs k previous Previous) as [old [value [Old [Value Typed]]]].
     destruct (boolean_register_reset_cycle 7945 bubble7945_present (Logic.eq_refl true) (Logic.eq_refl true) bubble7945_initial_safe pipeline_bubble_7945_reset_commit (generated_observation_input inputs k) previous old states value Old Value Typed Reset Next) as [env [Env Bubble]].
     unfold top_environment in Early;rewrite Env Bubble in Early;discriminate.
   + destruct (generated_successful_commit memory inputs k states Run) as [observed [Observe Commit]].
     exact (pipeline_front_fetch_adjacent_normal memory inputs k observed states Observe PriorLegal Run Reset Early).
Qed.
Require Import ObservedPipelinePCAdjacency StagedObservedRegister StagedCircuitRegisterHold.
Theorem pipeline_front_fetch_adjacent_observed memory inputs k observed :
 generated_observe memory inputs k = Some observed -> generated_legal_trace memory inputs k ->
 VM.find 7945 (top_environment observed) = Some (Gval (Fuint 1) [::false]) ->
 pipeline_front_fetch_adjacent (top_environment observed).
Proof.
 intros Observe Legal Early. pose proof Observe as Expanded;unfold generated_observe in Expanded.
 destruct (generated_run memory inputs k) as [previous|] eqn:Run;[|discriminate Expanded].
 destruct (bubble7945_run_type memory inputs k previous Run) as [old [value [Old [Value Typed]]]].
 pose proof (staged_observed_register_copies memory inputs k previous old observed 7945 (Logic.eq_refl true) (Logic.eq_refl true) bubble7945_initial_safe bubble7945_present Run Old Observe) as Copy.
 assert (PriorEarly : VM.find 7945 (top_environment previous) = Some (Gval (Fuint 1) [::false])).
 { unfold top_environment;rewrite Old. unfold staged_register_lookup in Copy.
   unfold top_environment in Early. destruct (SVM.find nil observed);[rewrite Early in Copy;symmetry;exact Copy|discriminate Early]. }
 pose proof (pipeline_front_fetch_adjacent_reachable memory inputs k previous Run Legal PriorEarly) as Adjacent.
 unfold top_environment in Adjacent;rewrite Old in Adjacent.
 exact (proj1 (observed_pipeline_pc_adjacency memory inputs k previous old observed Run Old Observe) Adjacent).
Qed.
Require Import EarlyBubbleBitReachable ObservedLateBubbleTransfer Bubble7947Type.
Theorem pipeline_commit_front_adjacent_normal memory inputs k observed next :
 generated_observe memory inputs k = Some observed -> generated_legal_trace memory inputs k ->
 generated_run memory inputs (S k) = Some next ->
 VM.find 1 (formal_external_inputs (generated_observation_input inputs k)) = Some (Gval (Fuint 1) [::false]) ->
 VM.find 7947 (top_environment next) = Some (Gval (Fuint 1) [::false]) ->
 pipeline_commit_front_adjacent (top_environment next).
Proof.
 intros Observe Legal Next Reset Late.
 destruct (early_bubble_known_observation memory inputs k observed Observe Legal) as [early Early].
 destruct (bubble7947_observe_type memory inputs k observed Observe) as [old [Old Typed]].
 pose proof (observed_late_bubble_normal_step memory inputs k observed next early old Observe Legal Next Reset Early Old Typed) as NewLate.
 rewrite Late in NewLate;destruct early;[discriminate NewLate|].
 apply (pipeline_pc_adjacent_transfer memory inputs k observed next Observe Legal Next Reset).
 exact (pipeline_front_fetch_adjacent_observed memory inputs k observed Observe Legal Early).
Qed.
Theorem pipeline_commit_front_adjacent_reachable memory inputs k states :
 generated_run memory inputs k = Some states -> generated_legal_trace memory inputs k ->
 VM.find 7947 (top_environment states) = Some (Gval (Fuint 1) [::false]) ->
 pipeline_commit_front_adjacent (top_environment states).
Proof.
 destruct k as [|k];intros Run Legal Late.
 - destruct (pipeline_bubbles_run_zero memory inputs states Run) as [env [Env [Early Bubble]]].
   unfold top_environment in Late;rewrite Env Bubble in Late;discriminate.
 - assert (PriorLegal : generated_legal_trace memory inputs k).
   { apply (joint_legal_trace_prefix memory inputs (S k) k Legal);lia. }
   destruct (legal_observation_reset memory inputs k PriorLegal) as [reset Reset]. destruct reset.
   + pose proof Run as Next;rewrite generated_run_successor in Next.
     destruct (generated_run memory inputs k) as [previous|] eqn:Previous;[|discriminate Next].
     destruct (bubble7947_run_type memory inputs k previous Previous) as [old [value [Old [Value Typed]]]].
     destruct (boolean_register_reset_cycle 7947 bubble7947_present (Logic.eq_refl true) (Logic.eq_refl true) bubble7947_initial_safe pipeline_bubble_7947_reset_commit (generated_observation_input inputs k) previous old states value Old Value Typed Reset Next) as [env [Env Bubble]].
     unfold top_environment in Late;rewrite Env Bubble in Late;discriminate.
   + destruct (generated_successful_commit memory inputs k states Run) as [observed [Observe Commit]].
     exact (pipeline_commit_front_adjacent_normal memory inputs k observed states Observe PriorLegal Run Reset Late).
Qed.
Theorem pipeline_commit_front_adjacent_observed memory inputs k observed :
 generated_observe memory inputs k = Some observed -> generated_legal_trace memory inputs k ->
 VM.find 7947 (top_environment observed) = Some (Gval (Fuint 1) [::false]) ->
 pipeline_commit_front_adjacent (top_environment observed).
Proof.
 intros Observe Legal Late. pose proof Observe as Expanded;unfold generated_observe in Expanded.
 destruct (generated_run memory inputs k) as [previous|] eqn:Run;[|discriminate Expanded].
 destruct (bubble7947_run_type memory inputs k previous Run) as [old [value [Old [Value Typed]]]].
 pose proof (staged_observed_register_copies memory inputs k previous old observed 7947 (Logic.eq_refl true) (Logic.eq_refl true) bubble7947_initial_safe bubble7947_present Run Old Observe) as Copy.
 assert (PriorLate : VM.find 7947 (top_environment previous) = Some (Gval (Fuint 1) [::false])).
 { unfold top_environment;rewrite Old. unfold staged_register_lookup in Copy.
   unfold top_environment in Late. destruct (SVM.find nil observed);[rewrite Late in Copy;symmetry;exact Copy|discriminate Late]. }
 pose proof (pipeline_commit_front_adjacent_reachable memory inputs k previous Run Legal PriorLate) as Adjacent.
 unfold top_environment in Adjacent;rewrite Old in Adjacent.
 exact (proj2 (observed_pipeline_pc_adjacency memory inputs k previous old observed Run Old Observe) Adjacent).
Qed.
Require Import PipelinePCActiveSequential PipelinePCRelation ReferencePCSequentialObserved.
Theorem pipeline_pc_active_sequential_reachable memory inputs k observed next :
 generated_observe memory inputs k = Some observed -> generated_legal_trace memory inputs k ->
 generated_run memory inputs (S k) = Some next ->
 VM.find 1 (formal_external_inputs (generated_observation_input inputs k)) = Some (Gval (Fuint 1) [::false]) ->
 reference_pc_sequential_control_window (formal_invalid_policy (generated_observation_input inputs k) nil) (top_environment observed) ->
 pipeline_pc_relation (top_environment observed) ->
 VM.find 7947 (top_environment observed) = Some (Gval (Fuint 1) [::false]) ->
 VM.find 7945 (top_environment observed) = Some (Gval (Fuint 1) [::false]) ->
 pipeline_pc_relation (top_environment next).
Proof.
 intros Observe Legal Next Reset Window Relation Late Early.
 exact (pipeline_pc_active_sequential_window memory inputs k observed next Observe Legal Next Reset Window Relation
 (pipeline_commit_front_adjacent_observed memory inputs k observed Observe Legal Late) Late Early).
Qed.
