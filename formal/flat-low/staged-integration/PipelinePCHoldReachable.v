Require Import LegalInstructionClass DUTRedirectDecode.
From Coq Require Import NArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
Local Open Scope N_scope.
Lemma pipeline_legal_opcode_not_system instruction :
 legal_instruction_classified instruction -> N.land (to_N instruction) 127 <> 115.
Proof.
 intros [mask [code [Member Match]]].
 assert (Rows : forall pair, List.In pair legal_instruction_classes -> N.land (fst pair) 127 = 127 /\ N.land (snd pair) 127 <> 115).
 { intros [m c] MemberRow. unfold legal_instruction_classes in MemberRow.
   repeat destruct MemberRow as [Eq|MemberRow];try contradiction;inversion Eq;subst;vm_compute;split;congruence. }
 destruct (Rows (mask,code) Member) as [Mask Code]. cbn [fst snd] in Mask,Code.
 rewrite <- Match in Code. rewrite <- N.land_assoc, Mask in Code. exact Code.
Qed.
Lemma pipeline_epc_row_system n : (n < 49)%coq_nat ->
 dd_selector (dut_decode_row n) = 3 ->
 N.land (dd_mask (dut_decode_row n)) 127 = 127 /\
 N.land (dd_code (dut_decode_row n)) 127 = 115.
Proof. intro Bound;do 49 (destruct n as [|n];[vm_compute;intro H;first[discriminate H|split;reflexivity]|]);lia. Qed.
Lemma pipeline_legal_no_epc_row instruction n : legal_instruction_classified instruction -> (n < 49)%coq_nat ->
 dut_decode_test (to_N instruction) n = true ->
 to_N (from_N 2 (dd_selector (dut_decode_row n))) <> 3.
Proof.
 intros Legal Bound Guard.
 assert (Small : dd_selector (dut_decode_row n) < 4).
 { revert Bound;do 49 (destruct n as [|n];[vm_compute;reflexivity|]);lia. }
 rewrite to_N_from_N. change (2 ^ N.of_nat 2) with 4. rewrite (N.mod_small _ _ Small).
 intro EPC. destruct (pipeline_epc_row_system n Bound EPC) as [Mask Code].
 unfold dut_decode_test in Guard;apply N.eqb_eq in Guard.
 apply (pipeline_legal_opcode_not_system instruction Legal).
 rewrite <- Guard in Code. rewrite <- N.land_assoc, Mask in Code;exact Code.
Qed.
Theorem pipeline_legal_no_epc instruction count : legal_instruction_classified instruction -> (count <= 49)%coq_nat ->
 to_N (dut_decode_mux_value false (to_N instruction) count) <> 3.
Proof.
 intros Legal;induction count as [|count IH];intro Bound;[discriminate|].
 cbn [dut_decode_mux_value]. destruct (dut_decode_test (to_N instruction) (Nat.sub 48 count)) eqn:Guard.
 - apply (pipeline_legal_no_epc_row instruction (Nat.sub 48 count));[exact Legal|lia|exact Guard].
 - apply IH;lia.
Qed.
Require Import CoreSocModel ComparisonNodes PipelinePCSuccessor FetchPCSequentialExact FormalPCChoiceNodes FormalSuccessfulNodeEvaluation FormalLocalHistory FormalTypedNodeEquation ScalarNodeFrames.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Theorem pipeline_pc_hold_source invalid s0 s1 s2 s3 s4 s5 pc :
 size pc = 33%nat ->
 VM.find 7768 s0 = Some (Gval (Fuint 33) pc) ->
 VM.find 7776 s0 = Some (Gval (Fuint 1) [::true]) ->
 VM.find 7773 s1 = Some (Gval (Fuint 1) [::false]) ->
 VM.find 7771 s2 = Some (Gval (Fuint 1) [::false]) ->
 VM.find 128 s3 = Some (Gval (Fuint 1) [::false]) ->
 VM.find 7765 s4 = Some (Gval (Fuint 1) [::false]) ->
 formal_flat_local_step invalid s0 s1 -> formal_flat_local_step invalid s1 s2 ->
 formal_flat_local_step invalid s2 s3 -> formal_flat_local_step invalid s3 s4 ->
 formal_flat_local_step invalid s4 s5 ->
 exists value, VM.find 7781 s5 = Some value /\ fetch_pc_extension pc value.
Proof.
 intros Size PC Hold Taken Eret Trap Stall S1 S2 S3 S4 S5.
 destruct (formal_successful_node_evaluation 8283 flat_statements pc_choice_7777_tail 7777 pc_choice_7777_expr invalid flat_memories s0 false s0 s1 pc_choice_7777_position S1) as [value Eval].
 change (eval_hfexpr_with_memory flat_memories pc_choice_7777_expr s0 s0 = Some value) in Eval.
 pose proof (pipeline_pc_true_mux_extension flat_memories s0 7776 7768 7770 pc (Gval (Fuint 33) pc) value Size (fetch_pc_base_extension pc Size) Hold PC Eval) as Ext.
 assert (V1 : VM.find 7777 s1 = Some value).
 { destruct Ext as [width [Width Shape]]. subst value. eapply formal_combinational_known_node;
   [exact pc_choice_7777_position|exact pc_choice_7777_suffix|exact pc_choice_7777_nonregister|exact Eval|reflexivity|exact S1]. }
 destruct (fetch_pc_sequential_7778 invalid s1 s1 s2 pc value Size Ext Taken V1 S2) as [v2 [V2 E2]].
 destruct (fetch_pc_sequential_7779 invalid s2 s2 s3 pc v2 Size E2 Eret V2 S3) as [v3 [V3 E3]].
 destruct (fetch_pc_sequential_7780 invalid s3 s3 s4 pc v3 Size E3 Trap V3 S4) as [v4 [V4 E4]].
 exact (fetch_pc_sequential_7781 invalid s4 s4 s5 pc v4 Size E4 Stall V4 S5).
Qed.

Require Import FetchPCSelectorStability ExceptionSourceNoTrap FormalStallHistory FormalCheckerResetConnections JointBoundaryRegisters ConcreteRegisterInitialization.
Theorem pipeline_pc_hold_source_history inputs path history pc :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < 9259)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 (forall i, (i <= 9259)%coq_nat -> VM.find 1 (history i) = Some (Gval (Fuint 1) [::false])) ->
 size pc = 33%nat ->
 VM.find 7768 (history 9254%nat) = Some (Gval (Fuint 33) pc) ->
 VM.find 7776 (history 9259%nat) = Some (Gval (Fuint 1) [::true]) ->
 VM.find 7773 (history 9259%nat) = Some (Gval (Fuint 1) [::false]) ->
 VM.find 7771 (history 9259%nat) = Some (Gval (Fuint 1) [::false]) ->
 VM.find 45 (history 9254%nat) = Some (Gval (Fuint 1) [::false]) ->
 VM.find 65 (history 9259%nat) = Some (Gval (Fuint 1) [::false]) /\
 exists value, VM.find 7781 (history 9259%nat) = Some value /\ fetch_pc_extension pc value.
Proof.
 intros Boundary Steps Resets Size PC Sel2 Sel3 Sel4 NoTrap.
 assert (C3 : VM.find 7773 (history 9255%nat) = Some (Gval (Fuint 1) [::false])).
 { rewrite (fetch_pc_selector_7773_same inputs path history 9259 Boundary Steps 9255 9259 ltac:(vm_compute;lia) ltac:(vm_compute;lia) ltac:(vm_compute;lia) ltac:(vm_compute;lia)). exact Sel3. }
 assert (C4 : VM.find 7771 (history 9256%nat) = Some (Gval (Fuint 1) [::false])).
 { rewrite (fetch_pc_selector_7771_same inputs path history 9259 Boundary Steps 9256 9259 ltac:(vm_compute;lia) ltac:(vm_compute;lia) ltac:(vm_compute;lia) ltac:(vm_compute;lia)). exact Sel4. }
 pose proof (exception_source_false_after_settling inputs path history Boundary Steps NoTrap 9257 ltac:(vm_compute;lia) ltac:(vm_compute;lia)) as C5.
 assert (C6 : VM.find 7765 (history 9258%nat) = Some (Gval (Fuint 1) [::false])).
 { apply (stall_after_six (formal_invalid_policy inputs path) (history 9252%nat) (history 9253%nat) (history 9254%nat) (history 9255%nat) (history 9256%nat) (history 9257%nat) (history 9258%nat) false);
 [apply Resets|apply Steps|apply Steps|apply Steps|apply Steps|apply Steps|apply Steps]; vm_compute;lia. }
 assert (Reset : VM.find 65 (history 9259%nat) = Some (Gval (Fuint 1) [::false])).
 { apply (reset_connection_65_transfer (formal_invalid_policy inputs path) (history 9258%nat) (history 9258%nat) (history 9259%nat) false).
 - apply (reset_connection_24_transfer (formal_invalid_policy inputs path) (history 9257%nat) (history 9257%nat) (history 9258%nat) false);
 [apply Resets|apply Steps]; vm_compute;lia.
 - apply Steps. vm_compute;lia. }
 split; [exact Reset|].
 assert (C2 : VM.find 7776 (history 9254%nat) = Some (Gval (Fuint 1) [::true])).
 { rewrite (fetch_pc_selector_7776_same inputs path history 9259 Boundary Steps 9254 9259 ltac:(vm_compute;lia) ltac:(vm_compute;lia) ltac:(vm_compute;lia) ltac:(vm_compute;lia));exact Sel2. }
 apply (pipeline_pc_hold_source (formal_invalid_policy inputs path) (history 9254%nat) (history 9255%nat) (history 9256%nat) (history 9257%nat) (history 9258%nat) (history 9259%nat) pc Size PC C2 C3 C4 C5 C6);apply Steps;vm_compute;lia.
Qed.

Require Import ALUOutputTransfer FormalObservationCommit StagedFlatCircuitIteration ObservedJointRegisterConcrete FormalLegalObservation LegalNoTrapWindow JointUpdateBoundaryHistory.
Theorem pipeline_pc_hold_observed memory inputs k observed next pc :
 generated_observe memory inputs k = Some observed -> generated_legal_trace memory inputs k ->
 generated_run memory inputs (S k) = Some next ->
 VM.find 1 (formal_external_inputs (generated_observation_input inputs k)) = Some (Gval (Fuint 1) [::false]) ->
 size pc = 33%nat -> VM.find 7768 (top_environment observed) = Some (Gval (Fuint 33) pc) ->
 VM.find 7776 (top_environment observed) = Some (Gval (Fuint 1) [::true]) ->
 VM.find 7773 (top_environment observed) = Some (Gval (Fuint 1) [::false]) ->
 VM.find 7771 (top_environment observed) = Some (Gval (Fuint 1) [::false]) ->
 VM.find 7768 (top_environment next) = Some (Gval (Fuint 33) pc).
Proof.
 intros Observe Legal Next Reset Size PC Hold Taken Eret.
 destruct (alu_output_observed_transfer_context memory inputs k observed next Observe Legal Next Reset)
 as [history [Last [Boundary [Steps [Resets ALU]]]]].
 assert (LocalAssume : generated_assume_m0_0_local (history 9259%nat)).
 { rewrite Last. destruct (legal_observation_assumptions memory inputs k observed Legal Observe) as [_ Assume].
   apply (proj1 (flat_assumption_at_top observed)) in Assume.
   unfold top_environment; destruct (SVM.find nil observed);[exact Assume|contradiction]. }
 assert (NoTrap : VM.find 45 (history 9254%nat) = Some (Gval (Fuint 1) [::false])).
 { apply (legal_no_trap_history_window _ history 9259 9254 Steps); try (vm_compute;lia).
   - apply Resets;vm_compute;lia.
   - exact LocalAssume. }

 assert (PC4 : VM.find 7768 (history 9254%nat) = Some (Gval (Fuint 33) pc)).
 { rewrite (joint_update_register_history_same _ history 9259 7768 33 ltac:(apply (List.nth_error_In joint_boundary_registers 67%nat);vm_compute;reflexivity) Steps 9254 ltac:(vm_compute;lia)).
   rewrite <- (joint_update_register_history_same _ history 9259 7768 33 ltac:(apply (List.nth_error_In joint_boundary_registers 67%nat);vm_compute;reflexivity) Steps 9259 (le_n _)). rewrite Last;exact PC. }
 destruct (pipeline_pc_hold_source_history (generated_observation_input inputs k) nil history pc Boundary Steps Resets Size PC4
 ltac:(rewrite Last;exact Hold) ltac:(rewrite Last;exact Taken) ltac:(rewrite Last;exact Eret) NoTrap) as [Root [value [Value Ext]]].
 rewrite (observation_then_commit memory inputs k observed Observe) in Next.
 destruct (flat_iteration_projection _ observed true next Next) as [before [after [Before [Step After]]]].
 assert (Top : top_environment observed = before) by (unfold top_environment;rewrite Before;reflexivity).
 rewrite <- Top in Step;rewrite <- Last in Step.
 unfold top_environment;rewrite After.
 apply (fetch_pc_sequential_commit (formal_invalid_policy (generated_observation_input inputs k) nil) (history 9259%nat) (history 9259%nat) after pc pc value Size Ext).
 - rewrite Last;exact PC.
 - exact Root.
 - exact Value.
 - exact Step.
Qed.
Require Import PipelineRedirectPhase.
Lemma pipeline_kill_selector_row n : (n < 49)%coq_nat -> nth false pipeline_kill_rows n = true ->
 from_N 2 (dd_selector (dut_decode_row n)) = [::true;false] \/
 from_N 2 (dd_selector (dut_decode_row n)) = [::false;true] \/
 from_N 2 (dd_selector (dut_decode_row n)) = [::true;true].
Proof. intro Bound;do 49 (destruct n as [|n];[vm_compute;intro H;first[discriminate H|auto]|]);lia. Qed.
Lemma pipeline_kill_selector_cases instruction count : (count <= 49)%coq_nat -> pipeline_kill_decode instruction count = true ->
 dut_decode_mux_value false instruction count = [::true;false] \/
 dut_decode_mux_value false instruction count = [::false;true] \/
 dut_decode_mux_value false instruction count = [::true;true].
Proof.
 induction count as [|count IH];intros Bound Kill;[discriminate|].
 rewrite pipeline_kill_decode_S in Kill. cbn [dut_decode_mux_value].
 destruct (dut_decode_test instruction (Nat.sub 48 count)) eqn:Guard.
 - apply pipeline_kill_selector_row;[lia|exact Kill].
 - apply IH;[lia|exact Kill].
Qed.
Lemma pipeline_kill_no_redirect_selector instruction :
 legal_instruction_classified instruction -> pipeline_kill_decode (to_N instruction) 49 = true ->
 N.eqb (to_N (dut_decode_mux_value false (to_N instruction) 49)) 1 = false ->
 dut_decode_mux_value false (to_N instruction) 49 = [::false;true].
Proof.
 intros Legal Kill NoJump.
 pose proof (pipeline_legal_no_epc instruction 49 Legal ltac:(lia)) as NoEPC.
 destruct (pipeline_kill_selector_cases (to_N instruction) 49 ltac:(lia) Kill) as [Jump|[Hold|EPC]].
 - rewrite Jump in NoJump;discriminate.
 - exact Hold.
 - rewrite EPC in NoEPC;exfalso;apply NoEPC;reflexivity.
Qed.
Require Import EarlyControlWireBitNormalization EarlyBubbleNopControlKnown EarlyControlStabilityHistory EarlyBubbleValues StartupFlagInitialization PipelineBubbleNormalCommit FormalPCControlNodes ReferenceRedirectSpine.
Theorem pipeline_hold_controls_history inputs path history result instruction old :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < 9259)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 VM.find 7748 (history 9259%nat) = Some (Gval (Fuint 32) instruction) -> size instruction = 32%nat ->
 legal_instruction_classified instruction ->
 VM.find 7762 (history 9259%nat) = Some (Gval (Fuint 1) [::false]) ->
 VM.find 7773 (history 9259%nat) = Some (Gval (Fuint 1) [::false]) ->
 VM.find 45 (history 9254%nat) = Some (Gval (Fuint 1) [::false]) ->
 VM.find 65 (history 9259%nat) = Some (Gval (Fuint 1) [::false]) ->
 VM.find 7945 (history 9259%nat) = Some old -> type_of_val old = Gtyp (Fuint 1) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories (history 9259%nat) true (history 9259%nat) flat_statements = Some result ->
 VM.find 7945 result = Some (Gval (Fuint 1) [::true]) ->
 VM.find 7776 (history 9259%nat) = Some (Gval (Fuint 1) [::true]) /\
 VM.find 7771 (history 9259%nat) = Some (Gval (Fuint 1) [::false]).
Proof.
 intros Boundary Steps Front Size Legal Started NoTaken NoTrap Reset Old Typed Commit Early.
 destruct (early_control_wire_1360_normalized _ (history 9257%nat) (history 9257%nat) (history 9258%nat) (Steps 9257%nat ltac:(vm_compute;lia))) as [bv [BV BN]].
 destruct (early_bubble_normalized_concrete _ 1360 bv BV BN (early_control_concrete_1360_history inputs path history 9259 Boundary Steps 9258 ltac:(vm_compute;lia) ltac:(vm_compute;lia))) as [branch Branch].
 destruct (dut_decode_history inputs path history 9259 instruction Steps Front Size 9257 ltac:(vm_compute;lia) ltac:(vm_compute;lia)) as [Selector Kind].
 assert (Jump : VM.find 7772 (history 9258%nat) = Some (Gval (Fuint 1) [::N.eqb (to_N (dut_decode_mux_value false (to_N instruction) 49)) 1])).
 { eapply (pc_control_node_7772 _ (history 9257%nat) (history 9257%nat));[|reflexivity|apply Steps;vm_compute;lia].
   cbn [pc_control_expr_7772 eval_hfexpr_with_memory eval_href_with_memory];rewrite Selector.
   change (Some (Gval (Fuint 1) [::(to_N (dut_decode_mux_value false (to_N instruction) 49) == 1)]) = Some (Gval (Fuint 1) [::N.eqb (to_N (dut_decode_mux_value false (to_N instruction) 49)) 1])).
   rewrite redirect_N_eqb;reflexivity. }
 assert (Raw : VM.find 7773 (history 9259%nat) = Some (Gval (Fuint 1) [::N.eqb (to_N (dut_decode_mux_value false (to_N instruction) 49)) 1 || branch])).
 { eapply (pc_control_node_7773 _ (history 9258%nat) (history 9258%nat));[|reflexivity|apply Steps;vm_compute;lia].
   cbn [pc_control_expr_7773 eval_hfexpr_with_memory eval_href_with_memory];rewrite Jump Branch.
   destruct (N.eqb (to_N (dut_decode_mux_value false (to_N instruction) 49)) 1),branch;reflexivity. }
 rewrite NoTaken in Raw.
 pose proof (f_equal (fun value => match value with Some (Gval _ (bit::_)) => bit | _ => false end) Raw) as Decision.
 change (false = (N.eqb (to_N (dut_decode_mux_value false (to_N instruction) 49)) 1 || branch)) in Decision.
 symmetry in Decision;apply Bool.orb_false_iff in Decision;destruct Decision as [NoJump NoBranch];subst branch.
 assert (Started6 : VM.find 7762 (history 9256%nat) = Some (Gval (Fuint 1) [::false])).
 { rewrite (joint_update_register_history_same _ history 9259 7762 1 startup_register_member Steps 9256 ltac:(vm_compute;lia)).
   rewrite <- (joint_update_register_history_same _ history 9259 7762 1 startup_register_member Steps 9259 (le_n _));exact Started. }
 pose proof (pipeline_kill_history inputs path history 9259 instruction Steps Front Size 9256 ltac:(vm_compute;lia) ltac:(vm_compute;lia)) as Kill.
 assert (Branch7 : VM.find 1360 (history 9257%nat) = Some (Gval (Fuint 1) [::false])).
 { rewrite (early_control_stable_1360_history inputs path history 9259 Boundary Steps 9257 9258 ltac:(vm_compute;lia) ltac:(vm_compute;lia) ltac:(vm_compute;lia) ltac:(vm_compute;lia));exact Branch. }
 pose proof (exception_source_false_after_settling inputs path history Boundary Steps NoTrap 9258 ltac:(vm_compute;lia) ltac:(vm_compute;lia)) as Exception.
 pose proof (early_bubble_value_after_three (formal_invalid_policy inputs path) (history 9256%nat) (history 9257%nat) (history 9258%nat) (history 9259%nat) false (pipeline_kill_decode (to_N instruction) 49) false false Started6 Kill Branch7 Exception
 (Steps 9256%nat ltac:(vm_compute;lia)) (Steps 9257%nat ltac:(vm_compute;lia)) (Steps 9258%nat ltac:(vm_compute;lia))) as Source.
 rewrite !Bool.orb_false_r Bool.orb_false_l in Source.
 pose proof (pipeline_bubble_7945_normal_commit (formal_invalid_policy inputs path) (history 9259%nat) (history 9259%nat) result old (pipeline_kill_decode (to_N instruction) 49) Old Typed Reset Source Commit) as NewEarly.
 rewrite Early in NewEarly.
 pose proof (f_equal (fun value => match value with Some (Gval _ (bit::_)) => bit | _ => false end) NewEarly) as IsKill.
 change (true = pipeline_kill_decode (to_N instruction) 49) in IsKill.
 pose proof (pipeline_kill_no_redirect_selector instruction Legal (Logic.eq_sym IsKill) NoJump) as Hold.
 destruct (dut_decode_history inputs path history 9259 instruction Steps Front Size 9258 ltac:(vm_compute;lia) ltac:(vm_compute;lia)) as [Selector8 Kind8].
 rewrite Hold in Selector8. split.
 - eapply (pc_control_node_7776 _ (history 9258%nat) (history 9258%nat));[|reflexivity|apply Steps;vm_compute;lia].
   cbn [pc_control_expr_7776 eval_hfexpr_with_memory eval_href_with_memory];rewrite Selector8;reflexivity.
 - eapply (pc_control_node_7771 _ (history 9258%nat) (history 9258%nat));[|reflexivity|apply Steps;vm_compute;lia].
   cbn [pc_control_expr_7771 eval_hfexpr_with_memory eval_href_with_memory];rewrite Selector8;reflexivity.
Qed.

Require Import Bubble7945Type FormalCheckerResetConnections.
Theorem pipeline_pc_kill_hold_observed memory inputs k observed next instruction pc :
 generated_observe memory inputs k = Some observed -> generated_legal_trace memory inputs k ->
 generated_run memory inputs (S k) = Some next ->
 VM.find 1 (formal_external_inputs (generated_observation_input inputs k)) = Some (Gval (Fuint 1) [::false]) ->
 VM.find 7748 (top_environment observed) = Some (Gval (Fuint 32) instruction) -> size instruction = 32%nat ->
 legal_instruction_classified instruction ->
 VM.find 7762 (top_environment observed) = Some (Gval (Fuint 1) [::false]) ->
 VM.find 7773 (top_environment observed) = Some (Gval (Fuint 1) [::false]) ->
 VM.find 7945 (top_environment next) = Some (Gval (Fuint 1) [::true]) ->
 size pc = 33%nat -> VM.find 7768 (top_environment observed) = Some (Gval (Fuint 33) pc) ->
 VM.find 7768 (top_environment next) = Some (Gval (Fuint 33) pc).
Proof.
 intros Observe Legal Next Reset Front Size Classified Started NoTaken Early PCSize PC.
 destruct (alu_output_observed_transfer_context memory inputs k observed next Observe Legal Next Reset)
 as [history [Last [Boundary [Steps [Resets ALU]]]]].
 assert (LocalAssume : generated_assume_m0_0_local (history 9259%nat)).
 { rewrite Last. destruct (legal_observation_assumptions memory inputs k observed Legal Observe) as [_ Assume].
   apply (proj1 (flat_assumption_at_top observed)) in Assume.
   unfold top_environment; destruct (SVM.find nil observed);[exact Assume|contradiction]. }
 assert (NoTrap : VM.find 45 (history 9254%nat) = Some (Gval (Fuint 1) [::false])).
 { apply (legal_no_trap_history_window _ history 9259 9254 Steps); try (vm_compute;lia).
   - apply Resets;vm_compute;lia.
   - exact LocalAssume. }


 destruct (bubble7945_observe_type memory inputs k observed Observe) as [old [Old Typed]].
 assert (Root : VM.find 65 (history 9259%nat) = Some (Gval (Fuint 1) [::false])).
 { apply (reset_connection_65_transfer (formal_invalid_policy (generated_observation_input inputs k) nil) (history 9258%nat) (history 9258%nat) (history 9259%nat) false).
   - apply (reset_connection_24_transfer (formal_invalid_policy (generated_observation_input inputs k) nil) (history 9257%nat) (history 9257%nat) (history 9258%nat) false);[apply Resets|apply Steps];vm_compute;lia.
   - apply Steps;vm_compute;lia. }
 pose proof Next as Commit. rewrite (observation_then_commit memory inputs k observed Observe) in Commit.
 destruct (flat_iteration_projection _ observed true next Commit) as [before [after [Before [Step After]]]].
 assert (Top : top_environment observed = before) by (unfold top_environment;rewrite Before;reflexivity).
 rewrite <- Top in Step;rewrite <- Last in Step.
 assert (EarlyAfter : VM.find 7945 after = Some (Gval (Fuint 1) [::true])).
 { unfold top_environment in Early;rewrite After in Early;exact Early. }
 destruct (pipeline_hold_controls_history (generated_observation_input inputs k) nil history after instruction old Boundary Steps ltac:(rewrite Last;exact Front) Size Classified ltac:(rewrite Last;exact Started) ltac:(rewrite Last;exact NoTaken) NoTrap Root ltac:(rewrite Last;exact Old) Typed Step EarlyAfter) as [Hold Eret].
 rewrite Last in Hold,Eret.
 exact (pipeline_pc_hold_observed memory inputs k observed next pc Observe Legal Next Reset PCSize PC Hold NoTaken Eret).
Qed.

Require Import ComparisonNodes StagedCircuitRegisterHold CoreSocModel FormalLocalHistory FormalObservationCommit Bubble7945Type PipelineBubbleInitialization PipelineBubbleResetCommit PipelineBubbleResetBase BooleanRegisterResetCycle StartupFlagReachable JointBoundaryInduction ExternalReset ObservedPipelinePCRelation JointBoundaryRegisters StagedObservedRegister.
From Coq Require Import ZArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque generated_modules generated_top flat_statements flat_memories generated_run.
Theorem pipeline_early_reset_successor memory inputs k next :
 VM.find 1 (formal_external_inputs (generated_observation_input inputs k)) = Some (Gval (Fuint 1) [::true]) ->
 generated_run memory inputs (S k) = Some next ->
 VM.find 7945 (top_environment next) = Some (Gval (Fuint 1) [::true]).
Proof.
 intros Reset Next. rewrite generated_run_successor in Next.
 destruct (generated_run memory inputs k) as [previous|] eqn:Run; [|discriminate Next].
 destruct (bubble7945_run_type memory inputs k previous Run) as [old [late [Old [Late Typed]]]].
 destruct (boolean_register_reset_cycle 7945 bubble7945_present (Logic.eq_refl true) (Logic.eq_refl true)
 bubble7945_initial_safe pipeline_bubble_7945_reset_commit (generated_observation_input inputs k) previous old next late
 Old Late Typed Reset Next) as [env [Env Value]].
 unfold top_environment. rewrite Env. exact Value.
Qed.
Theorem pipeline_front_active_run_startup_false memory inputs k states :
 generated_run memory inputs k = Some states ->
 generated_legal_trace memory inputs k ->
 VM.find 7945 (top_environment states) = Some (Gval (Fuint 1) [::false]) ->
 VM.find 7762 (top_environment states) = Some (Gval (Fuint 1) [::false]).
Proof.
 destruct k as [|k]; intros Run Legal Active.
 - destruct (pipeline_bubbles_run_zero memory inputs states Run) as [env [Env [Early Late]]].
   unfold top_environment in Active. rewrite Env Early in Active. discriminate Active.
 - assert (PriorLegal : generated_legal_trace memory inputs k).
   { apply (joint_legal_trace_prefix memory inputs (S k) k Legal). lia. }
   destruct (legal_observation_reset memory inputs k PriorLegal) as [reset Reset].
   destruct reset.
   + pose proof (pipeline_early_reset_successor memory inputs k states Reset Run) as Late.
     rewrite Late in Active. discriminate Active.
   + destruct (startup_flag_normal_successor memory inputs k states PriorLegal Reset Run) as [env [Env Value]].
     unfold top_environment. rewrite Env. exact Value.
Qed.
Theorem pipeline_front_active_observed_startup_false memory inputs k observed :
 generated_observe memory inputs k = Some observed ->
 generated_legal_trace memory inputs k ->
 VM.find 7945 (top_environment observed) = Some (Gval (Fuint 1) [::false]) ->
 VM.find 7762 (top_environment observed) = Some (Gval (Fuint 1) [::false]).
Proof.
 intros Observe Legal Active. pose proof Observe as Expanded. unfold generated_observe in Expanded.
 destruct (generated_run memory inputs k) as [previous|] eqn:Run; [|discriminate Expanded].
 destruct (bubble7945_run_type memory inputs k previous Run) as [old [late [Old [Late Typed]]]].
 pose proof (staged_observed_register_copies memory inputs k previous old observed 7945
 (Logic.eq_refl true) (Logic.eq_refl true) bubble7945_initial_safe bubble7945_present Run Old Observe) as Copy.
 unfold staged_register_lookup in Copy.
 assert (ActiveOld : VM.find 7945 (top_environment previous) = Some (Gval (Fuint 1) [::false])).
 { unfold top_environment. rewrite Old. rewrite <- Copy.
   unfold top_environment in Active. destruct (SVM.find nil observed); [exact Active|discriminate Active]. }
 pose proof (pipeline_front_active_run_startup_false memory inputs k previous Run Legal ActiveOld) as Started.
 unfold top_environment in Started. rewrite Old in Started.
 rewrite (observed_joint_register_copy memory inputs k previous old observed 7762%nat 1%nat
 ltac:(apply (List.nth_error_In joint_boundary_registers 66%nat); vm_compute;reflexivity) Run Old Observe).
 exact Started.
Qed.
Require Import FormalPCControlConcrete.
Lemma pipeline_raw_redirect_known memory inputs k observed next :
 generated_observe memory inputs k = Some observed -> generated_legal_trace memory inputs k ->
 generated_run memory inputs (S k) = Some next ->
 VM.find 1 (formal_external_inputs (generated_observation_input inputs k)) = Some (Gval (Fuint 1) [::false]) ->
 exists bit, VM.find 7773 (top_environment observed) = Some (Gval (Fuint 1) [::bit]).
Proof.
 intros Observe Legal Next Reset.
 destruct (alu_output_observed_transfer_context memory inputs k observed next Observe Legal Next Reset)
 as [history [Last [Boundary [Steps [Resets ALU]]]]].
 destruct (fetch_pc_decode_same_history _ _ history 9259 Boundary Steps 9257 9257 ltac:(vm_compute;lia) ltac:(vm_compute;lia) ltac:(vm_compute;lia) ltac:(vm_compute;lia)) as [word [Selector Rest]].
 destruct (pc_control_concrete_7772 _ (history 9257%nat) (history 9257%nat) (history 9258%nat) 2 word Selector (Steps 9257%nat ltac:(vm_compute;lia))) as [jump Jump].
 destruct (early_control_wire_1360_normalized _ (history 9257%nat) (history 9257%nat) (history 9258%nat) (Steps 9257%nat ltac:(vm_compute;lia))) as [value [Value Normal]].
 destruct (early_bubble_normalized_concrete _ 1360 value Value Normal (early_control_concrete_1360_history _ _ history 9259 Boundary Steps 9258 ltac:(vm_compute;lia) ltac:(vm_compute;lia))) as [branch Branch].
 rewrite <- Last. exact (pc_control_concrete_7773 _ (history 9258%nat) (history 9258%nat) (history 9259%nat) jump branch Jump Branch (Steps 9258%nat ltac:(vm_compute;lia))).
Qed.
Require Import PipelinePCSequentialReachable PipelinePCActiveBubbleSequential PipelinePCAdjacentTransfer ReferenceIllegalObserved DelayedDUTRedirectSemantics DelayedRedirectObserved ObservedInstructionNormalTransfer ObservedFrontPCTransfer EarlyBubbleBitReachable ObservedLateBubbleTransfer Bubble7947Type StartupLateBubbleInvariant.
Theorem pipeline_commit_fetch_adjacent_observed memory inputs k observed :
 generated_observe memory inputs k = Some observed -> generated_legal_trace memory inputs k ->
 VM.find 1 (formal_external_inputs (generated_observation_input inputs k)) = Some (Gval (Fuint 1) [::false]) ->
 VM.find 7947 (top_environment observed) = Some (Gval (Fuint 1) [::false]) ->
 VM.find 7945 (top_environment observed) = Some (Gval (Fuint 1) [::true]) ->
 VM.find 7760 (top_environment observed) = Some (Gval (Fuint 1) [::false]) ->
 pipeline_commit_fetch_adjacent (top_environment observed).
Proof.
 intros Observe Legal Reset Late Early NoRedirect.
 pose proof Observe as Expanded;unfold generated_observe in Expanded.
 destruct (generated_run memory inputs k) as [states|] eqn:Run;[|discriminate Expanded].
 destruct (bubble7947_run_type memory inputs k states Run) as [old [value [Old [Value Typed]]]].
 pose proof (staged_observed_register_copies memory inputs k states old observed 7947 (Logic.eq_refl true) (Logic.eq_refl true) bubble7947_initial_safe bubble7947_present Run Old Observe) as CopyLate.
 pose proof (staged_observed_register_copies memory inputs k states old observed 7945 (Logic.eq_refl true) (Logic.eq_refl true) bubble7945_initial_safe bubble7945_present Run Old Observe) as CopyEarly.
 assert (LateState : VM.find 7947 (top_environment states) = Some (Gval (Fuint 1) [::false])).
 { unfold top_environment;rewrite Old. unfold staged_register_lookup in CopyLate.
   unfold top_environment in Late;destruct (SVM.find nil observed);[rewrite Late in CopyLate;symmetry;exact CopyLate|discriminate Late]. }
 assert (EarlyState : VM.find 7945 (top_environment states) = Some (Gval (Fuint 1) [::true])).
 { unfold top_environment;rewrite Old. unfold staged_register_lookup in CopyEarly.
   unfold top_environment in Early;destruct (SVM.find nil observed);[rewrite Early in CopyEarly;symmetry;exact CopyEarly|discriminate Early]. }
 assert (FlagState : VM.find 7760 (top_environment states) = Some (Gval (Fuint 1) [::false])).
 { pose proof (delayed_joint_observed_copy memory inputs k states observed 7760 1
   ltac:(apply (List.nth_error_In joint_boundary_registers 65%nat);vm_compute;reflexivity) Run Observe) as Copy.
   change (VM.find 7760 (top_environment observed) = VM.find 7760 (top_environment states)) in Copy.
   rewrite <- Copy;exact NoRedirect. }
 destruct k as [|k].
 - destruct (pipeline_bubbles_run_zero memory inputs states Run) as [env [Env [E L]]].
   unfold top_environment in LateState;rewrite Env L in LateState;discriminate.
 - assert (PriorLegal : generated_legal_trace memory inputs k).
   { apply (joint_legal_trace_prefix memory inputs (S k) k Legal);lia. }
   destruct (legal_observation_reset memory inputs k PriorLegal) as [reset PriorReset];destruct reset.
   + pose proof (late_bubble_reset_successor memory inputs k states PriorReset Run) as L.
     rewrite LateState in L;discriminate.
   + destruct (generated_successful_commit memory inputs k states Run) as [prior [PriorObserve Commit]].
     destruct (early_bubble_known_observation memory inputs k prior PriorObserve PriorLegal) as [early PriorEarly].
     destruct (bubble7947_observe_type memory inputs k prior PriorObserve) as [lateValue [PriorLate PriorLateType]].
     pose proof (observed_late_bubble_normal_step memory inputs k prior states early lateValue PriorObserve PriorLegal Run PriorReset PriorEarly PriorLate PriorLateType) as NewLate.
     rewrite LateState in NewLate;destruct early;[discriminate|].
     pose proof (pipeline_front_active_observed_startup_false memory inputs k prior PriorObserve PriorLegal PriorEarly) as Started.
     destruct (pipeline_raw_redirect_known memory inputs k prior states PriorObserve PriorLegal Run PriorReset) as [bit Raw].
     pose proof (delayed_redirect_observed_step memory inputs k prior states bit PriorObserve PriorLegal Run PriorReset Raw) as NewFlag.
     rewrite FlagState in NewFlag;destruct bit;[discriminate|].
     destruct (observed_joint_register_concrete memory inputs k prior 7748 32 PriorObserve PriorLegal
       ltac:(apply (List.nth_error_In joint_boundary_registers 53%nat);vm_compute;reflexivity)) as [instruction [InstSize Inst]].
     pose proof (observed_instruction_normal_transfer memory inputs k prior states instruction PriorObserve PriorLegal Run PriorReset InstSize Inst) as NextInst.
     assert (CommitInst : VM.find 7750 (top_environment observed) = Some (Gval (Fuint 32) instruction)).
     { pose proof (delayed_joint_observed_copy memory inputs (S k) states observed 7750 32
       ltac:(apply (List.nth_error_In joint_boundary_registers 55%nat);vm_compute;reflexivity) Run Observe) as Copy.
       change (VM.find 7750 (top_environment observed) = VM.find 7750 (top_environment states)) in Copy.
       rewrite Copy;exact NextInst. }
     pose proof (legal_observed_instruction_classified memory inputs (S k) observed instruction Observe Legal Reset CommitInst) as Classified.
     destruct (observed_joint_register_concrete memory inputs k prior 7768 33 PriorObserve PriorLegal
       ltac:(apply (List.nth_error_In joint_boundary_registers 67%nat);vm_compute;reflexivity)) as [fetch [FetchSize Fetch]].
     pose proof (pipeline_pc_kill_hold_observed memory inputs k prior states instruction fetch PriorObserve PriorLegal Run PriorReset Inst InstSize Classified Started Raw EarlyState FetchSize Fetch) as Held.
     pose proof (adjacent_transfer_observed_reset memory inputs k prior PriorObserve PriorLegal PriorReset) as PriorRoot.
     pose proof (observed_front_pc_transfer memory inputs k prior states fetch PriorObserve PriorLegal Run PriorRoot FetchSize Fetch) as NextFront.
     assert (ObservedFetch : VM.find 7768 (top_environment observed) = Some (Gval (Fuint 33) fetch)).
     { pose proof (delayed_joint_observed_copy memory inputs (S k) states observed 7768 33
       ltac:(apply (List.nth_error_In joint_boundary_registers 67%nat);vm_compute;reflexivity) Run Observe) as Copy.
       change (VM.find 7768 (top_environment observed) = VM.find 7768 (top_environment states)) in Copy.
       rewrite Copy;exact Held. }
     assert (ObservedFront : VM.find 7749 (top_environment observed) = Some (Gval (Fuint 32) (take 32 fetch))).
     { pose proof (delayed_joint_observed_copy memory inputs (S k) states observed 7749 32
       ltac:(apply (List.nth_error_In joint_boundary_registers 54%nat);vm_compute;reflexivity) Run Observe) as Copy.
       change (VM.find 7749 (top_environment observed) = VM.find 7749 (top_environment states)) in Copy.
       rewrite Copy;exact NextFront. }
     destruct (pipeline_commit_front_adjacent_observed memory inputs (S k) observed Observe Legal Late) as [commit [front [CommitPC [FrontPC Adjacent]]]].
     rewrite ObservedFront in FrontPC;inversion FrontPC;subst front.
     exists commit,fetch. split;[exact FetchSize|]. split;[exact CommitPC|]. split;[exact ObservedFetch|exact Adjacent].
Qed.
Require Import PipelinePCActiveSequentialCases PipelinePCRelation ReferencePCSequentialObserved.
Theorem pipeline_pc_active_no_redirect_sequential memory inputs k observed next :
 generated_observe memory inputs k = Some observed -> generated_legal_trace memory inputs k ->
 generated_run memory inputs (S k) = Some next ->
 VM.find 1 (formal_external_inputs (generated_observation_input inputs k)) = Some (Gval (Fuint 1) [::false]) ->
 reference_pc_sequential_control_window (formal_invalid_policy (generated_observation_input inputs k) nil) (top_environment observed) ->
 pipeline_pc_relation (top_environment observed) ->
 VM.find 7947 (top_environment observed) = Some (Gval (Fuint 1) [::false]) ->
 VM.find 7760 (top_environment observed) = Some (Gval (Fuint 1) [::false]) ->
 pipeline_pc_relation (top_environment next).
Proof.
 intros Observe Legal Next Reset Window Relation Late NoRedirect.
 apply (pipeline_pc_active_sequential_cases memory inputs k observed next Observe Legal Next Reset Window Relation);[|exact Late].
 split.
 - intro Early;exact (pipeline_commit_front_adjacent_observed memory inputs k observed Observe Legal Late).
 - intro Early;exact (pipeline_commit_fetch_adjacent_observed memory inputs k observed Observe Legal Reset Late Early NoRedirect).
Qed.
Require Import DUTRedirectReachability PipelineRedirectPhaseReachable EarlyBubbleNopReachable ObservedNopControls ObservedEarlyBubbleClear.
Lemma pipeline_redirect_target_low_aligned word : size word = 32%nat -> N.testbit (to_N word) 1 = false ->
 take 2 (take 32 (pipeline_redirect_target word)) = [::false;false].
Proof.
 intros Size Bit. rewrite (pipeline_redirect_target_bits word Size).
 change (N.testbit (to_N word) (N.of_nat 1) = false) in Bit;rewrite redirect_to_N_testbit in Bit.
 destruct word as [|a [|b rest]];try discriminate Size.
 cbn [nth] in Bit;subst b;cbn [drop cat take];rewrite take0;reflexivity.
Qed.
Theorem pipeline_delayed_fetch_aligned_observed memory inputs k observed :
 generated_observe memory inputs k = Some observed -> generated_legal_trace memory inputs k ->
 VM.find 1 (formal_external_inputs (generated_observation_input inputs k)) = Some (Gval (Fuint 1) [::false]) ->
 VM.find 7760 (top_environment observed) = Some (Gval (Fuint 1) [::true]) ->
 exists word, size word = 32%nat /\ VM.find 7752 (top_environment observed) = Some (Gval (Fuint 32) word) /\
 VM.find 7768 (top_environment observed) = Some (Gval (Fuint 33) (pipeline_redirect_target word)) /\
 take 2 (take 32 (pipeline_redirect_target word)) = [::false;false] /\
 VM.find 7945 (top_environment observed) = Some (Gval (Fuint 1) [::true]).
Proof.
 intros Observe Legal Reset Taken.
 destruct (pipeline_late_redirect_phase_observed memory inputs k observed Observe Legal Taken) as [word [Size [Target [Fetch Early]]]].
 exists word. split;[exact Size|]. split;[exact Target|]. split;[exact Fetch|]. split;[|exact Early].
 apply (pipeline_redirect_target_low_aligned word Size).
 exact (dut_no_trap_target_bit_observed memory inputs k observed word Observe Legal Reset Taken Target Size).
Qed.
Theorem pipeline_pc_active_redirect_target memory inputs k observed next :
 generated_observe memory inputs k = Some observed -> generated_legal_trace memory inputs k ->
 generated_run memory inputs (S k) = Some next ->
 VM.find 1 (formal_external_inputs (generated_observation_input inputs k)) = Some (Gval (Fuint 1) [::false]) ->
 VM.find 7947 (top_environment observed) = Some (Gval (Fuint 1) [::false]) ->
 VM.find 7760 (top_environment observed) = Some (Gval (Fuint 1) [::true]) ->
 (forall word, size word = 32%nat -> VM.find 7752 (top_environment observed) = Some (Gval (Fuint 32) word) ->
  VM.find 7331 (top_environment next) = Some (Gval (Fuint 32) (take 32 (pipeline_redirect_target word)))) ->
 pipeline_pc_relation (top_environment next).
Proof.
 intros Observe Legal Next Reset Late Taken ReferenceNext.
 destruct (pipeline_delayed_fetch_aligned_observed memory inputs k observed Observe Legal Reset Taken) as [word [Size [Target [Fetch [Aligned Early]]]]].
 pose proof (pipeline_redirect_target_size word Size) as FetchSize.
 pose proof (adjacent_transfer_observed_reset memory inputs k observed Observe Legal Reset) as Root.
 pose proof (observed_front_pc_transfer memory inputs k observed next (pipeline_redirect_target word) Observe Legal Next Root FetchSize Fetch) as FrontNext.
 pose proof (observed_late_bubble_normal_step memory inputs k observed next true (Gval (Fuint 1) [::false]) Observe Legal Next Reset Early Late (Logic.eq_refl _)) as LateNext.
 pose proof (active_observation_startup_false memory inputs k observed Observe Legal Late) as Started.
 pose proof (early_bubble_nop_all_observations memory inputs k observed Observe Legal Early) as Nop.
 destruct (observed_nop_controls_false memory inputs k observed Observe Legal Nop) as [Kill Branch].
 pose proof (observed_early_bubble_clear_step memory inputs k observed next (Gval (Fuint 1) [::true]) Observe Legal Next Reset Started Kill Branch Early (Logic.eq_refl _)) as EarlyNext.
 exists (take 32 (pipeline_redirect_target word)). split.
 - rewrite size_take FetchSize;reflexivity.
 - split;[exact Aligned|]. split;[exact (ReferenceNext word Size Target)|].
   right;left. split;[exact LateNext|]. split;[exact EarlyNext|exact FrontNext].
Qed.
Require Import PipelinePCAssertions PipelinePCPreservationReduction.
(* These are the remaining reference-model obligations. All DUT stage,
   address-adjacency, hold, bubble and target-alignment premises are discharged
   above from reachable executions; this proposition is not a new assumption
   of the circuit and must still be proved to close the original assertions. *)
Definition pipeline_reference_pc_obligations memory inputs : Prop :=
 forall k observed next,
 generated_observe memory inputs k = Some observed -> generated_legal_trace memory inputs k ->
 generated_run memory inputs (S k) = Some next ->
 VM.find 1 (formal_external_inputs (generated_observation_input inputs k)) = Some (Gval (Fuint 1) [::false]) ->
 pipeline_pc_relation (top_environment observed) ->
 VM.find 7947 (top_environment observed) = Some (Gval (Fuint 1) [::false]) ->
 (VM.find 7760 (top_environment observed) = Some (Gval (Fuint 1) [::false]) ->
  reference_pc_sequential_control_window (formal_invalid_policy (generated_observation_input inputs k) nil) (top_environment observed)) /\
 (VM.find 7760 (top_environment observed) = Some (Gval (Fuint 1) [::true]) ->
  forall word, size word = 32%nat -> VM.find 7752 (top_environment observed) = Some (Gval (Fuint 32) word) ->
  VM.find 7331 (top_environment next) = Some (Gval (Fuint 32) (take 32 (pipeline_redirect_target word)))).
Theorem pipeline_pc_active_from_reference_obligations memory inputs :
 pipeline_reference_pc_obligations memory inputs -> pipeline_pc_active_preservation memory inputs.
Proof.
 intros Reference k observed next Observe Legal Next Reset Relation Late.
 destruct (Reference k observed next Observe Legal Next Reset Relation Late) as [Sequential Redirect].
 destruct (observed_joint_register_concrete memory inputs k observed 7760 1 Observe Legal
 ltac:(apply (List.nth_error_In joint_boundary_registers 65%nat);vm_compute;reflexivity)) as [bits [Size Flag]].
 destruct bits as [|bit [|extra rest]];try discriminate Size.
 change (VM.find 7760 (top_environment observed) = Some (Gval (Fuint 1) [::bit])) in Flag.
 destruct bit.
 - exact (pipeline_pc_active_redirect_target memory inputs k observed next Observe Legal Next Reset Late Flag (Redirect Flag)).
 - exact (pipeline_pc_active_no_redirect_sequential memory inputs k observed next Observe Legal Next Reset (Sequential Flag) Relation Late Flag).
Qed.
Theorem pc_assertions_from_reference_pc_obligations memory inputs :
 pipeline_reference_pc_obligations memory inputs ->
 forall k observed, generated_observe memory inputs k = Some observed -> generated_legal_trace memory inputs k ->
 generated_assert_m0_7_all observed /\ generated_assert_m0_43_all observed.
Proof.
 intro Reference. apply pc_assertions_from_active_preservation.
 exact (pipeline_pc_active_from_reference_obligations memory inputs Reference).
Qed.
