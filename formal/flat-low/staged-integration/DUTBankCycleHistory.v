Require Import ExceptionPCSourceRegisters StagedRegisterHold RFWriteEffect ConcreteRegisterInitialization ExceptionSourceNoTrap FormalStallHistory JointBoundaryReachable JointBoundaryPreparation ObservedJointRegisterConcrete CoreSocModel ComparisonNodes RFNonAluBubbleHazard FormalLocalHistory RFEffectState RFArchitecturalNormalRelation RFPipelineEnable RFPreviewEffect RFScalarControl RFArchitecturalRelation RFReferenceNopHistory JointUpdateExpressionCertificates JointUpdateNodePositions FormalGroundNodeEquation FormalRFResetConnections FormalCheckerResetConnections FormalRFDestination FormalRFWriteEnable JointBoundaryRegisters JointUpdateBoundaryHistory ReferenceRedirectSpine ObservedLegalNoTrap.
From Coq Require Import NArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Theorem dut_bank_cycle_history inputs path history result bank instruction enabled data :
 (forall node width,List.In(node,width)joint_boundary_registers ->map_uint_concrete(N.of_nat node)width(history 0%nat)) ->
 (forall time,(time<9259)%coq_nat ->formal_value_iter(formal_invalid_policy inputs path)flat_memories(history time)false(history time)flat_statements=Some(history(S time))) ->
 (forall time,(time<=9259)%coq_nat ->VM.find 1(history time)=Some(Gval(Fuint 1)[::false])) ->
 VM.find 45(history 9254%nat)=Some(Gval(Fuint 1)[::false]) ->
 rf_dut_bank_at(history 0%nat)bank ->bank 0%nat=nseq 32 false ->
 size instruction=32%nat ->size data=32%nat ->
 VM.find 7750(history 9259%nat)=Some(Gval(Fuint 32)instruction) ->
 VM.find 7757(history 9259%nat)=Some(Gval(Fuint 1)[::enabled]) ->
 VM.find 786(history 9256%nat)=Some(Gval(Fuint 32)data) ->
 formal_value_iter(formal_invalid_policy inputs path)flat_memories(history 9259%nat)true(history 9259%nat)flat_statements=Some result ->
 rf_dut_bank_at result(rf_apply_effect bank(if enabled then RFWrite(to_nat(rf_instruction_rd instruction))data else RFNoWrite)).
Proof.
 intros Boundary Steps Resets NoTrap Bank Zero Size DataSize Instruction Enable Data Commit.
 assert(Inst:VM.find 7750(history 9254%nat)=Some(Gval(Fuint 32)instruction)).
 { rewrite(flat_register_history_same _ history 9259 7750(proj2(joint_boundary_register_properties 7750 32 rf_pipeline_enable_instruction_member))Steps 9254 ltac:(vm_compute;lia)).
 rewrite(flat_register_history_same _ history 9259 7750(proj2(joint_boundary_register_properties 7750 32 rf_pipeline_enable_instruction_member))Steps 9259 ltac:(vm_compute;lia))in Instruction. exact Instruction. }
 assert(En:VM.find 7757(history 9254%nat)=Some(Gval(Fuint 1)[::enabled])).
 { rewrite(flat_register_history_same _ history 9259 7757(proj2(joint_boundary_register_properties 7757 1 rf_nonalu_enable_member))Steps 9254 ltac:(vm_compute;lia)).
 rewrite(flat_register_history_same _ history 9259 7757(proj2(joint_boundary_register_properties 7757 1 rf_nonalu_enable_member))Steps 9259 ltac:(vm_compute;lia))in Enable. exact Enable. }
 assert(Stall:VM.find 7765(history 9253%nat)=Some(Gval(Fuint 1)[::false])).
 { exact(stall_after_six _ (history 9247%nat)(history 9248%nat)(history 9249%nat)(history 9250%nat)(history 9251%nat)(history 9252%nat)(history 9253%nat)false(Resets 9247 ltac:(vm_compute;lia))(Steps 9247 ltac:(vm_compute;lia))(Steps 9248 ltac:(vm_compute;lia))(Steps 9249 ltac:(vm_compute;lia))(Steps 9250 ltac:(vm_compute;lia))(Steps 9251 ltac:(vm_compute;lia))(Steps 9252 ltac:(vm_compute;lia))). }
 pose proof(exception_source_false_after_settling inputs path history Boundary Steps NoTrap 9254 ltac:(vm_compute;lia)ltac:(vm_compute;lia))as Exception.
 pose proof(rf_pipeline_wen_after_four _ (history 9253%nat)(history 9254%nat)(history 9255%nat)(history 9256%nat)(history 9257%nat)enabled Stall En Exception(Steps 9253 ltac:(vm_compute;lia))(Steps 9254 ltac:(vm_compute;lia))(Steps 9255 ltac:(vm_compute;lia))(Steps 9256 ltac:(vm_compute;lia)))as Wen.
 pose proof(rf_destination_port_after_two _ (history 9254%nat)(history 9255%nat)(history 9256%nat)instruction Size Inst(Steps 9254 ltac:(vm_compute;lia))(Steps 9255 ltac:(vm_compute;lia)))as RD.
 pose proof(rf_address_nonzero_node _ (history 9256%nat)(history 9256%nat)(history 9257%nat)(rf_instruction_rd instruction)RD(Steps 9256 ltac:(vm_compute;lia)))as Nonzero.
 rewrite(rf_nonzero_five _ (rf_instruction_rd_size instruction Size))in Nonzero.
 pose proof(rf_write_enable_node _ (history 9257%nat)(history 9257%nat)(history 9258%nat)enabled(rf_instruction_nonzero instruction)Wen Nonzero(Steps 9257 ltac:(vm_compute;lia)))as Gate.
 assert(RDnext:VM.find 785(history 9257%nat)=Some(Gval(Fuint 5)(rf_instruction_rd instruction))).
 { assert(Inst5:VM.find 7750(history 9255%nat)=Some(Gval(Fuint 32)instruction)).
   { rewrite(flat_register_history_same _ history 9259 7750(proj2(joint_boundary_register_properties 7750 32 rf_pipeline_enable_instruction_member))Steps 9255 ltac:(vm_compute;lia)).
     rewrite(flat_register_history_same _ history 9259 7750(proj2(joint_boundary_register_properties 7750 32 rf_pipeline_enable_instruction_member))Steps 9254 ltac:(vm_compute;lia))in Inst. exact Inst. }
   exact(rf_destination_port_after_two _ (history 9255%nat)(history 9256%nat)(history 9257%nat)instruction Size Inst5(Steps 9255 ltac:(vm_compute;lia))(Steps 9256 ltac:(vm_compute;lia))). }
 assert(DataPort:VM.find 955(history 9257%nat)=Some(Gval(Fuint 32)data)).
 { eapply(reference_redirect_ground_step joint_update_node_offsets joint_update_expected_nodes 955 joint_update_expr_955);[exact joint_update_node_positions|exact joint_update_node_safety|apply(List.nth_error_In joint_update_expected_nodes 610);reflexivity| |exact(Steps 9256 ltac:(vm_compute;lia))]. intros site. exact Data. }
 pose proof(reset_connection_24_transfer _ (history 9256%nat)(history 9256%nat)(history 9257%nat)false(Resets 9256 ltac:(vm_compute;lia))(Steps 9256 ltac:(vm_compute;lia)))as R24.
 pose proof(reset_connection_65_transfer _ (history 9257%nat)(history 9257%nat)(history 9258%nat)false R24(Steps 9257 ltac:(vm_compute;lia)))as R65.
 assert(Reset:VM.find 779(history 9259%nat)=Some(Gval(Fuint 1)[::false])).
 { eapply rf_reset_connection_779;[exact R65|reflexivity|exact(Steps 9258 ltac:(vm_compute;lia))]. }
 assert(Guard:enabled && rf_instruction_nonzero instruction=true ->to_nat(rf_instruction_rd instruction)<>0%nat).
 { rewrite rf_instruction_nonzero_correct. move/andP=>[_ /eqP H]. exact H. }
 pose proof(rf_dut_bank_effect_commit _ (history 9257%nat)(history 9258%nat)(history 9259%nat)result bank(rf_instruction_rd instruction)data(enabled && rf_instruction_nonzero instruction)
 (rf_dut_bank_history_hold _ history 9259 bank Bank Steps 9257 ltac:(vm_compute;lia))Zero DataSize Guard RDnext DataPort Gate Reset(Steps 9257 ltac:(vm_compute;lia))(Steps 9258 ltac:(vm_compute;lia))Commit)as Actual.
 intros index Bound. specialize(Actual index Bound).
 unfold rf_instruction_nonzero in Actual.
 rewrite<- (rf_nonzero_five _ (rf_instruction_rd_size instruction Size))in Actual.
 rewrite rf_preview_effect_remove_zero_guard in Actual. exact Actual.
Qed.
