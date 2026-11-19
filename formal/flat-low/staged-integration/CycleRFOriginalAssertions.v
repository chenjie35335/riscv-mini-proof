Require Import ReferenceBankCycleInputs.
Require Import RFReferenceNopHistory.
Require Import RFArchitecturalRelation RFModeInvariant ReferenceInstructionDecode.
Require Import ExceptionPCSourceRegisters.
Require Import CycleISAReferenceAdvance RFReferenceWriteEffect RFEffectState RFPipelineEnable ControlWritebackKill ReferenceControlRegisters.
Require Import RFOriginalDUTPreview RFOriginalPreviewHistory CycleISACurrentEffectInputs CycleReferenceBankInputs ReferenceMISAConcrete RFArchitecturalWriteEffect CycleInstructionClassReachable DUTBankCycleStep StagedFlatObservation GeneratedAssertion8 PipelinePCAssertions RFReferenceNopCycle ReferenceBankConcreteReachable FormalInstructionResetConstants.
Require Import DUTBankCycleHistory DUTWritebackHistory DUTBankObservation CycleView RFAluWritebackObserved RFBitwiseEffectAgreement RFWriteEffect RFScalarControl RFReadPorts RFArchitecturalNormalRelation RFArchitecturalRelation ReferenceControlRegisters RFNonAluBubbleHazard RFPipelineEnable ObservedLegalNoTrap FormalFetchType JointBoundaryReachable JointBoundaryPreparation ConcreteRegisterInitialization FormalResetPreparation FormalLocalHistory JointUpdateBoundaryHistory JointBoundaryRegisters ObservedJointRegisterConcrete CoreSocModel ComparisonNodes.
From Coq Require Import NArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Theorem cycle_rf_original_assertion_normal memory inputs k observed v index :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 cycle_reset inputs k false ->cycle_view_at(top_environment observed)v ->
 cycle_banks_agree v ->cycle_isa_pending v ->(index<32)%coq_nat ->rf_original_assertion_all index observed.
Proof.
 intros Observe Legal Reset View Banks Pending Index.
 destruct index as[|index]. { exact(generated_assert_8 memory inputs k observed Observe Legal). }
 destruct(observed_legal_no_trap_history memory inputs k observed Observe Legal Reset)
 as[committed[initial[history[Run[Prepare[First[Last[Steps NoTrap]]]]]]]].
 destruct(fetch9220_run_type memory inputs k committed Run)as[env[value[Env Rest]]].
 destruct(joint_boundary_reachable memory inputs k committed Run Legal)as[Registers Storage].
 unfold top_environment in Registers;rewrite Env in Registers.
 assert(Boundary:forall node width,List.In(node,width)joint_boundary_registers ->map_uint_concrete(N.of_nat node)width(history 0%nat)).
 { intros node width Member. rewrite First. exact(joint_boundary_prepared_concrete committed env _ initial node width Member(Registers node width Member)Env Prepare). }
 destruct(top_reset_prepared(Some committed)_ initial _ Reset Prepare)as[initial_env[InitialEnv InitialReset]].
 assert(Reset0:VM.find 1(history 0%nat)=Some(Gval(Fuint 1)[::false])).
 { rewrite First. unfold top_environment;rewrite InitialEnv;exact InitialReset. }
 pose proof(legal_local_reset_history _ history 9259 false Steps Reset0)as Resets.
 assert(Bank:rf_dut_bank_at(history 0%nat)(cv_dut_bank v)).
 { intros lane Bound. destruct(cva_dut_bank _ _ View lane Bound)as[Size Value]. split;[exact Size|].
   destruct(rf_architectural_register_properties _ (rf_dut_register_member lane Bound))as[Present RestProps].
   rewrite<-(reference_control_register_history_same _ history 9259 _ Present Steps 9259%nat ltac:(lia)). rewrite Last;exact Value. }
 assert(Top:SVM.find nil observed=Some(top_environment observed)).
 { destruct(observed_last_iteration memory inputs k observed Observe)as[c[i[p[o[n[_[_[_[_[_ State]]]]]]]]]]. unfold top_environment;rewrite State;reflexivity. }
 assert(InitialInstruction:VM.find 7750(history 0%nat)=Some(Gval(Fuint 32)(cv_commit_instruction v))).
 { pose proof(flat_register_history_same _ history 9259 7750(proj2(joint_boundary_register_properties 7750 32 rf_pipeline_enable_instruction_member))Steps)as Hold.
   rewrite<-(Hold 9259%nat ltac:(lia)). rewrite Last;exact(cva_commit_instruction _ _ View). }
 destruct(List.list_eq_dec Bool.bool_dec(cv_commit_instruction v)instruction_nop)as[Nop|NonNop].
 - eapply(rf_original_assertion_from_common_effect (S index) _ (history 9258%nat)(history 9259%nat) observed(cv_dut_bank v)RFNoWrite);[exact Index|rewrite Last;exact Top|apply Steps;vm_compute;lia|].
   intro Enabled. rewrite Last in Enabled.
   destruct(pipeline_pc_enabled_observed (S(S index)) memory inputs k observed(cv_late_bubble v)ltac:(lia)Observe Legal(cva_late_bubble _ _ View)Enabled)as[Bubble _].
   assert(RefBank:rf_reference_bank_at(history 0%nat)(cv_reference_bank v)).
   { intros lane Bound. destruct(cva_reference_bank _ _ View lane Bound)as[Size Value]. split;[exact Size|].
     destruct(rf_architectural_register_properties _ (rf_reference_register_member lane Bound))as[Present _].
     rewrite<-(reference_control_register_history_same _ history 9259 _ Present Steps 9259%nat ltac:(lia)). rewrite Last;exact Value. }
   rewrite Nop in InitialInstruction.
   assert(DZero:cv_dut_bank v 0%nat=nseq 32 false)by exact(cycle_dut_x0 memory inputs k observed v Observe Legal View).
   assert(RZero:cv_reference_bank v 0%nat=nseq 32 false)by(rewrite<-(Banks 0%nat ltac:(lia));exact DZero).
   assert(NoWrite:rf_apply_effect(cv_dut_bank v)RFNoWrite(S index)=cv_dut_bank v(S index))by reflexivity.
   rewrite NoWrite.
   split.
   + exact(rf_dut_nop_original_outputs _ history _ Bank DZero InitialInstruction Steps (S index)Index).
   + rewrite(Banks (S index)Index). eapply(rf_reference_nop_original_outputs _ history _ RefBank RZero InitialInstruction Steps Resets);[rewrite Last (cva_late_bubble _ _ View) Bubble;reflexivity|exact Index].
 - assert(Mode:cv_write_select_low v && cv_write_select_high v=false).
   { destruct(cip_mode _ Pending NonNop)as[Low High]. rewrite Low High.
     destruct(cycle_commit_instruction_reference_row memory inputs k observed v Observe Legal Reset View)as[row[Row Match]]. exact(dut_isa_mode_not_csr _ row Row Match). }
 assert(Modes:forall t,(t<=9259)%coq_nat ->VM.find 7756(history t)=Some(Gval(Fuint 2)[::cv_write_select_low v;cv_write_select_high v])).
 { intros t Upper. pose proof(joint_update_register_history_same _ history 9259 7756 2 rf_nonalu_mode_member Steps)as Hold.
   rewrite(Hold t Upper). rewrite<-(Hold 9259%nat ltac:(lia)). rewrite Last;exact(cva_write_select _ _ View). }
 destruct(dut_writeback_history_stable _ history 9259 _ _ Boundary Steps Modes Mode)as[data Data].
 assert(DataActual:data=cv_write_data v).
 { pose proof(Data 9259%nat ltac:(vm_compute;lia)ltac:(vm_compute;lia))as Value.
   rewrite Last (cva_write_data _ _ View)in Value;inversion Value;reflexivity. }
 subst data.
 destruct(observed_joint_register_concrete memory inputs k observed 7750 32 Observe Legal rf_pipeline_enable_instruction_member)as[instruction[InstructionSize Instruction]].
 rewrite(cva_commit_instruction _ _ View)in Instruction. inversion Instruction;subst instruction.
   assert(Dut:VM.find(N.of_nat(Nat.add 1399(S index)))(history 9258%nat)=Some(Gval(Fuint 32)(rf_apply_effect(cv_dut_bank v)(cycle_pending_effect v)(S index)))).
   { unfold cycle_pending_effect. rewrite(cycle_destination_observed memory inputs k observed v Observe Legal View).
     eapply(dut_original_preview_history _ nil history _ _ _ _ Boundary Steps Resets NoTrap Bank InstructionSize(cva_write_width _ _ View));[rewrite Last;exact(cva_commit_instruction _ _ View)|rewrite Last;exact(cva_write_enabled _ _ View)|exact Data|exact Index]. }
   destruct(reference_misa_observed_concrete memory inputs k observed Observe Legal)as[csr[Width CSR]].
   destruct(cycle_reference_bank_inputs memory inputs k observed v csr Observe Legal Reset View Pending CSR Width)as[NopActual|[Controls[Selected Destination]]].
   { rewrite(cva_commit_instruction _ _ View)in NopActual. inversion NopActual;contradiction. }
   pose proof(reference_original_preview_history memory inputs k observed(cv_reference_bank v)history(S index)Observe Legal Last Steps Resets(cva_reference_bank _ _ View)Controls Selected Destination ltac:(lia)Index)as Ref.
   pose proof(cycle_isa_current_effect_agreement memory inputs k observed v Observe Legal Reset View Pending)as Agreement.
   assert(Effect:rf_apply_effect(cv_reference_bank v)(ref_write_effect(top_environment observed))(S index)=rf_apply_effect(cv_dut_bank v)(cycle_pending_effect v)(S index)).
   { rewrite<-(rf_normalized_effect_agreement (cv_reference_bank v) _ _ Agreement (S index)).
     unfold rf_apply_effect. rewrite<-(Banks (S index)Index). reflexivity. }
   rewrite Effect in Ref.
   eapply(rf_original_assertion_from_common_effect (S index) _ (history 9258%nat)(history 9259%nat) observed(cv_dut_bank v)(cycle_pending_effect v));[exact Index|rewrite Last;exact Top|apply Steps;vm_compute;lia|]. intros _;split;assumption.
Qed.

Require Import Assertion2ResetGuard LoadPipelineClassification.
Theorem cycle_rf_original_assertion_reset memory inputs k observed index :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 cycle_reset inputs k true ->(index<32)%coq_nat ->rf_original_assertion_all index observed.
Proof.
 intros Observe Legal Reset Index.
 destruct(assertion2_history_with_reset memory inputs k observed true Observe Reset)as[history[Last[Steps Resets]]].
 assert(Top:SVM.find nil observed=Some(top_environment observed)).
 { destruct(observed_last_iteration memory inputs k observed Observe)as[c[i[p[o[n[_[_[_[_[_ State]]]]]]]]]]. unfold top_environment;rewrite State;reflexivity. }
 destruct(load_pipeline_late_observed memory inputs k observed Observe Legal)as[bubble[Bubble _]].
 eapply(rf_original_assertion_from_common_effect index _ (history 9258%nat)(history 9259%nat) observed(fun _=>nseq 32 false)RFNoWrite);[exact Index|rewrite Last;exact Top|apply Steps;vm_compute;lia|].
 intro Enabled. assert(BH:VM.find 7947(history 9259%nat)=Some(Gval(Fuint 1)[::bubble]))by(rewrite Last;exact Bubble).
 destruct(pipeline_pc_enabled_history (S index) _ history bubble true ltac:(lia)Steps Resets BH Enabled)as[_[Impossible _]]. discriminate Impossible.
Qed.
