Require Import CoreSocModel ComparisonNodes CycleView MemoryCycleStep ReferenceConditionalBranchImmediate ReferenceBranchImmediate DUTImmediateModes RFALUData RFPipelineEnable ReferenceInstructionDecode LoadExecuteControl DUTRedirectDecode ALUOperandTransfer ALUInputStability ALUOutputTransfer LoadEffectiveAddress ReferenceLoadSemantics FormalObservedHistory FormalLocalHistory ObservedJointRegisterConcrete JointBoundaryRegisters RFReadPorts ReferenceBankObservation.
From Coq Require Import NArith Arith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Require Import MemoryAddressInputs RFAluWritebackObserved RFWriteEffect.
Definition jalr_match (instruction:bits) := N.land(to_N instruction)(reference_instruction_mask 22)=reference_instruction_code 22.
Lemma jalr_decode_control instruction which : (which<4)%coq_nat ->jalr_match instruction ->
 load_execute_decode which(to_N instruction)49=from_N(load_execute_width which)(load_execute_expected which).
Proof.
 intros Which Match.
 cbn[load_execute_decode].
 repeat match goal with |-context[dut_decode_test(to_N instruction)?stage]=>rewrite(rf_dut_decode_wb_choice instruction stage ltac:(vm_compute;lia))(rf_wb_choice_onehot instruction 22%nat(Nat.sub 48 stage)ltac:(lia) ltac:(vm_compute;lia)Match)end.
 do 4(destruct which as[|which];[reflexivity|]);lia.
Qed.
Theorem jalr_control_observed memory inputs k observed instruction :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 VM.find 7748(top_environment observed)=Some(Gval(Fuint 32)instruction) ->size instruction=32%nat ->jalr_match instruction ->
 VM.find 86(top_environment observed)=Some(Gval(Fuint 1)[::true]) /\
 VM.find 87(top_environment observed)=Some(Gval(Fuint 1)[::false]) /\
 VM.find 88(top_environment observed)=Some(Gval(Fuint 3)(dut_imm_selector 0)) /\
 VM.find 89(top_environment observed)=Some(Gval(Fuint 4)[::false;false;false;false]).
Proof.
 intros Observe Legal Front Size Match.
 destruct(observed_history memory inputs k observed Observe Legal)as[reset[history[Last[Steps Resets]]]].
 assert(Control:forall which,(which<4)%coq_nat ->VM.find(load_execute_wire_target which true)(top_environment observed)=Some(Gval(Fuint(load_execute_width which))(from_N(load_execute_width which)(load_execute_expected which)))).
 { intros which Which. rewrite <-Last.
 rewrite(load_execute_decode_history (generated_observation_input inputs k)nil history 9259 instruction which Which Steps ltac:(rewrite Last;exact Front)Size 9259 ltac:(vm_compute;lia)ltac:(vm_compute;lia))(jalr_decode_control instruction which Which Match);reflexivity. }
 split;[exact(Control 0%nat ltac:(lia))|]. split;[exact(Control 1%nat ltac:(lia))|]. split;[|exact(Control 3%nat ltac:(lia))].
 exact(Control 2%nat ltac:(lia)).
Qed.
Theorem cycle_jalr_address_step memory inputs k current next before after :
 cycle_transition memory inputs k current next ->cycle_reset inputs k false ->
 cycle_view_at(top_environment current)before ->cycle_view_at(top_environment next)after ->
 jalr_match(cv_front_instruction before) ->
 cv_commit_instruction after=cv_front_instruction before /\
 cv_pending_alu after=reference_load_address(cv_left before)(dut_imm_result 0(cv_front_instruction before)).
Proof.
 intros Transition Reset Before After Match.
 split;[exact(cycle_front_to_commit memory inputs k current next before after Transition Reset Before After)|].
 destruct Transition as[Observe[Legal[NextObserve[NextLegal[committed Run]]]]].
 destruct(observed_joint_register_concrete memory inputs k current 7748%nat 32%nat Observe Legal rf_read_front_member)as[instruction[Size Inst]].
 rewrite(cva_front_instruction _ _ Before)in Inst;inversion Inst;subst instruction.
 destruct(jalr_control_observed memory inputs k current(cv_front_instruction before)Observe Legal(cva_front_instruction _ _ Before)Size Match)as[A[B[Select Mode]]].
 pose proof(dut_imm_observed 0 memory inputs k current(cv_front_instruction before)ltac:(lia)Observe Legal(cva_front_instruction _ _ Before)Size Select)as Immediate.
 pose proof(memory_effective_address_commit_observed memory inputs k current committed(cv_left before)(dut_imm_result 0(cv_front_instruction before))
 Observe Legal Run Reset(cva_left_width _ _ Before)(dut_imm_result_size 0 _ ltac:(lia)Size)A B Mode(cva_left _ _ Before)Immediate)as Value.
 pose proof(joint_register_run_observed memory inputs(S k)committed next 7752 32 rf_read_alu_member Run NextObserve)as Copy.
 rewrite(cva_pending_alu _ _ After)Value in Copy.
 exact(f_equal(fun value=>match value with Some(Gval _ word)=>word|_=>[::]end)Copy).
Qed.
Theorem cycle_jalr_address_forwarded memory inputs k current next before after :
 cycle_transition memory inputs k current next ->cycle_reset inputs k false ->
 cycle_view_at(top_environment current)before ->cycle_view_at(top_environment next)after ->
 cycle_banks_agree before ->jalr_match(cv_front_instruction before) ->
 cv_pending_alu after=reference_load_address
 (rf_apply_effect(cv_reference_bank before)(cycle_pending_effect before)
 (to_nat(rf_instruction_address false(cv_front_instruction before))))
 (dut_imm_result 0(cv_front_instruction before)).
Proof.
 intros Transition Reset Before After Banks Match.
 pose proof(proj2(cycle_jalr_address_step memory inputs k current next before after Transition Reset Before After Match))as Value.
 destruct Transition as[Observe[Legal Rest]].
 rewrite(cycle_forwarded_read memory inputs k current before false Observe Legal Before Banks)in Value.
 exact Value.
Qed.
