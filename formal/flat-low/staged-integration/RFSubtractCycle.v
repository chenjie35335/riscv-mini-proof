Require Import DUTRedirectSemantics RFSubtractArithmetic RFInstructionControl RFALUData RFPipelineEnable RFScalarControl LoadExecuteControl DUTRedirectDecode ControlWritebackKill ReferenceInstructionDecode CoreSocModel ComparisonNodes JointBoundaryRegisters JointUpdateBoundaryHistory.
From Coq Require Import NArith List Lia PeanoNat.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Require Import ConcreteRegisterInitialization ALUOperandTransfer LoadEffectiveAddress LoadImmediateSemantics RFReadPorts.
Theorem rf_subtract_operand_history inputs path history limit instruction left right :
 size instruction=32%nat ->size left=32%nat ->size right=32%nat ->
 N.land(to_N instruction)(reference_instruction_mask(19%nat))=reference_instruction_code(19%nat) ->
 (forall node width,List.In(node,width)joint_boundary_registers ->map_uint_concrete(N.of_nat node)width(history 0%nat)) ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter(formal_invalid_policy inputs path)flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 VM.find 7748(history limit)=Some(Gval(Fuint 32)instruction) ->
 (forall t,(55<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 7816(history t)=Some(Gval(Fuint 32)left)) ->
 (forall t,(55<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 7819(history t)=Some(Gval(Fuint 32)right)) ->
 forall time,(100<=time)%coq_nat ->(time<=limit)%coq_nat ->
 VM.find 1151(history time)=Some(Gval(Fuint 32)left) /\
 VM.find 1152(history time)=Some(Gval(Fuint 32)right) /\
 VM.find 1153(history time)=Some(Gval(Fuint 4)(from_N 4(1))).
Proof.
 intros Size LeftSize RightSize Match Boundary Steps Front Left Right.
 pose proof(rf_isa_execute_control_history inputs path history limit instruction 19%nat)as Control.
 assert(A:forall time,(71<=time)%coq_nat ->(time<=limit)%coq_nat ->VM.find 1151(history time)=Some(Gval(Fuint 32)left)).
 { apply(alu_operand_selected_history _ history limit 68 true left LeftSize Steps false).
 - intros t L U. exact(Control 0%nat ltac:(lia) ltac:(lia)Size Match Steps Front t ltac:(lia)U).
 - intros t L U. apply Left;lia.
 - intros t L U. destruct(joint_update_register_history_concrete _ history limit 7749 32 ltac:(apply(List.nth_error_In joint_boundary_registers 54%nat);vm_compute;reflexivity) (Boundary 7749%nat 32%nat ltac:(apply(List.nth_error_In joint_boundary_registers 54%nat);vm_compute;reflexivity)) Steps t U)as[word[W V]]. exists(Gval(Fuint 32)word);split;[exact V|reflexivity]. }
 assert(B:forall time,(71<=time)%coq_nat ->(time<=limit)%coq_nat ->VM.find 1152(history time)=Some(Gval(Fuint 32)right)).
 { apply(alu_operand_selected_history _ history limit 68 true right RightSize Steps true).
 - intros t L U. exact(Control 1%nat ltac:(lia)ltac:(lia)Size Match Steps Front t ltac:(lia)U).
 - intros t L U. apply Right;lia.
 - intros [|t] L U;try lia. exact(alu_immediate_wire_type _ (history t)(history t)(history(S t))(Steps t ltac:(lia))). }
 intros [|time] Lower Upper;try lia. split;[apply A;lia|]. split;[apply B;lia|].
 exact(load_operand_wire_value 2%nat _ (history time)(history time)(history(S time))(from_N 4(1))ltac:(lia)(size_from_N _ _)(Control 3%nat ltac:(lia) ltac:(lia)Size Match Steps Front time ltac:(lia)ltac:(lia))(Steps time ltac:(lia))).
Qed.

Require Import ReferenceLoadSemantics FormalLocalHistory ALUInputStability ALUOutputTransfer ObservedJointRegisterConcrete EarlyControlStabilityHistory CycleView ReferenceBankObservation.
Theorem rf_subtract_observed_commit memory inputs k observed next instruction left right :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 generated_run memory inputs(S k)=Some next ->
 VM.find 1(formal_external_inputs(generated_observation_input inputs k))=Some(Gval(Fuint 1)[::false]) ->
 VM.find 7748(top_environment observed)=Some(Gval(Fuint 32)instruction) ->
 N.land(to_N instruction)(reference_instruction_mask(19%nat))=reference_instruction_code(19%nat) ->
 size left=32%nat ->size right=32%nat ->
 VM.find 7816(top_environment observed)=Some(Gval(Fuint 32)left) ->VM.find 7819(top_environment observed)=Some(Gval(Fuint 32)right) ->
 VM.find 7752(top_environment next)=Some(Gval(Fuint 32)(dut_branch_difference left right)).
Proof.
 intros Observe Legal Next Reset Instruction Match LeftSize RightSize Left Right.
 destruct(observed_joint_register_concrete memory inputs k observed 7748%nat 32%nat Observe Legal load_imm_front_member)as[word[Size Word]]. rewrite Instruction in Word;inversion Word;subst word.
 destruct(rf_alu_observed_transfer_context memory inputs k observed next Observe Legal Next Reset)as[history[Last[Boundary[Steps[Resets Transfer]]]]].
 assert(L:forall t,(55<=t)%coq_nat ->(t<=9259)%coq_nat ->VM.find 7816(history t)=Some(Gval(Fuint 32)left)).
 { intros t Lower Upper. rewrite(early_control_stable_7816_history (generated_observation_input inputs k)nil history 9259 Boundary Steps t 9259 ltac:(lia)ltac:(vm_compute;lia)Upper ltac:(vm_compute;lia))Last;exact Left. }
 assert(R:forall t,(55<=t)%coq_nat ->(t<=9259)%coq_nat ->VM.find 7819(history t)=Some(Gval(Fuint 32)right)).
 { intros t Lower Upper. rewrite(early_control_stable_7819_history (generated_observation_input inputs k)nil history 9259 Boundary Steps t 9259 ltac:(lia)ltac:(vm_compute;lia)Upper ltac:(vm_compute;lia))Last;exact Right. }
 pose proof(rf_subtract_operand_history (generated_observation_input inputs k)nil history 9259 instruction left right Size LeftSize RightSize Match Boundary Steps ltac:(rewrite Last;exact Instruction)L R)as Inputs.
 assert(Sum:VM.find 1161(history 9255%nat)=Some(Gval(Fuint 32)(dut_branch_difference left right))).
 { apply(rf_alu_subtract_from_inputs (formal_invalid_policy(generated_observation_input inputs k)nil) (fun t=>history (Nat.add 9250 t)) left right LeftSize RightSize).
 - exact(proj1(proj2(Inputs 9250%nat ltac:(vm_compute;lia)ltac:(vm_compute;lia)))).
 - exact(proj2(proj2(Inputs 9251%nat ltac:(vm_compute;lia)ltac:(vm_compute;lia)))).
 - exact(proj1(proj2(Inputs 9252%nat ltac:(vm_compute;lia)ltac:(vm_compute;lia)))).
 - exact(proj1(Inputs 9253%nat ltac:(vm_compute;lia)ltac:(vm_compute;lia))).
 - intros t Bound. apply Steps; do 5(destruct t as[|t];[vm_compute;lia|]);lia. }
 assert(WordSize:size(dut_branch_difference left right)=32%nat).
 { unfold dut_branch_difference. rewrite size_take size_from_Z;reflexivity. }
 apply(Transfer _ WordSize).
 eapply(rf_alu_output_sum_history true (formal_invalid_policy(generated_observation_input inputs k)nil) (history 9253%nat)(history 9254%nat)(history 9255%nat)(history 9256%nat)(history 9257%nat) _ WordSize).
 - exact(proj2(proj2(Inputs 9253%nat ltac:(vm_compute;lia)ltac:(vm_compute;lia)))).
 - exact Sum.
 - apply Steps;vm_compute;lia.
 - apply Steps;vm_compute;lia.
 - apply Steps;vm_compute;lia.
 - apply Steps;vm_compute;lia.

Qed.
Theorem cycle_subtract_step memory inputs k current next before after :
 cycle_transition memory inputs k current next ->cycle_reset inputs k false ->
 cycle_view_at(top_environment current)before ->cycle_view_at(top_environment next)after ->
 
 N.land(to_N(cv_front_instruction before))(reference_instruction_mask(19%nat))=reference_instruction_code(19%nat) ->
 cv_pending_alu after=dut_branch_difference(cv_left before)(cv_right before).
Proof.
 intros[Observe[Legal[NextObserve[NextLegal[committed Run]]]]]Reset Before After Match.
 pose proof(rf_subtract_observed_commit memory inputs k current committed(cv_front_instruction before)(cv_left before)(cv_right before)Observe Legal Run Reset(cva_front_instruction _ _ Before)Match(cva_left_width _ _ Before)(cva_right_width _ _ Before)(cva_left _ _ Before)(cva_right _ _ Before))as Value.
 pose proof(joint_register_run_observed memory inputs(S k)committed next 7752 32 ltac:(apply(List.nth_error_In joint_boundary_registers 57%nat);vm_compute;reflexivity)Run NextObserve)as Copy.
 rewrite(cva_pending_alu _ _ After)Value in Copy.
 exact(f_equal(fun value=>match value with Some(Gval _ word)=>word|_=>[::]end)Copy).
Qed.
