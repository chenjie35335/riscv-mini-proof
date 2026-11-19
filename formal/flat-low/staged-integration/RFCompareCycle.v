Require Import RFRegisterOperands RFCompareArithmetic RFCompareOutput RFCompareInputArithmetic DUTRedirectSemantics RFSubtractArithmetic RFInstructionControl RFALUData RFPipelineEnable RFScalarControl LoadExecuteControl DUTRedirectDecode ControlWritebackKill ReferenceInstructionDecode CoreSocModel ComparisonNodes JointBoundaryRegisters JointUpdateBoundaryHistory.
From Coq Require Import NArith List Lia PeanoNat.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Require Import ConcreteRegisterInitialization ALUOperandTransfer LoadEffectiveAddress LoadImmediateSemantics RFReadPorts.
Definition rf_compare_class unsigned :=if unsigned then 13%nat else 12%nat.
Definition rf_compare_word unsigned left right :=zext_to 32[::rf_compare_bit unsigned left right].
Lemma rf_compare_word_size unsigned left right :size(rf_compare_word unsigned left right)=32%nat.
Proof. unfold rf_compare_word,zext_to. rewrite size_zext;reflexivity. Qed.
Lemma rf_compare_control unsigned :from_N 4(rf_isa_execute_control(rf_compare_class unsigned)3)=[::true;unsigned;true;false].
Proof. destruct unsigned;reflexivity. Qed.
Require Import ReferenceLoadSemantics FormalLocalHistory ALUInputStability ALUOutputTransfer ObservedJointRegisterConcrete EarlyControlStabilityHistory CycleView ReferenceBankObservation.
Theorem rf_compare_observed_commit memory inputs k observed next instruction unsigned left right :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 generated_run memory inputs(S k)=Some next ->
 VM.find 1(formal_external_inputs(generated_observation_input inputs k))=Some(Gval(Fuint 1)[::false]) ->
 VM.find 7748(top_environment observed)=Some(Gval(Fuint 32)instruction) ->
 N.land(to_N instruction)(reference_instruction_mask(rf_compare_class unsigned))=reference_instruction_code(rf_compare_class unsigned) ->
 size left=32%nat ->size right=32%nat ->
 VM.find 7816(top_environment observed)=Some(Gval(Fuint 32)left) ->VM.find 7819(top_environment observed)=Some(Gval(Fuint 32)right) ->
 VM.find 7752(top_environment next)=Some(Gval(Fuint 32)(rf_compare_word unsigned left right)).
Proof.
 intros Observe Legal Next Reset Instruction Match LeftSize RightSize Left Right.
 destruct(observed_joint_register_concrete memory inputs k observed 7748%nat 32%nat Observe Legal load_imm_front_member)as[word[Size Word]]. rewrite Instruction in Word;inversion Word;subst word.
 destruct(rf_alu_observed_transfer_context memory inputs k observed next Observe Legal Next Reset)as[history[Last[Boundary[Steps[Resets Transfer]]]]].
 assert(L:forall t,(55<=t)%coq_nat ->(t<=9259)%coq_nat ->VM.find 7816(history t)=Some(Gval(Fuint 32)left)).
 { intros t Lower Upper. rewrite(early_control_stable_7816_history (generated_observation_input inputs k)nil history 9259 Boundary Steps t 9259 ltac:(lia)ltac:(vm_compute;lia)Upper ltac:(vm_compute;lia))Last;exact Left. }
 assert(R:forall t,(55<=t)%coq_nat ->(t<=9259)%coq_nat ->VM.find 7819(history t)=Some(Gval(Fuint 32)right)).
 { intros t Lower Upper. rewrite(early_control_stable_7819_history (generated_observation_input inputs k)nil history 9259 Boundary Steps t 9259 ltac:(lia)ltac:(vm_compute;lia)Upper ltac:(vm_compute;lia))Last;exact Right. }
 pose proof(rf_register_operand_history (generated_observation_input inputs k)nil history 9259 instruction(rf_compare_class unsigned)left right ltac:(destruct unsigned;vm_compute;lia)ltac:(destruct unsigned;vm_compute;lia)Size LeftSize RightSize Match Boundary Steps ltac:(rewrite Last;exact Instruction)L R)as Inputs.
 assert(Mode:forall t,(100<=t)%coq_nat ->(t<=9259)%coq_nat ->VM.find 1153(history t)=Some(Gval(Fuint 4)[::true;unsigned;true;false])).
 { intros t Lower Upper. rewrite<-(rf_compare_control unsigned). exact(proj2(proj2(Inputs t Lower Upper))). }
 assert(Sum:VM.find 1161(history 9252%nat)=Some(Gval(Fuint 32)(dut_branch_difference left right))).
 { apply(rf_compare_subtract_from_inputs unsigned (formal_invalid_policy(generated_observation_input inputs k)nil)(fun t=>history(Nat.add 9247 t))left right LeftSize RightSize).
 - exact(proj1(proj2(Inputs 9247%nat ltac:(vm_compute;lia)ltac:(vm_compute;lia)))).
 - apply Mode;vm_compute;lia.
 - exact(proj1(proj2(Inputs 9249%nat ltac:(vm_compute;lia)ltac:(vm_compute;lia)))).
 - exact(proj1(Inputs 9250%nat ltac:(vm_compute;lia)ltac:(vm_compute;lia))).
 - intros t Bound. apply Steps;do 5(destruct t as[|t];[vm_compute;lia|]);lia. }
 assert(Bit:VM.find 1170(history 9254%nat)=Some(Gval(Fuint 1)[::rf_compare_bit unsigned left right])).
 { eapply(rf_compare_sign_history unsigned (formal_invalid_policy(generated_observation_input inputs k)nil)(history 9251%nat)(history 9252%nat)(history 9253%nat)(history 9254%nat)left right LeftSize RightSize).
 - exact(proj1(Inputs 9251%nat ltac:(vm_compute;lia)ltac:(vm_compute;lia))).
 - exact(proj1(proj2(Inputs 9251%nat ltac:(vm_compute;lia)ltac:(vm_compute;lia)))).
 - apply Mode;vm_compute;lia.
 - exact Sum.
 - apply Steps;vm_compute;lia.
 - apply Steps;vm_compute;lia.
 - apply Steps;vm_compute;lia. }
 apply(Transfer _ (rf_compare_word_size unsigned left right)).
 eapply(rf_compare_output_history unsigned (formal_invalid_policy(generated_observation_input inputs k)nil)(history 9252%nat)(history 9253%nat)(history 9254%nat)(history 9255%nat)(history 9256%nat)(history 9257%nat)).
 - apply Mode;vm_compute;lia.
 - apply Mode;vm_compute;lia.
 - exact Bit.
 - apply Steps;vm_compute;lia.
 - apply Steps;vm_compute;lia.
 - apply Steps;vm_compute;lia.
 - apply Steps;vm_compute;lia.
 - apply Steps;vm_compute;lia.

Qed.
Theorem cycle_compare_step memory inputs k current next before after unsigned :
 cycle_transition memory inputs k current next ->cycle_reset inputs k false ->
 cycle_view_at(top_environment current)before ->cycle_view_at(top_environment next)after ->
 
 N.land(to_N(cv_front_instruction before))(reference_instruction_mask(rf_compare_class unsigned))=reference_instruction_code(rf_compare_class unsigned) ->
 cv_pending_alu after=rf_compare_word unsigned(cv_left before)(cv_right before).
Proof.
 intros[Observe[Legal[NextObserve[NextLegal[committed Run]]]]]Reset Before After Match.
 pose proof(rf_compare_observed_commit memory inputs k current committed(cv_front_instruction before)unsigned(cv_left before)(cv_right before)Observe Legal Run Reset(cva_front_instruction _ _ Before)Match(cva_left_width _ _ Before)(cva_right_width _ _ Before)(cva_left _ _ Before)(cva_right _ _ Before))as Value.
 pose proof(joint_register_run_observed memory inputs(S k)committed next 7752 32 ltac:(apply(List.nth_error_In joint_boundary_registers 57%nat);vm_compute;reflexivity)Run NextObserve)as Copy.
 rewrite(cva_pending_alu _ _ After)Value in Copy.
 exact(f_equal(fun value=>match value with Some(Gval _ word)=>word|_=>[::]end)Copy).
Qed.
