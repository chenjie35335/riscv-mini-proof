Require Import RFALUData RFPipelineEnable RFScalarControl LoadExecuteControl DUTRedirectDecode ControlWritebackKill ReferenceInstructionDecode CoreSocModel ComparisonNodes JointBoundaryRegisters JointUpdateBoundaryHistory.
From Coq Require Import NArith List Lia PeanoNat.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Definition rf_add_class lane :=if Nat.eqb lane 0 then 11%nat else 0%nat.
Definition rf_add_control lane which :N :=match which with 0%nat=>1|1%nat=>if Nat.eqb lane 0 then 1 else 0|2%nat=>if Nat.eqb lane 0 then 0 else 1|_=>0 end.
Lemma rf_add_decode_control instruction lane which :(lane<2)%coq_nat ->(which<4)%coq_nat ->
 N.land(to_N instruction)(reference_instruction_mask(rf_add_class lane))=reference_instruction_code(rf_add_class lane) ->
 load_execute_decode which(to_N instruction)49=from_N(load_execute_width which)(rf_add_control lane which).
Proof.
 intros Lane Which Match.
 assert(Row:(rf_add_class lane<37)%coq_nat).
 { unfold rf_add_class. destruct(Nat.eqb lane 0);lia. }
 cbn[load_execute_decode].
 repeat match goal with |-context[dut_decode_test(to_N instruction)?stage]=>rewrite(rf_dut_decode_wb_choice instruction stage ltac:(vm_compute;lia))(rf_wb_choice_onehot instruction(rf_add_class lane)(Nat.sub 48 stage)Row ltac:(vm_compute;lia)Match)end.
 do 2(destruct lane as[|lane];[do 4(destruct which as[|which];[reflexivity|]);lia|]);lia.
Qed.
Theorem rf_add_control_history inputs path history limit instruction lane which :
 (lane<2)%coq_nat ->(which<4)%coq_nat ->size instruction=32%nat ->
 N.land(to_N instruction)(reference_instruction_mask(rf_add_class lane))=reference_instruction_code(rf_add_class lane) ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter(formal_invalid_policy inputs path)flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 VM.find 7748(history limit)=Some(Gval(Fuint 32)instruction) ->
 forall time,(55<=time)%coq_nat ->(time<=limit)%coq_nat ->
 VM.find(load_execute_wire_target which true)(history time)=Some(Gval(Fuint(load_execute_width which))(from_N(load_execute_width which)(rf_add_control lane which))).
Proof.
 intros Lane Which Size Match Steps Front time Lower Upper.
 rewrite -(rf_add_decode_control instruction lane which Lane Which Match).
 exact(load_execute_decode_history inputs path history limit instruction which Which Steps Front Size time Lower Upper).
Qed.

Require Import ConcreteRegisterInitialization ALUOperandTransfer LoadEffectiveAddress LoadImmediateSemantics RFReadPorts.
Definition rf_add_operand_right lane instruction right :=if Nat.eqb lane 0 then right else load_i_immediate instruction.
Theorem rf_add_operand_history inputs path history limit instruction lane left right :
 (lane<2)%coq_nat ->size instruction=32%nat ->size left=32%nat ->size right=32%nat ->
 N.land(to_N instruction)(reference_instruction_mask(rf_add_class lane))=reference_instruction_code(rf_add_class lane) ->
 (forall node width,List.In(node,width)joint_boundary_registers ->map_uint_concrete(N.of_nat node)width(history 0%nat)) ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter(formal_invalid_policy inputs path)flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 VM.find 7748(history limit)=Some(Gval(Fuint 32)instruction) ->
 (forall t,(55<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 7816(history t)=Some(Gval(Fuint 32)left)) ->
 (forall t,(55<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 7819(history t)=Some(Gval(Fuint 32)right)) ->
 forall time,(100<=time)%coq_nat ->(time<=limit)%coq_nat ->
 VM.find 1151(history time)=Some(Gval(Fuint 32)left) /\
 VM.find 1152(history time)=Some(Gval(Fuint 32)(rf_add_operand_right lane instruction right)) /\
 VM.find 1153(history time)=Some(Gval(Fuint 4)(from_N 4(0))).
Proof.
 intros Lane Size LeftSize RightSize Match Boundary Steps Front Left Right.
 pose proof(rf_add_control_history inputs path history limit instruction lane)as Control.
 assert(Imm:Nat.eqb lane 0=false ->forall t,(68<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1308(history t)=Some(Gval(Fuint 32)(load_i_immediate instruction))).
 { intros Immediate t Lower Upper. eapply(load_imm_front_register_history _ history limit 55 instruction Size);[| |exact Steps|exact Lower|exact Upper].
 - pose proof(joint_update_register_history_same _ history limit 7748 32 load_imm_front_member Steps limit (Nat.le_refl _))as Hold. change(VM.find 7748(history limit)=VM.find 7748(history 0%nat))in Hold. rewrite<-Hold;exact Front.
 - intros u L U. pose proof(Control 2%nat Lane ltac:(lia)Size Match Steps Front u L U)as C. cbn[rf_add_control]in C. rewrite Immediate in C. exact C. }
 assert(A:forall time,(71<=time)%coq_nat ->(time<=limit)%coq_nat ->VM.find 1151(history time)=Some(Gval(Fuint 32)left)).
 { apply(alu_operand_selected_history _ history limit 68 true left LeftSize Steps false).
 - intros t L U. exact(Control 0%nat Lane ltac:(lia)Size Match Steps Front t ltac:(lia)U).
 - intros t L U. apply Left;lia.
 - intros t L U. destruct(joint_update_register_history_concrete _ history limit 7749 32 ltac:(apply(List.nth_error_In joint_boundary_registers 54%nat);vm_compute;reflexivity) (Boundary 7749%nat 32%nat ltac:(apply(List.nth_error_In joint_boundary_registers 54%nat);vm_compute;reflexivity)) Steps t U)as[word[W V]]. exists(Gval(Fuint 32)word);split;[exact V|reflexivity]. }
 assert(B:forall time,(71<=time)%coq_nat ->(time<=limit)%coq_nat ->VM.find 1152(history time)=Some(Gval(Fuint 32)(rf_add_operand_right lane instruction right))).
 { assert(BSize:size(rf_add_operand_right lane instruction right)=32%nat).
 { unfold rf_add_operand_right. destruct(Nat.eqb lane 0);[exact RightSize|exact(load_i_immediate_size instruction Size)]. }
 apply(alu_operand_selected_history _ history limit 68 (Nat.eqb lane 0)(rf_add_operand_right lane instruction right) BSize Steps true).
 - intros t L U. pose proof(Control 1%nat Lane ltac:(lia)Size Match Steps Front t ltac:(lia)U)as C. cbn[rf_add_control]in C. destruct(Nat.eqb lane 0);exact C.
 - intros t L U. unfold rf_add_operand_right. destruct(Nat.eqb lane 0)eqn:Reg;[apply Right;lia|apply Imm;[reflexivity|exact L|exact U]].
 - intros [|t] L U;try lia. destruct(Nat.eqb lane 0)eqn:Reg.
 + exact(alu_immediate_wire_type _ (history t)(history t)(history(S t))(Steps t ltac:(lia))).
 + exists(Gval(Fuint 32)right);split;[apply Right;lia|reflexivity]. }
 intros [|time] Lower Upper;try lia. split;[apply A;lia|]. split;[apply B;lia|].
 exact(load_operand_wire_value 2%nat _ (history time)(history time)(history(S time))(from_N 4(0))ltac:(lia)(size_from_N _ _)(Control 3%nat Lane ltac:(lia)Size Match Steps Front time ltac:(lia)ltac:(lia))(Steps time ltac:(lia))).
Qed.

Require Import ReferenceLoadSemantics FormalLocalHistory ALUInputStability ALUOutputTransfer ObservedJointRegisterConcrete EarlyControlStabilityHistory CycleView ReferenceBankObservation.
Theorem rf_add_observed_commit memory inputs k observed next instruction lane left right :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 generated_run memory inputs(S k)=Some next ->
 VM.find 1(formal_external_inputs(generated_observation_input inputs k))=Some(Gval(Fuint 1)[::false]) ->
 (lane<2)%coq_nat ->VM.find 7748(top_environment observed)=Some(Gval(Fuint 32)instruction) ->
 N.land(to_N instruction)(reference_instruction_mask(rf_add_class lane))=reference_instruction_code(rf_add_class lane) ->
 size left=32%nat ->size right=32%nat ->
 VM.find 7816(top_environment observed)=Some(Gval(Fuint 32)left) ->VM.find 7819(top_environment observed)=Some(Gval(Fuint 32)right) ->
 VM.find 7752(top_environment next)=Some(Gval(Fuint 32)(reference_load_address left(rf_add_operand_right lane instruction right))).
Proof.
 intros Observe Legal Next Reset Lane Instruction Match LeftSize RightSize Left Right.
 destruct(observed_joint_register_concrete memory inputs k observed 7748%nat 32%nat Observe Legal load_imm_front_member)as[word[Size Word]]. rewrite Instruction in Word;inversion Word;subst word.
 destruct(alu_output_observed_transfer_context memory inputs k observed next Observe Legal Next Reset)as[history[Last[Boundary[Steps[Resets Transfer]]]]].
 assert(L:forall t,(55<=t)%coq_nat ->(t<=9259)%coq_nat ->VM.find 7816(history t)=Some(Gval(Fuint 32)left)).
 { intros t Lower Upper. rewrite(early_control_stable_7816_history (generated_observation_input inputs k)nil history 9259 Boundary Steps t 9259 ltac:(lia)ltac:(vm_compute;lia)Upper ltac:(vm_compute;lia))Last;exact Left. }
 assert(R:forall t,(55<=t)%coq_nat ->(t<=9259)%coq_nat ->VM.find 7819(history t)=Some(Gval(Fuint 32)right)).
 { intros t Lower Upper. rewrite(early_control_stable_7819_history (generated_observation_input inputs k)nil history 9259 Boundary Steps t 9259 ltac:(lia)ltac:(vm_compute;lia)Upper ltac:(vm_compute;lia))Last;exact Right. }
 pose proof(rf_add_operand_history (generated_observation_input inputs k)nil history 9259 instruction lane left right Lane Size LeftSize RightSize Match Boundary Steps ltac:(rewrite Last;exact Instruction)L R)as Inputs.
 assert(RSize:size(rf_add_operand_right lane instruction right)=32%nat).
 { unfold rf_add_operand_right. destruct(Nat.eqb lane 0);[exact RightSize|exact(load_i_immediate_size instruction Size)]. }
 apply(Transfer left(rf_add_operand_right lane instruction right)RSize).
 - exact(proj1(proj2(Inputs 9250%nat ltac:(vm_compute;lia)ltac:(vm_compute;lia)))).
 - exact(proj2(proj2(Inputs 9251%nat ltac:(vm_compute;lia)ltac:(vm_compute;lia)))).
 - exact(proj1(proj2(Inputs 9252%nat ltac:(vm_compute;lia)ltac:(vm_compute;lia)))).
 - exact(proj1(Inputs 9253%nat ltac:(vm_compute;lia)ltac:(vm_compute;lia))).
 - exact(proj2(proj2(Inputs 9253%nat ltac:(vm_compute;lia)ltac:(vm_compute;lia)))).
Qed.
Theorem cycle_add_step memory inputs k current next before after lane :
 cycle_transition memory inputs k current next ->cycle_reset inputs k false ->
 cycle_view_at(top_environment current)before ->cycle_view_at(top_environment next)after ->
 (lane<2)%coq_nat ->
 N.land(to_N(cv_front_instruction before))(reference_instruction_mask(rf_add_class lane))=reference_instruction_code(rf_add_class lane) ->
 cv_pending_alu after=reference_load_address(cv_left before)(rf_add_operand_right lane(cv_front_instruction before)(cv_right before)).
Proof.
 intros[Observe[Legal[NextObserve[NextLegal[committed Run]]]]]Reset Before After Lane Match.
 pose proof(rf_add_observed_commit memory inputs k current committed(cv_front_instruction before)lane(cv_left before)(cv_right before)Observe Legal Run Reset Lane(cva_front_instruction _ _ Before)Match(cva_left_width _ _ Before)(cva_right_width _ _ Before)(cva_left _ _ Before)(cva_right _ _ Before))as Value.
 pose proof(joint_register_run_observed memory inputs(S k)committed next 7752 32 ltac:(apply(List.nth_error_In joint_boundary_registers 57%nat);vm_compute;reflexivity)Run NextObserve)as Copy.
 rewrite(cva_pending_alu _ _ After)Value in Copy.
 exact(f_equal(fun value=>match value with Some(Gval _ word)=>word|_=>[::]end)Copy).
Qed.
