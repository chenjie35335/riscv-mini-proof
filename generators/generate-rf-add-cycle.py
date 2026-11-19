#!/usr/bin/env python3
"""Reuse the verified operand-selection proof schema for ADD and ADDI."""
from pathlib import Path
root=Path(__file__).resolve().parents[2]
s=(root/'formal/flat-low/staged-integration/RFALUData.v').read_text()
a=s[s.index('Lemma rf_bitwise_decode_control'):s.index('\nRequire Import FormalLocalHistory FormalObservationCommit')]
a=a.replace('rf_bitwise','rf_add').replace('(lane<6)','(lane<2)').replace('Nat.ltb lane 3','Nat.eqb lane 0').replace('do 6','do 2')
a=a.replace('unfold rf_add_class. destruct(Nat.eqb lane 0)eqn:Small;[apply Nat.ltb_lt in Small|];lia.','unfold rf_add_class. destruct(Nat.eqb lane 0);lia.')
a=a.replace('N.of_nat(Nat.add 2(Nat.modulo lane 3))','0')
a=a.replace('rf_add_right','rf_add_operand_right')
head='''Require Import RFALUData RFPipelineEnable RFScalarControl LoadExecuteControl DUTRedirectDecode ControlWritebackKill ReferenceInstructionDecode CoreSocModel ComparisonNodes JointBoundaryRegisters JointUpdateBoundaryHistory.
From Coq Require Import NArith List Lia PeanoNat.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Definition rf_add_class lane :=if Nat.eqb lane 0 then 11%nat else 0%nat.
Definition rf_add_control lane which :N :=match which with 0%nat=>1|1%nat=>if Nat.eqb lane 0 then 1 else 0|2%nat=>if Nat.eqb lane 0 then 0 else 1|_=>0 end.
'''
tail='''
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
'''
(root/'formal/flat-low/staged-integration/RFAddCycle.v').write_text(head+a+tail)
