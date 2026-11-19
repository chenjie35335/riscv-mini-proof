Require Import CycleView RFALUData ReferenceBankObservation JointBoundaryRegisters CoreSocModel ComparisonNodes FormalLocalHistory ReferenceInstructionDecode.
From Coq Require Import NArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque generated_run generated_observe flat_statements flat_memories generated_modules generated_top.
Definition cycle_bitwise_instruction (view:cycle_view) lane :Prop :=
 (lane<6)%coq_nat /\
 N.land(to_N(cv_front_instruction view))(reference_instruction_mask(rf_bitwise_class lane))=reference_instruction_code(rf_bitwise_class lane).
Definition cycle_bitwise_result (view:cycle_view) lane :bits :=
 rf_bitwise_word lane(cv_left view)(rf_bitwise_right lane(cv_front_instruction view)(cv_right view)).
Theorem cycle_bitwise_step memory inputs k current next before after lane :
 cycle_transition memory inputs k current next ->cycle_reset inputs k false ->
 cycle_view_at(top_environment current)before ->cycle_view_at(top_environment next)after ->
 cycle_bitwise_instruction before lane ->
 cv_pending_alu after=cycle_bitwise_result before lane.
Proof.
 intros[Observe[Legal[NextObserve[NextLegal[committed Run]]]]]Reset Before After[Lane Match].
 pose proof(rf_bitwise_observed_commit memory inputs k current committed(cv_front_instruction before)lane(cv_left before)(cv_right before) Observe Legal Run Reset Lane(cva_front_instruction _ _ Before)Match(cva_left_width _ _ Before)(cva_right_width _ _ Before)(cva_left _ _ Before)(cva_right _ _ Before))as Value.
 pose proof(joint_register_run_observed memory inputs(S k)committed next 7752%nat 32%nat ltac:(apply(List.nth_error_In joint_boundary_registers 57%nat);vm_compute;reflexivity)Run NextObserve)as Hold.
 change(VM.find 7752(top_environment next)=VM.find 7752(top_environment committed))in Hold.
 rewrite Value(cva_pending_alu _ _ After)in Hold. inversion Hold;assumption.
Qed.
