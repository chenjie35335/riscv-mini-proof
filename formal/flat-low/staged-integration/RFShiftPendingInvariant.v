Require Import CycleInstructionNop CycleView RFShiftCycle RFShiftSemanticBank RFAluWritebackObserved RFReadPorts RFWriteEffect RFScalarControl ReferenceInstructionDecode MemoryCycleStep MemoryPendingInvariant FormalInstructionResetConstants FormalLocalHistory ObservedJointRegisterConcrete JointBoundaryRegisters CoreSocModel.
From Coq Require Import NArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Definition cycle_rf_shift_pending v :Prop :=forall immediate lane,(lane<3)%coq_nat ->
 N.land(to_N(cv_commit_instruction v))(reference_instruction_mask(rf_shift_class immediate lane))=reference_instruction_code(rf_shift_class immediate lane) ->
 to_nat(rf_instruction_rd(cv_commit_instruction v))<>0%nat ->
 cv_pending_alu v=cycle_shift_semantics immediate lane(cv_reference_bank v)(cv_commit_instruction v).
Lemma cycle_rf_shift_pending_nop v :cv_commit_instruction v=instruction_nop ->cycle_rf_shift_pending v.
Proof. intros Nop immediate lane Lane Match Nonzero. rewrite Nop in Nonzero;exfalso;apply Nonzero;reflexivity. Qed.
Theorem cycle_rf_shift_pending_base memory inputs observed v :
 generated_observe memory inputs 0=Some observed ->cycle_view_at(top_environment observed)v ->cycle_rf_shift_pending v.
Proof. intros Observe View. apply cycle_rf_shift_pending_nop. exact(cycle_initial_commit_nop memory inputs observed v Observe View). Qed.
Theorem cycle_rf_shift_pending_reset memory inputs k current next after :
 cycle_transition memory inputs k current next ->cycle_reset inputs k true ->
 cycle_view_at(top_environment next)after ->cycle_rf_shift_pending after.
Proof. intros Transition Reset After. apply cycle_rf_shift_pending_nop. exact(cycle_reset_commit_nop memory inputs k current next after Transition Reset After). Qed.
Theorem cycle_shift_pending_forwarded memory inputs k current next before after immediate lane :
 cycle_transition memory inputs k current next ->cycle_reset inputs k false ->
 cycle_view_at(top_environment current)before ->cycle_view_at(top_environment next)after ->
 cycle_banks_agree before ->(lane<3)%coq_nat ->
 N.land(to_N(cv_front_instruction before))(reference_instruction_mask(rf_shift_class immediate lane))=reference_instruction_code(rf_shift_class immediate lane) ->
 cv_pending_alu after=cycle_shift_semantics immediate lane
 (rf_apply_effect(cv_reference_bank before)(cycle_pending_effect before))(cv_front_instruction before).
Proof.
 intros Transition Reset Before After Banks Lane Match.
 pose proof(cycle_shift_step memory inputs k current next before after immediate lane Transition Reset Before After Lane Match)as Data.
 destruct Transition as[Observe[Legal Rest]].
 pose proof(cycle_forwarded_read memory inputs k current before false Observe Legal Before Banks)as Left.
 pose proof(cycle_forwarded_read memory inputs k current before true Observe Legal Before Banks)as Right.
 rewrite Left Right in Data. exact Data.
Qed.
Theorem cycle_rf_shift_pending_normal memory inputs k current next before after :
 cycle_transition memory inputs k current next ->cycle_reset inputs k false ->
 cycle_view_at(top_environment current)before ->cycle_view_at(top_environment next)after ->
 cycle_banks_agree before ->cycle_reference_effect_step before after ->cycle_rf_shift_pending after.
Proof.
 intros Transition Reset Before After Banks Advance immediate lane Lane Match Nonzero.
 pose proof(cycle_front_to_commit memory inputs k current next before after Transition Reset Before After)as Instruction.
 rewrite Instruction in Match.
 pose proof(cycle_shift_pending_forwarded memory inputs k current next before after immediate lane Transition Reset Before After Banks Lane Match)as Data.
 rewrite Instruction Data. symmetry. apply cycle_shift_semantics_bank_ext;[|exact Advance].
 destruct Transition as[Observe[Legal Rest]].
 destruct(observed_joint_register_concrete memory inputs k current 7748%nat 32%nat Observe Legal ltac:(apply(List.nth_error_In joint_boundary_registers 53%nat);vm_compute;reflexivity))as[word[Size Word]].
 rewrite(cva_front_instruction _ _ Before)in Word;inversion Word;subst word;exact Size.
Qed.
