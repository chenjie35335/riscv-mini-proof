Require Import CycleInstructionNop CycleView RFAddCycle RFAddReferenceData RFAluWritebackObserved RFReadPorts RFWriteEffect RFScalarControl ReferenceInstructionDecode MemoryCycleStep MemoryPendingInvariant FormalInstructionResetConstants FormalLocalHistory ObservedJointRegisterConcrete JointBoundaryRegisters CoreSocModel.
From Coq Require Import NArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Definition cycle_rf_add_pending v :Prop :=forall lane,(lane<2)%coq_nat ->
 N.land(to_N(cv_commit_instruction v))(reference_instruction_mask(rf_add_class lane))=reference_instruction_code(rf_add_class lane) ->
 to_nat(rf_instruction_rd(cv_commit_instruction v))<>0%nat ->
 cv_pending_alu v=cycle_add_semantics lane(cv_reference_bank v)(cv_commit_instruction v).
Lemma cycle_rf_add_pending_nop v :cv_commit_instruction v=instruction_nop ->cycle_rf_add_pending v.
Proof. intros Nop lane Lane Match Nonzero. rewrite Nop in Nonzero;exfalso;apply Nonzero;reflexivity. Qed.
Theorem cycle_rf_add_pending_base memory inputs observed v :
 generated_observe memory inputs 0=Some observed ->cycle_view_at(top_environment observed)v ->cycle_rf_add_pending v.
Proof. intros Observe View. apply cycle_rf_add_pending_nop. exact(cycle_initial_commit_nop memory inputs observed v Observe View). Qed.
Theorem cycle_rf_add_pending_reset memory inputs k current next after :
 cycle_transition memory inputs k current next ->cycle_reset inputs k true ->
 cycle_view_at(top_environment next)after ->cycle_rf_add_pending after.
Proof. intros Transition Reset After. apply cycle_rf_add_pending_nop. exact(cycle_reset_commit_nop memory inputs k current next after Transition Reset After). Qed.
Lemma cycle_add_semantics_bank_ext lane instruction left right :
 size instruction=32%nat ->(forall index,(index<32)%coq_nat ->left index=right index) ->
 cycle_add_semantics lane left instruction=cycle_add_semantics lane right instruction.
Proof.
 intros Size Banks. unfold cycle_add_semantics.
 assert(Bound:forall second,(to_nat(rf_instruction_address second instruction)<32)%coq_nat).
 { intro second. pose proof(to_nat_bounded(rf_instruction_address second instruction))as B.
 rewrite(rf_instruction_address_size second instruction Size)in B. exact(elimT ltP B). }
 rewrite(Banks _ (Bound false))(Banks _ (Bound true)). reflexivity.
Qed.
Theorem cycle_add_pending_forwarded memory inputs k current next before after lane :
 cycle_transition memory inputs k current next ->cycle_reset inputs k false ->
 cycle_view_at(top_environment current)before ->cycle_view_at(top_environment next)after ->
 cycle_banks_agree before ->(lane<2)%coq_nat ->
 N.land(to_N(cv_front_instruction before))(reference_instruction_mask(rf_add_class lane))=reference_instruction_code(rf_add_class lane) ->
 cv_pending_alu after=cycle_add_semantics lane
 (rf_apply_effect(cv_reference_bank before)(cycle_pending_effect before))(cv_front_instruction before).
Proof.
 intros Transition Reset Before After Banks Lane Match.
 pose proof(cycle_add_step memory inputs k current next before after lane Transition Reset Before After Lane Match)as Data.
 destruct Transition as[Observe[Legal Rest]].
 pose proof(cycle_forwarded_read memory inputs k current before false Observe Legal Before Banks)as Left.
 pose proof(cycle_forwarded_read memory inputs k current before true Observe Legal Before Banks)as Right.
 rewrite Left Right in Data. exact Data.
Qed.
Theorem cycle_rf_add_pending_normal memory inputs k current next before after :
 cycle_transition memory inputs k current next ->cycle_reset inputs k false ->
 cycle_view_at(top_environment current)before ->cycle_view_at(top_environment next)after ->
 cycle_banks_agree before ->cycle_reference_effect_step before after ->cycle_rf_add_pending after.
Proof.
 intros Transition Reset Before After Banks Advance lane Lane Match Nonzero.
 pose proof(cycle_front_to_commit memory inputs k current next before after Transition Reset Before After)as Instruction.
 rewrite Instruction in Match.
 pose proof(cycle_add_pending_forwarded memory inputs k current next before after lane Transition Reset Before After Banks Lane Match)as Data.
 rewrite Instruction Data. symmetry. apply cycle_add_semantics_bank_ext;[|exact Advance].
 destruct Transition as[Observe[Legal Rest]].
 destruct(observed_joint_register_concrete memory inputs k current 7748%nat 32%nat Observe Legal ltac:(apply(List.nth_error_In joint_boundary_registers 53%nat);vm_compute;reflexivity))as[word[Size Word]].
 rewrite(cva_front_instruction _ _ Before)in Word;inversion Word;subst word;exact Size.
Qed.
