Require Import CycleInstructionNop CycleView RFUpperDUTCycle RFUpperSemantics PCRelativeAddressCycle
 ReferenceInstructionDecode MemoryCycleStep FormalInstructionResetConstants FormalLocalHistory CoreSocModel.
From Coq Require Import NArith Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque generated_modules generated_top.
Definition cycle_rf_upper_pending v :Prop :=forall auipc,
 N.land(to_N(cv_commit_instruction v))(reference_instruction_mask(rf_upper_class auipc))=reference_instruction_code(rf_upper_class auipc) ->
 cv_pending_alu v=cycle_upper_semantics auipc(cv_commit_pc v)(cv_commit_instruction v).
Lemma rf_upper_not_nop auipc :
 N.land(to_N instruction_nop)(reference_instruction_mask(rf_upper_class auipc))<>reference_instruction_code(rf_upper_class auipc).
Proof. destruct auipc;vm_compute;discriminate. Qed.
Lemma cycle_rf_upper_pending_nop v :cv_commit_instruction v=instruction_nop ->cycle_rf_upper_pending v.
Proof.
 intros Nop auipc Match. rewrite Nop in Match. exfalso. exact(rf_upper_not_nop auipc Match).
Qed.
Theorem cycle_rf_upper_pending_base memory inputs observed v :
 generated_observe memory inputs 0=Some observed ->cycle_view_at(top_environment observed)v ->cycle_rf_upper_pending v.
Proof. intros Observe View. apply cycle_rf_upper_pending_nop. exact(cycle_initial_commit_nop memory inputs observed v Observe View). Qed.
Theorem cycle_rf_upper_pending_reset memory inputs k current next after :
 cycle_transition memory inputs k current next ->cycle_reset inputs k true ->
 cycle_view_at(top_environment next)after ->cycle_rf_upper_pending after.
Proof. intros Transition Reset After. apply cycle_rf_upper_pending_nop. exact(cycle_reset_commit_nop memory inputs k current next after Transition Reset After). Qed.
Theorem cycle_rf_upper_pending_normal memory inputs k current next before after :
 cycle_transition memory inputs k current next ->cycle_reset inputs k false ->
 cycle_view_at(top_environment current)before ->cycle_view_at(top_environment next)after ->
 cycle_rf_upper_pending after.
Proof.
 intros Transition Reset Before After auipc Match.
 pose proof(cycle_front_to_commit memory inputs k current next before after Transition Reset Before After)as Instruction.
 pose proof(cycle_pc_front_to_commit memory inputs k current next before after Transition Reset Before After)as PC.
 rewrite Instruction in Match. rewrite Instruction PC.
 exact(cycle_upper_step memory inputs k current next before after auipc Transition Reset Before After Match).
Qed.
Theorem cycle_rf_upper_pending_preserved memory inputs k current next before after reset :
 cycle_transition memory inputs k current next ->cycle_reset inputs k reset ->
 cycle_view_at(top_environment current)before ->cycle_view_at(top_environment next)after ->
 cycle_rf_upper_pending after.
Proof.
 intros Transition Reset Before After. destruct reset.
 - exact(cycle_rf_upper_pending_reset memory inputs k current next after Transition Reset After).
 - exact(cycle_rf_upper_pending_normal memory inputs k current next before after Transition Reset Before After).
Qed.
