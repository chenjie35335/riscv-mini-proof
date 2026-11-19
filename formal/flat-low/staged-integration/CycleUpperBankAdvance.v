Require Import CycleBanksAgreeStep RFModeInvariant RFScalarControl CycleView CycleReferenceGuardedStep RFUpperBankInputs RFUpperEffectAgreement RFUpperPendingInvariant RFAluWritebackObserved RFUpperSemantics ReferenceInstructionDecode MemoryPendingInvariant FormalLocalHistory.
From Coq Require Import NArith Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
Local Open Scope N_scope.
Theorem cycle_upper_reference_advance memory inputs k current next before after auipc :
 cycle_transition memory inputs k current next ->cycle_reset inputs k false ->
 cycle_view_at(top_environment current)before ->cycle_view_at(top_environment next)after ->
 cycle_banks_agree before ->cycle_writeback_mode before ->cycle_rf_upper_pending before ->cycle_pc_phase before ->
 N.land(to_N(cv_commit_instruction before))(reference_instruction_mask(rf_upper_class auipc))=reference_instruction_code(rf_upper_class auipc) ->
 cycle_reference_effect_step before after.
Proof.
 intros Transition Reset Before After Banks Mode Pending Phase Match.
 pose proof(proj1 Transition)as Observe. pose proof(proj1(proj2 Transition))as Legal.
 destruct(rf_upper_bank_inputs memory inputs k current(cv_commit_instruction before)auipc(cv_reference_pc before) Observe Legal Reset
 (cva_commit_instruction _ _ Before)Match(cva_reference_pc_width _ _ Before)(cva_reference_pc _ _ Before))as[Controls[Data Destination]].
 apply(cycle_reference_guarded_effect_step memory inputs k current next before after Transition Reset Before After).
 - rewrite<-(Banks 0%nat ltac:(lia)). exact(cycle_dut_x0 memory inputs k current before Observe Legal Before).
 - exact Controls.
 - exact Data.
 - exact Destination.
 - exact(cycle_upper_effect_agreement memory inputs k current before auipc Observe Legal Reset Before Mode Phase Pending Match).
Qed.
Theorem cycle_upper_banks_agree memory inputs k current next before after auipc :
 cycle_transition memory inputs k current next ->cycle_reset inputs k false ->
 cycle_view_at(top_environment current)before ->cycle_view_at(top_environment next)after ->
 cycle_banks_agree before ->cycle_writeback_mode before ->cycle_rf_upper_pending before ->cycle_pc_phase before ->
 N.land(to_N(cv_commit_instruction before))(reference_instruction_mask(rf_upper_class auipc))=reference_instruction_code(rf_upper_class auipc) ->
 cycle_banks_agree after.
Proof.
 intros Transition Reset Before After Banks Mode Pending Phase Match.
 apply(cycle_banks_agree_isa_step memory inputs k current next before after(rf_upper_class auipc)Transition Reset Before After Banks Mode).
 - exact(cycle_upper_reference_advance memory inputs k current next before after auipc Transition Reset Before After Banks Mode Pending Phase Match).
 - exact(rf_upper_class_bound auipc).
 - exact Match.
Qed.
