Require Import CycleBanksAgreeStep RFModeInvariant RFScalarControl CycleView CycleReferenceGuardedStep RFSubtractAllBankInputs RFSubtractEffectAgreement RFSubtractPendingInvariant RFAluWritebackObserved RFSubtractCycle ReferenceInstructionDecode MemoryPendingInvariant FormalLocalHistory.
From Coq Require Import NArith Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
Local Open Scope N_scope.
Theorem cycle_subtract_reference_advance memory inputs k current next before after :
 cycle_transition memory inputs k current next ->cycle_reset inputs k false ->
 cycle_view_at(top_environment current)before ->cycle_view_at(top_environment next)after ->
 cycle_banks_agree before ->cycle_writeback_mode before ->cycle_rf_subtract_pending before ->
 N.land(to_N(cv_commit_instruction before))(reference_instruction_mask(19%nat))=reference_instruction_code(19%nat) ->
 cycle_reference_effect_step before after.
Proof.
 intros Transition Reset Before After Banks Mode Pending Match.
 pose proof(proj1 Transition)as Observe. pose proof(proj1(proj2 Transition))as Legal.
 destruct(rf_subtract_bank_inputs_all memory inputs k current(cv_commit_instruction before)(cv_reference_bank before) Observe Legal Reset (cva_commit_instruction _ _ Before)Match(cva_reference_bank _ _ Before))as[Controls[Data Destination]].
 apply(cycle_reference_guarded_effect_step memory inputs k current next before after Transition Reset Before After).
 - rewrite<-(Banks 0%nat ltac:(lia)). exact(cycle_dut_x0 memory inputs k current before Observe Legal Before).
 - exact Controls.
 - exact Data.
 - exact Destination.
 - exact(cycle_subtract_effect_agreement memory inputs k current before Observe Legal Reset Before Mode Pending Match).
Qed.
Theorem cycle_subtract_banks_agree memory inputs k current next before after :
 cycle_transition memory inputs k current next ->cycle_reset inputs k false ->
 cycle_view_at(top_environment current)before ->cycle_view_at(top_environment next)after ->
 cycle_banks_agree before ->cycle_writeback_mode before ->cycle_rf_subtract_pending before ->
 N.land(to_N(cv_commit_instruction before))(reference_instruction_mask(19%nat))=reference_instruction_code(19%nat) ->
 cycle_banks_agree after.
Proof.
 intros Transition Reset Before After Banks Mode Pending Match.
 apply(cycle_banks_agree_isa_step memory inputs k current next before after(19%nat)Transition Reset Before After Banks Mode).
 - exact(cycle_subtract_reference_advance memory inputs k current next before after Transition Reset Before After Banks Mode Pending Match).
 - lia.
 - exact Match.
Qed.
