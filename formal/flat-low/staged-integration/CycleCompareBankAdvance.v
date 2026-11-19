Require Import CycleBanksAgreeStep RFModeInvariant RFScalarControl CycleView CycleReferenceGuardedStep RFCompareAllBankInputs RFCompareEffectAgreement RFComparePendingInvariant RFAluWritebackObserved RFCompareCycle ReferenceInstructionDecode MemoryPendingInvariant FormalLocalHistory.
From Coq Require Import NArith Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
Local Open Scope N_scope.
Theorem cycle_compare_reference_advance memory inputs k current next before after unsigned :
 cycle_transition memory inputs k current next ->cycle_reset inputs k false ->
 cycle_view_at(top_environment current)before ->cycle_view_at(top_environment next)after ->
 cycle_banks_agree before ->cycle_writeback_mode before ->cycle_rf_compare_pending before ->
 N.land(to_N(cv_commit_instruction before))(reference_instruction_mask(rf_compare_class unsigned))=reference_instruction_code(rf_compare_class unsigned) ->
 cycle_reference_effect_step before after.
Proof.
 intros Transition Reset Before After Banks Mode Pending Match.
 pose proof(proj1 Transition)as Observe. pose proof(proj1(proj2 Transition))as Legal.
 destruct(rf_compare_bank_inputs_all memory inputs k current(cv_commit_instruction before)unsigned(cv_reference_bank before) Observe Legal Reset (cva_commit_instruction _ _ Before)Match(cva_reference_bank _ _ Before))as[Controls[Data Destination]].
 apply(cycle_reference_guarded_effect_step memory inputs k current next before after Transition Reset Before After).
 - rewrite<-(Banks 0%nat ltac:(lia)). exact(cycle_dut_x0 memory inputs k current before Observe Legal Before).
 - exact Controls.
 - exact Data.
 - exact Destination.
 - exact(cycle_compare_effect_agreement memory inputs k current before unsigned Observe Legal Reset Before Mode Pending Match).
Qed.
Theorem cycle_compare_banks_agree memory inputs k current next before after unsigned :
 cycle_transition memory inputs k current next ->cycle_reset inputs k false ->
 cycle_view_at(top_environment current)before ->cycle_view_at(top_environment next)after ->
 cycle_banks_agree before ->cycle_writeback_mode before ->cycle_rf_compare_pending before ->
 N.land(to_N(cv_commit_instruction before))(reference_instruction_mask(rf_compare_class unsigned))=reference_instruction_code(rf_compare_class unsigned) ->
 cycle_banks_agree after.
Proof.
 intros Transition Reset Before After Banks Mode Pending Match.
 apply(cycle_banks_agree_isa_step memory inputs k current next before after(rf_compare_class unsigned)Transition Reset Before After Banks Mode).
 - exact(cycle_compare_reference_advance memory inputs k current next before after unsigned Transition Reset Before After Banks Mode Pending Match).
 - destruct unsigned;vm_compute;lia.
 - exact Match.
Qed.
