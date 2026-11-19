Require Import CycleBanksAgreeStep RFModeInvariant RFScalarControl CycleView CycleReferenceGuardedStep RFShiftBankInputs RFShiftEffectAgreement RFShiftPendingInvariant RFAluWritebackObserved RFShiftCycle ReferenceInstructionDecode MemoryPendingInvariant FormalLocalHistory.
From Coq Require Import NArith Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
Local Open Scope N_scope.
Theorem cycle_shift_reference_advance memory inputs k current next before after immediate lane :
 cycle_transition memory inputs k current next ->cycle_reset inputs k false ->
 cycle_view_at(top_environment current)before ->cycle_view_at(top_environment next)after ->
 cycle_banks_agree before ->cycle_writeback_mode before ->cycle_rf_shift_pending before ->(lane<3)%coq_nat ->
 N.land(to_N(cv_commit_instruction before))(reference_instruction_mask(rf_shift_class immediate lane))=reference_instruction_code(rf_shift_class immediate lane) ->
 cycle_reference_effect_step before after.
Proof.
 intros Transition Reset Before After Banks Mode Pending Lane Match.
 pose proof(proj1 Transition)as Observe. pose proof(proj1(proj2 Transition))as Legal.
 destruct(rf_shift_bank_inputs memory inputs k current(cv_commit_instruction before)immediate lane(cv_reference_bank before) Observe Legal Reset (cva_commit_instruction _ _ Before)Lane Match(cva_reference_bank _ _ Before))as[Controls[Data Destination]].
 apply(cycle_reference_guarded_effect_step memory inputs k current next before after Transition Reset Before After).
 - rewrite<-(Banks 0%nat ltac:(lia)). exact(cycle_dut_x0 memory inputs k current before Observe Legal Before).
 - exact Controls.
 - exact Data.
 - exact Destination.
 - exact(cycle_shift_effect_agreement memory inputs k current before immediate lane Observe Legal Reset Before Mode Pending Lane Match).
Qed.
Theorem cycle_shift_banks_agree memory inputs k current next before after immediate lane :
 cycle_transition memory inputs k current next ->cycle_reset inputs k false ->
 cycle_view_at(top_environment current)before ->cycle_view_at(top_environment next)after ->
 cycle_banks_agree before ->cycle_writeback_mode before ->cycle_rf_shift_pending before ->(lane<3)%coq_nat ->
 N.land(to_N(cv_commit_instruction before))(reference_instruction_mask(rf_shift_class immediate lane))=reference_instruction_code(rf_shift_class immediate lane) ->
 cycle_banks_agree after.
Proof.
 intros Transition Reset Before After Banks Mode Pending Lane Match.
 apply(cycle_banks_agree_isa_step memory inputs k current next before after(rf_shift_class immediate lane)Transition Reset Before After Banks Mode).
 - exact(cycle_shift_reference_advance memory inputs k current next before after immediate lane Transition Reset Before After Banks Mode Pending Lane Match).
 - exact(rf_shift_class_bound immediate lane Lane).
 - exact Match.
Qed.
