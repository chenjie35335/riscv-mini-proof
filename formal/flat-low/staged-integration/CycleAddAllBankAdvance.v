Require Import CycleNopBankAdvance FormalInstructionResetConstants CycleBanksAgreeStep RFModeInvariant RFScalarControl CycleView CycleReferenceGuardedStep RFAddAllBankInputs RFAddEffectAgreement RFAddPendingInvariant RFAluWritebackObserved RFAddCycle ReferenceInstructionDecode MemoryPendingInvariant FormalLocalHistory.
From Coq Require Import NArith Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
Local Open Scope N_scope.
Theorem cycle_add_reference_advance_nonnop memory inputs k current next before after lane :
 cycle_transition memory inputs k current next ->cycle_reset inputs k false ->
 cycle_view_at(top_environment current)before ->cycle_view_at(top_environment next)after ->
 cycle_banks_agree before ->cycle_writeback_mode before ->cycle_rf_add_pending before ->(lane<2)%coq_nat ->
 N.land(to_N(cv_commit_instruction before))(reference_instruction_mask(rf_add_class lane))=reference_instruction_code(rf_add_class lane) ->
 cv_commit_instruction before<>instruction_nop ->
 cycle_reference_effect_step before after.
Proof.
 intros Transition Reset Before After Banks Mode Pending Lane Match NonNop.
 pose proof(proj1 Transition)as Observe. pose proof(proj1(proj2 Transition))as Legal.
 destruct(rf_add_bank_inputs_nonnop memory inputs k current(cv_commit_instruction before)lane(cv_reference_bank before) Observe Legal Reset Lane (cva_commit_instruction _ _ Before)Match NonNop(cva_reference_bank _ _ Before))as[Controls[Data Destination]].
 apply(cycle_reference_guarded_effect_step memory inputs k current next before after Transition Reset Before After).
 - rewrite<-(Banks 0%nat ltac:(lia)). exact(cycle_dut_x0 memory inputs k current before Observe Legal Before).
 - exact Controls.
 - exact Data.
 - exact Destination.
 - exact(cycle_add_effect_agreement memory inputs k current before lane Observe Legal Reset Before Mode Pending Lane Match).
Qed.
Theorem cycle_add_banks_agree_nonnop memory inputs k current next before after lane :
 cycle_transition memory inputs k current next ->cycle_reset inputs k false ->
 cycle_view_at(top_environment current)before ->cycle_view_at(top_environment next)after ->
 cycle_banks_agree before ->cycle_writeback_mode before ->cycle_rf_add_pending before ->(lane<2)%coq_nat ->
 N.land(to_N(cv_commit_instruction before))(reference_instruction_mask(rf_add_class lane))=reference_instruction_code(rf_add_class lane) ->
 cv_commit_instruction before<>instruction_nop ->
 cycle_banks_agree after.
Proof.
 intros Transition Reset Before After Banks Mode Pending Lane Match NonNop.
 apply(cycle_banks_agree_isa_step memory inputs k current next before after(rf_add_class lane)Transition Reset Before After Banks Mode).
 - exact(cycle_add_reference_advance_nonnop memory inputs k current next before after lane Transition Reset Before After Banks Mode Pending Lane Match NonNop).
 - do 2(destruct lane as[|lane];[vm_compute;lia|]);lia.
 - exact Match.
Qed.

Theorem cycle_add_reference_advance_all memory inputs k current next before after lane :
 cycle_transition memory inputs k current next ->cycle_reset inputs k false ->
 cycle_view_at(top_environment current)before ->cycle_view_at(top_environment next)after ->
 cycle_banks_agree before ->cycle_writeback_mode before ->cycle_rf_add_pending before ->(lane<2)%coq_nat ->
 N.land(to_N(cv_commit_instruction before))(reference_instruction_mask(rf_add_class lane))=reference_instruction_code(rf_add_class lane) ->
 cycle_reference_effect_step before after.
Proof.
 intros Transition Reset Before After Banks Mode Pending Lane Match.
 destruct(List.list_eq_dec Bool.bool_dec (cv_commit_instruction before)instruction_nop)as[Nop|NonNop].
 - exact(cycle_nop_reference_advance memory inputs k current next before after Transition Reset Before After Banks Nop).
 - exact(cycle_add_reference_advance_nonnop memory inputs k current next before after lane Transition Reset Before After Banks Mode Pending Lane Match NonNop).
Qed.
Theorem cycle_add_banks_agree_all memory inputs k current next before after lane :
 cycle_transition memory inputs k current next ->cycle_reset inputs k false ->
 cycle_view_at(top_environment current)before ->cycle_view_at(top_environment next)after ->
 cycle_banks_agree before ->cycle_writeback_mode before ->cycle_rf_add_pending before ->(lane<2)%coq_nat ->
 N.land(to_N(cv_commit_instruction before))(reference_instruction_mask(rf_add_class lane))=reference_instruction_code(rf_add_class lane) ->
 cycle_banks_agree after.
Proof.
 intros Transition Reset Before After Banks Mode Pending Lane Match.
 apply(cycle_banks_agree_isa_step memory inputs k current next before after(rf_add_class lane)Transition Reset Before After Banks Mode).
 - exact(cycle_add_reference_advance_all memory inputs k current next before after lane Transition Reset Before After Banks Mode Pending Lane Match).
 - do 2(destruct lane as[|lane];[vm_compute;lia|]);lia.
 - exact Match.
Qed.
