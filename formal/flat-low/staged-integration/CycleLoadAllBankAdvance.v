Require Import CycleBanksAgreeStep RFModeInvariant RFScalarControl CycleView CycleReferenceGuardedStep RFLoadAllBankInputs RFLoadBankInputs RFLoadEffectAgreement LoadTypeCorrespondence RFAluWritebackObserved RFLoadAllBankInputs RFLoadBankInputs ReferenceInstructionDecode MemoryPendingInvariant FormalLocalHistory.
From Coq Require Import NArith Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
Local Open Scope N_scope.
Theorem cycle_load_reference_advance memory inputs k current next before after lane :
 cycle_transition memory inputs k current next ->cycle_reset inputs k false ->
 cycle_view_at(top_environment current)before ->cycle_view_at(top_environment next)after ->
 cycle_banks_agree before ->cycle_writeback_mode before ->cycle_memory_pending before ->(lane<5)%coq_nat ->
 load_type_is_load(cv_commit_instruction before)lane ->
 cycle_reference_effect_step before after.
Proof.
 intros Transition Reset Before After Banks Mode Pending Lane Match.
 pose proof(proj1 Transition)as Observe. pose proof(proj1(proj2 Transition))as Legal.
 destruct(cycle_load_bank_inputs_all memory inputs k current before lane Observe Legal Reset Before Pending Mode Lane Match)as[Controls[Data Destination]].
 apply(cycle_reference_guarded_effect_step memory inputs k current next before after Transition Reset Before After).
 - rewrite<-(Banks 0%nat ltac:(lia)). exact(cycle_dut_x0 memory inputs k current before Observe Legal Before).
 - exact Controls.
 - exact Data.
 - exact Destination.
 - exact(cycle_load_effect_agreement memory inputs k current before lane Observe Legal Reset Before Pending Mode Lane Match).
Qed.
Theorem cycle_load_banks_agree memory inputs k current next before after lane :
 cycle_transition memory inputs k current next ->cycle_reset inputs k false ->
 cycle_view_at(top_environment current)before ->cycle_view_at(top_environment next)after ->
 cycle_banks_agree before ->cycle_writeback_mode before ->cycle_memory_pending before ->(lane<5)%coq_nat ->
 load_type_is_load(cv_commit_instruction before)lane ->
 cycle_banks_agree after.
Proof.
 intros Transition Reset Before After Banks Mode Pending Lane Match.
 apply(cycle_banks_agree_isa_step memory inputs k current next before after(rf_load_class lane)Transition Reset Before After Banks Mode).
 - exact(cycle_load_reference_advance memory inputs k current next before after lane Transition Reset Before After Banks Mode Pending Lane Match).
 - exact(rf_load_class_bound lane Lane).
 - exact(rf_load_class_match _ lane Lane Match).
Qed.
