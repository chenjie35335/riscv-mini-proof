Require Import CycleBanksAgreeStep RFModeInvariant RFScalarControl CycleView CycleReferenceGuardedStep RFNonwriteBankInputs RFNonwriteEffectAgreement RFAluWritebackObserved  ReferenceInstructionDecode MemoryPendingInvariant FormalLocalHistory.
From Coq Require Import NArith Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
Local Open Scope N_scope.
Theorem cycle_nonwrite_reference_advance memory inputs k current next before after row :
 cycle_transition memory inputs k current next ->cycle_reset inputs k false ->
 cycle_view_at(top_environment current)before ->cycle_view_at(top_environment next)after ->
 cycle_banks_agree before ->cycle_writeback_mode before ->(row<37)%coq_nat ->
 N.land(to_N(cv_commit_instruction before))(reference_instruction_mask row)=reference_instruction_code row ->
 rf_isa_writes row=false ->
 cycle_reference_effect_step before after.
Proof.
 intros Transition Reset Before After Banks Mode Row Match NoWrite.
 pose proof(proj1 Transition)as Observe. pose proof(proj1(proj2 Transition))as Legal.
 destruct(rf_nonwrite_bank_inputs memory inputs k current(cv_commit_instruction before)row Observe Legal Reset(cva_commit_instruction _ _ Before)Row Match NoWrite)as[Controls[Data Destination]].
 apply(cycle_reference_guarded_effect_step memory inputs k current next before after Transition Reset Before After).
 - rewrite<-(Banks 0%nat ltac:(lia)). exact(cycle_dut_x0 memory inputs k current before Observe Legal Before).
 - exact Controls.
 - exact Data.
 - exact Destination.
 - exact(cycle_nonwrite_effect_agreement memory inputs k current before row Observe Legal Reset Before Row Match NoWrite).
Qed.
Theorem cycle_nonwrite_banks_agree memory inputs k current next before after row :
 cycle_transition memory inputs k current next ->cycle_reset inputs k false ->
 cycle_view_at(top_environment current)before ->cycle_view_at(top_environment next)after ->
 cycle_banks_agree before ->cycle_writeback_mode before ->(row<37)%coq_nat ->
 N.land(to_N(cv_commit_instruction before))(reference_instruction_mask row)=reference_instruction_code row ->
 rf_isa_writes row=false ->
 cycle_banks_agree after.
Proof.
 intros Transition Reset Before After Banks Mode Row Match NoWrite.
 apply(cycle_banks_agree_isa_step memory inputs k current next before after row Transition Reset Before After Banks Mode).
 - exact(cycle_nonwrite_reference_advance memory inputs k current next before after row Transition Reset Before After Banks Mode Row Match NoWrite).
 - exact Row.
 - exact Match.
Qed.
