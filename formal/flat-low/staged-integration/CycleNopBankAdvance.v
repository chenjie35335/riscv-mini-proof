Require Import CycleBanksAgreeStep CycleReferenceGuardedStep ReferenceBankNopObserved RFBitwiseEffectAgreement RFModeInvariant RFAluWritebackObserved RFWriteEffect CycleView MemoryPendingInvariant FormalInstructionResetConstants FormalLocalHistory.
From Coq Require Import NArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Theorem cycle_nop_reference_advance memory inputs k current next before after :
 cycle_transition memory inputs k current next ->cycle_reset inputs k false ->
 cycle_view_at(top_environment current)before ->cycle_view_at(top_environment next)after ->
 cycle_banks_agree before ->cv_commit_instruction before=instruction_nop ->
 cycle_reference_effect_step before after.
Proof.
 intros[Observe[Legal[NextObserve[NextLegal[committed Run]]]]]Reset Before After Banks Nop.
 assert(Zero:cv_reference_bank before 0%nat=nseq 32 false).
 { rewrite<-(Banks 0%nat ltac:(lia)). exact(cycle_dut_x0 memory inputs k current before Observe Legal Before). }
 assert(Instruction:VM.find 7750(top_environment current)=Some(Gval(Fuint 32)instruction_nop)).
 { rewrite(cva_commit_instruction _ _ Before) Nop;reflexivity. }
 pose proof(reference_bank_nop_observed_next memory inputs k current committed next(cv_reference_bank before)Observe Legal Run NextObserve Reset(cva_reference_bank _ _ Before)Zero Instruction)as Actual.
 assert(Destination:to_nat(cv_destination before)=0%nat).
 { rewrite(cycle_destination_observed memory inputs k current before Observe Legal Before) Nop;reflexivity. }
 intros index Bound.
 pose proof(proj2(Actual index Bound))as Value.
 rewrite(proj2(cva_reference_bank _ _ After index Bound))in Value.
 assert(Same:cv_reference_bank after index=cv_reference_bank before index)by(congruence).
 rewrite Same. unfold cycle_pending_effect,rf_apply_effect. rewrite Destination.
 destruct(index==0%nat)eqn:AtZero.
 - move/eqP:AtZero=>Index;subst index;exact Zero.
 - destruct(cv_write_enabled before);[rewrite AtZero|];reflexivity.
Qed.
Theorem cycle_nop_banks_agree memory inputs k current next before after :
 cycle_transition memory inputs k current next ->cycle_reset inputs k false ->
 cycle_view_at(top_environment current)before ->cycle_view_at(top_environment next)after ->
 cycle_banks_agree before ->cycle_writeback_mode before ->cv_commit_instruction before=instruction_nop ->
 cycle_banks_agree after.
Proof.
 intros Transition Reset Before After Banks Mode Nop.
 apply(cycle_banks_agree_isa_step memory inputs k current next before after 0%nat Transition Reset Before After Banks Mode).
 - exact(cycle_nop_reference_advance memory inputs k current next before after Transition Reset Before After Banks Nop).
 - lia.
 - rewrite Nop;reflexivity.
Qed.
