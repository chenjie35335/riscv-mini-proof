Require Import RFLinkBankInputs RFLinkEffectAgreement RFLinkReferenceEffect ReferenceBankCycleInputs RFModeInvariant RFScalarControl RFAluWritebackObserved CycleView CycleReferenceGuardedStep CycleBanksAgreeStep MemoryPendingInvariant ReferenceInstructionDecode FormalLocalHistory CycleJALAlignment JALRTakenInvariant PCRelativePendingInvariant CycleRedirectDecision JALRPendingAlignment JALRAddressCycle.
From Coq Require Import NArith Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Theorem cycle_link_reference_advance memory inputs k current next before after lane csr :
 cycle_transition memory inputs k current next ->cycle_reset inputs k false ->
 cycle_view_at(top_environment current)before ->cycle_view_at(top_environment next)after ->
 cycle_banks_agree before ->cycle_writeback_mode before ->cycle_pc_aligned before ->cycle_pc_relative_pending before ->cycle_redirect_decision before ->
 cycle_jalr_pending before ->cycle_jalr_taken before ->(lane<2)%coq_nat ->
 N.land(to_N(cv_commit_instruction before))(reference_instruction_mask(rf_link_class lane))=reference_instruction_code(rf_link_class lane) ->
 VM.find 7332(top_environment current)=Some(Gval(Fuint 32)csr) ->size csr=32%nat ->
 cycle_reference_effect_step before after.
Proof.
 intros Transition Reset Before After Banks Mode PC Pending Decision JPending JTaken Lane Match Csr CsrSize.
 pose proof(proj1 Transition)as Observe. pose proof(proj1(proj2 Transition))as Legal.
 assert(Alignment:VM.find(rf_link_alignment lane)(top_environment current)=Some(Gval(Fuint 1)[::true])).
 { destruct lane as[|[|lane]];[| |lia].
   - exact(cycle_jal_alignment_guard memory inputs k current before csr Observe Legal Reset Before Match(cycle_link_active memory inputs k current before 0%nat Observe Legal Before ltac:(lia)Match)PC Pending Decision Csr CsrSize).
   - exact(cycle_jalr_alignment_from_invariants memory inputs k current before csr Observe Legal Reset Before JPending JTaken Match Csr CsrSize). }
 destruct(cycle_link_bank_inputs memory inputs k current before lane Observe Legal Reset Before Lane Match Alignment)as[Controls[Data Destination]].
 apply(cycle_reference_guarded_effect_step memory inputs k current next before after Transition Reset Before After).
 - rewrite<-(Banks 0%nat ltac:(lia)). exact(cycle_dut_x0 memory inputs k current before Observe Legal Before).
 - exact Controls.
 - exact Data.
 - exact Destination.
 - exact(cycle_link_effect_with_alignment memory inputs k current before lane Observe Legal Reset Before Mode(proj2 PC)Lane Match Alignment).
Qed.
Theorem cycle_link_banks_agree memory inputs k current next before after lane csr :
 cycle_transition memory inputs k current next ->cycle_reset inputs k false ->
 cycle_view_at(top_environment current)before ->cycle_view_at(top_environment next)after ->
 cycle_banks_agree before ->cycle_writeback_mode before ->cycle_pc_aligned before ->cycle_pc_relative_pending before ->cycle_redirect_decision before ->
 cycle_jalr_pending before ->cycle_jalr_taken before ->(lane<2)%coq_nat ->
 N.land(to_N(cv_commit_instruction before))(reference_instruction_mask(rf_link_class lane))=reference_instruction_code(rf_link_class lane) ->
 VM.find 7332(top_environment current)=Some(Gval(Fuint 32)csr) ->size csr=32%nat ->
 cycle_banks_agree after.
Proof.
 intros Transition Reset Before After Banks Mode PC Pending Decision JPending JTaken Lane Match Csr CsrSize.
 apply(cycle_banks_agree_isa_step memory inputs k current next before after(rf_link_class lane)Transition Reset Before After Banks Mode).
 - exact(cycle_link_reference_advance memory inputs k current next before after lane csr Transition Reset Before After Banks Mode PC Pending Decision JPending JTaken Lane Match Csr CsrSize).
 - unfold rf_link_class;lia.
 - exact Match.
Qed.
