Require Import CycleISAReferenceAdvance CycleWriteDataAssertion RFArithmeticPendingClosure StorePendingInvariant MemoryPendingInvariant
 CycleView ReferenceInstructionDecode RFScalarControl FormalLocalHistory CoreSocModel.
From Coq Require Import NArith Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque generated_modules generated_top.
Theorem cycle_data_normal_step memory inputs k current next before after row csr :
 cycle_transition memory inputs k current next ->cycle_reset inputs k false ->
 cycle_view_at(top_environment current)before ->cycle_view_at(top_environment next)after ->
 cycle_banks_agree before ->cycle_isa_pending before ->
 (row<37)%coq_nat ->N.land(to_N(cv_commit_instruction before))(reference_instruction_mask row)=reference_instruction_code row ->
 VM.find 7332(top_environment current)=Some(Gval(Fuint 32)csr) ->size csr=32%nat ->
 cycle_banks_agree after /\cycle_rf_arithmetic_pending after /\
 cycle_memory_pending after /\cycle_store_pending(top_environment next)after /\
 generated_assert_m0_5_local(top_environment next).
Proof.
 intros Transition Reset Before After Banks Pending Row Match CSR CSRSize.
 pose proof(cycle_isa_reference_advance memory inputs k current next before after row csr
 Transition Reset Before After Banks Pending Row Match CSR CSRSize)as Effect.
 pose proof(cycle_isa_banks_agree memory inputs k current next before after row csr
 Transition Reset Before After Banks Pending Row Match CSR CSRSize)as NextBanks.
 pose proof(cycle_rf_arithmetic_pending_normal memory inputs k current next before after Transition Reset Before After Banks Effect)as Arithmetic.
 pose proof(cycle_memory_pending_normal memory inputs k current next before after Transition Reset Before After Banks Effect)as Memory.
 pose proof(cycle_store_pending_normal memory inputs k current next before after Transition Reset Before After Banks Effect)as Store.
 split;[exact NextBanks|]. split;[exact Arithmetic|]. split;[exact Memory|]. split;[exact Store|].
 destruct Transition as[Observe[Legal[NextObserve[NextLegal Run]]]].
 exact(cycle_write_data_assertion memory inputs(S k)next after NextObserve NextLegal After Memory Store).
Qed.
Require Import CycleBanksReset.
Theorem cycle_data_base memory inputs observed v :
 generated_observe memory inputs 0=Some observed ->generated_legal_trace memory inputs 0 ->
 cycle_view_at(top_environment observed)v ->
 cycle_banks_agree v /\cycle_rf_arithmetic_pending v /\
 cycle_memory_pending v /\cycle_store_pending(top_environment observed)v /\
 generated_assert_m0_5_local(top_environment observed).
Proof.
 intros Observe Legal View.
 pose proof(cycle_memory_pending_base memory inputs observed v Observe View)as Memory.
 pose proof(cycle_store_pending_base memory inputs observed v Observe View)as Store.
 split;[exact(cycle_banks_agree_base memory inputs observed v Observe View)|].
 split;[exact(cycle_rf_arithmetic_pending_base memory inputs observed v Observe View)|].
 split;[exact Memory|]. split;[exact Store|].
 exact(cycle_write_data_assertion memory inputs 0 observed v Observe Legal View Memory Store).
Qed.
Theorem cycle_data_reset_step memory inputs k current next before after :
 cycle_transition memory inputs k current next ->cycle_reset inputs k true ->
 cycle_view_at(top_environment current)before ->cycle_view_at(top_environment next)after ->
 cycle_banks_agree after /\cycle_rf_arithmetic_pending after /\
 cycle_memory_pending after /\cycle_store_pending(top_environment next)after /\
 generated_assert_m0_5_local(top_environment next).
Proof.
 intros Transition Reset Before After.
 pose proof(cycle_memory_pending_reset memory inputs k current next after Transition Reset After)as Memory.
 pose proof(cycle_store_pending_reset memory inputs k current next after Transition Reset After)as Store.
 split;[exact(cycle_banks_agree_reset memory inputs k current next before after Transition Reset Before After)|].
 split;[exact(cycle_rf_arithmetic_pending_reset memory inputs k current next after Transition Reset After)|].
 split;[exact Memory|]. split;[exact Store|].
 destruct Transition as[Observe[Legal[NextObserve[NextLegal Run]]]].
 exact(cycle_write_data_assertion memory inputs(S k)next after NextObserve NextLegal After Memory Store).
Qed.
