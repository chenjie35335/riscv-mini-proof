Require Import CycleView CycleReferenceGuardedStep RFBitwiseBankInputs RFBitwiseEffectAgreement RFBitwisePendingInvariant RFAluWritebackObserved RFALUData ReferenceInstructionDecode MemoryPendingInvariant FormalLocalHistory.
From Coq Require Import NArith Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
Local Open Scope N_scope.
Theorem cycle_bitwise_reference_advance memory inputs k current next before after lane :
 cycle_transition memory inputs k current next ->cycle_reset inputs k false ->
 cycle_view_at(top_environment current)before ->cycle_view_at(top_environment next)after ->
 cycle_banks_agree before ->cycle_rf_bitwise_pending before ->(lane<6)%coq_nat ->
 N.land(to_N(cv_commit_instruction before))(reference_instruction_mask(rf_bitwise_class lane))=reference_instruction_code(rf_bitwise_class lane) ->
 cycle_reference_effect_step before after.
Proof.
 intros Transition Reset Before After Banks Pending Lane Match.
 pose proof(proj1 Transition)as Observe. pose proof(proj1(proj2 Transition))as Legal.
 destruct(rf_bitwise_bank_inputs memory inputs k current(cv_commit_instruction before)lane(cv_reference_bank before)
 Observe Legal Reset Lane(cva_commit_instruction _ _ Before)Match(cva_reference_bank _ _ Before))as[Controls[Data Destination]].
 apply(cycle_reference_guarded_effect_step memory inputs k current next before after Transition Reset Before After).
 - rewrite<-(Banks 0%nat ltac:(lia)). exact(cycle_dut_x0 memory inputs k current before Observe Legal Before).
 - exact Controls.
 - exact Data.
 - exact Destination.
 - exact(cycle_bitwise_effect_agreement memory inputs k current before lane Observe Legal Reset Before Pending Lane Match).
Qed.
