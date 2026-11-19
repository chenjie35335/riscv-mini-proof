Require Import CycleView MemoryPendingInvariant DUTBankCycleStep RFModeInvariant RFWriteEffect RFAluWritebackObserved FormalLocalHistory ReferenceInstructionDecode.
From Coq Require Import NArith Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
Local Open Scope N_scope.
Theorem cycle_banks_agree_from_effect_steps before after :
 cycle_banks_agree before ->cycle_reference_effect_step before after ->
 (forall index,(index<32)%coq_nat ->cv_dut_bank after index=rf_apply_effect(cv_dut_bank before)(cycle_pending_effect before)index) ->
 cycle_banks_agree after.
Proof.
 intros Banks Reference DUT index Bound. rewrite(DUT index Bound)(Reference index Bound).
 unfold rf_apply_effect. rewrite(Banks index Bound). reflexivity.
Qed.
Theorem cycle_banks_agree_isa_step memory inputs k current next before after row :
 cycle_transition memory inputs k current next ->cycle_reset inputs k false ->
 cycle_view_at(top_environment current)before ->cycle_view_at(top_environment next)after ->
 cycle_banks_agree before ->cycle_writeback_mode before ->cycle_reference_effect_step before after ->
 (row<37)%coq_nat ->N.land(to_N(cv_commit_instruction before))(reference_instruction_mask row)=reference_instruction_code row ->
 cycle_banks_agree after.
Proof.
 intros Transition Reset Before After Banks Mode Reference Row Match.
 exact(cycle_banks_agree_from_effect_steps before after Banks Reference
 (cycle_dut_bank_isa_step memory inputs k current next before after row Transition Reset Before After Mode Row Match)).
Qed.
