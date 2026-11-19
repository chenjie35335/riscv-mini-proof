Require Import CycleView CycleRFBitwise RFALUData RFAluWritebackObserved RFReadPorts RFWriteEffect CoreSocModel FormalLocalHistory.
From Coq Require Import NArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
Definition cycle_bitwise_semantics lane (bank:rf_bank) instruction :=
 rf_bitwise_word lane(bank(to_nat(rf_instruction_address false instruction)))
 (rf_bitwise_right lane instruction(bank(to_nat(rf_instruction_address true instruction)))).
Theorem cycle_bitwise_pending_forwarded memory inputs k current next before after lane :
 cycle_transition memory inputs k current next ->cycle_reset inputs k false ->
 cycle_view_at(top_environment current)before ->cycle_view_at(top_environment next)after ->
 cycle_banks_agree before ->cycle_bitwise_instruction before lane ->
 cv_pending_alu after=cycle_bitwise_semantics lane
 (rf_apply_effect(cv_reference_bank before)(cycle_pending_effect before))(cv_front_instruction before).
Proof.
 intros Transition Reset Before After Banks Class.
 pose proof(cycle_bitwise_step memory inputs k current next before after lane Transition Reset Before After Class)as Result.
 destruct Transition as[Observe[Legal Rest]].
 pose proof(cycle_forwarded_read memory inputs k current before false Observe Legal Before Banks)as Left.
 pose proof(cycle_forwarded_read memory inputs k current before true Observe Legal Before Banks)as Right.
 unfold cycle_bitwise_result in Result. rewrite Left Right in Result. exact Result.
Qed.
