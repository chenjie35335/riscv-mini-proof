Require Import RFAddPendingInvariant RFBitwisePendingInvariant RFSubtractPendingInvariant RFComparePendingInvariant RFCompareImmediatePendingInvariant RFShiftPendingInvariant RFUpperPendingInvariant RFModeReachability MemoryPendingInvariant CycleView CoreSocModel FormalLocalHistory.
Local Opaque generated_modules generated_top.
Definition cycle_rf_arithmetic_pending v : Prop :=
 cycle_rf_add_pending v /\
 cycle_rf_bitwise_pending v /\
 cycle_rf_subtract_pending v /\
 cycle_rf_compare_pending v /\
 cycle_rf_compare_immediate_pending v /\
 cycle_rf_shift_pending v /\
 cycle_rf_upper_pending v.
Theorem cycle_rf_arithmetic_pending_base memory inputs observed v :
 generated_observe memory inputs 0=Some observed ->cycle_view_at(top_environment observed)v ->cycle_rf_arithmetic_pending v.
Proof. intros Observe View. unfold cycle_rf_arithmetic_pending.
 split;[exact(cycle_rf_add_pending_base memory inputs observed v Observe View)|].
  split;[exact(cycle_rf_bitwise_pending_base memory inputs observed v Observe View)|].
  split;[exact(cycle_rf_subtract_pending_base memory inputs observed v Observe View)|].
  split;[exact(cycle_rf_compare_pending_base memory inputs observed v Observe View)|].
  split;[exact(cycle_rf_compare_immediate_pending_base memory inputs observed v Observe View)|].
  split;[exact(cycle_rf_shift_pending_base memory inputs observed v Observe View)|].
  exact(cycle_rf_upper_pending_base memory inputs observed v Observe View).
Qed.
Theorem cycle_rf_arithmetic_pending_reset memory inputs k current next after :
 cycle_transition memory inputs k current next ->cycle_reset inputs k true ->cycle_view_at(top_environment next)after ->cycle_rf_arithmetic_pending after.
Proof. intros Transition Reset After. unfold cycle_rf_arithmetic_pending.
 split;[exact(cycle_rf_add_pending_reset memory inputs k current next after Transition Reset After)|].
  split;[exact(cycle_rf_bitwise_pending_reset memory inputs k current next after Transition Reset After)|].
  split;[exact(cycle_rf_subtract_pending_reset memory inputs k current next after Transition Reset After)|].
  split;[exact(cycle_rf_compare_pending_reset memory inputs k current next after Transition Reset After)|].
  split;[exact(cycle_rf_compare_immediate_pending_reset memory inputs k current next after Transition Reset After)|].
  split;[exact(cycle_rf_shift_pending_reset memory inputs k current next after Transition Reset After)|].
  exact(cycle_rf_upper_pending_reset memory inputs k current next after Transition Reset After).
Qed.
Theorem cycle_rf_arithmetic_pending_normal memory inputs k current next before after :
 cycle_transition memory inputs k current next ->cycle_reset inputs k false ->
 cycle_view_at(top_environment current)before ->cycle_view_at(top_environment next)after ->
 cycle_banks_agree before ->cycle_reference_effect_step before after ->cycle_rf_arithmetic_pending after.
Proof. intros Transition Reset Before After Banks Advance. unfold cycle_rf_arithmetic_pending.
 split;[exact(cycle_rf_add_pending_normal memory inputs k current next before after Transition Reset Before After Banks Advance)|].
  split;[exact(cycle_rf_bitwise_pending_normal memory inputs k current next before after Transition Reset Before After Banks Advance)|].
  split;[exact(cycle_rf_subtract_pending_normal memory inputs k current next before after Transition Reset Before After Banks Advance)|].
  split;[exact(cycle_rf_compare_pending_normal memory inputs k current next before after Transition Reset Before After Banks Advance)|].
  split;[exact(cycle_rf_compare_immediate_pending_normal memory inputs k current next before after Transition Reset Before After Banks Advance)|].
  split;[exact(cycle_rf_shift_pending_normal memory inputs k current next before after Transition Reset Before After Banks Advance)|].
  exact(cycle_rf_upper_pending_normal memory inputs k current next before after Transition Reset Before After).
Qed.
