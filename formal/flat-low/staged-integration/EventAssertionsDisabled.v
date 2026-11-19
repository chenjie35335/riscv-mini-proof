Require Import CycleJointInvariant CycleJointReachability CycleDataReachability CycleReferenceNoException CycleView
 Assertion40Enable Assertion42Enable Assertion43Enable Assertion44Enable Assertion2ResetGuard
 ObservedAssertion43EventContext ReferenceControlStabilityHistory ExternalReset
 CoreSocModel ComparisonNodes FormalLocalHistory FormalObservedHistory.
From Coq Require Import NArith Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque generated_modules generated_top flat_statements flat_memories.
Theorem event_assertion_guards_observed memory inputs k observed bit :
 generated_observe memory inputs k=Some observed ->cycle_reset inputs k bit ->
 VM.find 7730(top_environment observed)=Some(Gval(Fuint 1)[::negb bit]) /\
 VM.find 7738(top_environment observed)=Some(Gval(Fuint 1)[::negb bit]) /\
 VM.find 7742(top_environment observed)=Some(Gval(Fuint 1)[::negb bit]).
Proof.
 intros Observe Reset.
 destruct(assertion2_history_with_reset memory inputs k observed bit Observe Reset)as[history[Last[Steps Resets]]].
 pose proof(assertion44_checker_reset_after_three _ (history 9254%nat)(history 9255%nat)(history 9256%nat)(history 9257%nat)bit
 (Resets 9254%nat ltac:(vm_compute;lia))(Steps 9254%nat ltac:(vm_compute;lia))
 (Steps 9255%nat ltac:(vm_compute;lia))(Steps 9256%nat ltac:(vm_compute;lia)))as CheckerReset.
 rewrite <-Last. split;[exact(assertion40_guard_after_two _ _ _ _ bit CheckerReset(Steps 9257%nat ltac:(vm_compute;lia))(Steps 9258%nat ltac:(vm_compute;lia)))|].
 split;[exact(assertion42_guard_after_two _ _ _ _ bit CheckerReset(Steps 9257%nat ltac:(vm_compute;lia))(Steps 9258%nat ltac:(vm_compute;lia)))|].
 exact(assertion43_guard_after_two _ _ _ _ bit CheckerReset(Steps 9257%nat ltac:(vm_compute;lia))(Steps 9258%nat ltac:(vm_compute;lia))).
Qed.
Theorem event_assertion43_not_enabled memory inputs k observed :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 ~generated_expr_true assertion43_enable(top_environment observed).
Proof.
 intros Observe Legal Enabled.
 destruct(legal_observation_reset memory inputs k Legal)as[bit Reset].
 destruct(assertion2_history_with_reset memory inputs k observed bit Observe Reset)as[h[Last[Steps Resets]]].
 pose proof(assertion44_checker_reset_after_three _ (h 9254%nat)(h 9255%nat)(h 9256%nat)(h 9257%nat)bit
 (Resets 9254%nat ltac:(vm_compute;lia))(Steps 9254%nat ltac:(vm_compute;lia))
 (Steps 9255%nat ltac:(vm_compute;lia))(Steps 9256%nat ltac:(vm_compute;lia)))as CheckerReset.
 assert(FalseBit:bit=false).
 { exact(proj1(assertion43_enabled_reset_and_or _ _ _ _ bit CheckerReset
 (Steps 9257%nat ltac:(vm_compute;lia))(Steps 9258%nat ltac:(vm_compute;lia))ltac:(rewrite Last;exact Enabled))). }
 subst bit.
 destruct(cycle_joint_observed_invariant memory inputs k observed Observe Legal)as[v[View[PC[Data[Relative[Decision[Jalr Taken]]]]]]].
 destruct Data as[Banks[Arithmetic[Memory[Store Assertion]]]].
 pose proof(cycle_reference_no_exception memory inputs k observed v Observe Legal Reset View Memory PC Relative Decision Jalr Taken)as Quiet.
 destruct(observed_assertion43_event_context memory inputs k observed Observe Legal Enabled)
 as[history[Final[HistorySteps[HistoryResets[Boundary[NoException[Raised[Valid[cw[cb[Raise Nonzero]]]]]]]]]]].
 pose proof(reference_control_stable_6780_history (generated_observation_input inputs k) nil history 9259 false HistoryResets HistorySteps
 9253 9259 ltac:(vm_compute;lia)ltac:(vm_compute;lia)ltac:(vm_compute;lia)ltac:(vm_compute;lia))as Stable.
 rewrite Stable Final Quiet in Raise. inversion Raise;subst. discriminate Nonzero.
Qed.
Theorem event_assertion40_not_enabled memory inputs k observed :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 ~generated_expr_true assertion40_enable(top_environment observed).
Proof.
 intros Observe Legal Enabled.
 destruct(legal_observation_reset memory inputs k Legal)as[bit Reset].
 destruct(event_assertion_guards_observed memory inputs k observed bit Observe Reset)as[G40[G42 G43]].
 apply(event_assertion43_not_enabled memory inputs k observed Observe Legal).
 unfold generated_expr_true,assertion40_enable in Enabled.
 unfold generated_expr_true,assertion43_enable.
 cbn[eval_hfexpr eval_href]in Enabled|-*. rewrite G40 in Enabled. rewrite G43. exact Enabled.
Qed.
Theorem event_assertion42_not_enabled memory inputs k observed :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 ~generated_expr_true assertion42_enable(top_environment observed).
Proof.
 intros Observe Legal Enabled.
 destruct(legal_observation_reset memory inputs k Legal)as[bit Reset].
 destruct(event_assertion_guards_observed memory inputs k observed bit Observe Reset)as[G40[G42 G43]].
 apply(event_assertion43_not_enabled memory inputs k observed Observe Legal).
 unfold generated_expr_true,assertion42_enable in Enabled.
 unfold generated_expr_true,assertion43_enable.
 cbn[eval_hfexpr eval_href]in Enabled|-*. rewrite G42 in Enabled. rewrite G43. exact Enabled.
Qed.
