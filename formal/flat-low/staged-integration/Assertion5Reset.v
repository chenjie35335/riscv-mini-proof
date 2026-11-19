Require Import CoreSocModel ComparisonNodes CycleView Assertion5ResetGuard Assertion2ResetGuard Assertion5Disabled WriteEnableNormalized NormalizedBit FormalLocalHistory.
From Coq Require Import NArith Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Theorem assertion5_reset_observed memory inputs k observed :
 generated_observe memory inputs k=Some observed ->cycle_reset inputs k true ->
 generated_assert_m0_5_local(top_environment observed).
Proof.
 intros Observe Reset.
 pose proof(assertion5_reset_guard_observed memory inputs k observed true Observe Reset)as Guard.
 destruct(assertion2_history_with_reset memory inputs k observed true Observe Reset)as[history[Last[Steps Resets]]].
 destruct(write_valid_or_normalized _ (history 9257%nat)(history 9258%nat)(history 9259%nat)
 (Steps 9257%nat ltac:(vm_compute;lia))(Steps 9258%nat ltac:(vm_compute;lia)))as[value[Value Normal]].
 rewrite Last in Value. exact(assertion5_disabled_by_guard _ value Value Normal Guard).
Qed.
