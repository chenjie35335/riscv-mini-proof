Require Import CoreSocModel ComparisonNodes CycleView Assertion2ResetGuard RequestEnableNormalized NormalizedBit FormalLocalHistory.
From Coq Require Import NArith Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Lemma assertion2_disabled_by_reset env value :
 VM.find 7569 env=Some value ->normalized_bit value ->
 VM.find 7576 env=Some(Gval(Fuint 1)[::false]) ->generated_assert_m0_2_local env.
Proof.
 intros Value Normal Guard.
 unfold generated_assert_m0_2_local,generated_expr_true.
 cbn [eval_hfexpr eval_href]. rewrite Value Guard.
 destruct Normal as[bit| | |];try destruct bit;vm_compute;intro Impossible;discriminate Impossible.
Qed.
Theorem assertion2_reset_observed memory inputs k observed :
 generated_observe memory inputs k=Some observed ->cycle_reset inputs k true ->
 generated_assert_m0_2_local(top_environment observed).
Proof.
 intros Observe Reset.
 pose proof(assertion2_reset_guard_observed memory inputs k observed true Observe Reset)as Guard.
 destruct(assertion2_history_with_reset memory inputs k observed true Observe Reset)as[history[Last[Steps Resets]]].
 destruct(read_valid_or_normalized _ (history 9257%nat)(history 9258%nat)(history 9259%nat)
 (Steps 9257%nat ltac:(vm_compute;lia))(Steps 9258%nat ltac:(vm_compute;lia)))as[value[Value Normal]].
 rewrite Last in Value. exact(assertion2_disabled_by_reset _ value Value Normal Guard).
Qed.
