Require Import ComparisonNodes Assertion5GuardNodes Assertion2ResetGuard Assertion44Enable CoreSocModel FormalObservedHistory FormalLocalHistory ExternalReset FormalResetPreparation FormalTopResetHold StagedIterationCount CycleView.
From Coq Require Import NArith Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths Firrtl_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Lemma assertion5_guard_after_two invalid s0 s1 s2 bit :
 VM.find 1394 s0 = Some (Gval (Fuint 1) [::bit]) ->
 formal_value_iter invalid flat_memories s0 false s0 flat_statements = Some s1 ->
 formal_value_iter invalid flat_memories s1 false s1 flat_statements = Some s2 ->
 VM.find 7589 s2 = Some (Gval (Fuint 1) [::negb bit]).
Proof.
 intros Reset S1 S2.
 assert (Extract : VM.find 7588 s1 = Some (Gval (Fuint 1) [::bit])).
 { rewrite (reference_event_equation_7588 invalid s0 s0 s1 S1).
   cbn [reference_event_expr_7588 eval_hfexpr_with_memory eval_href_with_memory]. rewrite Reset. destruct bit; reflexivity. }
 rewrite (reference_event_equation_7589 invalid s1 s1 s2 S2).
 cbn [reference_event_expr_7589 eval_hfexpr_with_memory eval_href_with_memory]. rewrite Extract. destruct bit; reflexivity.
Qed.
Theorem assertion5_reset_guard_observed memory inputs k observed bit :
 generated_observe memory inputs k=Some observed ->cycle_reset inputs k bit ->
 VM.find 7589(top_environment observed)=Some(Gval(Fuint 1)[::negb bit]).
Proof.
 intros Observe Reset.
 destruct(assertion2_history_with_reset memory inputs k observed bit Observe Reset)as[history[Last[Steps Resets]]].
 pose proof(assertion44_checker_reset_after_three _ (history 9254%nat)(history 9255%nat)(history 9256%nat)(history 9257%nat)bit
 (Resets 9254%nat ltac:(vm_compute;lia))(Steps 9254%nat ltac:(vm_compute;lia))
 (Steps 9255%nat ltac:(vm_compute;lia))(Steps 9256%nat ltac:(vm_compute;lia)))as CheckerReset.
 rewrite <- Last.
 exact(assertion5_guard_after_two _ (history 9257%nat)(history 9258%nat)(history 9259%nat)bit CheckerReset
 (Steps 9257%nat ltac:(vm_compute;lia))(Steps 9258%nat ltac:(vm_compute;lia))).
Qed.
