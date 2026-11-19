Require Import ComparisonNodes Assertion2GuardNodes Assertion44Enable CoreSocModel FormalObservedHistory FormalLocalHistory ExternalReset FormalResetPreparation FormalTopResetHold StagedIterationCount CycleView.
From Coq Require Import NArith Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths Firrtl_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Lemma assertion2_guard_after_two invalid s0 s1 s2 bit :
 VM.find 1394 s0 = Some (Gval (Fuint 1) [::bit]) ->
 formal_value_iter invalid flat_memories s0 false s0 flat_statements = Some s1 ->
 formal_value_iter invalid flat_memories s1 false s1 flat_statements = Some s2 ->
 VM.find 7576 s2 = Some (Gval (Fuint 1) [::negb bit]).
Proof.
 intros Reset S1 S2.
 assert (Extract : VM.find 7575 s1 = Some (Gval (Fuint 1) [::bit])).
 { rewrite (reference_event_equation_7575 invalid s0 s0 s1 S1).
   cbn [reference_event_expr_7575 eval_hfexpr_with_memory eval_href_with_memory]. rewrite Reset. destruct bit; reflexivity. }
 rewrite (reference_event_equation_7576 invalid s1 s1 s2 S2).
 cbn [reference_event_expr_7576 eval_hfexpr_with_memory eval_href_with_memory]. rewrite Extract. destruct bit; reflexivity.
Qed.
Theorem assertion2_history_with_reset memory inputs k states bit :
 generated_observe memory inputs k = Some states -> cycle_reset inputs k bit ->
 exists history,
 history 9259%nat = top_environment states /\
 (forall i, (i < 9259)%coq_nat -> formal_flat_local_step
   (formal_invalid_policy (generated_observation_input inputs k) nil) (history i) (history (S i))) /\
 (forall i, (i <= 9259)%coq_nat -> VM.find 1 (history i) = Some (Gval (Fuint 1) [::bit])).
Proof.
 intros Observe External.
 unfold generated_observe, generated_observe_cycle in Observe.
 destruct (generated_run memory inputs k) as [committed|] eqn:Run; [|discriminate Observe].
 destruct (circuit_initial_map_with_memory generated_modules generated_top (Some committed)
   (formal_external_inputs (generated_observation_input inputs k))) as [initial|] eqn:Prepare; [|discriminate Observe].
 pose proof flat_iteration_count_exact as Count. unfold flat_iteration_count in Count. rewrite Count in Observe.
 destruct (local_iteration_history (generated_observation_input inputs k) 9259 initial states Observe)
 as [history [First [Last Steps]]].
 destruct (top_reset_prepared (Some committed) _ initial _ External Prepare) as [env [Env Reset]].
 assert (Start : VM.find 1 (history 0%nat) = Some (Gval (Fuint 1) [::bit])).
 { rewrite First. unfold top_environment. rewrite Env. exact Reset. }
 exists history. split; [exact Last|]. split; [exact Steps|].
 intros i. induction i as [|i IH]; intro Bound; [exact Start|].
 eapply (top_reset_iteration (formal_invalid_policy (generated_observation_input inputs k) nil) (history i) (history i) (history (S i)) bit); [apply IH; lia|apply Steps; lia].
Qed.
Theorem assertion2_reset_guard_observed memory inputs k observed bit :
 generated_observe memory inputs k=Some observed ->cycle_reset inputs k bit ->
 VM.find 7576(top_environment observed)=Some(Gval(Fuint 1)[::negb bit]).
Proof.
 intros Observe Reset.
 destruct(assertion2_history_with_reset memory inputs k observed bit Observe Reset)as[history[Last[Steps Resets]]].
 pose proof(assertion44_checker_reset_after_three _ (history 9254%nat)(history 9255%nat)(history 9256%nat)(history 9257%nat)bit
 (Resets 9254%nat ltac:(vm_compute;lia))(Steps 9254%nat ltac:(vm_compute;lia))
 (Steps 9255%nat ltac:(vm_compute;lia))(Steps 9256%nat ltac:(vm_compute;lia)))as CheckerReset.
 rewrite <- Last.
 exact(assertion2_guard_after_two _ (history 9257%nat)(history 9258%nat)(history 9259%nat)bit CheckerReset
 (Steps 9257%nat ltac:(vm_compute;lia))(Steps 9258%nat ltac:(vm_compute;lia))).
Qed.
