Require Import CoreSocModel ComparisonNodes FormalNodeEquation FormalTypedNodeEquation FormalTypedNodeFrames MemorySuffixCertificates MemoryWriteFrames ScalarNodeFrames RegisterInvariants.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths Firrtl_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Definition reference_event_expr_7571 := (@Ecast VarOrder.T AsUInt (@Eref VarOrder.T (@Eid VarOrder.T 1394))).
Definition reference_event_tail_7571 := match straight_drop 8041 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma reference_event_position_7571 : straight_drop 8040 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7571 reference_event_expr_7571) reference_event_tail_7571).
Proof. vm_compute. reflexivity. Qed.
Lemma reference_event_suffix_7571 : memory_suffix_safe flat_memories 7571 reference_event_tail_7571.
Proof. apply memory_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma reference_event_nonregister_7571 : has_register 7571 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem reference_event_equation_7571 invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 7571 result = eval_hfexpr_with_memory flat_memories reference_event_expr_7571 old old.
Proof.
 intro Step. exact (formal_combinational_node_equation _ _ _ _ _ invalid flat_memories old current result
 reference_event_position_7571 reference_event_suffix_7571 reference_event_nonregister_7571 Step).
Qed.
Definition reference_event_expr_7572 := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 7571)) (@Econst VarOrder.T (Fuint 1) [::false])).
Definition reference_event_tail_7572 := match straight_drop 8042 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma reference_event_position_7572 : straight_drop 8041 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7572 reference_event_expr_7572) reference_event_tail_7572).
Proof. vm_compute. reflexivity. Qed.
Lemma reference_event_suffix_7572 : memory_suffix_safe flat_memories 7572 reference_event_tail_7572.
Proof. apply memory_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma reference_event_nonregister_7572 : has_register 7572 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem reference_event_equation_7572 invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 7572 result = eval_hfexpr_with_memory flat_memories reference_event_expr_7572 old old.
Proof.
 intro Step. exact (formal_combinational_node_equation _ _ _ _ _ invalid flat_memories old current result
 reference_event_position_7572 reference_event_suffix_7572 reference_event_nonregister_7572 Step).
Qed.

Require Import ComparisonNodes Assertion2GuardNodes Assertion44Enable CoreSocModel FormalObservedHistory FormalLocalHistory ExternalReset FormalResetPreparation FormalTopResetHold StagedIterationCount CycleView.
From Coq Require Import NArith Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths Firrtl_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Lemma address_assertion1_guard_after_two invalid s0 s1 s2 bit :
 VM.find 1394 s0 = Some (Gval (Fuint 1) [::bit]) ->
 formal_value_iter invalid flat_memories s0 false s0 flat_statements = Some s1 ->
 formal_value_iter invalid flat_memories s1 false s1 flat_statements = Some s2 ->
 VM.find 7572 s2 = Some (Gval (Fuint 1) [::negb bit]).
Proof.
 intros Reset S1 S2.
 assert (Extract : VM.find 7571 s1 = Some (Gval (Fuint 1) [::bit])).
 { rewrite (reference_event_equation_7571 invalid s0 s0 s1 S1).
   cbn [reference_event_expr_7571 eval_hfexpr_with_memory eval_href_with_memory]. rewrite Reset. destruct bit; reflexivity. }
 rewrite (reference_event_equation_7572 invalid s1 s1 s2 S2).
 cbn [reference_event_expr_7572 eval_hfexpr_with_memory eval_href_with_memory]. rewrite Extract. destruct bit; reflexivity.
Qed.
Theorem address_assertion1_history_with_reset memory inputs k states bit :
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
Theorem address_assertion1_reset_guard_observed memory inputs k observed bit :
 generated_observe memory inputs k=Some observed ->cycle_reset inputs k bit ->
 VM.find 7572(top_environment observed)=Some(Gval(Fuint 1)[::negb bit]).
Proof.
 intros Observe Reset.
 destruct(address_assertion1_history_with_reset memory inputs k observed bit Observe Reset)as[history[Last[Steps Resets]]].
 pose proof(assertion44_checker_reset_after_three _ (history 9254%nat)(history 9255%nat)(history 9256%nat)(history 9257%nat)bit
 (Resets 9254%nat ltac:(vm_compute;lia))(Steps 9254%nat ltac:(vm_compute;lia))
 (Steps 9255%nat ltac:(vm_compute;lia))(Steps 9256%nat ltac:(vm_compute;lia)))as CheckerReset.
 rewrite <- Last.
 exact(address_assertion1_guard_after_two _ (history 9257%nat)(history 9258%nat)(history 9259%nat)bit CheckerReset
 (Steps 9257%nat ltac:(vm_compute;lia))(Steps 9258%nat ltac:(vm_compute;lia))).
Qed.

Require Import CoreSocModel ComparisonNodes CycleView Assertion2ResetGuard RequestEnableNormalized NormalizedBit FormalLocalHistory.
From Coq Require Import NArith Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Lemma address_assertion1_disabled_by_reset env value :
 VM.find 7569 env=Some value ->normalized_bit value ->
 VM.find 7572 env=Some(Gval(Fuint 1)[::false]) ->generated_assert_m0_1_local env.
Proof.
 intros Value Normal Guard.
 unfold generated_assert_m0_1_local,generated_expr_true.
 cbn [eval_hfexpr eval_href]. rewrite Value Guard.
 destruct Normal as[bit| | |];try destruct bit;vm_compute;intro Impossible;discriminate Impossible.
Qed.
Theorem address_assertion1_reset_observed memory inputs k observed :
 generated_observe memory inputs k=Some observed ->cycle_reset inputs k true ->
 generated_assert_m0_1_local(top_environment observed).
Proof.
 intros Observe Reset.
 pose proof(address_assertion1_reset_guard_observed memory inputs k observed true Observe Reset)as Guard.
 destruct(address_assertion1_history_with_reset memory inputs k observed true Observe Reset)as[history[Last[Steps Resets]]].
 destruct(read_valid_or_normalized _ (history 9257%nat)(history 9258%nat)(history 9259%nat)
 (Steps 9257%nat ltac:(vm_compute;lia))(Steps 9258%nat ltac:(vm_compute;lia)))as[value[Value Normal]].
 rewrite Last in Value. exact(address_assertion1_disabled_by_reset _ value Value Normal Guard).
Qed.
