Require Import CoreSocModel ComparisonNodes FormalObservedHistory FormalLocalHistory FormalX0EnabledReference FormalX0Enable FormalAssertionDischarge ComparisonTruth AssertionInstances StagedFlatObservation.
From Coq Require Import ZArith Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From nbits Require Import NBits.
From firrtl Require Import Env_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque generated_modules generated_top flat_statements flat_memories.
(* Only the implementation-side zero invariant remains an external obligation. *)
Theorem observed_x0_from_implementation_zero memory inputs k states :
 generated_observe memory inputs k = Some states ->
 generated_legal_trace memory inputs k ->
 (forall bit (history : nat -> VM.t hvalue),
 history 9259%nat = top_environment states ->
 (forall i, (i < 9259)%coq_nat -> formal_flat_local_step (formal_invalid_policy (generated_observation_input inputs k) nil) (history i) (history (S i))) ->
 (forall i, (i <= 9259)%coq_nat -> VM.find 1 (history i) = Some (Gval (Fuint 1) [::bit])) ->
 generated_expr_true x0_enable (top_environment states) ->
 VM.find 1399 (history 9258%nat) = Some (Gval (Fuint 32) (zeros 32))) ->
 generated_assert_m0_8_all states.
Proof.
 intros Observe Legal Implementation.
 destruct (observed_history memory inputs k states Observe Legal) as [bit [history [Last [Steps Resets]]]].
 destruct (observed_last_iteration memory inputs k states Observe) as [committed [initial [previous [old [next [Run [Prepare [Prefix [Old [Step State]]]]]]]]]].
 assert (Top : top_environment states = next) by (unfold top_environment; rewrite State; reflexivity).
 apply (proj2 (assertion_8_at_top states)). rewrite State. rewrite <- Top.
 pose proof (Steps 9258%nat ltac:(vm_compute; lia)) as FinalStep.
 change (formal_value_iter (formal_invalid_policy (generated_observation_input inputs k) nil) flat_memories (history 9258%nat) false (history 9258%nat) flat_statements = Some (history 9259%nat)) in FinalStep.
 rewrite Last in FinalStep.
 apply (assertion_8_from_enabled_agreement _ _ _ _ FinalStep).
 intro Enabled.
 pose proof (Implementation bit history Last Steps Resets Enabled) as Left.
 assert (Right : VM.find 1597 (history 9258%nat) = Some (Gval (Fuint 32) (zeros 32))).
 { apply (x0_enabled_reference_previous _ history 9259 bit ltac:(vm_compute; lia) Steps Resets).
   rewrite Last. exact Enabled. }
 exists 32%nat, 32%nat, (zeros 32), (zeros 32).
 split; [exact Left|]. split; [exact Right|reflexivity].
Qed.
Print Assumptions observed_x0_from_implementation_zero.
