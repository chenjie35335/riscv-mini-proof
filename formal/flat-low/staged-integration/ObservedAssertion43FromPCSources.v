Require Import StagedFlatObservation.
Require Import CoreSocModel ComparisonNodes ComparisonTruth FormalObservedHistory FormalLocalHistory FormalAssertionDischarge AssertionInstances Assertion43Enable ObservedAssertion43EventContext ExceptionPCWindow.
From Coq Require Import ZArith Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque generated_modules generated_top flat_statements flat_memories.
Definition exception_pc_sources_agree env : Prop :=
 exists bits, size bits = 32%nat /\ take 2 bits = [::false;false] /\
 VM.find 7751 env = Some (Gval (Fuint 32) bits) /\
 VM.find 7331 env = Some (Gval (Fuint 32) bits).
Theorem observed_assertion43_from_pc_sources memory inputs k states :
 generated_observe memory inputs k = Some states ->
 generated_legal_trace memory inputs k ->
 (generated_expr_true assertion43_enable (top_environment states) ->
  exception_pc_sources_agree (top_environment states)) ->
 generated_assert_m0_43_all states.
Proof.
 intros Observe Legal Sources.
 destruct (observed_last_iteration memory inputs k states Observe)
 as [committed [initial [previous [old [next [Run [Prepare [Prefix [Old [Step State]]]]]]]]]].
 assert (Top : top_environment states = next) by (unfold top_environment; rewrite State; reflexivity).
 apply (proj2 (assertion_43_at_top states)). rewrite State. rewrite <- Top.
 unfold generated_assert_m0_43_local. intro Enabled.
 destruct (Sources Enabled) as [bits [Size [Low [Implementation Reference]]]].
 destruct (observed_assertion43_event_context memory inputs k states Observe Legal Enabled)
 as [history [Last [Steps [Resets [Boundary [NoException [Raised [Valid Raise]]]]]]]].
 assert (Agree : comparison_inputs_agree (history 9258%nat) 1472 1670).
 { apply (exception_pc_window_agreement _ history 9259 9250 bits Steps).
   - vm_compute; lia.
   - exact Size.
   - exact Low.
   - rewrite Last. exact Implementation.
   - rewrite Last. exact Reference.
   - exact Raise.
   - exact Valid. }
 pose proof (Steps 9258%nat ltac:(vm_compute; lia)) as FinalStep.
 change (formal_value_iter (formal_invalid_policy (generated_observation_input inputs k) nil) flat_memories
 (history 9258%nat) false (history 9258%nat) flat_statements = Some (history 9259%nat)) in FinalStep.
 rewrite Last in FinalStep.
 exact ((assertion_43_from_enabled_agreement _ _ _ _ FinalStep (fun _ => Agree)) Enabled).
Qed.
Print Assumptions observed_assertion43_from_pc_sources.
