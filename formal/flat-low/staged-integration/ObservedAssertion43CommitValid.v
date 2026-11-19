Require Import CoreSocModel ComparisonNodes FormalLocalHistory ObservedAssertion43EventContext Assertion43Enable ReferenceValidNormalizedLink FormalCheckerValidStability.
From Coq Require Import ZArith Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque generated_modules generated_top flat_statements flat_memories.
Theorem observed_assertion43_commit_valid memory inputs k states :
 generated_observe memory inputs k = Some states ->
 generated_legal_trace memory inputs k ->
 generated_expr_true assertion43_enable (top_environment states) ->
 VM.find 1395 (top_environment states) = Some (Gval (Fuint 1) [::true]).
Proof.
 intros Observe Legal Enabled.
 destruct (observed_assertion43_event_context memory inputs k states Observe Legal Enabled)
 as [history [Last [Steps [Resets [Boundary [NoException [Raised [Valid Raise]]]]]]]].
 assert (Earlier : VM.find 1395 (history 9252%nat) = Some (Gval (Fuint 1) [::true])).
 { apply (reference_valid_true_recovers_checker (formal_invalid_policy (generated_observation_input inputs k) nil) (history 9249%nat) (history 9250%nat)
 (history 9251%nat) (history 9252%nat) (history 9253%nat) (history 9254%nat));
 try exact Valid; apply Steps; vm_compute; lia. }
 pose proof (checker_valid_history_stable _ history 9259 9240 9247 false Steps Resets
 ltac:(vm_compute; lia) ltac:(vm_compute; lia)) as Same.
 change (VM.find 1395 (history 9252%nat) = VM.find 1395 (history 9259%nat)) in Same.
 rewrite Last in Same. rewrite <- Same. exact Earlier.
Qed.
Print Assumptions observed_assertion43_commit_valid.
