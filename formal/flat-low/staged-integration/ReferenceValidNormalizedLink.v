Require Import CoreSocModel ComparisonNodes FormalReferenceValid FormalCheckerValidShape FormalCheckerValidOutput NormalizedBit SymbolicBit.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Lemma checker_valid_normalized_after_three invalid s0 s1 s2 s3 :
 formal_value_iter invalid flat_memories s0 false s0 flat_statements = Some s1 ->
 formal_value_iter invalid flat_memories s1 false s1 flat_statements = Some s2 ->
 formal_value_iter invalid flat_memories s2 false s2 flat_statements = Some s3 ->
 exists value, VM.find 1395 s3 = Some value /\ normalized_bit value.
Proof.
 intros S1 S2 S3.
 destruct (checker_valid_comparison_normalized invalid s0 s0 s1 S1) as [value [Value Normal]].
 exists value. split; [|exact Normal].
 exact (checker_output_after_two invalid s1 s2 s3 value Normal Value S2 S3).
Qed.
Lemma reference_valid_normalized_after_two invalid s0 s1 s2 value :
 normalized_bit value -> VM.find 1395 s0 = Some value ->
 formal_value_iter invalid flat_memories s0 false s0 flat_statements = Some s1 ->
 formal_value_iter invalid flat_memories s1 false s1 flat_statements = Some s2 ->
 VM.find 1707 s2 = Some value.
Proof.
 intros Normal Source S1 S2.
 pose proof (normalized_bit_adapt value Normal) as Adapt.
 pose proof (reference_valid_connection_1517 invalid s0 s0 s1 value value Source Adapt S1) as Middle.
 exact (reference_valid_connection_1707 invalid s1 s1 s2 value value Middle Adapt S2).
Qed.
Theorem reference_valid_true_recovers_checker invalid s0 s1 s2 s3 s4 s5 :
 formal_value_iter invalid flat_memories s0 false s0 flat_statements = Some s1 ->
 formal_value_iter invalid flat_memories s1 false s1 flat_statements = Some s2 ->
 formal_value_iter invalid flat_memories s2 false s2 flat_statements = Some s3 ->
 formal_value_iter invalid flat_memories s3 false s3 flat_statements = Some s4 ->
 formal_value_iter invalid flat_memories s4 false s4 flat_statements = Some s5 ->
 VM.find 1707 s5 = Some (Gval (Fuint 1) [::true]) ->
 VM.find 1395 s3 = Some (Gval (Fuint 1) [::true]).
Proof.
 intros S1 S2 S3 S4 S5 True.
 destruct (checker_valid_normalized_after_three invalid s0 s1 s2 s3 S1 S2 S3) as [value [Value Normal]].
 pose proof (reference_valid_normalized_after_two invalid s3 s4 s5 value Normal Value S4 S5) as Ref.
 rewrite True in Ref. inversion Ref; subst. exact Value.
Qed.
Print Assumptions reference_valid_true_recovers_checker.
