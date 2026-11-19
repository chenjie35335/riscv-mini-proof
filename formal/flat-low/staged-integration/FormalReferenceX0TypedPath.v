Require Import CoreSocModel ComparisonNodes FormalReferenceX0DataType FormalReferenceX0Path.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From nbits Require Import NBits.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Theorem formal_reference_x0_after_six invalid s0 s1 s2 s3 s4 s5 s6 :
 VM.find 1707 s2 = Some (Gval (Fuint 1) [::true]) ->
 formal_value_iter invalid flat_memories s0 false s0 flat_statements = Some s1 ->
 formal_value_iter invalid flat_memories s1 false s1 flat_statements = Some s2 ->
 formal_value_iter invalid flat_memories s2 false s2 flat_statements = Some s3 ->
 formal_value_iter invalid flat_memories s3 false s3 flat_statements = Some s4 ->
 formal_value_iter invalid flat_memories s4 false s4 flat_statements = Some s5 ->
 formal_value_iter invalid flat_memories s5 false s5 flat_statements = Some s6 ->
 VM.find 1597 s6 = Some (Gval (Fuint 32) (zeros 32)).
Proof.
 intros Valid S1 S2 S3 S4 S5 S6.
 destruct (reference_x0_data_type_after_two invalid s0 s1 s2 S1 S2) as [value [Value Typed]].
 exact (formal_reference_x0_after_four invalid s2 s3 s4 s5 s6 value Valid Value Typed S3 S4 S5 S6).
Qed.
Print Assumptions formal_reference_x0_after_six.
