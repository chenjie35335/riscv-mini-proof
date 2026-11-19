Require Import CoreSocModel ComparisonNodes ExceptionPCHistory ExceptionPCShiftValues.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Theorem implementation_exception_pc_aligned_after_seven invalid s0 s1 s2 s3 s4 s5 s6 s7 bits :
 size bits = 32%nat ->
 take 2 bits = [::false;false] ->
 VM.find 121 s0 = Some (Gval (Fuint 32) bits) ->
 formal_value_iter invalid flat_memories s0 false s0 flat_statements = Some s1 ->
 formal_value_iter invalid flat_memories s1 false s1 flat_statements = Some s2 ->
 formal_value_iter invalid flat_memories s2 false s2 flat_statements = Some s3 ->
 formal_value_iter invalid flat_memories s3 false s3 flat_statements = Some s4 ->
 formal_value_iter invalid flat_memories s4 false s4 flat_statements = Some s5 ->
 formal_value_iter invalid flat_memories s5 false s5 flat_statements = Some s6 ->
 formal_value_iter invalid flat_memories s6 false s6 flat_statements = Some s7 ->
 VM.find 1472 s7 = Some (Gval (Fuint 32) bits).
Proof.
 intros Size Low Source S1 S2 S3 S4 S5 S6 S7.
 pose proof (exception_pc_round_down_after_two invalid s0 s1 s2 bits Source S1 S2) as Rounded.
 rewrite (exception_pc_round_down_identity bits Low) in Rounded.
 exact (implementation_exception_pc_after_five invalid s2 s3 s4 s5 s6 s7 bits Size Rounded S3 S4 S5 S6 S7).
Qed.
Print Assumptions implementation_exception_pc_aligned_after_seven.
