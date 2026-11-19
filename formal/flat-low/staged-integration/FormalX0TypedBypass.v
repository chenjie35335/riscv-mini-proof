Require Import CoreSocModel ComparisonNodes FlatRegFileX0 FormalRegFileX0Iteration FormalX0WriteDataShape.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Theorem x0_bypass_after_four invalid s0 s1 s2 s3 s4 enable b0 b1 b2 b3 b4 :
 VM.find 785 s1 = Some (Gval (Fuint 5) [::b0;b1;b2;b3;b4]) ->
 VM.find 785 s2 = Some (Gval (Fuint 5) [::b0;b1;b2;b3;b4]) ->
 VM.find 784 s2 = Some (Gval (Fuint 1) [::enable]) ->
 formal_value_iter invalid flat_memories s0 false s0 flat_statements = Some s1 ->
 formal_value_iter invalid flat_memories s1 false s1 flat_statements = Some s2 ->
 formal_value_iter invalid flat_memories s2 false s2 flat_statements = Some s3 ->
 formal_value_iter invalid flat_memories s3 false s3 flat_statements = Some s4 ->
 VM.find 1053 s4 = Some rf_zero32.
Proof.
 intros Addr1 Addr2 Enable S1 S2 S3 S4.
 destruct (x0_write_data_typed_after_two invalid s0 s1 s2 S1 S2) as [value [Value Typed]].
 exact (real_three_iterations_rf_x0_typed invalid s1 s2 s3 s4 enable b0 b1 b2 b3 b4 value Addr1 Addr2 Enable Value Typed S2 S3 S4).
Qed.
Print Assumptions x0_bypass_after_four.
