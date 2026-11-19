Require Import CoreSocModel ComparisonNodes FlatRegFileX0 FormalRegFileX0Iteration FormalX0TypedBypass FormalImplementationX0Path.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Theorem x0_output_after_nine invalid s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 enable b0 b1 b2 b3 b4 :
 VM.find 785 s1 = Some (Gval (Fuint 5) [::b0;b1;b2;b3;b4]) ->
 VM.find 785 s2 = Some (Gval (Fuint 5) [::b0;b1;b2;b3;b4]) ->
 VM.find 784 s2 = Some (Gval (Fuint 1) [::enable]) ->
 formal_value_iter invalid flat_memories s0 false s0 flat_statements = Some s1 ->
 formal_value_iter invalid flat_memories s1 false s1 flat_statements = Some s2 ->
 formal_value_iter invalid flat_memories s2 false s2 flat_statements = Some s3 ->
 formal_value_iter invalid flat_memories s3 false s3 flat_statements = Some s4 ->
 formal_value_iter invalid flat_memories s4 false s4 flat_statements = Some s5 ->
 formal_value_iter invalid flat_memories s5 false s5 flat_statements = Some s6 ->
 formal_value_iter invalid flat_memories s6 false s6 flat_statements = Some s7 ->
 formal_value_iter invalid flat_memories s7 false s7 flat_statements = Some s8 ->
 formal_value_iter invalid flat_memories s8 false s8 flat_statements = Some s9 ->
 VM.find 1399 s9 = Some rf_zero32.
Proof.
 intros Addr1 Addr2 Enable S1 S2 S3 S4 S5 S6 S7 S8 S9.
 exact (implementation_x0_after_five invalid s4 s5 s6 s7 s8 s9
  (x0_bypass_after_four invalid s0 s1 s2 s3 s4 enable b0 b1 b2 b3 b4 Addr1 Addr2 Enable S1 S2 S3 S4) S5 S6 S7 S8 S9).
Qed.
Print Assumptions x0_output_after_nine.
