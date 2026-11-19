Require Import CoreSocModel ComparisonNodes ExceptionPCNodes ExceptionPCConnections FormalRFResetPropagation.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Theorem implementation_exception_pc_after_five invalid s0 s1 s2 s3 s4 s5 bits :
 size bits = 32%nat ->
 VM.find 772 s0 = Some (Gval (Fuint 32) bits) ->
 formal_value_iter invalid flat_memories s0 false s0 flat_statements = Some s1 ->
 formal_value_iter invalid flat_memories s1 false s1 flat_statements = Some s2 ->
 formal_value_iter invalid flat_memories s2 false s2 flat_statements = Some s3 ->
 formal_value_iter invalid flat_memories s3 false s3 flat_statements = Some s4 ->
 formal_value_iter invalid flat_memories s4 false s4 flat_statements = Some s5 ->
 VM.find 1472 s5 = Some (Gval (Fuint 32) bits).
Proof.
 intros Size Source S1 S2 S3 S4 S5.
 pose proof (sized_uint_adapt_identity 32 bits Size) as Adapt.
 pose proof (exception_pc_776_value invalid s0 s0 s1 bits Source S1) as V1.
 pose proof (exception_pc_137_value invalid s1 s1 s2 _ _ V1 Adapt S2) as V2.
 pose proof (exception_pc_8156_value invalid s2 s2 s3 bits V2 S3) as V3.
 pose proof (exception_pc_8245_value invalid s3 s3 s4 bits V3 S4) as V4.
 exact (exception_pc_1472_value invalid s4 s4 s5 _ _ V4 Adapt S5).
Qed.
Theorem reference_exception_pc_after_three invalid s0 s1 s2 s3 bits :
 size bits = 32%nat ->
 VM.find 7119 s0 = Some (Gval (Fuint 32) bits) ->
 formal_value_iter invalid flat_memories s0 false s0 flat_statements = Some s1 ->
 formal_value_iter invalid flat_memories s1 false s1 flat_statements = Some s2 ->
 formal_value_iter invalid flat_memories s2 false s2 flat_statements = Some s3 ->
 VM.find 1670 s3 = Some (Gval (Fuint 32) bits).
Proof.
 intros Size Source S1 S2 S3.
 pose proof (sized_uint_adapt_identity 32 bits Size) as Adapt.
 pose proof (exception_pc_7206_value invalid s0 s0 s1 bits Source S1) as V1.
 pose proof (exception_pc_1860_value invalid s1 s1 s2 _ _ V1 Adapt S2) as V2.
 exact (exception_pc_1670_value invalid s2 s2 s3 _ _ V2 Adapt S3).
Qed.
Print Assumptions implementation_exception_pc_after_five.
Print Assumptions reference_exception_pc_after_three.
