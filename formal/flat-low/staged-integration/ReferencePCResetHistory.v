Require Import CoreSocModel ComparisonNodes FormalCheckerResetConnections ReferencePCResetConnections.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Theorem reference_pc_reset_after_four invalid s0 s1 s2 s3 s4 bit :
 VM.find 1 s0 = Some (Gval (Fuint 1) [::bit]) ->
 formal_value_iter invalid flat_memories s0 false s0 flat_statements = Some s1 ->
 formal_value_iter invalid flat_memories s1 false s1 flat_statements = Some s2 ->
 formal_value_iter invalid flat_memories s2 false s2 flat_statements = Some s3 ->
 formal_value_iter invalid flat_memories s3 false s3 flat_statements = Some s4 ->
 VM.find 1515 s4 = Some (Gval (Fuint 1) [::bit]).
Proof.
 intros Reset S1 S2 S3 S4.
 pose proof (reset_connection_24_transfer invalid s0 s0 s1 bit Reset S1) as R1.
 pose proof (reset_connection_65_transfer invalid s1 s1 s2 bit R1 S2) as R2.
 pose proof (reset_connection_1394_transfer invalid s2 s2 s3 bit R2 S3) as R3.
 apply (exception_pc_1515_value invalid s3 s3 s4 _ _ R3); [destruct bit; reflexivity|exact S4].
Qed.
Print Assumptions reference_pc_reset_after_four.
