Require Import CoreSocModel ComparisonNodes FormalImplementationX0Aliases FormalImplementationX0Connections.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From nbits Require Import NBits.
From firrtl Require Import Env_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Theorem implementation_x0_after_five invalid s0 s1 s2 s3 s4 s5 :
 VM.find 1053 s0 = Some (Gval (Fuint 32) (zeros 32)) ->
 formal_value_iter invalid flat_memories s0 false s0 flat_statements = Some s1 ->
 formal_value_iter invalid flat_memories s1 false s1 flat_statements = Some s2 ->
 formal_value_iter invalid flat_memories s2 false s2 flat_statements = Some s3 ->
 formal_value_iter invalid flat_memories s3 false s3 flat_statements = Some s4 ->
 formal_value_iter invalid flat_memories s4 false s4 flat_statements = Some s5 ->
 VM.find 1399 s5 = Some (Gval (Fuint 32) (zeros 32)).
Proof.
 intros Zero S1 S2 S3 S4 S5.
 pose proof (node_1117_transfer invalid s0 s0 s1 32 _ Zero (Logic.eq_refl _) S1) as A.
 assert (B : VM.find 819 s2 = Some (Gval (Fuint 32) (zeros 32))).
 { eapply implementation_x0_connection_819; [exact A|reflexivity|exact S2]. }
 pose proof (node_8041_transfer invalid s2 s2 s3 32 _ B (Logic.eq_refl _) S3) as C.
 pose proof (node_8166_transfer invalid s3 s3 s4 32 _ C (Logic.eq_refl _) S4) as D.
 eapply implementation_x0_connection_1399; [exact D|reflexivity|exact S5].
Qed.
Print Assumptions implementation_x0_after_five.
