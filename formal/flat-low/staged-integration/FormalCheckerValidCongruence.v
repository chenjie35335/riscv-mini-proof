Require Import CoreSocModel ComparisonNodes FormalCheckerValidNodes.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
(* Equality of source values suffices; no concreteness premise is used. *)
Theorem checker_valid_congruent_after_four invalid l0 l1 l2 l3 l4 r0 r1 r2 r3 r4 :
 VM.find 7947 l0 = VM.find 7947 r0 ->
 VM.find 7765 l0 = VM.find 7765 r0 ->
 VM.find 65 l0 = VM.find 65 r0 ->
 formal_value_iter invalid flat_memories l0 false l0 flat_statements = Some l1 ->
 formal_value_iter invalid flat_memories l1 false l1 flat_statements = Some l2 ->
 formal_value_iter invalid flat_memories l2 false l2 flat_statements = Some l3 ->
 formal_value_iter invalid flat_memories l3 false l3 flat_statements = Some l4 ->
 formal_value_iter invalid flat_memories r0 false r0 flat_statements = Some r1 ->
 formal_value_iter invalid flat_memories r1 false r1 flat_statements = Some r2 ->
 formal_value_iter invalid flat_memories r2 false r2 flat_statements = Some r3 ->
 formal_value_iter invalid flat_memories r3 false r3 flat_statements = Some r4 ->
 VM.find 7952 l4 = VM.find 7952 r4.
Proof.
 intros Reg Stall Reset L1 L2 L3 L4 R1 R2 R3 R4.
 pose proof (checker_valid_congruent_7948 invalid l0 r0 l1 r1 Reg Stall L1 R1) as A.
 pose proof (checker_valid_congruent_7949 invalid l0 r0 l1 r1 Reset L1 R1) as B.
 pose proof (checker_valid_congruent_7950 invalid l1 r1 l2 r2 A B L2 R2) as C.
 pose proof (checker_valid_congruent_7951 invalid l2 r2 l3 r3 C L3 R3) as D.
 exact (checker_valid_congruent_7952 invalid l3 r3 l4 r4 D L4 R4).
Qed.
Print Assumptions checker_valid_congruent_after_four.
