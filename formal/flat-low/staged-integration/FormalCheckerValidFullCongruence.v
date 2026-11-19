Require Import CoreSocModel ComparisonNodes FormalCheckerValidCongruence FormalCheckerValidShape FormalCheckerValidOutput.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
(* Equality of source values suffices; no concreteness premise is used. *)
Theorem checker_valid_congruent_after_six invalid l0 l1 l2 l3 l4 l5 l6 r0 r1 r2 r3 r4 r5 r6 :
 VM.find 7947 l0 = VM.find 7947 r0 ->
 VM.find 7765 l0 = VM.find 7765 r0 ->
 VM.find 65 l0 = VM.find 65 r0 ->
 formal_value_iter invalid flat_memories l0 false l0 flat_statements = Some l1 ->
 formal_value_iter invalid flat_memories l1 false l1 flat_statements = Some l2 ->
 formal_value_iter invalid flat_memories l2 false l2 flat_statements = Some l3 ->
 formal_value_iter invalid flat_memories l3 false l3 flat_statements = Some l4 ->
 formal_value_iter invalid flat_memories l4 false l4 flat_statements = Some l5 ->
 formal_value_iter invalid flat_memories l5 false l5 flat_statements = Some l6 ->
 formal_value_iter invalid flat_memories r0 false r0 flat_statements = Some r1 ->
 formal_value_iter invalid flat_memories r1 false r1 flat_statements = Some r2 ->
 formal_value_iter invalid flat_memories r2 false r2 flat_statements = Some r3 ->
 formal_value_iter invalid flat_memories r3 false r3 flat_statements = Some r4 ->
 formal_value_iter invalid flat_memories r4 false r4 flat_statements = Some r5 ->
 formal_value_iter invalid flat_memories r5 false r5 flat_statements = Some r6 ->
 VM.find 1395 l6 = VM.find 1395 r6.
Proof.
 intros Reg Stall Reset L1 L2 L3 L4 L5 L6 R1 R2 R3 R4 R5 R6.
 pose proof (checker_valid_congruent_after_four invalid l0 l1 l2 l3 l4 r0 r1 r2 r3 r4 Reg Stall Reset L1 L2 L3 L4 R1 R2 R3 R4) as Equal.
 destruct (checker_valid_comparison_normalized invalid l3 l3 l4 L4) as [value [Value Normal]].
 assert (Right : VM.find 7952 r4 = Some value) by (rewrite <- Equal; exact Value).
 rewrite (checker_output_after_two invalid l4 l5 l6 value Normal Value L5 L6).
 rewrite (checker_output_after_two invalid r4 r5 r6 value Normal Right R5 R6).
 reflexivity.
Qed.
Print Assumptions checker_valid_congruent_after_six.
