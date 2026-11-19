Require Import CoreSocModel ComparisonNodes EarlyBubbleInstructionControl.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Theorem early_bubble_control_congruent_after_three invalid l0 l1 l2 l3 r0 r1 r2 r3 :
 VM.find 7762 l0 = VM.find 7762 r0 ->
 VM.find 85 l0 = VM.find 85 r0 ->
 VM.find 1360 l1 = VM.find 1360 r1 ->
 VM.find 128 l2 = VM.find 128 r2 ->
 formal_value_iter invalid flat_memories l0 false l0 flat_statements = Some l1 ->
 formal_value_iter invalid flat_memories l1 false l1 flat_statements = Some l2 ->
 formal_value_iter invalid flat_memories l2 false l2 flat_statements = Some l3 ->
 formal_value_iter invalid flat_memories r0 false r0 flat_statements = Some r1 ->
 formal_value_iter invalid flat_memories r1 false r1 flat_statements = Some r2 ->
 formal_value_iter invalid flat_memories r2 false r2 flat_statements = Some r3 ->
 VM.find 7944 l3 = VM.find 7944 r3.
Proof.
 intros Started Kill Branch Exception L1 L2 L3 R1 R2 R3.
 assert (A : VM.find 7942 l1 = VM.find 7942 r1).
 { rewrite (bubble_instruction_equation_7942 invalid l0 l0 l1 L1)
   (bubble_instruction_equation_7942 invalid r0 r0 r1 R1).
   cbn [bubble_instruction_expr_7942 eval_hfexpr_with_memory eval_href_with_memory].
   rewrite Started Kill. reflexivity. }
 assert (B : VM.find 7943 l2 = VM.find 7943 r2).
 { rewrite (bubble_instruction_equation_7943 invalid l1 l1 l2 L2)
   (bubble_instruction_equation_7943 invalid r1 r1 r2 R2).
   cbn [bubble_instruction_expr_7943 eval_hfexpr_with_memory eval_href_with_memory].
   rewrite A Branch. reflexivity. }
 rewrite (bubble_instruction_equation_7944 invalid l2 l2 l3 L3)
 (bubble_instruction_equation_7944 invalid r2 r2 r3 R3).
 cbn [bubble_instruction_expr_7944 eval_hfexpr_with_memory eval_href_with_memory].
 rewrite B Exception. reflexivity.
Qed.
Print Assumptions early_bubble_control_congruent_after_three.
