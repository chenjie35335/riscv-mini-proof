Require Import FormalGroundNodeEquation.
Require Import CoreSocModel ComparisonNodes SelectedNodeSafety X0ConcretePositionCertificate X0ConcreteSafetyCertificate FormalSuccessfulNodeEvaluation FormalTypedNodeEquation ConcreteExpressionClosure ConcreteGroundOperations.
From Coq Require Import List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Theorem selected_node_concrete_ground_output offsets stmts entries node expression inputs path mm old current result :
 select_node_offsets offsets stmts = Some entries ->
 selected_node_safety mm stmts offsets stmts ->
 List.In (node, expression) entries ->
 concrete_expression_ready old expression ->
 formal_value_iter (formal_invalid_policy inputs path) mm old false current stmts = Some result ->
 exists ground bits, VM.find node result = Some (Gval ground bits).
Proof.
 intros Selected Safe Member Ready Step.
 destruct (selected_node_safe_position mm stmts offsets stmts entries node expression Selected Safe Member)
 as [count [tail [Position [Suffix Nonreg]]]].
 destruct (formal_successful_node_evaluation count stmts tail node expression _ mm old false current result Position Step)
 as [value Eval]. rewrite add0n in Eval.
 destruct (concrete_expression_closure inputs path mm old expression Ready _ value Eval)
 as [ground [bits Value]]. subst value.
 pose proof (formal_combinational_known_ground_node count stmts tail node expression ground (Gval ground bits)
 (formal_invalid_policy inputs path) mm old current result Position Suffix Nonreg Eval (Logic.eq_refl _) Step) as Lookup.
 exists ground, bits. exact Lookup.
Qed.
Print Assumptions selected_node_concrete_ground_output.
