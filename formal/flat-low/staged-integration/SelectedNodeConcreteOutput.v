Require Import CoreSocModel ComparisonNodes SelectedNodeSafety X0ConcretePositionCertificate X0ConcreteSafetyCertificate FormalSuccessfulNodeEvaluation FormalTypedNodeEquation ConcreteExpressionClosure ConcreteGroundOperations.
From Coq Require Import List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Theorem selected_node_concrete_output offsets stmts entries node expression inputs path mm old current result :
 select_node_offsets offsets stmts = Some entries ->
 selected_node_safety mm stmts offsets stmts ->
 List.In (node, expression) entries ->
 concrete_expression_ready old expression ->
 (forall site value,
   eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm expression old old = Some value ->
   exists width, type_of_val value = Gtyp (Fuint width)) ->
 formal_value_iter (formal_invalid_policy inputs path) mm old false current stmts = Some result ->
 exists width bits, VM.find node result = Some (Gval (Fuint width) bits).
Proof.
 intros Selected Safe Member Ready Typed Step.
 destruct (selected_node_safe_position mm stmts offsets stmts entries node expression Selected Safe Member)
 as [count [tail [Position [Suffix Nonreg]]]].
 destruct (formal_successful_node_evaluation count stmts tail node expression _ mm old false current result Position Step)
 as [value Eval]. rewrite add0n in Eval.
 destruct (Typed _ value Eval) as [width ValueType].
 pose proof (formal_combinational_known_node count stmts tail node expression width value
 (formal_invalid_policy inputs path) mm old current result Position Suffix Nonreg Eval ValueType Step) as Lookup.
 destruct (concrete_expression_closure inputs path mm old expression Ready _ value Eval)
 as [ground [bits Value]]. subst value.
 cbn [type_of_val] in ValueType. inversion ValueType; subst ground.
 exists width, bits. exact Lookup.
Qed.
Corollary x0_selected_node_concrete_output node expression inputs path old current result :
 List.In (node, expression) x0_expected_nodes ->
 concrete_expression_ready old expression ->
 (forall site value,
   eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site flat_memories expression old old = Some value ->
   exists width, type_of_val value = Gtyp (Fuint width)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists width bits, VM.find node result = Some (Gval (Fuint width) bits).
Proof.
 intros Member Ready Typed Step.
 exact (selected_node_concrete_output x0_node_offsets flat_statements x0_expected_nodes node expression inputs path flat_memories old current result
 x0_actual_node_expressions x0_actual_nodes_safe Member Ready Typed Step).
Qed.
Print Assumptions x0_selected_node_concrete_output.
