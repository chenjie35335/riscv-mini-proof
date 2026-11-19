Require Import CoreSocModel ComparisonNodes SelectedNodeSafety X0ConcretePositionCertificate X0ConcreteSafetyCertificate FormalSuccessfulNodeEvaluation FormalTypedNodeEquation.
From Coq Require Import List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Theorem x0_selected_uint_node_congruent node expression invalid left right next_left next_right :
 List.In (node,expression) x0_expected_nodes ->
 (forall site, eval_hfexpr_validif_policy (isolated_validif_policy invalid) site flat_memories expression left left =
               eval_hfexpr_validif_policy (isolated_validif_policy invalid) site flat_memories expression right right) ->
 (forall site value, eval_hfexpr_validif_policy (isolated_validif_policy invalid) site flat_memories expression left left = Some value ->
   exists width, type_of_val value = Gtyp (Fuint width)) ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find node next_left = VM.find node next_right.
Proof.
 intros Member Equal Typed Left Right.
 destruct (selected_node_safe_position flat_memories flat_statements x0_node_offsets flat_statements
 x0_expected_nodes node expression x0_actual_node_expressions x0_actual_nodes_safe Member)
 as [count [tail [Position [Suffix Nonreg]]]].
 destruct (formal_successful_node_evaluation count flat_statements tail node expression invalid flat_memories left false left next_left Position Left)
 as [value Eval]. rewrite add0n in Eval.
 destruct (Typed _ value Eval) as [width ValueType].
 pose proof (formal_combinational_known_node count flat_statements tail node expression width value invalid
 flat_memories left left next_left Position Suffix Nonreg Eval ValueType Left) as LeftValue.
 assert (RightEval : eval_hfexpr_validif_policy (isolated_validif_policy invalid)
 (validif_raw_address nil count 0 nil) flat_memories expression right right = Some value).
 { rewrite <- Equal. exact Eval. }
 pose proof (formal_combinational_known_node count flat_statements tail node expression width value invalid
 flat_memories right right next_right Position Suffix Nonreg RightEval ValueType Right) as RightValue.
 rewrite LeftValue RightValue. reflexivity.
Qed.
Print Assumptions x0_selected_uint_node_congruent.
