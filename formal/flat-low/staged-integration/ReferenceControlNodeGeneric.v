Require Import FormalTypedNodeFrames RegisterInvariants ScalarNodeFrames.
Require Import CoreSocModel ComparisonNodes ReferenceControlGroundOperations ReferenceControlGroundExpressions FormalGroundNodeEquation FormalSuccessfulNodeEvaluation SelectedGroundNodeCongruence SelectedNodeSafety.
From Coq Require Import List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Theorem reference_control_node_ground count tail node expression inputs path old current result :
 straight_drop count flat_statements = Some (Qcons (Snode node expression) tail) ->
 formal_typed_suffix_safe flat_memories node tail -> has_register node flat_statements = false ->
 reference_control_ready old expression ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find node result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros Position Safe Nonregister Ready Step.
 destruct (formal_successful_node_evaluation count flat_statements tail node expression (formal_invalid_policy inputs path) flat_memories old false current result Position Step)
 as [value Eval]. rewrite add0n in Eval.
 destruct (reference_control_expression_ground inputs path flat_memories old expression Ready _ value Eval) as [ground Typed].
 exists value, ground. split; [|exact Typed].
 exact (formal_combinational_known_ground_node count flat_statements tail node expression ground value (formal_invalid_policy inputs path)
 flat_memories old current result Position Safe Nonregister Eval Typed Step).
Qed.
Theorem reference_control_node_congruent count tail node expression inputs path left right next_left next_right :
 straight_drop count flat_statements = Some (Qcons (Snode node expression) tail) ->
 formal_typed_suffix_safe flat_memories node tail -> has_register node flat_statements = false ->
 reference_control_ready left expression ->
 (forall site, eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site flat_memories expression left left =
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site flat_memories expression right right) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find node next_left = VM.find node next_right.
Proof.
 intros Position Safe Nonreg Ready Equal Left Right.
 apply (selected_ground_node_congruent count tail node expression (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg Equal).
 - intros site value Eval. exact (reference_control_expression_ground inputs path flat_memories left expression Ready site value Eval).
 - exact Left.
 - exact Right.
Qed.
