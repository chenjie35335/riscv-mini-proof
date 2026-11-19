Require Import CoreSocModel ComparisonNodes JointUpdateNodePositions JointUpdateExpressionCertificates SelectedNodeSafety FormalTypedNodeEquation.
From Coq Require Import ZArith List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Lemma startup_cast_member : List.In (7761,joint_update_expr_7761) joint_update_expected_nodes.
Proof. apply (List.nth_error_In joint_update_expected_nodes 881%nat). vm_compute. reflexivity. Qed.
Theorem startup_cast_value invalid old current result bit :
 VM.find 65 old = Some (Gval (Fuint 1) [::bit]) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 7761 result = Some (Gval (Fuint 1) [::bit]).
Proof.
 intros Reset Step.
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 7761 joint_update_expr_7761 joint_update_node_positions joint_update_node_safety startup_cast_member)
 as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [joint_update_expr_7761 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite Reset. destruct bit; reflexivity.
Qed.
Print Assumptions startup_cast_value.
