Require Import CoreSocModel ComparisonNodes JointUpdateNodePositions JointUpdateExpressionCertificates SelectedNodeSafety FormalTypedNodeEquation FormalInstructionResetConstants.
From Coq Require Import ZArith List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Lemma front_instruction_member_7797 : List.In (7797,joint_update_expr_7797) joint_update_expected_nodes.
Proof. apply (List.nth_error_In joint_update_expected_nodes 900%nat). vm_compute. reflexivity. Qed.
Theorem front_instruction_node_7797 invalid old current result value :
 eval_hfexpr_with_memory flat_memories joint_update_expr_7797 old old = Some value ->
 type_of_val value = Gtyp (Fuint 32) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 7797 result = Some value.
Proof.
 intros Eval Typed Step.
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 7797 joint_update_expr_7797 joint_update_node_positions joint_update_node_safety front_instruction_member_7797)
 as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg|exact Eval|exact Typed|exact Step].
Qed.
Lemma front_instruction_member_7801 : List.In (7801,joint_update_expr_7801) joint_update_expected_nodes.
Proof. apply (List.nth_error_In joint_update_expected_nodes 903%nat). vm_compute. reflexivity. Qed.
Theorem front_instruction_node_7801 invalid old current result value :
 eval_hfexpr_with_memory flat_memories joint_update_expr_7801 old old = Some value ->
 type_of_val value = Gtyp (Fuint 32) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 7801 result = Some value.
Proof.
 intros Eval Typed Step.
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 7801 joint_update_expr_7801 joint_update_node_positions joint_update_node_safety front_instruction_member_7801)
 as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg|exact Eval|exact Typed|exact Step].
Qed.
Theorem front_instruction_inject_nop invalid old current result source :
 VM.find 7796 old = Some (Gval (Fuint 1) [::true]) ->
 VM.find 75 old = Some source -> type_of_val source = Gtyp (Fuint 32) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 7797 result = Some (Gval (Fuint 32) instruction_nop).
Proof.
 intros Kill Source Typed Step.
 apply (front_instruction_node_7797 invalid old current result _); [|reflexivity|exact Step].
 cbn [joint_update_expr_7797 eval_hfexpr_with_memory eval_href_with_memory]. rewrite Kill.
 unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref]. rewrite Source.
 cbn [option_map]. rewrite Typed. reflexivity.
Qed.
Theorem front_instruction_select_nop invalid old current result held :
 VM.find 7799 old = Some (Gval (Fuint 1) [::true]) ->
 VM.find 7797 old = Some (Gval (Fuint 32) instruction_nop) ->
 VM.find 7748 old = Some held -> type_of_val held = Gtyp (Fuint 32) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 7801 result = Some (Gval (Fuint 32) instruction_nop).
Proof.
 intros Advance Nop Held Typed Step.
 apply (front_instruction_node_7801 invalid old current result _); [|reflexivity|exact Step].
 cbn [joint_update_expr_7801 eval_hfexpr_with_memory eval_href_with_memory]. rewrite Advance.
 cbn [eval_hfexpr_with_memory eval_href_with_memory]. rewrite Nop.
 unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref]. rewrite Held.
 cbn [option_map]. rewrite Typed. reflexivity.
Qed.
Print Assumptions front_instruction_inject_nop.
Print Assumptions front_instruction_select_nop.
