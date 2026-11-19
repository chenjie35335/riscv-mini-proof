Require Import CoreSocModel ComparisonNodes JointUpdateNodePositions JointUpdateExpressionCertificates SelectedNodeSafety FormalTypedNodeEquation FrontPCNormalCommit.
From Coq Require Import ZArith List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Lemma front_pc_member_7799 : List.In (7799,joint_update_expr_7799) joint_update_expected_nodes.
Proof. apply (List.nth_error_In joint_update_expected_nodes 901%nat). vm_compute. reflexivity. Qed.
Theorem front_pc_node_7799 invalid old current result value :
 eval_hfexpr_with_memory flat_memories joint_update_expr_7799 old old = Some value ->
 type_of_val value = Gtyp (Fuint 1) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 7799 result = Some value.
Proof.
 intros Eval Typed Step.
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 7799 joint_update_expr_7799 joint_update_node_positions joint_update_node_safety front_pc_member_7799)
 as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg|exact Eval|exact Typed|exact Step].
Qed.
Lemma front_pc_member_7800 : List.In (7800,joint_update_expr_7800) joint_update_expected_nodes.
Proof. apply (List.nth_error_In joint_update_expected_nodes 902%nat). vm_compute. reflexivity. Qed.
Theorem front_pc_node_7800 invalid old current result value :
 eval_hfexpr_with_memory flat_memories joint_update_expr_7800 old old = Some value ->
 type_of_val value = Gtyp (Fuint 33) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 7800 result = Some value.
Proof.
 intros Eval Typed Step.
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 7800 joint_update_expr_7800 joint_update_node_positions joint_update_node_safety front_pc_member_7800)
 as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg|exact Eval|exact Typed|exact Step].
Qed.
Lemma front_pc_member_8159 : List.In (8159,joint_update_expr_8159) joint_update_expected_nodes.
Proof. apply (List.nth_error_In joint_update_expected_nodes 1041%nat). vm_compute. reflexivity. Qed.
Theorem front_pc_node_8159 invalid old current result value :
 eval_hfexpr_with_memory flat_memories joint_update_expr_8159 old old = Some value ->
 type_of_val value = Gtyp (Fuint 32) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8159 result = Some value.
Proof.
 intros Eval Typed Step.
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8159 joint_update_expr_8159 joint_update_node_positions joint_update_node_safety front_pc_member_8159)
 as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg|exact Eval|exact Typed|exact Step].
Qed.
Theorem front_pc_advance_control invalid old current result :
 VM.find 7765 old = Some (Gval (Fuint 1) [::false]) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 7799 result = Some (Gval (Fuint 1) [::true]).
Proof.
 intros Stall Step. apply (front_pc_node_7799 invalid old current result _); [|reflexivity|exact Step].
 cbn [joint_update_expr_7799 eval_hfexpr_with_memory eval_href_with_memory]. rewrite Stall. reflexivity.
Qed.
Theorem front_pc_fetch_selection invalid old current result fetch front :
 VM.find 7799 old = Some (Gval (Fuint 1) [::true]) ->
 VM.find 7768 old = Some (Gval (Fuint 33) fetch) -> size fetch = 33%nat ->
 VM.find 7749 old = Some (Gval (Fuint 32) front) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 7800 result = Some (Gval (Fuint 33) fetch).
Proof.
 intros Select Fetch Size Front Step.
 apply (front_pc_node_7800 invalid old current result _); [|reflexivity|exact Step].
 cbn [joint_update_expr_7800 eval_hfexpr_with_memory eval_href_with_memory]. rewrite Select.
 cbn [is_zero eval_hfexpr_with_memory eval_href_with_memory]. rewrite Fetch.
 unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref]. rewrite Front.
 cbn [option_map make_ftype_explicit type_of_val extend_hvalue_as_type ftype_mux fgtyp_mux adapt_hvalue_as_type].
 assert (Zero : is_zero [::true] = false) by (vm_compute;reflexivity).
 assert (Max : maxn 33 32 = 33%nat) by (vm_compute;reflexivity).
 rewrite Zero Max (front_pc_resize_sized 33 fetch Size). reflexivity.
Qed.
Theorem front_pc_reset_constant invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8159 result = Some (Gval (Fuint 32) (nseq 32 false)).
Proof. intro Step. apply (front_pc_node_8159 invalid old current result _); [reflexivity|reflexivity|exact Step]. Qed.
Print Assumptions front_pc_fetch_selection.
