Require Import CoreSocModel ComparisonNodes SelectedGroundNodeCongruence SelectedNodeSafety JointUpdateExpressionCertificates JointUpdateNodePositions ConcreteExpressionClosure.
From Coq Require Import ZArith List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Lemma early_control_joint_member_1361 : List.In (1361,joint_update_expr_1361) joint_update_expected_nodes.
Proof. apply (List.nth_error_In joint_update_expected_nodes 849%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_1361_congruent inputs path left right next_left next_right :
 (exists ground bits, VM.find 1357 left = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1358 left = Some (Gval ground bits)) ->
 VM.find 1357 left = VM.find 1357 right ->
 VM.find 1358 left = VM.find 1358 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 1361 next_left = VM.find 1361 next_right.
Proof.
 intros H1357 H1358 E1357 E1358 L R.
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 1361 joint_update_expr_1361 joint_update_node_positions joint_update_node_safety early_control_joint_member_1361)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_ground_node_congruent count tail 1361 joint_update_expr_1361 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [joint_update_expr_1361 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E1357.
   rewrite E1358.
   reflexivity.
 - intros site value Eval.
   destruct (concrete_expression_closure inputs path flat_memories left joint_update_expr_1361 (joint_update_ready_1361 left H1357 H1358) site value Eval) as [ground [bits Value]].
   subst value. exists ground. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_joint_member_1362 : List.In (1362,joint_update_expr_1362) joint_update_expected_nodes.
Proof. apply (List.nth_error_In joint_update_expected_nodes 850%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_1362_congruent inputs path left right next_left next_right :
 (exists ground bits, VM.find 1361 left = Some (Gval ground bits)) ->
 VM.find 1361 left = VM.find 1361 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 1362 next_left = VM.find 1362 next_right.
Proof.
 intros H1361 E1361 L R.
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 1362 joint_update_expr_1362 joint_update_node_positions joint_update_node_safety early_control_joint_member_1362)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_ground_node_congruent count tail 1362 joint_update_expr_1362 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [joint_update_expr_1362 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E1361.
   reflexivity.
 - intros site value Eval.
   destruct (concrete_expression_closure inputs path flat_memories left joint_update_expr_1362 (joint_update_ready_1362 left H1361) site value Eval) as [ground [bits Value]].
   subst value. exists ground. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_joint_member_1363 : List.In (1363,joint_update_expr_1363) joint_update_expected_nodes.
Proof. apply (List.nth_error_In joint_update_expected_nodes 851%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_1363_congruent inputs path left right next_left next_right :
 (exists ground bits, VM.find 1362 left = Some (Gval ground bits)) ->
 VM.find 1362 left = VM.find 1362 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 1363 next_left = VM.find 1363 next_right.
Proof.
 intros H1362 E1362 L R.
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 1363 joint_update_expr_1363 joint_update_node_positions joint_update_node_safety early_control_joint_member_1363)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_ground_node_congruent count tail 1363 joint_update_expr_1363 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [joint_update_expr_1363 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E1362.
   reflexivity.
 - intros site value Eval.
   destruct (concrete_expression_closure inputs path flat_memories left joint_update_expr_1363 (joint_update_ready_1363 left H1362) site value Eval) as [ground [bits Value]].
   subst value. exists ground. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_joint_member_1364 : List.In (1364,joint_update_expr_1364) joint_update_expected_nodes.
Proof. apply (List.nth_error_In joint_update_expected_nodes 852%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_1364_congruent inputs path left right next_left next_right :
 (exists ground bits, VM.find 1363 left = Some (Gval ground bits)) ->
 VM.find 1363 left = VM.find 1363 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 1364 next_left = VM.find 1364 next_right.
Proof.
 intros H1363 E1363 L R.
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 1364 joint_update_expr_1364 joint_update_node_positions joint_update_node_safety early_control_joint_member_1364)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_ground_node_congruent count tail 1364 joint_update_expr_1364 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [joint_update_expr_1364 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E1363.
   reflexivity.
 - intros site value Eval.
   destruct (concrete_expression_closure inputs path flat_memories left joint_update_expr_1364 (joint_update_ready_1364 left H1363) site value Eval) as [ground [bits Value]].
   subst value. exists ground. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_joint_member_1365 : List.In (1365,joint_update_expr_1365) joint_update_expected_nodes.
Proof. apply (List.nth_error_In joint_update_expected_nodes 853%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_1365_congruent inputs path left right next_left next_right :
 (exists ground bits, VM.find 1357 left = Some (Gval ground bits)) ->
 VM.find 1357 left = VM.find 1357 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 1365 next_left = VM.find 1365 next_right.
Proof.
 intros H1357 E1357 L R.
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 1365 joint_update_expr_1365 joint_update_node_positions joint_update_node_safety early_control_joint_member_1365)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_ground_node_congruent count tail 1365 joint_update_expr_1365 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [joint_update_expr_1365 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E1357.
   reflexivity.
 - intros site value Eval.
   destruct (concrete_expression_closure inputs path flat_memories left joint_update_expr_1365 (joint_update_ready_1365 left H1357) site value Eval) as [ground [bits Value]].
   subst value. exists ground. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_joint_member_1366 : List.In (1366,joint_update_expr_1366) joint_update_expected_nodes.
Proof. apply (List.nth_error_In joint_update_expected_nodes 854%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_1366_congruent inputs path left right next_left next_right :
 (exists ground bits, VM.find 1358 left = Some (Gval ground bits)) ->
 VM.find 1358 left = VM.find 1358 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 1366 next_left = VM.find 1366 next_right.
Proof.
 intros H1358 E1358 L R.
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 1366 joint_update_expr_1366 joint_update_node_positions joint_update_node_safety early_control_joint_member_1366)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_ground_node_congruent count tail 1366 joint_update_expr_1366 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [joint_update_expr_1366 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E1358.
   reflexivity.
 - intros site value Eval.
   destruct (concrete_expression_closure inputs path flat_memories left joint_update_expr_1366 (joint_update_ready_1366 left H1358) site value Eval) as [ground [bits Value]].
   subst value. exists ground. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_joint_member_1367 : List.In (1367,joint_update_expr_1367) joint_update_expected_nodes.
Proof. apply (List.nth_error_In joint_update_expected_nodes 855%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_1367_congruent inputs path left right next_left next_right :
 (exists ground bits, VM.find 1365 left = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1366 left = Some (Gval ground bits)) ->
 VM.find 1365 left = VM.find 1365 right ->
 VM.find 1366 left = VM.find 1366 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 1367 next_left = VM.find 1367 next_right.
Proof.
 intros H1365 H1366 E1365 E1366 L R.
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 1367 joint_update_expr_1367 joint_update_node_positions joint_update_node_safety early_control_joint_member_1367)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_ground_node_congruent count tail 1367 joint_update_expr_1367 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [joint_update_expr_1367 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E1365.
   rewrite E1366.
   reflexivity.
 - intros site value Eval.
   destruct (concrete_expression_closure inputs path flat_memories left joint_update_expr_1367 (joint_update_ready_1367 left H1365 H1366) site value Eval) as [ground [bits Value]].
   subst value. exists ground. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_joint_member_1368 : List.In (1368,joint_update_expr_1368) joint_update_expected_nodes.
Proof. apply (List.nth_error_In joint_update_expected_nodes 856%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_1368_congruent inputs path left right next_left next_right :
 (exists ground bits, VM.find 1362 left = Some (Gval ground bits)) ->
 VM.find 1362 left = VM.find 1362 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 1368 next_left = VM.find 1368 next_right.
Proof.
 intros H1362 E1362 L R.
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 1368 joint_update_expr_1368 joint_update_node_positions joint_update_node_safety early_control_joint_member_1368)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_ground_node_congruent count tail 1368 joint_update_expr_1368 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [joint_update_expr_1368 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E1362.
   reflexivity.
 - intros site value Eval.
   destruct (concrete_expression_closure inputs path flat_memories left joint_update_expr_1368 (joint_update_ready_1368 left H1362) site value Eval) as [ground [bits Value]].
   subst value. exists ground. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_joint_member_1369 : List.In (1369,joint_update_expr_1369) joint_update_expected_nodes.
Proof. apply (List.nth_error_In joint_update_expected_nodes 857%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_1369_congruent inputs path left right next_left next_right :
 (exists ground bits, VM.find 1357 left = Some (Gval ground bits)) ->
 VM.find 1357 left = VM.find 1357 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 1369 next_left = VM.find 1369 next_right.
Proof.
 intros H1357 E1357 L R.
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 1369 joint_update_expr_1369 joint_update_node_positions joint_update_node_safety early_control_joint_member_1369)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_ground_node_congruent count tail 1369 joint_update_expr_1369 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [joint_update_expr_1369 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E1357.
   reflexivity.
 - intros site value Eval.
   destruct (concrete_expression_closure inputs path flat_memories left joint_update_expr_1369 (joint_update_ready_1369 left H1357) site value Eval) as [ground [bits Value]].
   subst value. exists ground. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_joint_member_1370 : List.In (1370,joint_update_expr_1370) joint_update_expected_nodes.
Proof. apply (List.nth_error_In joint_update_expected_nodes 858%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_1370_congruent inputs path left right next_left next_right :
 (exists ground bits, VM.find 1367 left = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1368 left = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1369 left = Some (Gval ground bits)) ->
 VM.find 1367 left = VM.find 1367 right ->
 VM.find 1368 left = VM.find 1368 right ->
 VM.find 1369 left = VM.find 1369 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 1370 next_left = VM.find 1370 next_right.
Proof.
 intros H1367 H1368 H1369 E1367 E1368 E1369 L R.
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 1370 joint_update_expr_1370 joint_update_node_positions joint_update_node_safety early_control_joint_member_1370)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_ground_node_congruent count tail 1370 joint_update_expr_1370 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [joint_update_expr_1370 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E1367.
   rewrite E1368.
   rewrite E1369.
   reflexivity.
 - intros site value Eval.
   destruct (concrete_expression_closure inputs path flat_memories left joint_update_expr_1370 (joint_update_ready_1370 left H1367 H1368 H1369) site value Eval) as [ground [bits Value]].
   subst value. exists ground. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_joint_member_1371 : List.In (1371,joint_update_expr_1371) joint_update_expected_nodes.
Proof. apply (List.nth_error_In joint_update_expected_nodes 859%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_1371_congruent inputs path left right next_left next_right :
 (exists ground bits, VM.find 1362 left = Some (Gval ground bits)) ->
 VM.find 1362 left = VM.find 1362 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 1371 next_left = VM.find 1371 next_right.
Proof.
 intros H1362 E1362 L R.
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 1371 joint_update_expr_1371 joint_update_node_positions joint_update_node_safety early_control_joint_member_1371)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_ground_node_congruent count tail 1371 joint_update_expr_1371 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [joint_update_expr_1371 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E1362.
   reflexivity.
 - intros site value Eval.
   destruct (concrete_expression_closure inputs path flat_memories left joint_update_expr_1371 (joint_update_ready_1371 left H1362) site value Eval) as [ground [bits Value]].
   subst value. exists ground. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_joint_member_1372 : List.In (1372,joint_update_expr_1372) joint_update_expected_nodes.
Proof. apply (List.nth_error_In joint_update_expected_nodes 860%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_1372_congruent inputs path left right next_left next_right :
 (exists ground bits, VM.find 1358 left = Some (Gval ground bits)) ->
 VM.find 1358 left = VM.find 1358 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 1372 next_left = VM.find 1372 next_right.
Proof.
 intros H1358 E1358 L R.
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 1372 joint_update_expr_1372 joint_update_node_positions joint_update_node_safety early_control_joint_member_1372)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_ground_node_congruent count tail 1372 joint_update_expr_1372 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [joint_update_expr_1372 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E1358.
   reflexivity.
 - intros site value Eval.
   destruct (concrete_expression_closure inputs path flat_memories left joint_update_expr_1372 (joint_update_ready_1372 left H1358) site value Eval) as [ground [bits Value]].
   subst value. exists ground. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_joint_member_1373 : List.In (1373,joint_update_expr_1373) joint_update_expected_nodes.
Proof. apply (List.nth_error_In joint_update_expected_nodes 861%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_1373_congruent inputs path left right next_left next_right :
 (exists ground bits, VM.find 1367 left = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1371 left = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1372 left = Some (Gval ground bits)) ->
 VM.find 1367 left = VM.find 1367 right ->
 VM.find 1371 left = VM.find 1371 right ->
 VM.find 1372 left = VM.find 1372 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 1373 next_left = VM.find 1373 next_right.
Proof.
 intros H1367 H1371 H1372 E1367 E1371 E1372 L R.
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 1373 joint_update_expr_1373 joint_update_node_positions joint_update_node_safety early_control_joint_member_1373)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_ground_node_congruent count tail 1373 joint_update_expr_1373 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [joint_update_expr_1373 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E1367.
   rewrite E1371.
   rewrite E1372.
   reflexivity.
 - intros site value Eval.
   destruct (concrete_expression_closure inputs path flat_memories left joint_update_expr_1373 (joint_update_ready_1373 left H1367 H1371 H1372) site value Eval) as [ground [bits Value]].
   subst value. exists ground. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_joint_member_1374 : List.In (1374,joint_update_expr_1374) joint_update_expected_nodes.
Proof. apply (List.nth_error_In joint_update_expected_nodes 862%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_1374_congruent inputs path left right next_left next_right :
 (exists ground bits, VM.find 1370 left = Some (Gval ground bits)) ->
 VM.find 1370 left = VM.find 1370 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 1374 next_left = VM.find 1374 next_right.
Proof.
 intros H1370 E1370 L R.
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 1374 joint_update_expr_1374 joint_update_node_positions joint_update_node_safety early_control_joint_member_1374)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_ground_node_congruent count tail 1374 joint_update_expr_1374 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [joint_update_expr_1374 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E1370.
   reflexivity.
 - intros site value Eval.
   destruct (concrete_expression_closure inputs path flat_memories left joint_update_expr_1374 (joint_update_ready_1374 left H1370) site value Eval) as [ground [bits Value]].
   subst value. exists ground. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_joint_member_1375 : List.In (1375,joint_update_expr_1375) joint_update_expected_nodes.
Proof. apply (List.nth_error_In joint_update_expected_nodes 863%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_1375_congruent inputs path left right next_left next_right :
 (exists ground bits, VM.find 1373 left = Some (Gval ground bits)) ->
 VM.find 1373 left = VM.find 1373 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 1375 next_left = VM.find 1375 next_right.
Proof.
 intros H1373 E1373 L R.
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 1375 joint_update_expr_1375 joint_update_node_positions joint_update_node_safety early_control_joint_member_1375)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_ground_node_congruent count tail 1375 joint_update_expr_1375 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [joint_update_expr_1375 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E1373.
   reflexivity.
 - intros site value Eval.
   destruct (concrete_expression_closure inputs path flat_memories left joint_update_expr_1375 (joint_update_ready_1375 left H1373) site value Eval) as [ground [bits Value]].
   subst value. exists ground. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_joint_member_1376 : List.In (1376,joint_update_expr_1376) joint_update_expected_nodes.
Proof. apply (List.nth_error_In joint_update_expected_nodes 864%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_1376_congruent inputs path left right next_left next_right :
 (exists ground bits, VM.find 1359 left = Some (Gval ground bits)) ->
 VM.find 1359 left = VM.find 1359 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 1376 next_left = VM.find 1376 next_right.
Proof.
 intros H1359 E1359 L R.
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 1376 joint_update_expr_1376 joint_update_node_positions joint_update_node_safety early_control_joint_member_1376)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_ground_node_congruent count tail 1376 joint_update_expr_1376 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [joint_update_expr_1376 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E1359.
   reflexivity.
 - intros site value Eval.
   destruct (concrete_expression_closure inputs path flat_memories left joint_update_expr_1376 (joint_update_ready_1376 left H1359) site value Eval) as [ground [bits Value]].
   subst value. exists ground. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_joint_member_1377 : List.In (1377,joint_update_expr_1377) joint_update_expected_nodes.
Proof. apply (List.nth_error_In joint_update_expected_nodes 865%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_1377_congruent inputs path left right next_left next_right :
 (exists ground bits, VM.find 1364 left = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1376 left = Some (Gval ground bits)) ->
 VM.find 1364 left = VM.find 1364 right ->
 VM.find 1376 left = VM.find 1376 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 1377 next_left = VM.find 1377 next_right.
Proof.
 intros H1364 H1376 E1364 E1376 L R.
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 1377 joint_update_expr_1377 joint_update_node_positions joint_update_node_safety early_control_joint_member_1377)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_ground_node_congruent count tail 1377 joint_update_expr_1377 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [joint_update_expr_1377 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E1364.
   rewrite E1376.
   reflexivity.
 - intros site value Eval.
   destruct (concrete_expression_closure inputs path flat_memories left joint_update_expr_1377 (joint_update_ready_1377 left H1364 H1376) site value Eval) as [ground [bits Value]].
   subst value. exists ground. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_joint_member_1378 : List.In (1378,joint_update_expr_1378) joint_update_expected_nodes.
Proof. apply (List.nth_error_In joint_update_expected_nodes 866%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_1378_congruent inputs path left right next_left next_right :
 (exists ground bits, VM.find 1359 left = Some (Gval ground bits)) ->
 VM.find 1359 left = VM.find 1359 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 1378 next_left = VM.find 1378 next_right.
Proof.
 intros H1359 E1359 L R.
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 1378 joint_update_expr_1378 joint_update_node_positions joint_update_node_safety early_control_joint_member_1378)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_ground_node_congruent count tail 1378 joint_update_expr_1378 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [joint_update_expr_1378 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E1359.
   reflexivity.
 - intros site value Eval.
   destruct (concrete_expression_closure inputs path flat_memories left joint_update_expr_1378 (joint_update_ready_1378 left H1359) site value Eval) as [ground [bits Value]].
   subst value. exists ground. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_joint_member_1379 : List.In (1379,joint_update_expr_1379) joint_update_expected_nodes.
Proof. apply (List.nth_error_In joint_update_expected_nodes 867%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_1379_congruent inputs path left right next_left next_right :
 (exists ground bits, VM.find 1363 left = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1378 left = Some (Gval ground bits)) ->
 VM.find 1363 left = VM.find 1363 right ->
 VM.find 1378 left = VM.find 1378 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 1379 next_left = VM.find 1379 next_right.
Proof.
 intros H1363 H1378 E1363 E1378 L R.
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 1379 joint_update_expr_1379 joint_update_node_positions joint_update_node_safety early_control_joint_member_1379)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_ground_node_congruent count tail 1379 joint_update_expr_1379 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [joint_update_expr_1379 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E1363.
   rewrite E1378.
   reflexivity.
 - intros site value Eval.
   destruct (concrete_expression_closure inputs path flat_memories left joint_update_expr_1379 (joint_update_ready_1379 left H1363 H1378) site value Eval) as [ground [bits Value]].
   subst value. exists ground. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_joint_member_1380 : List.In (1380,joint_update_expr_1380) joint_update_expected_nodes.
Proof. apply (List.nth_error_In joint_update_expected_nodes 868%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_1380_congruent inputs path left right next_left next_right :
 (exists ground bits, VM.find 1377 left = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1379 left = Some (Gval ground bits)) ->
 VM.find 1377 left = VM.find 1377 right ->
 VM.find 1379 left = VM.find 1379 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 1380 next_left = VM.find 1380 next_right.
Proof.
 intros H1377 H1379 E1377 E1379 L R.
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 1380 joint_update_expr_1380 joint_update_node_positions joint_update_node_safety early_control_joint_member_1380)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_ground_node_congruent count tail 1380 joint_update_expr_1380 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [joint_update_expr_1380 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E1377.
   rewrite E1379.
   reflexivity.
 - intros site value Eval.
   destruct (concrete_expression_closure inputs path flat_memories left joint_update_expr_1380 (joint_update_ready_1380 left H1377 H1379) site value Eval) as [ground [bits Value]].
   subst value. exists ground. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_joint_member_1381 : List.In (1381,joint_update_expr_1381) joint_update_expected_nodes.
Proof. apply (List.nth_error_In joint_update_expected_nodes 869%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_1381_congruent inputs path left right next_left next_right :
 (exists ground bits, VM.find 1359 left = Some (Gval ground bits)) ->
 VM.find 1359 left = VM.find 1359 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 1381 next_left = VM.find 1381 next_right.
Proof.
 intros H1359 E1359 L R.
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 1381 joint_update_expr_1381 joint_update_node_positions joint_update_node_safety early_control_joint_member_1381)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_ground_node_congruent count tail 1381 joint_update_expr_1381 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [joint_update_expr_1381 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E1359.
   reflexivity.
 - intros site value Eval.
   destruct (concrete_expression_closure inputs path flat_memories left joint_update_expr_1381 (joint_update_ready_1381 left H1359) site value Eval) as [ground [bits Value]].
   subst value. exists ground. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_joint_member_1382 : List.In (1382,joint_update_expr_1382) joint_update_expected_nodes.
Proof. apply (List.nth_error_In joint_update_expected_nodes 870%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_1382_congruent inputs path left right next_left next_right :
 (exists ground bits, VM.find 1370 left = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1381 left = Some (Gval ground bits)) ->
 VM.find 1370 left = VM.find 1370 right ->
 VM.find 1381 left = VM.find 1381 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 1382 next_left = VM.find 1382 next_right.
Proof.
 intros H1370 H1381 E1370 E1381 L R.
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 1382 joint_update_expr_1382 joint_update_node_positions joint_update_node_safety early_control_joint_member_1382)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_ground_node_congruent count tail 1382 joint_update_expr_1382 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [joint_update_expr_1382 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E1370.
   rewrite E1381.
   reflexivity.
 - intros site value Eval.
   destruct (concrete_expression_closure inputs path flat_memories left joint_update_expr_1382 (joint_update_ready_1382 left H1370 H1381) site value Eval) as [ground [bits Value]].
   subst value. exists ground. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_joint_member_1383 : List.In (1383,joint_update_expr_1383) joint_update_expected_nodes.
Proof. apply (List.nth_error_In joint_update_expected_nodes 871%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_1383_congruent inputs path left right next_left next_right :
 (exists ground bits, VM.find 1380 left = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1382 left = Some (Gval ground bits)) ->
 VM.find 1380 left = VM.find 1380 right ->
 VM.find 1382 left = VM.find 1382 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 1383 next_left = VM.find 1383 next_right.
Proof.
 intros H1380 H1382 E1380 E1382 L R.
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 1383 joint_update_expr_1383 joint_update_node_positions joint_update_node_safety early_control_joint_member_1383)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_ground_node_congruent count tail 1383 joint_update_expr_1383 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [joint_update_expr_1383 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E1380.
   rewrite E1382.
   reflexivity.
 - intros site value Eval.
   destruct (concrete_expression_closure inputs path flat_memories left joint_update_expr_1383 (joint_update_ready_1383 left H1380 H1382) site value Eval) as [ground [bits Value]].
   subst value. exists ground. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_joint_member_1384 : List.In (1384,joint_update_expr_1384) joint_update_expected_nodes.
Proof. apply (List.nth_error_In joint_update_expected_nodes 872%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_1384_congruent inputs path left right next_left next_right :
 (exists ground bits, VM.find 1359 left = Some (Gval ground bits)) ->
 VM.find 1359 left = VM.find 1359 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 1384 next_left = VM.find 1384 next_right.
Proof.
 intros H1359 E1359 L R.
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 1384 joint_update_expr_1384 joint_update_node_positions joint_update_node_safety early_control_joint_member_1384)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_ground_node_congruent count tail 1384 joint_update_expr_1384 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [joint_update_expr_1384 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E1359.
   reflexivity.
 - intros site value Eval.
   destruct (concrete_expression_closure inputs path flat_memories left joint_update_expr_1384 (joint_update_ready_1384 left H1359) site value Eval) as [ground [bits Value]].
   subst value. exists ground. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_joint_member_1385 : List.In (1385,joint_update_expr_1385) joint_update_expected_nodes.
Proof. apply (List.nth_error_In joint_update_expected_nodes 873%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_1385_congruent inputs path left right next_left next_right :
 (exists ground bits, VM.find 1374 left = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1384 left = Some (Gval ground bits)) ->
 VM.find 1374 left = VM.find 1374 right ->
 VM.find 1384 left = VM.find 1384 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 1385 next_left = VM.find 1385 next_right.
Proof.
 intros H1374 H1384 E1374 E1384 L R.
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 1385 joint_update_expr_1385 joint_update_node_positions joint_update_node_safety early_control_joint_member_1385)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_ground_node_congruent count tail 1385 joint_update_expr_1385 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [joint_update_expr_1385 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E1374.
   rewrite E1384.
   reflexivity.
 - intros site value Eval.
   destruct (concrete_expression_closure inputs path flat_memories left joint_update_expr_1385 (joint_update_ready_1385 left H1374 H1384) site value Eval) as [ground [bits Value]].
   subst value. exists ground. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_joint_member_1386 : List.In (1386,joint_update_expr_1386) joint_update_expected_nodes.
Proof. apply (List.nth_error_In joint_update_expected_nodes 874%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_1386_congruent inputs path left right next_left next_right :
 (exists ground bits, VM.find 1383 left = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1385 left = Some (Gval ground bits)) ->
 VM.find 1383 left = VM.find 1383 right ->
 VM.find 1385 left = VM.find 1385 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 1386 next_left = VM.find 1386 next_right.
Proof.
 intros H1383 H1385 E1383 E1385 L R.
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 1386 joint_update_expr_1386 joint_update_node_positions joint_update_node_safety early_control_joint_member_1386)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_ground_node_congruent count tail 1386 joint_update_expr_1386 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [joint_update_expr_1386 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E1383.
   rewrite E1385.
   reflexivity.
 - intros site value Eval.
   destruct (concrete_expression_closure inputs path flat_memories left joint_update_expr_1386 (joint_update_ready_1386 left H1383 H1385) site value Eval) as [ground [bits Value]].
   subst value. exists ground. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_joint_member_1387 : List.In (1387,joint_update_expr_1387) joint_update_expected_nodes.
Proof. apply (List.nth_error_In joint_update_expected_nodes 875%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_1387_congruent inputs path left right next_left next_right :
 (exists ground bits, VM.find 1359 left = Some (Gval ground bits)) ->
 VM.find 1359 left = VM.find 1359 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 1387 next_left = VM.find 1387 next_right.
Proof.
 intros H1359 E1359 L R.
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 1387 joint_update_expr_1387 joint_update_node_positions joint_update_node_safety early_control_joint_member_1387)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_ground_node_congruent count tail 1387 joint_update_expr_1387 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [joint_update_expr_1387 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E1359.
   reflexivity.
 - intros site value Eval.
   destruct (concrete_expression_closure inputs path flat_memories left joint_update_expr_1387 (joint_update_ready_1387 left H1359) site value Eval) as [ground [bits Value]].
   subst value. exists ground. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_joint_member_1388 : List.In (1388,joint_update_expr_1388) joint_update_expected_nodes.
Proof. apply (List.nth_error_In joint_update_expected_nodes 876%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_1388_congruent inputs path left right next_left next_right :
 (exists ground bits, VM.find 1373 left = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1387 left = Some (Gval ground bits)) ->
 VM.find 1373 left = VM.find 1373 right ->
 VM.find 1387 left = VM.find 1387 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 1388 next_left = VM.find 1388 next_right.
Proof.
 intros H1373 H1387 E1373 E1387 L R.
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 1388 joint_update_expr_1388 joint_update_node_positions joint_update_node_safety early_control_joint_member_1388)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_ground_node_congruent count tail 1388 joint_update_expr_1388 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [joint_update_expr_1388 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E1373.
   rewrite E1387.
   reflexivity.
 - intros site value Eval.
   destruct (concrete_expression_closure inputs path flat_memories left joint_update_expr_1388 (joint_update_ready_1388 left H1373 H1387) site value Eval) as [ground [bits Value]].
   subst value. exists ground. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_joint_member_1389 : List.In (1389,joint_update_expr_1389) joint_update_expected_nodes.
Proof. apply (List.nth_error_In joint_update_expected_nodes 877%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_1389_congruent inputs path left right next_left next_right :
 (exists ground bits, VM.find 1386 left = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1388 left = Some (Gval ground bits)) ->
 VM.find 1386 left = VM.find 1386 right ->
 VM.find 1388 left = VM.find 1388 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 1389 next_left = VM.find 1389 next_right.
Proof.
 intros H1386 H1388 E1386 E1388 L R.
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 1389 joint_update_expr_1389 joint_update_node_positions joint_update_node_safety early_control_joint_member_1389)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_ground_node_congruent count tail 1389 joint_update_expr_1389 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [joint_update_expr_1389 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E1386.
   rewrite E1388.
   reflexivity.
 - intros site value Eval.
   destruct (concrete_expression_closure inputs path flat_memories left joint_update_expr_1389 (joint_update_ready_1389 left H1386 H1388) site value Eval) as [ground [bits Value]].
   subst value. exists ground. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_joint_member_1390 : List.In (1390,joint_update_expr_1390) joint_update_expected_nodes.
Proof. apply (List.nth_error_In joint_update_expected_nodes 878%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_1390_congruent inputs path left right next_left next_right :
 (exists ground bits, VM.find 1359 left = Some (Gval ground bits)) ->
 VM.find 1359 left = VM.find 1359 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 1390 next_left = VM.find 1390 next_right.
Proof.
 intros H1359 E1359 L R.
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 1390 joint_update_expr_1390 joint_update_node_positions joint_update_node_safety early_control_joint_member_1390)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_ground_node_congruent count tail 1390 joint_update_expr_1390 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [joint_update_expr_1390 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E1359.
   reflexivity.
 - intros site value Eval.
   destruct (concrete_expression_closure inputs path flat_memories left joint_update_expr_1390 (joint_update_ready_1390 left H1359) site value Eval) as [ground [bits Value]].
   subst value. exists ground. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_joint_member_1391 : List.In (1391,joint_update_expr_1391) joint_update_expected_nodes.
Proof. apply (List.nth_error_In joint_update_expected_nodes 879%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_1391_congruent inputs path left right next_left next_right :
 (exists ground bits, VM.find 1375 left = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1390 left = Some (Gval ground bits)) ->
 VM.find 1375 left = VM.find 1375 right ->
 VM.find 1390 left = VM.find 1390 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 1391 next_left = VM.find 1391 next_right.
Proof.
 intros H1375 H1390 E1375 E1390 L R.
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 1391 joint_update_expr_1391 joint_update_node_positions joint_update_node_safety early_control_joint_member_1391)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_ground_node_congruent count tail 1391 joint_update_expr_1391 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [joint_update_expr_1391 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E1375.
   rewrite E1390.
   reflexivity.
 - intros site value Eval.
   destruct (concrete_expression_closure inputs path flat_memories left joint_update_expr_1391 (joint_update_ready_1391 left H1375 H1390) site value Eval) as [ground [bits Value]].
   subst value. exists ground. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_joint_member_1392 : List.In (1392,joint_update_expr_1392) joint_update_expected_nodes.
Proof. apply (List.nth_error_In joint_update_expected_nodes 880%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_1392_congruent inputs path left right next_left next_right :
 (exists ground bits, VM.find 1389 left = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1391 left = Some (Gval ground bits)) ->
 VM.find 1389 left = VM.find 1389 right ->
 VM.find 1391 left = VM.find 1391 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 1392 next_left = VM.find 1392 next_right.
Proof.
 intros H1389 H1391 E1389 E1391 L R.
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 1392 joint_update_expr_1392 joint_update_node_positions joint_update_node_safety early_control_joint_member_1392)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_ground_node_congruent count tail 1392 joint_update_expr_1392 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [joint_update_expr_1392 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E1389.
   rewrite E1391.
   reflexivity.
 - intros site value Eval.
   destruct (concrete_expression_closure inputs path flat_memories left joint_update_expr_1392 (joint_update_ready_1392 left H1389 H1391) site value Eval) as [ground [bits Value]].
   subst value. exists ground. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_joint_member_8606 : List.In (8606,joint_update_expr_8606) joint_update_expected_nodes.
Proof. apply (List.nth_error_In joint_update_expected_nodes 1095%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8606_congruent inputs path left right next_left next_right :
 (exists ground bits, VM.find 8360 left = Some (Gval ground bits)) ->
 VM.find 8360 left = VM.find 8360 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8606 next_left = VM.find 8606 next_right.
Proof.
 intros H8360 E8360 L R.
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8606 joint_update_expr_8606 joint_update_node_positions joint_update_node_safety early_control_joint_member_8606)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_ground_node_congruent count tail 8606 joint_update_expr_8606 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [joint_update_expr_8606 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8360.
   reflexivity.
 - intros site value Eval.
   destruct (concrete_expression_closure inputs path flat_memories left joint_update_expr_8606 (joint_update_ready_8606 left H8360) site value Eval) as [ground [bits Value]].
   subst value. exists ground. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_joint_member_8607 : List.In (8607,joint_update_expr_8607) joint_update_expected_nodes.
Proof. apply (List.nth_error_In joint_update_expected_nodes 1096%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8607_congruent inputs path left right next_left next_right :
 (exists ground bits, VM.find 8358 left = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8606 left = Some (Gval ground bits)) ->
 VM.find 8358 left = VM.find 8358 right ->
 VM.find 8606 left = VM.find 8606 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8607 next_left = VM.find 8607 next_right.
Proof.
 intros H8358 H8606 E8358 E8606 L R.
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8607 joint_update_expr_8607 joint_update_node_positions joint_update_node_safety early_control_joint_member_8607)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_ground_node_congruent count tail 8607 joint_update_expr_8607 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [joint_update_expr_8607 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8358.
   rewrite E8606.
   reflexivity.
 - intros site value Eval.
   destruct (concrete_expression_closure inputs path flat_memories left joint_update_expr_8607 (joint_update_ready_8607 left H8358 H8606) site value Eval) as [ground [bits Value]].
   subst value. exists ground. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_joint_member_8608 : List.In (8608,joint_update_expr_8608) joint_update_expected_nodes.
Proof. apply (List.nth_error_In joint_update_expected_nodes 1097%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8608_congruent inputs path left right next_left next_right :
 (exists ground bits, VM.find 8356 left = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8607 left = Some (Gval ground bits)) ->
 VM.find 8356 left = VM.find 8356 right ->
 VM.find 8607 left = VM.find 8607 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8608 next_left = VM.find 8608 next_right.
Proof.
 intros H8356 H8607 E8356 E8607 L R.
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8608 joint_update_expr_8608 joint_update_node_positions joint_update_node_safety early_control_joint_member_8608)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_ground_node_congruent count tail 8608 joint_update_expr_8608 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [joint_update_expr_8608 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8356.
   rewrite E8607.
   reflexivity.
 - intros site value Eval.
   destruct (concrete_expression_closure inputs path flat_memories left joint_update_expr_8608 (joint_update_ready_8608 left H8356 H8607) site value Eval) as [ground [bits Value]].
   subst value. exists ground. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_joint_member_8609 : List.In (8609,joint_update_expr_8609) joint_update_expected_nodes.
Proof. apply (List.nth_error_In joint_update_expected_nodes 1098%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8609_congruent inputs path left right next_left next_right :
 (exists ground bits, VM.find 8354 left = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8608 left = Some (Gval ground bits)) ->
 VM.find 8354 left = VM.find 8354 right ->
 VM.find 8608 left = VM.find 8608 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8609 next_left = VM.find 8609 next_right.
Proof.
 intros H8354 H8608 E8354 E8608 L R.
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8609 joint_update_expr_8609 joint_update_node_positions joint_update_node_safety early_control_joint_member_8609)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_ground_node_congruent count tail 8609 joint_update_expr_8609 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [joint_update_expr_8609 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8354.
   rewrite E8608.
   reflexivity.
 - intros site value Eval.
   destruct (concrete_expression_closure inputs path flat_memories left joint_update_expr_8609 (joint_update_ready_8609 left H8354 H8608) site value Eval) as [ground [bits Value]].
   subst value. exists ground. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_joint_member_8610 : List.In (8610,joint_update_expr_8610) joint_update_expected_nodes.
Proof. apply (List.nth_error_In joint_update_expected_nodes 1099%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8610_congruent inputs path left right next_left next_right :
 (exists ground bits, VM.find 8352 left = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8609 left = Some (Gval ground bits)) ->
 VM.find 8352 left = VM.find 8352 right ->
 VM.find 8609 left = VM.find 8609 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8610 next_left = VM.find 8610 next_right.
Proof.
 intros H8352 H8609 E8352 E8609 L R.
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8610 joint_update_expr_8610 joint_update_node_positions joint_update_node_safety early_control_joint_member_8610)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_ground_node_congruent count tail 8610 joint_update_expr_8610 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [joint_update_expr_8610 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8352.
   rewrite E8609.
   reflexivity.
 - intros site value Eval.
   destruct (concrete_expression_closure inputs path flat_memories left joint_update_expr_8610 (joint_update_ready_8610 left H8352 H8609) site value Eval) as [ground [bits Value]].
   subst value. exists ground. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_joint_member_8611 : List.In (8611,joint_update_expr_8611) joint_update_expected_nodes.
Proof. apply (List.nth_error_In joint_update_expected_nodes 1100%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8611_congruent inputs path left right next_left next_right :
 (exists ground bits, VM.find 8350 left = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8610 left = Some (Gval ground bits)) ->
 VM.find 8350 left = VM.find 8350 right ->
 VM.find 8610 left = VM.find 8610 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8611 next_left = VM.find 8611 next_right.
Proof.
 intros H8350 H8610 E8350 E8610 L R.
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8611 joint_update_expr_8611 joint_update_node_positions joint_update_node_safety early_control_joint_member_8611)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_ground_node_congruent count tail 8611 joint_update_expr_8611 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [joint_update_expr_8611 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8350.
   rewrite E8610.
   reflexivity.
 - intros site value Eval.
   destruct (concrete_expression_closure inputs path flat_memories left joint_update_expr_8611 (joint_update_ready_8611 left H8350 H8610) site value Eval) as [ground [bits Value]].
   subst value. exists ground. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_joint_member_8612 : List.In (8612,joint_update_expr_8612) joint_update_expected_nodes.
Proof. apply (List.nth_error_In joint_update_expected_nodes 1101%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8612_congruent inputs path left right next_left next_right :
 (exists ground bits, VM.find 8348 left = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8611 left = Some (Gval ground bits)) ->
 VM.find 8348 left = VM.find 8348 right ->
 VM.find 8611 left = VM.find 8611 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8612 next_left = VM.find 8612 next_right.
Proof.
 intros H8348 H8611 E8348 E8611 L R.
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8612 joint_update_expr_8612 joint_update_node_positions joint_update_node_safety early_control_joint_member_8612)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_ground_node_congruent count tail 8612 joint_update_expr_8612 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [joint_update_expr_8612 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8348.
   rewrite E8611.
   reflexivity.
 - intros site value Eval.
   destruct (concrete_expression_closure inputs path flat_memories left joint_update_expr_8612 (joint_update_ready_8612 left H8348 H8611) site value Eval) as [ground [bits Value]].
   subst value. exists ground. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_joint_member_8613 : List.In (8613,joint_update_expr_8613) joint_update_expected_nodes.
Proof. apply (List.nth_error_In joint_update_expected_nodes 1102%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8613_congruent inputs path left right next_left next_right :
 (exists ground bits, VM.find 8346 left = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8612 left = Some (Gval ground bits)) ->
 VM.find 8346 left = VM.find 8346 right ->
 VM.find 8612 left = VM.find 8612 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8613 next_left = VM.find 8613 next_right.
Proof.
 intros H8346 H8612 E8346 E8612 L R.
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8613 joint_update_expr_8613 joint_update_node_positions joint_update_node_safety early_control_joint_member_8613)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_ground_node_congruent count tail 8613 joint_update_expr_8613 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [joint_update_expr_8613 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8346.
   rewrite E8612.
   reflexivity.
 - intros site value Eval.
   destruct (concrete_expression_closure inputs path flat_memories left joint_update_expr_8613 (joint_update_ready_8613 left H8346 H8612) site value Eval) as [ground [bits Value]].
   subst value. exists ground. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_joint_member_8614 : List.In (8614,joint_update_expr_8614) joint_update_expected_nodes.
Proof. apply (List.nth_error_In joint_update_expected_nodes 1103%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8614_congruent inputs path left right next_left next_right :
 (exists ground bits, VM.find 8344 left = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8613 left = Some (Gval ground bits)) ->
 VM.find 8344 left = VM.find 8344 right ->
 VM.find 8613 left = VM.find 8613 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8614 next_left = VM.find 8614 next_right.
Proof.
 intros H8344 H8613 E8344 E8613 L R.
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8614 joint_update_expr_8614 joint_update_node_positions joint_update_node_safety early_control_joint_member_8614)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_ground_node_congruent count tail 8614 joint_update_expr_8614 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [joint_update_expr_8614 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8344.
   rewrite E8613.
   reflexivity.
 - intros site value Eval.
   destruct (concrete_expression_closure inputs path flat_memories left joint_update_expr_8614 (joint_update_ready_8614 left H8344 H8613) site value Eval) as [ground [bits Value]].
   subst value. exists ground. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_joint_member_8615 : List.In (8615,joint_update_expr_8615) joint_update_expected_nodes.
Proof. apply (List.nth_error_In joint_update_expected_nodes 1104%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8615_congruent inputs path left right next_left next_right :
 (exists ground bits, VM.find 8342 left = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8614 left = Some (Gval ground bits)) ->
 VM.find 8342 left = VM.find 8342 right ->
 VM.find 8614 left = VM.find 8614 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8615 next_left = VM.find 8615 next_right.
Proof.
 intros H8342 H8614 E8342 E8614 L R.
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8615 joint_update_expr_8615 joint_update_node_positions joint_update_node_safety early_control_joint_member_8615)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_ground_node_congruent count tail 8615 joint_update_expr_8615 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [joint_update_expr_8615 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8342.
   rewrite E8614.
   reflexivity.
 - intros site value Eval.
   destruct (concrete_expression_closure inputs path flat_memories left joint_update_expr_8615 (joint_update_ready_8615 left H8342 H8614) site value Eval) as [ground [bits Value]].
   subst value. exists ground. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_joint_member_8616 : List.In (8616,joint_update_expr_8616) joint_update_expected_nodes.
Proof. apply (List.nth_error_In joint_update_expected_nodes 1105%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8616_congruent inputs path left right next_left next_right :
 (exists ground bits, VM.find 8340 left = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8615 left = Some (Gval ground bits)) ->
 VM.find 8340 left = VM.find 8340 right ->
 VM.find 8615 left = VM.find 8615 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8616 next_left = VM.find 8616 next_right.
Proof.
 intros H8340 H8615 E8340 E8615 L R.
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8616 joint_update_expr_8616 joint_update_node_positions joint_update_node_safety early_control_joint_member_8616)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_ground_node_congruent count tail 8616 joint_update_expr_8616 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [joint_update_expr_8616 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8340.
   rewrite E8615.
   reflexivity.
 - intros site value Eval.
   destruct (concrete_expression_closure inputs path flat_memories left joint_update_expr_8616 (joint_update_ready_8616 left H8340 H8615) site value Eval) as [ground [bits Value]].
   subst value. exists ground. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_joint_member_8617 : List.In (8617,joint_update_expr_8617) joint_update_expected_nodes.
Proof. apply (List.nth_error_In joint_update_expected_nodes 1106%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8617_congruent inputs path left right next_left next_right :
 (exists ground bits, VM.find 8338 left = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8616 left = Some (Gval ground bits)) ->
 VM.find 8338 left = VM.find 8338 right ->
 VM.find 8616 left = VM.find 8616 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8617 next_left = VM.find 8617 next_right.
Proof.
 intros H8338 H8616 E8338 E8616 L R.
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8617 joint_update_expr_8617 joint_update_node_positions joint_update_node_safety early_control_joint_member_8617)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_ground_node_congruent count tail 8617 joint_update_expr_8617 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [joint_update_expr_8617 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8338.
   rewrite E8616.
   reflexivity.
 - intros site value Eval.
   destruct (concrete_expression_closure inputs path flat_memories left joint_update_expr_8617 (joint_update_ready_8617 left H8338 H8616) site value Eval) as [ground [bits Value]].
   subst value. exists ground. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_joint_member_8618 : List.In (8618,joint_update_expr_8618) joint_update_expected_nodes.
Proof. apply (List.nth_error_In joint_update_expected_nodes 1107%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8618_congruent inputs path left right next_left next_right :
 (exists ground bits, VM.find 8336 left = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8617 left = Some (Gval ground bits)) ->
 VM.find 8336 left = VM.find 8336 right ->
 VM.find 8617 left = VM.find 8617 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8618 next_left = VM.find 8618 next_right.
Proof.
 intros H8336 H8617 E8336 E8617 L R.
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8618 joint_update_expr_8618 joint_update_node_positions joint_update_node_safety early_control_joint_member_8618)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_ground_node_congruent count tail 8618 joint_update_expr_8618 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [joint_update_expr_8618 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8336.
   rewrite E8617.
   reflexivity.
 - intros site value Eval.
   destruct (concrete_expression_closure inputs path flat_memories left joint_update_expr_8618 (joint_update_ready_8618 left H8336 H8617) site value Eval) as [ground [bits Value]].
   subst value. exists ground. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_joint_member_8619 : List.In (8619,joint_update_expr_8619) joint_update_expected_nodes.
Proof. apply (List.nth_error_In joint_update_expected_nodes 1108%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8619_congruent inputs path left right next_left next_right :
 (exists ground bits, VM.find 8334 left = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8618 left = Some (Gval ground bits)) ->
 VM.find 8334 left = VM.find 8334 right ->
 VM.find 8618 left = VM.find 8618 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8619 next_left = VM.find 8619 next_right.
Proof.
 intros H8334 H8618 E8334 E8618 L R.
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8619 joint_update_expr_8619 joint_update_node_positions joint_update_node_safety early_control_joint_member_8619)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_ground_node_congruent count tail 8619 joint_update_expr_8619 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [joint_update_expr_8619 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8334.
   rewrite E8618.
   reflexivity.
 - intros site value Eval.
   destruct (concrete_expression_closure inputs path flat_memories left joint_update_expr_8619 (joint_update_ready_8619 left H8334 H8618) site value Eval) as [ground [bits Value]].
   subst value. exists ground. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_joint_member_8620 : List.In (8620,joint_update_expr_8620) joint_update_expected_nodes.
Proof. apply (List.nth_error_In joint_update_expected_nodes 1109%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8620_congruent inputs path left right next_left next_right :
 (exists ground bits, VM.find 8332 left = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8619 left = Some (Gval ground bits)) ->
 VM.find 8332 left = VM.find 8332 right ->
 VM.find 8619 left = VM.find 8619 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8620 next_left = VM.find 8620 next_right.
Proof.
 intros H8332 H8619 E8332 E8619 L R.
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8620 joint_update_expr_8620 joint_update_node_positions joint_update_node_safety early_control_joint_member_8620)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_ground_node_congruent count tail 8620 joint_update_expr_8620 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [joint_update_expr_8620 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8332.
   rewrite E8619.
   reflexivity.
 - intros site value Eval.
   destruct (concrete_expression_closure inputs path flat_memories left joint_update_expr_8620 (joint_update_ready_8620 left H8332 H8619) site value Eval) as [ground [bits Value]].
   subst value. exists ground. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_joint_member_8621 : List.In (8621,joint_update_expr_8621) joint_update_expected_nodes.
Proof. apply (List.nth_error_In joint_update_expected_nodes 1110%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8621_congruent inputs path left right next_left next_right :
 (exists ground bits, VM.find 8330 left = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8620 left = Some (Gval ground bits)) ->
 VM.find 8330 left = VM.find 8330 right ->
 VM.find 8620 left = VM.find 8620 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8621 next_left = VM.find 8621 next_right.
Proof.
 intros H8330 H8620 E8330 E8620 L R.
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8621 joint_update_expr_8621 joint_update_node_positions joint_update_node_safety early_control_joint_member_8621)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_ground_node_congruent count tail 8621 joint_update_expr_8621 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [joint_update_expr_8621 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8330.
   rewrite E8620.
   reflexivity.
 - intros site value Eval.
   destruct (concrete_expression_closure inputs path flat_memories left joint_update_expr_8621 (joint_update_ready_8621 left H8330 H8620) site value Eval) as [ground [bits Value]].
   subst value. exists ground. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_joint_member_8622 : List.In (8622,joint_update_expr_8622) joint_update_expected_nodes.
Proof. apply (List.nth_error_In joint_update_expected_nodes 1111%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8622_congruent inputs path left right next_left next_right :
 (exists ground bits, VM.find 8328 left = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8621 left = Some (Gval ground bits)) ->
 VM.find 8328 left = VM.find 8328 right ->
 VM.find 8621 left = VM.find 8621 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8622 next_left = VM.find 8622 next_right.
Proof.
 intros H8328 H8621 E8328 E8621 L R.
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8622 joint_update_expr_8622 joint_update_node_positions joint_update_node_safety early_control_joint_member_8622)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_ground_node_congruent count tail 8622 joint_update_expr_8622 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [joint_update_expr_8622 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8328.
   rewrite E8621.
   reflexivity.
 - intros site value Eval.
   destruct (concrete_expression_closure inputs path flat_memories left joint_update_expr_8622 (joint_update_ready_8622 left H8328 H8621) site value Eval) as [ground [bits Value]].
   subst value. exists ground. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_joint_member_8623 : List.In (8623,joint_update_expr_8623) joint_update_expected_nodes.
Proof. apply (List.nth_error_In joint_update_expected_nodes 1112%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8623_congruent inputs path left right next_left next_right :
 (exists ground bits, VM.find 8326 left = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8622 left = Some (Gval ground bits)) ->
 VM.find 8326 left = VM.find 8326 right ->
 VM.find 8622 left = VM.find 8622 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8623 next_left = VM.find 8623 next_right.
Proof.
 intros H8326 H8622 E8326 E8622 L R.
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8623 joint_update_expr_8623 joint_update_node_positions joint_update_node_safety early_control_joint_member_8623)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_ground_node_congruent count tail 8623 joint_update_expr_8623 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [joint_update_expr_8623 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8326.
   rewrite E8622.
   reflexivity.
 - intros site value Eval.
   destruct (concrete_expression_closure inputs path flat_memories left joint_update_expr_8623 (joint_update_ready_8623 left H8326 H8622) site value Eval) as [ground [bits Value]].
   subst value. exists ground. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_joint_member_8624 : List.In (8624,joint_update_expr_8624) joint_update_expected_nodes.
Proof. apply (List.nth_error_In joint_update_expected_nodes 1113%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8624_congruent inputs path left right next_left next_right :
 (exists ground bits, VM.find 8324 left = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8623 left = Some (Gval ground bits)) ->
 VM.find 8324 left = VM.find 8324 right ->
 VM.find 8623 left = VM.find 8623 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8624 next_left = VM.find 8624 next_right.
Proof.
 intros H8324 H8623 E8324 E8623 L R.
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8624 joint_update_expr_8624 joint_update_node_positions joint_update_node_safety early_control_joint_member_8624)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_ground_node_congruent count tail 8624 joint_update_expr_8624 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [joint_update_expr_8624 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8324.
   rewrite E8623.
   reflexivity.
 - intros site value Eval.
   destruct (concrete_expression_closure inputs path flat_memories left joint_update_expr_8624 (joint_update_ready_8624 left H8324 H8623) site value Eval) as [ground [bits Value]].
   subst value. exists ground. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_joint_member_8625 : List.In (8625,joint_update_expr_8625) joint_update_expected_nodes.
Proof. apply (List.nth_error_In joint_update_expected_nodes 1114%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8625_congruent inputs path left right next_left next_right :
 (exists ground bits, VM.find 8322 left = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8624 left = Some (Gval ground bits)) ->
 VM.find 8322 left = VM.find 8322 right ->
 VM.find 8624 left = VM.find 8624 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8625 next_left = VM.find 8625 next_right.
Proof.
 intros H8322 H8624 E8322 E8624 L R.
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8625 joint_update_expr_8625 joint_update_node_positions joint_update_node_safety early_control_joint_member_8625)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_ground_node_congruent count tail 8625 joint_update_expr_8625 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [joint_update_expr_8625 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8322.
   rewrite E8624.
   reflexivity.
 - intros site value Eval.
   destruct (concrete_expression_closure inputs path flat_memories left joint_update_expr_8625 (joint_update_ready_8625 left H8322 H8624) site value Eval) as [ground [bits Value]].
   subst value. exists ground. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_joint_member_8626 : List.In (8626,joint_update_expr_8626) joint_update_expected_nodes.
Proof. apply (List.nth_error_In joint_update_expected_nodes 1115%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8626_congruent inputs path left right next_left next_right :
 (exists ground bits, VM.find 8320 left = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8625 left = Some (Gval ground bits)) ->
 VM.find 8320 left = VM.find 8320 right ->
 VM.find 8625 left = VM.find 8625 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8626 next_left = VM.find 8626 next_right.
Proof.
 intros H8320 H8625 E8320 E8625 L R.
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8626 joint_update_expr_8626 joint_update_node_positions joint_update_node_safety early_control_joint_member_8626)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_ground_node_congruent count tail 8626 joint_update_expr_8626 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [joint_update_expr_8626 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8320.
   rewrite E8625.
   reflexivity.
 - intros site value Eval.
   destruct (concrete_expression_closure inputs path flat_memories left joint_update_expr_8626 (joint_update_ready_8626 left H8320 H8625) site value Eval) as [ground [bits Value]].
   subst value. exists ground. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_joint_member_8627 : List.In (8627,joint_update_expr_8627) joint_update_expected_nodes.
Proof. apply (List.nth_error_In joint_update_expected_nodes 1116%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8627_congruent inputs path left right next_left next_right :
 (exists ground bits, VM.find 8318 left = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8626 left = Some (Gval ground bits)) ->
 VM.find 8318 left = VM.find 8318 right ->
 VM.find 8626 left = VM.find 8626 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8627 next_left = VM.find 8627 next_right.
Proof.
 intros H8318 H8626 E8318 E8626 L R.
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8627 joint_update_expr_8627 joint_update_node_positions joint_update_node_safety early_control_joint_member_8627)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_ground_node_congruent count tail 8627 joint_update_expr_8627 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [joint_update_expr_8627 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8318.
   rewrite E8626.
   reflexivity.
 - intros site value Eval.
   destruct (concrete_expression_closure inputs path flat_memories left joint_update_expr_8627 (joint_update_ready_8627 left H8318 H8626) site value Eval) as [ground [bits Value]].
   subst value. exists ground. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_joint_member_8628 : List.In (8628,joint_update_expr_8628) joint_update_expected_nodes.
Proof. apply (List.nth_error_In joint_update_expected_nodes 1117%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8628_congruent inputs path left right next_left next_right :
 (exists ground bits, VM.find 8316 left = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8627 left = Some (Gval ground bits)) ->
 VM.find 8316 left = VM.find 8316 right ->
 VM.find 8627 left = VM.find 8627 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8628 next_left = VM.find 8628 next_right.
Proof.
 intros H8316 H8627 E8316 E8627 L R.
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8628 joint_update_expr_8628 joint_update_node_positions joint_update_node_safety early_control_joint_member_8628)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_ground_node_congruent count tail 8628 joint_update_expr_8628 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [joint_update_expr_8628 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8316.
   rewrite E8627.
   reflexivity.
 - intros site value Eval.
   destruct (concrete_expression_closure inputs path flat_memories left joint_update_expr_8628 (joint_update_ready_8628 left H8316 H8627) site value Eval) as [ground [bits Value]].
   subst value. exists ground. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_joint_member_8629 : List.In (8629,joint_update_expr_8629) joint_update_expected_nodes.
Proof. apply (List.nth_error_In joint_update_expected_nodes 1118%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8629_congruent inputs path left right next_left next_right :
 (exists ground bits, VM.find 8314 left = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8628 left = Some (Gval ground bits)) ->
 VM.find 8314 left = VM.find 8314 right ->
 VM.find 8628 left = VM.find 8628 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8629 next_left = VM.find 8629 next_right.
Proof.
 intros H8314 H8628 E8314 E8628 L R.
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8629 joint_update_expr_8629 joint_update_node_positions joint_update_node_safety early_control_joint_member_8629)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_ground_node_congruent count tail 8629 joint_update_expr_8629 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [joint_update_expr_8629 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8314.
   rewrite E8628.
   reflexivity.
 - intros site value Eval.
   destruct (concrete_expression_closure inputs path flat_memories left joint_update_expr_8629 (joint_update_ready_8629 left H8314 H8628) site value Eval) as [ground [bits Value]].
   subst value. exists ground. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_joint_member_8630 : List.In (8630,joint_update_expr_8630) joint_update_expected_nodes.
Proof. apply (List.nth_error_In joint_update_expected_nodes 1119%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8630_congruent inputs path left right next_left next_right :
 (exists ground bits, VM.find 8312 left = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8629 left = Some (Gval ground bits)) ->
 VM.find 8312 left = VM.find 8312 right ->
 VM.find 8629 left = VM.find 8629 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8630 next_left = VM.find 8630 next_right.
Proof.
 intros H8312 H8629 E8312 E8629 L R.
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8630 joint_update_expr_8630 joint_update_node_positions joint_update_node_safety early_control_joint_member_8630)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_ground_node_congruent count tail 8630 joint_update_expr_8630 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [joint_update_expr_8630 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8312.
   rewrite E8629.
   reflexivity.
 - intros site value Eval.
   destruct (concrete_expression_closure inputs path flat_memories left joint_update_expr_8630 (joint_update_ready_8630 left H8312 H8629) site value Eval) as [ground [bits Value]].
   subst value. exists ground. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_joint_member_8631 : List.In (8631,joint_update_expr_8631) joint_update_expected_nodes.
Proof. apply (List.nth_error_In joint_update_expected_nodes 1120%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8631_congruent inputs path left right next_left next_right :
 (exists ground bits, VM.find 8310 left = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8630 left = Some (Gval ground bits)) ->
 VM.find 8310 left = VM.find 8310 right ->
 VM.find 8630 left = VM.find 8630 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8631 next_left = VM.find 8631 next_right.
Proof.
 intros H8310 H8630 E8310 E8630 L R.
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8631 joint_update_expr_8631 joint_update_node_positions joint_update_node_safety early_control_joint_member_8631)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_ground_node_congruent count tail 8631 joint_update_expr_8631 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [joint_update_expr_8631 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8310.
   rewrite E8630.
   reflexivity.
 - intros site value Eval.
   destruct (concrete_expression_closure inputs path flat_memories left joint_update_expr_8631 (joint_update_ready_8631 left H8310 H8630) site value Eval) as [ground [bits Value]].
   subst value. exists ground. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_joint_member_8632 : List.In (8632,joint_update_expr_8632) joint_update_expected_nodes.
Proof. apply (List.nth_error_In joint_update_expected_nodes 1121%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8632_congruent inputs path left right next_left next_right :
 (exists ground bits, VM.find 8308 left = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8631 left = Some (Gval ground bits)) ->
 VM.find 8308 left = VM.find 8308 right ->
 VM.find 8631 left = VM.find 8631 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8632 next_left = VM.find 8632 next_right.
Proof.
 intros H8308 H8631 E8308 E8631 L R.
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8632 joint_update_expr_8632 joint_update_node_positions joint_update_node_safety early_control_joint_member_8632)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_ground_node_congruent count tail 8632 joint_update_expr_8632 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [joint_update_expr_8632 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8308.
   rewrite E8631.
   reflexivity.
 - intros site value Eval.
   destruct (concrete_expression_closure inputs path flat_memories left joint_update_expr_8632 (joint_update_ready_8632 left H8308 H8631) site value Eval) as [ground [bits Value]].
   subst value. exists ground. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_joint_member_8633 : List.In (8633,joint_update_expr_8633) joint_update_expected_nodes.
Proof. apply (List.nth_error_In joint_update_expected_nodes 1122%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8633_congruent inputs path left right next_left next_right :
 (exists ground bits, VM.find 8306 left = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8632 left = Some (Gval ground bits)) ->
 VM.find 8306 left = VM.find 8306 right ->
 VM.find 8632 left = VM.find 8632 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8633 next_left = VM.find 8633 next_right.
Proof.
 intros H8306 H8632 E8306 E8632 L R.
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8633 joint_update_expr_8633 joint_update_node_positions joint_update_node_safety early_control_joint_member_8633)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_ground_node_congruent count tail 8633 joint_update_expr_8633 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [joint_update_expr_8633 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8306.
   rewrite E8632.
   reflexivity.
 - intros site value Eval.
   destruct (concrete_expression_closure inputs path flat_memories left joint_update_expr_8633 (joint_update_ready_8633 left H8306 H8632) site value Eval) as [ground [bits Value]].
   subst value. exists ground. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_joint_member_8634 : List.In (8634,joint_update_expr_8634) joint_update_expected_nodes.
Proof. apply (List.nth_error_In joint_update_expected_nodes 1123%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8634_congruent inputs path left right next_left next_right :
 (exists ground bits, VM.find 8304 left = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8633 left = Some (Gval ground bits)) ->
 VM.find 8304 left = VM.find 8304 right ->
 VM.find 8633 left = VM.find 8633 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8634 next_left = VM.find 8634 next_right.
Proof.
 intros H8304 H8633 E8304 E8633 L R.
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8634 joint_update_expr_8634 joint_update_node_positions joint_update_node_safety early_control_joint_member_8634)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_ground_node_congruent count tail 8634 joint_update_expr_8634 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [joint_update_expr_8634 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8304.
   rewrite E8633.
   reflexivity.
 - intros site value Eval.
   destruct (concrete_expression_closure inputs path flat_memories left joint_update_expr_8634 (joint_update_ready_8634 left H8304 H8633) site value Eval) as [ground [bits Value]].
   subst value. exists ground. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_joint_member_8635 : List.In (8635,joint_update_expr_8635) joint_update_expected_nodes.
Proof. apply (List.nth_error_In joint_update_expected_nodes 1124%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8635_congruent inputs path left right next_left next_right :
 (exists ground bits, VM.find 8302 left = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8634 left = Some (Gval ground bits)) ->
 VM.find 8302 left = VM.find 8302 right ->
 VM.find 8634 left = VM.find 8634 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8635 next_left = VM.find 8635 next_right.
Proof.
 intros H8302 H8634 E8302 E8634 L R.
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8635 joint_update_expr_8635 joint_update_node_positions joint_update_node_safety early_control_joint_member_8635)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_ground_node_congruent count tail 8635 joint_update_expr_8635 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [joint_update_expr_8635 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8302.
   rewrite E8634.
   reflexivity.
 - intros site value Eval.
   destruct (concrete_expression_closure inputs path flat_memories left joint_update_expr_8635 (joint_update_ready_8635 left H8302 H8634) site value Eval) as [ground [bits Value]].
   subst value. exists ground. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_joint_member_8636 : List.In (8636,joint_update_expr_8636) joint_update_expected_nodes.
Proof. apply (List.nth_error_In joint_update_expected_nodes 1125%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8636_congruent inputs path left right next_left next_right :
 (exists ground bits, VM.find 8300 left = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8635 left = Some (Gval ground bits)) ->
 VM.find 8300 left = VM.find 8300 right ->
 VM.find 8635 left = VM.find 8635 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8636 next_left = VM.find 8636 next_right.
Proof.
 intros H8300 H8635 E8300 E8635 L R.
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8636 joint_update_expr_8636 joint_update_node_positions joint_update_node_safety early_control_joint_member_8636)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_ground_node_congruent count tail 8636 joint_update_expr_8636 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [joint_update_expr_8636 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8300.
   rewrite E8635.
   reflexivity.
 - intros site value Eval.
   destruct (concrete_expression_closure inputs path flat_memories left joint_update_expr_8636 (joint_update_ready_8636 left H8300 H8635) site value Eval) as [ground [bits Value]].
   subst value. exists ground. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_joint_member_8637 : List.In (8637,joint_update_expr_8637) joint_update_expected_nodes.
Proof. apply (List.nth_error_In joint_update_expected_nodes 1126%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8637_congruent inputs path left right next_left next_right :
 (exists ground bits, VM.find 8298 left = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8636 left = Some (Gval ground bits)) ->
 VM.find 8298 left = VM.find 8298 right ->
 VM.find 8636 left = VM.find 8636 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8637 next_left = VM.find 8637 next_right.
Proof.
 intros H8298 H8636 E8298 E8636 L R.
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8637 joint_update_expr_8637 joint_update_node_positions joint_update_node_safety early_control_joint_member_8637)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_ground_node_congruent count tail 8637 joint_update_expr_8637 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [joint_update_expr_8637 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8298.
   rewrite E8636.
   reflexivity.
 - intros site value Eval.
   destruct (concrete_expression_closure inputs path flat_memories left joint_update_expr_8637 (joint_update_ready_8637 left H8298 H8636) site value Eval) as [ground [bits Value]].
   subst value. exists ground. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_joint_member_8638 : List.In (8638,joint_update_expr_8638) joint_update_expected_nodes.
Proof. apply (List.nth_error_In joint_update_expected_nodes 1127%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8638_congruent inputs path left right next_left next_right :
 (exists ground bits, VM.find 8296 left = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8637 left = Some (Gval ground bits)) ->
 VM.find 8296 left = VM.find 8296 right ->
 VM.find 8637 left = VM.find 8637 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8638 next_left = VM.find 8638 next_right.
Proof.
 intros H8296 H8637 E8296 E8637 L R.
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8638 joint_update_expr_8638 joint_update_node_positions joint_update_node_safety early_control_joint_member_8638)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_ground_node_congruent count tail 8638 joint_update_expr_8638 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [joint_update_expr_8638 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8296.
   rewrite E8637.
   reflexivity.
 - intros site value Eval.
   destruct (concrete_expression_closure inputs path flat_memories left joint_update_expr_8638 (joint_update_ready_8638 left H8296 H8637) site value Eval) as [ground [bits Value]].
   subst value. exists ground. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_joint_member_8639 : List.In (8639,joint_update_expr_8639) joint_update_expected_nodes.
Proof. apply (List.nth_error_In joint_update_expected_nodes 1128%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8639_congruent inputs path left right next_left next_right :
 (exists ground bits, VM.find 8294 left = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8638 left = Some (Gval ground bits)) ->
 VM.find 8294 left = VM.find 8294 right ->
 VM.find 8638 left = VM.find 8638 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8639 next_left = VM.find 8639 next_right.
Proof.
 intros H8294 H8638 E8294 E8638 L R.
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8639 joint_update_expr_8639 joint_update_node_positions joint_update_node_safety early_control_joint_member_8639)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_ground_node_congruent count tail 8639 joint_update_expr_8639 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [joint_update_expr_8639 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8294.
   rewrite E8638.
   reflexivity.
 - intros site value Eval.
   destruct (concrete_expression_closure inputs path flat_memories left joint_update_expr_8639 (joint_update_ready_8639 left H8294 H8638) site value Eval) as [ground [bits Value]].
   subst value. exists ground. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_joint_member_8640 : List.In (8640,joint_update_expr_8640) joint_update_expected_nodes.
Proof. apply (List.nth_error_In joint_update_expected_nodes 1129%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8640_congruent inputs path left right next_left next_right :
 (exists ground bits, VM.find 8292 left = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8639 left = Some (Gval ground bits)) ->
 VM.find 8292 left = VM.find 8292 right ->
 VM.find 8639 left = VM.find 8639 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8640 next_left = VM.find 8640 next_right.
Proof.
 intros H8292 H8639 E8292 E8639 L R.
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8640 joint_update_expr_8640 joint_update_node_positions joint_update_node_safety early_control_joint_member_8640)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_ground_node_congruent count tail 8640 joint_update_expr_8640 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [joint_update_expr_8640 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8292.
   rewrite E8639.
   reflexivity.
 - intros site value Eval.
   destruct (concrete_expression_closure inputs path flat_memories left joint_update_expr_8640 (joint_update_ready_8640 left H8292 H8639) site value Eval) as [ground [bits Value]].
   subst value. exists ground. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_joint_member_8641 : List.In (8641,joint_update_expr_8641) joint_update_expected_nodes.
Proof. apply (List.nth_error_In joint_update_expected_nodes 1130%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8641_congruent inputs path left right next_left next_right :
 (exists ground bits, VM.find 8290 left = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8640 left = Some (Gval ground bits)) ->
 VM.find 8290 left = VM.find 8290 right ->
 VM.find 8640 left = VM.find 8640 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8641 next_left = VM.find 8641 next_right.
Proof.
 intros H8290 H8640 E8290 E8640 L R.
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8641 joint_update_expr_8641 joint_update_node_positions joint_update_node_safety early_control_joint_member_8641)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_ground_node_congruent count tail 8641 joint_update_expr_8641 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [joint_update_expr_8641 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8290.
   rewrite E8640.
   reflexivity.
 - intros site value Eval.
   destruct (concrete_expression_closure inputs path flat_memories left joint_update_expr_8641 (joint_update_ready_8641 left H8290 H8640) site value Eval) as [ground [bits Value]].
   subst value. exists ground. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_joint_member_8642 : List.In (8642,joint_update_expr_8642) joint_update_expected_nodes.
Proof. apply (List.nth_error_In joint_update_expected_nodes 1131%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8642_congruent inputs path left right next_left next_right :
 (exists ground bits, VM.find 8288 left = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8641 left = Some (Gval ground bits)) ->
 VM.find 8288 left = VM.find 8288 right ->
 VM.find 8641 left = VM.find 8641 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8642 next_left = VM.find 8642 next_right.
Proof.
 intros H8288 H8641 E8288 E8641 L R.
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8642 joint_update_expr_8642 joint_update_node_positions joint_update_node_safety early_control_joint_member_8642)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_ground_node_congruent count tail 8642 joint_update_expr_8642 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [joint_update_expr_8642 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8288.
   rewrite E8641.
   reflexivity.
 - intros site value Eval.
   destruct (concrete_expression_closure inputs path flat_memories left joint_update_expr_8642 (joint_update_ready_8642 left H8288 H8641) site value Eval) as [ground [bits Value]].
   subst value. exists ground. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_joint_member_8643 : List.In (8643,joint_update_expr_8643) joint_update_expected_nodes.
Proof. apply (List.nth_error_In joint_update_expected_nodes 1132%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8643_congruent inputs path left right next_left next_right :
 (exists ground bits, VM.find 8286 left = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8642 left = Some (Gval ground bits)) ->
 VM.find 8286 left = VM.find 8286 right ->
 VM.find 8642 left = VM.find 8642 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8643 next_left = VM.find 8643 next_right.
Proof.
 intros H8286 H8642 E8286 E8642 L R.
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8643 joint_update_expr_8643 joint_update_node_positions joint_update_node_safety early_control_joint_member_8643)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_ground_node_congruent count tail 8643 joint_update_expr_8643 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [joint_update_expr_8643 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8286.
   rewrite E8642.
   reflexivity.
 - intros site value Eval.
   destruct (concrete_expression_closure inputs path flat_memories left joint_update_expr_8643 (joint_update_ready_8643 left H8286 H8642) site value Eval) as [ground [bits Value]].
   subst value. exists ground. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_joint_member_8644 : List.In (8644,joint_update_expr_8644) joint_update_expected_nodes.
Proof. apply (List.nth_error_In joint_update_expected_nodes 1133%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8644_congruent inputs path left right next_left next_right :
 (exists ground bits, VM.find 8284 left = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8643 left = Some (Gval ground bits)) ->
 VM.find 8284 left = VM.find 8284 right ->
 VM.find 8643 left = VM.find 8643 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8644 next_left = VM.find 8644 next_right.
Proof.
 intros H8284 H8643 E8284 E8643 L R.
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8644 joint_update_expr_8644 joint_update_node_positions joint_update_node_safety early_control_joint_member_8644)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_ground_node_congruent count tail 8644 joint_update_expr_8644 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [joint_update_expr_8644 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8284.
   rewrite E8643.
   reflexivity.
 - intros site value Eval.
   destruct (concrete_expression_closure inputs path flat_memories left joint_update_expr_8644 (joint_update_ready_8644 left H8284 H8643) site value Eval) as [ground [bits Value]].
   subst value. exists ground. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_joint_member_8645 : List.In (8645,joint_update_expr_8645) joint_update_expected_nodes.
Proof. apply (List.nth_error_In joint_update_expected_nodes 1134%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8645_congruent inputs path left right next_left next_right :
 (exists ground bits, VM.find 8282 left = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8644 left = Some (Gval ground bits)) ->
 VM.find 8282 left = VM.find 8282 right ->
 VM.find 8644 left = VM.find 8644 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8645 next_left = VM.find 8645 next_right.
Proof.
 intros H8282 H8644 E8282 E8644 L R.
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8645 joint_update_expr_8645 joint_update_node_positions joint_update_node_safety early_control_joint_member_8645)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_ground_node_congruent count tail 8645 joint_update_expr_8645 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [joint_update_expr_8645 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8282.
   rewrite E8644.
   reflexivity.
 - intros site value Eval.
   destruct (concrete_expression_closure inputs path flat_memories left joint_update_expr_8645 (joint_update_ready_8645 left H8282 H8644) site value Eval) as [ground [bits Value]].
   subst value. exists ground. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_joint_member_8646 : List.In (8646,joint_update_expr_8646) joint_update_expected_nodes.
Proof. apply (List.nth_error_In joint_update_expected_nodes 1135%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8646_congruent inputs path left right next_left next_right :
 (exists ground bits, VM.find 8280 left = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8645 left = Some (Gval ground bits)) ->
 VM.find 8280 left = VM.find 8280 right ->
 VM.find 8645 left = VM.find 8645 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8646 next_left = VM.find 8646 next_right.
Proof.
 intros H8280 H8645 E8280 E8645 L R.
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8646 joint_update_expr_8646 joint_update_node_positions joint_update_node_safety early_control_joint_member_8646)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_ground_node_congruent count tail 8646 joint_update_expr_8646 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [joint_update_expr_8646 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8280.
   rewrite E8645.
   reflexivity.
 - intros site value Eval.
   destruct (concrete_expression_closure inputs path flat_memories left joint_update_expr_8646 (joint_update_ready_8646 left H8280 H8645) site value Eval) as [ground [bits Value]].
   subst value. exists ground. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_joint_member_8647 : List.In (8647,joint_update_expr_8647) joint_update_expected_nodes.
Proof. apply (List.nth_error_In joint_update_expected_nodes 1136%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8647_congruent inputs path left right next_left next_right :
 (exists ground bits, VM.find 8278 left = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8646 left = Some (Gval ground bits)) ->
 VM.find 8278 left = VM.find 8278 right ->
 VM.find 8646 left = VM.find 8646 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8647 next_left = VM.find 8647 next_right.
Proof.
 intros H8278 H8646 E8278 E8646 L R.
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8647 joint_update_expr_8647 joint_update_node_positions joint_update_node_safety early_control_joint_member_8647)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_ground_node_congruent count tail 8647 joint_update_expr_8647 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [joint_update_expr_8647 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8278.
   rewrite E8646.
   reflexivity.
 - intros site value Eval.
   destruct (concrete_expression_closure inputs path flat_memories left joint_update_expr_8647 (joint_update_ready_8647 left H8278 H8646) site value Eval) as [ground [bits Value]].
   subst value. exists ground. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_joint_member_8648 : List.In (8648,joint_update_expr_8648) joint_update_expected_nodes.
Proof. apply (List.nth_error_In joint_update_expected_nodes 1137%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8648_congruent inputs path left right next_left next_right :
 (exists ground bits, VM.find 8276 left = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8647 left = Some (Gval ground bits)) ->
 VM.find 8276 left = VM.find 8276 right ->
 VM.find 8647 left = VM.find 8647 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8648 next_left = VM.find 8648 next_right.
Proof.
 intros H8276 H8647 E8276 E8647 L R.
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8648 joint_update_expr_8648 joint_update_node_positions joint_update_node_safety early_control_joint_member_8648)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_ground_node_congruent count tail 8648 joint_update_expr_8648 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [joint_update_expr_8648 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8276.
   rewrite E8647.
   reflexivity.
 - intros site value Eval.
   destruct (concrete_expression_closure inputs path flat_memories left joint_update_expr_8648 (joint_update_ready_8648 left H8276 H8647) site value Eval) as [ground [bits Value]].
   subst value. exists ground. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_joint_member_8649 : List.In (8649,joint_update_expr_8649) joint_update_expected_nodes.
Proof. apply (List.nth_error_In joint_update_expected_nodes 1138%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8649_congruent inputs path left right next_left next_right :
 (exists ground bits, VM.find 8274 left = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8648 left = Some (Gval ground bits)) ->
 VM.find 8274 left = VM.find 8274 right ->
 VM.find 8648 left = VM.find 8648 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8649 next_left = VM.find 8649 next_right.
Proof.
 intros H8274 H8648 E8274 E8648 L R.
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8649 joint_update_expr_8649 joint_update_node_positions joint_update_node_safety early_control_joint_member_8649)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_ground_node_congruent count tail 8649 joint_update_expr_8649 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [joint_update_expr_8649 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8274.
   rewrite E8648.
   reflexivity.
 - intros site value Eval.
   destruct (concrete_expression_closure inputs path flat_memories left joint_update_expr_8649 (joint_update_ready_8649 left H8274 H8648) site value Eval) as [ground [bits Value]].
   subst value. exists ground. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_joint_member_8650 : List.In (8650,joint_update_expr_8650) joint_update_expected_nodes.
Proof. apply (List.nth_error_In joint_update_expected_nodes 1139%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8650_congruent inputs path left right next_left next_right :
 (exists ground bits, VM.find 8272 left = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8649 left = Some (Gval ground bits)) ->
 VM.find 8272 left = VM.find 8272 right ->
 VM.find 8649 left = VM.find 8649 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8650 next_left = VM.find 8650 next_right.
Proof.
 intros H8272 H8649 E8272 E8649 L R.
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8650 joint_update_expr_8650 joint_update_node_positions joint_update_node_safety early_control_joint_member_8650)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_ground_node_congruent count tail 8650 joint_update_expr_8650 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [joint_update_expr_8650 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8272.
   rewrite E8649.
   reflexivity.
 - intros site value Eval.
   destruct (concrete_expression_closure inputs path flat_memories left joint_update_expr_8650 (joint_update_ready_8650 left H8272 H8649) site value Eval) as [ground [bits Value]].
   subst value. exists ground. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_joint_member_8651 : List.In (8651,joint_update_expr_8651) joint_update_expected_nodes.
Proof. apply (List.nth_error_In joint_update_expected_nodes 1140%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8651_congruent inputs path left right next_left next_right :
 (exists ground bits, VM.find 8270 left = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8650 left = Some (Gval ground bits)) ->
 VM.find 8270 left = VM.find 8270 right ->
 VM.find 8650 left = VM.find 8650 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8651 next_left = VM.find 8651 next_right.
Proof.
 intros H8270 H8650 E8270 E8650 L R.
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8651 joint_update_expr_8651 joint_update_node_positions joint_update_node_safety early_control_joint_member_8651)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_ground_node_congruent count tail 8651 joint_update_expr_8651 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [joint_update_expr_8651 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8270.
   rewrite E8650.
   reflexivity.
 - intros site value Eval.
   destruct (concrete_expression_closure inputs path flat_memories left joint_update_expr_8651 (joint_update_ready_8651 left H8270 H8650) site value Eval) as [ground [bits Value]].
   subst value. exists ground. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_joint_member_8652 : List.In (8652,joint_update_expr_8652) joint_update_expected_nodes.
Proof. apply (List.nth_error_In joint_update_expected_nodes 1141%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8652_congruent inputs path left right next_left next_right :
 (exists ground bits, VM.find 8268 left = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8651 left = Some (Gval ground bits)) ->
 VM.find 8268 left = VM.find 8268 right ->
 VM.find 8651 left = VM.find 8651 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8652 next_left = VM.find 8652 next_right.
Proof.
 intros H8268 H8651 E8268 E8651 L R.
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8652 joint_update_expr_8652 joint_update_node_positions joint_update_node_safety early_control_joint_member_8652)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_ground_node_congruent count tail 8652 joint_update_expr_8652 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [joint_update_expr_8652 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8268.
   rewrite E8651.
   reflexivity.
 - intros site value Eval.
   destruct (concrete_expression_closure inputs path flat_memories left joint_update_expr_8652 (joint_update_ready_8652 left H8268 H8651) site value Eval) as [ground [bits Value]].
   subst value. exists ground. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_joint_member_8653 : List.In (8653,joint_update_expr_8653) joint_update_expected_nodes.
Proof. apply (List.nth_error_In joint_update_expected_nodes 1142%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8653_congruent inputs path left right next_left next_right :
 (exists ground bits, VM.find 8266 left = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8652 left = Some (Gval ground bits)) ->
 VM.find 8266 left = VM.find 8266 right ->
 VM.find 8652 left = VM.find 8652 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8653 next_left = VM.find 8653 next_right.
Proof.
 intros H8266 H8652 E8266 E8652 L R.
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8653 joint_update_expr_8653 joint_update_node_positions joint_update_node_safety early_control_joint_member_8653)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_ground_node_congruent count tail 8653 joint_update_expr_8653 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [joint_update_expr_8653 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8266.
   rewrite E8652.
   reflexivity.
 - intros site value Eval.
   destruct (concrete_expression_closure inputs path flat_memories left joint_update_expr_8653 (joint_update_ready_8653 left H8266 H8652) site value Eval) as [ground [bits Value]].
   subst value. exists ground. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_joint_member_8654 : List.In (8654,joint_update_expr_8654) joint_update_expected_nodes.
Proof. apply (List.nth_error_In joint_update_expected_nodes 1143%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8654_congruent inputs path left right next_left next_right :
 (exists ground bits, VM.find 8264 left = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8653 left = Some (Gval ground bits)) ->
 VM.find 8264 left = VM.find 8264 right ->
 VM.find 8653 left = VM.find 8653 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8654 next_left = VM.find 8654 next_right.
Proof.
 intros H8264 H8653 E8264 E8653 L R.
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8654 joint_update_expr_8654 joint_update_node_positions joint_update_node_safety early_control_joint_member_8654)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_ground_node_congruent count tail 8654 joint_update_expr_8654 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [joint_update_expr_8654 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8264.
   rewrite E8653.
   reflexivity.
 - intros site value Eval.
   destruct (concrete_expression_closure inputs path flat_memories left joint_update_expr_8654 (joint_update_ready_8654 left H8264 H8653) site value Eval) as [ground [bits Value]].
   subst value. exists ground. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_joint_member_8655 : List.In (8655,joint_update_expr_8655) joint_update_expected_nodes.
Proof. apply (List.nth_error_In joint_update_expected_nodes 1144%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8655_congruent inputs path left right next_left next_right :
 (exists ground bits, VM.find 8360 left = Some (Gval ground bits)) ->
 VM.find 8360 left = VM.find 8360 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8655 next_left = VM.find 8655 next_right.
Proof.
 intros H8360 E8360 L R.
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8655 joint_update_expr_8655 joint_update_node_positions joint_update_node_safety early_control_joint_member_8655)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_ground_node_congruent count tail 8655 joint_update_expr_8655 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [joint_update_expr_8655 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8360.
   reflexivity.
 - intros site value Eval.
   destruct (concrete_expression_closure inputs path flat_memories left joint_update_expr_8655 (joint_update_ready_8655 left H8360) site value Eval) as [ground [bits Value]].
   subst value. exists ground. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_joint_member_8656 : List.In (8656,joint_update_expr_8656) joint_update_expected_nodes.
Proof. apply (List.nth_error_In joint_update_expected_nodes 1145%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8656_congruent inputs path left right next_left next_right :
 (exists ground bits, VM.find 8358 left = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8655 left = Some (Gval ground bits)) ->
 VM.find 8358 left = VM.find 8358 right ->
 VM.find 8655 left = VM.find 8655 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8656 next_left = VM.find 8656 next_right.
Proof.
 intros H8358 H8655 E8358 E8655 L R.
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8656 joint_update_expr_8656 joint_update_node_positions joint_update_node_safety early_control_joint_member_8656)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_ground_node_congruent count tail 8656 joint_update_expr_8656 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [joint_update_expr_8656 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8358.
   rewrite E8655.
   reflexivity.
 - intros site value Eval.
   destruct (concrete_expression_closure inputs path flat_memories left joint_update_expr_8656 (joint_update_ready_8656 left H8358 H8655) site value Eval) as [ground [bits Value]].
   subst value. exists ground. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_joint_member_8657 : List.In (8657,joint_update_expr_8657) joint_update_expected_nodes.
Proof. apply (List.nth_error_In joint_update_expected_nodes 1146%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8657_congruent inputs path left right next_left next_right :
 (exists ground bits, VM.find 8356 left = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8656 left = Some (Gval ground bits)) ->
 VM.find 8356 left = VM.find 8356 right ->
 VM.find 8656 left = VM.find 8656 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8657 next_left = VM.find 8657 next_right.
Proof.
 intros H8356 H8656 E8356 E8656 L R.
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8657 joint_update_expr_8657 joint_update_node_positions joint_update_node_safety early_control_joint_member_8657)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_ground_node_congruent count tail 8657 joint_update_expr_8657 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [joint_update_expr_8657 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8356.
   rewrite E8656.
   reflexivity.
 - intros site value Eval.
   destruct (concrete_expression_closure inputs path flat_memories left joint_update_expr_8657 (joint_update_ready_8657 left H8356 H8656) site value Eval) as [ground [bits Value]].
   subst value. exists ground. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_joint_member_8658 : List.In (8658,joint_update_expr_8658) joint_update_expected_nodes.
Proof. apply (List.nth_error_In joint_update_expected_nodes 1147%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8658_congruent inputs path left right next_left next_right :
 (exists ground bits, VM.find 8354 left = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8657 left = Some (Gval ground bits)) ->
 VM.find 8354 left = VM.find 8354 right ->
 VM.find 8657 left = VM.find 8657 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8658 next_left = VM.find 8658 next_right.
Proof.
 intros H8354 H8657 E8354 E8657 L R.
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8658 joint_update_expr_8658 joint_update_node_positions joint_update_node_safety early_control_joint_member_8658)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_ground_node_congruent count tail 8658 joint_update_expr_8658 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [joint_update_expr_8658 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8354.
   rewrite E8657.
   reflexivity.
 - intros site value Eval.
   destruct (concrete_expression_closure inputs path flat_memories left joint_update_expr_8658 (joint_update_ready_8658 left H8354 H8657) site value Eval) as [ground [bits Value]].
   subst value. exists ground. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_joint_member_8659 : List.In (8659,joint_update_expr_8659) joint_update_expected_nodes.
Proof. apply (List.nth_error_In joint_update_expected_nodes 1148%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8659_congruent inputs path left right next_left next_right :
 (exists ground bits, VM.find 8352 left = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8658 left = Some (Gval ground bits)) ->
 VM.find 8352 left = VM.find 8352 right ->
 VM.find 8658 left = VM.find 8658 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8659 next_left = VM.find 8659 next_right.
Proof.
 intros H8352 H8658 E8352 E8658 L R.
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8659 joint_update_expr_8659 joint_update_node_positions joint_update_node_safety early_control_joint_member_8659)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_ground_node_congruent count tail 8659 joint_update_expr_8659 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [joint_update_expr_8659 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8352.
   rewrite E8658.
   reflexivity.
 - intros site value Eval.
   destruct (concrete_expression_closure inputs path flat_memories left joint_update_expr_8659 (joint_update_ready_8659 left H8352 H8658) site value Eval) as [ground [bits Value]].
   subst value. exists ground. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_joint_member_8660 : List.In (8660,joint_update_expr_8660) joint_update_expected_nodes.
Proof. apply (List.nth_error_In joint_update_expected_nodes 1149%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8660_congruent inputs path left right next_left next_right :
 (exists ground bits, VM.find 8350 left = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8659 left = Some (Gval ground bits)) ->
 VM.find 8350 left = VM.find 8350 right ->
 VM.find 8659 left = VM.find 8659 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8660 next_left = VM.find 8660 next_right.
Proof.
 intros H8350 H8659 E8350 E8659 L R.
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8660 joint_update_expr_8660 joint_update_node_positions joint_update_node_safety early_control_joint_member_8660)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_ground_node_congruent count tail 8660 joint_update_expr_8660 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [joint_update_expr_8660 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8350.
   rewrite E8659.
   reflexivity.
 - intros site value Eval.
   destruct (concrete_expression_closure inputs path flat_memories left joint_update_expr_8660 (joint_update_ready_8660 left H8350 H8659) site value Eval) as [ground [bits Value]].
   subst value. exists ground. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_joint_member_8661 : List.In (8661,joint_update_expr_8661) joint_update_expected_nodes.
Proof. apply (List.nth_error_In joint_update_expected_nodes 1150%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8661_congruent inputs path left right next_left next_right :
 (exists ground bits, VM.find 8348 left = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8660 left = Some (Gval ground bits)) ->
 VM.find 8348 left = VM.find 8348 right ->
 VM.find 8660 left = VM.find 8660 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8661 next_left = VM.find 8661 next_right.
Proof.
 intros H8348 H8660 E8348 E8660 L R.
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8661 joint_update_expr_8661 joint_update_node_positions joint_update_node_safety early_control_joint_member_8661)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_ground_node_congruent count tail 8661 joint_update_expr_8661 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [joint_update_expr_8661 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8348.
   rewrite E8660.
   reflexivity.
 - intros site value Eval.
   destruct (concrete_expression_closure inputs path flat_memories left joint_update_expr_8661 (joint_update_ready_8661 left H8348 H8660) site value Eval) as [ground [bits Value]].
   subst value. exists ground. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_joint_member_8662 : List.In (8662,joint_update_expr_8662) joint_update_expected_nodes.
Proof. apply (List.nth_error_In joint_update_expected_nodes 1151%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8662_congruent inputs path left right next_left next_right :
 (exists ground bits, VM.find 8346 left = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8661 left = Some (Gval ground bits)) ->
 VM.find 8346 left = VM.find 8346 right ->
 VM.find 8661 left = VM.find 8661 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8662 next_left = VM.find 8662 next_right.
Proof.
 intros H8346 H8661 E8346 E8661 L R.
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8662 joint_update_expr_8662 joint_update_node_positions joint_update_node_safety early_control_joint_member_8662)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_ground_node_congruent count tail 8662 joint_update_expr_8662 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [joint_update_expr_8662 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8346.
   rewrite E8661.
   reflexivity.
 - intros site value Eval.
   destruct (concrete_expression_closure inputs path flat_memories left joint_update_expr_8662 (joint_update_ready_8662 left H8346 H8661) site value Eval) as [ground [bits Value]].
   subst value. exists ground. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_joint_member_8663 : List.In (8663,joint_update_expr_8663) joint_update_expected_nodes.
Proof. apply (List.nth_error_In joint_update_expected_nodes 1152%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8663_congruent inputs path left right next_left next_right :
 (exists ground bits, VM.find 8344 left = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8662 left = Some (Gval ground bits)) ->
 VM.find 8344 left = VM.find 8344 right ->
 VM.find 8662 left = VM.find 8662 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8663 next_left = VM.find 8663 next_right.
Proof.
 intros H8344 H8662 E8344 E8662 L R.
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8663 joint_update_expr_8663 joint_update_node_positions joint_update_node_safety early_control_joint_member_8663)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_ground_node_congruent count tail 8663 joint_update_expr_8663 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [joint_update_expr_8663 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8344.
   rewrite E8662.
   reflexivity.
 - intros site value Eval.
   destruct (concrete_expression_closure inputs path flat_memories left joint_update_expr_8663 (joint_update_ready_8663 left H8344 H8662) site value Eval) as [ground [bits Value]].
   subst value. exists ground. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_joint_member_8664 : List.In (8664,joint_update_expr_8664) joint_update_expected_nodes.
Proof. apply (List.nth_error_In joint_update_expected_nodes 1153%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8664_congruent inputs path left right next_left next_right :
 (exists ground bits, VM.find 8342 left = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8663 left = Some (Gval ground bits)) ->
 VM.find 8342 left = VM.find 8342 right ->
 VM.find 8663 left = VM.find 8663 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8664 next_left = VM.find 8664 next_right.
Proof.
 intros H8342 H8663 E8342 E8663 L R.
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8664 joint_update_expr_8664 joint_update_node_positions joint_update_node_safety early_control_joint_member_8664)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_ground_node_congruent count tail 8664 joint_update_expr_8664 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [joint_update_expr_8664 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8342.
   rewrite E8663.
   reflexivity.
 - intros site value Eval.
   destruct (concrete_expression_closure inputs path flat_memories left joint_update_expr_8664 (joint_update_ready_8664 left H8342 H8663) site value Eval) as [ground [bits Value]].
   subst value. exists ground. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_joint_member_8665 : List.In (8665,joint_update_expr_8665) joint_update_expected_nodes.
Proof. apply (List.nth_error_In joint_update_expected_nodes 1154%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8665_congruent inputs path left right next_left next_right :
 (exists ground bits, VM.find 8340 left = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8664 left = Some (Gval ground bits)) ->
 VM.find 8340 left = VM.find 8340 right ->
 VM.find 8664 left = VM.find 8664 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8665 next_left = VM.find 8665 next_right.
Proof.
 intros H8340 H8664 E8340 E8664 L R.
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8665 joint_update_expr_8665 joint_update_node_positions joint_update_node_safety early_control_joint_member_8665)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_ground_node_congruent count tail 8665 joint_update_expr_8665 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [joint_update_expr_8665 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8340.
   rewrite E8664.
   reflexivity.
 - intros site value Eval.
   destruct (concrete_expression_closure inputs path flat_memories left joint_update_expr_8665 (joint_update_ready_8665 left H8340 H8664) site value Eval) as [ground [bits Value]].
   subst value. exists ground. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_joint_member_8666 : List.In (8666,joint_update_expr_8666) joint_update_expected_nodes.
Proof. apply (List.nth_error_In joint_update_expected_nodes 1155%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8666_congruent inputs path left right next_left next_right :
 (exists ground bits, VM.find 8338 left = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8665 left = Some (Gval ground bits)) ->
 VM.find 8338 left = VM.find 8338 right ->
 VM.find 8665 left = VM.find 8665 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8666 next_left = VM.find 8666 next_right.
Proof.
 intros H8338 H8665 E8338 E8665 L R.
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8666 joint_update_expr_8666 joint_update_node_positions joint_update_node_safety early_control_joint_member_8666)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_ground_node_congruent count tail 8666 joint_update_expr_8666 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [joint_update_expr_8666 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8338.
   rewrite E8665.
   reflexivity.
 - intros site value Eval.
   destruct (concrete_expression_closure inputs path flat_memories left joint_update_expr_8666 (joint_update_ready_8666 left H8338 H8665) site value Eval) as [ground [bits Value]].
   subst value. exists ground. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_joint_member_8667 : List.In (8667,joint_update_expr_8667) joint_update_expected_nodes.
Proof. apply (List.nth_error_In joint_update_expected_nodes 1156%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8667_congruent inputs path left right next_left next_right :
 (exists ground bits, VM.find 8336 left = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8666 left = Some (Gval ground bits)) ->
 VM.find 8336 left = VM.find 8336 right ->
 VM.find 8666 left = VM.find 8666 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8667 next_left = VM.find 8667 next_right.
Proof.
 intros H8336 H8666 E8336 E8666 L R.
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8667 joint_update_expr_8667 joint_update_node_positions joint_update_node_safety early_control_joint_member_8667)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_ground_node_congruent count tail 8667 joint_update_expr_8667 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [joint_update_expr_8667 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8336.
   rewrite E8666.
   reflexivity.
 - intros site value Eval.
   destruct (concrete_expression_closure inputs path flat_memories left joint_update_expr_8667 (joint_update_ready_8667 left H8336 H8666) site value Eval) as [ground [bits Value]].
   subst value. exists ground. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_joint_member_8668 : List.In (8668,joint_update_expr_8668) joint_update_expected_nodes.
Proof. apply (List.nth_error_In joint_update_expected_nodes 1157%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8668_congruent inputs path left right next_left next_right :
 (exists ground bits, VM.find 8334 left = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8667 left = Some (Gval ground bits)) ->
 VM.find 8334 left = VM.find 8334 right ->
 VM.find 8667 left = VM.find 8667 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8668 next_left = VM.find 8668 next_right.
Proof.
 intros H8334 H8667 E8334 E8667 L R.
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8668 joint_update_expr_8668 joint_update_node_positions joint_update_node_safety early_control_joint_member_8668)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_ground_node_congruent count tail 8668 joint_update_expr_8668 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [joint_update_expr_8668 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8334.
   rewrite E8667.
   reflexivity.
 - intros site value Eval.
   destruct (concrete_expression_closure inputs path flat_memories left joint_update_expr_8668 (joint_update_ready_8668 left H8334 H8667) site value Eval) as [ground [bits Value]].
   subst value. exists ground. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_joint_member_8669 : List.In (8669,joint_update_expr_8669) joint_update_expected_nodes.
Proof. apply (List.nth_error_In joint_update_expected_nodes 1158%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8669_congruent inputs path left right next_left next_right :
 (exists ground bits, VM.find 8332 left = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8668 left = Some (Gval ground bits)) ->
 VM.find 8332 left = VM.find 8332 right ->
 VM.find 8668 left = VM.find 8668 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8669 next_left = VM.find 8669 next_right.
Proof.
 intros H8332 H8668 E8332 E8668 L R.
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8669 joint_update_expr_8669 joint_update_node_positions joint_update_node_safety early_control_joint_member_8669)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_ground_node_congruent count tail 8669 joint_update_expr_8669 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [joint_update_expr_8669 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8332.
   rewrite E8668.
   reflexivity.
 - intros site value Eval.
   destruct (concrete_expression_closure inputs path flat_memories left joint_update_expr_8669 (joint_update_ready_8669 left H8332 H8668) site value Eval) as [ground [bits Value]].
   subst value. exists ground. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_joint_member_8670 : List.In (8670,joint_update_expr_8670) joint_update_expected_nodes.
Proof. apply (List.nth_error_In joint_update_expected_nodes 1159%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8670_congruent inputs path left right next_left next_right :
 (exists ground bits, VM.find 8330 left = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8669 left = Some (Gval ground bits)) ->
 VM.find 8330 left = VM.find 8330 right ->
 VM.find 8669 left = VM.find 8669 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8670 next_left = VM.find 8670 next_right.
Proof.
 intros H8330 H8669 E8330 E8669 L R.
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8670 joint_update_expr_8670 joint_update_node_positions joint_update_node_safety early_control_joint_member_8670)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_ground_node_congruent count tail 8670 joint_update_expr_8670 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [joint_update_expr_8670 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8330.
   rewrite E8669.
   reflexivity.
 - intros site value Eval.
   destruct (concrete_expression_closure inputs path flat_memories left joint_update_expr_8670 (joint_update_ready_8670 left H8330 H8669) site value Eval) as [ground [bits Value]].
   subst value. exists ground. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_joint_member_8671 : List.In (8671,joint_update_expr_8671) joint_update_expected_nodes.
Proof. apply (List.nth_error_In joint_update_expected_nodes 1160%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8671_congruent inputs path left right next_left next_right :
 (exists ground bits, VM.find 8328 left = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8670 left = Some (Gval ground bits)) ->
 VM.find 8328 left = VM.find 8328 right ->
 VM.find 8670 left = VM.find 8670 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8671 next_left = VM.find 8671 next_right.
Proof.
 intros H8328 H8670 E8328 E8670 L R.
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8671 joint_update_expr_8671 joint_update_node_positions joint_update_node_safety early_control_joint_member_8671)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_ground_node_congruent count tail 8671 joint_update_expr_8671 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [joint_update_expr_8671 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8328.
   rewrite E8670.
   reflexivity.
 - intros site value Eval.
   destruct (concrete_expression_closure inputs path flat_memories left joint_update_expr_8671 (joint_update_ready_8671 left H8328 H8670) site value Eval) as [ground [bits Value]].
   subst value. exists ground. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_joint_member_8672 : List.In (8672,joint_update_expr_8672) joint_update_expected_nodes.
Proof. apply (List.nth_error_In joint_update_expected_nodes 1161%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8672_congruent inputs path left right next_left next_right :
 (exists ground bits, VM.find 8326 left = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8671 left = Some (Gval ground bits)) ->
 VM.find 8326 left = VM.find 8326 right ->
 VM.find 8671 left = VM.find 8671 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8672 next_left = VM.find 8672 next_right.
Proof.
 intros H8326 H8671 E8326 E8671 L R.
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8672 joint_update_expr_8672 joint_update_node_positions joint_update_node_safety early_control_joint_member_8672)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_ground_node_congruent count tail 8672 joint_update_expr_8672 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [joint_update_expr_8672 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8326.
   rewrite E8671.
   reflexivity.
 - intros site value Eval.
   destruct (concrete_expression_closure inputs path flat_memories left joint_update_expr_8672 (joint_update_ready_8672 left H8326 H8671) site value Eval) as [ground [bits Value]].
   subst value. exists ground. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_joint_member_8673 : List.In (8673,joint_update_expr_8673) joint_update_expected_nodes.
Proof. apply (List.nth_error_In joint_update_expected_nodes 1162%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8673_congruent inputs path left right next_left next_right :
 (exists ground bits, VM.find 8324 left = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8672 left = Some (Gval ground bits)) ->
 VM.find 8324 left = VM.find 8324 right ->
 VM.find 8672 left = VM.find 8672 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8673 next_left = VM.find 8673 next_right.
Proof.
 intros H8324 H8672 E8324 E8672 L R.
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8673 joint_update_expr_8673 joint_update_node_positions joint_update_node_safety early_control_joint_member_8673)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_ground_node_congruent count tail 8673 joint_update_expr_8673 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [joint_update_expr_8673 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8324.
   rewrite E8672.
   reflexivity.
 - intros site value Eval.
   destruct (concrete_expression_closure inputs path flat_memories left joint_update_expr_8673 (joint_update_ready_8673 left H8324 H8672) site value Eval) as [ground [bits Value]].
   subst value. exists ground. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_joint_member_8674 : List.In (8674,joint_update_expr_8674) joint_update_expected_nodes.
Proof. apply (List.nth_error_In joint_update_expected_nodes 1163%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8674_congruent inputs path left right next_left next_right :
 (exists ground bits, VM.find 8322 left = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8673 left = Some (Gval ground bits)) ->
 VM.find 8322 left = VM.find 8322 right ->
 VM.find 8673 left = VM.find 8673 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8674 next_left = VM.find 8674 next_right.
Proof.
 intros H8322 H8673 E8322 E8673 L R.
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8674 joint_update_expr_8674 joint_update_node_positions joint_update_node_safety early_control_joint_member_8674)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_ground_node_congruent count tail 8674 joint_update_expr_8674 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [joint_update_expr_8674 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8322.
   rewrite E8673.
   reflexivity.
 - intros site value Eval.
   destruct (concrete_expression_closure inputs path flat_memories left joint_update_expr_8674 (joint_update_ready_8674 left H8322 H8673) site value Eval) as [ground [bits Value]].
   subst value. exists ground. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_joint_member_8675 : List.In (8675,joint_update_expr_8675) joint_update_expected_nodes.
Proof. apply (List.nth_error_In joint_update_expected_nodes 1164%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8675_congruent inputs path left right next_left next_right :
 (exists ground bits, VM.find 8320 left = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8674 left = Some (Gval ground bits)) ->
 VM.find 8320 left = VM.find 8320 right ->
 VM.find 8674 left = VM.find 8674 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8675 next_left = VM.find 8675 next_right.
Proof.
 intros H8320 H8674 E8320 E8674 L R.
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8675 joint_update_expr_8675 joint_update_node_positions joint_update_node_safety early_control_joint_member_8675)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_ground_node_congruent count tail 8675 joint_update_expr_8675 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [joint_update_expr_8675 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8320.
   rewrite E8674.
   reflexivity.
 - intros site value Eval.
   destruct (concrete_expression_closure inputs path flat_memories left joint_update_expr_8675 (joint_update_ready_8675 left H8320 H8674) site value Eval) as [ground [bits Value]].
   subst value. exists ground. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_joint_member_8676 : List.In (8676,joint_update_expr_8676) joint_update_expected_nodes.
Proof. apply (List.nth_error_In joint_update_expected_nodes 1165%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8676_congruent inputs path left right next_left next_right :
 (exists ground bits, VM.find 8318 left = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8675 left = Some (Gval ground bits)) ->
 VM.find 8318 left = VM.find 8318 right ->
 VM.find 8675 left = VM.find 8675 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8676 next_left = VM.find 8676 next_right.
Proof.
 intros H8318 H8675 E8318 E8675 L R.
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8676 joint_update_expr_8676 joint_update_node_positions joint_update_node_safety early_control_joint_member_8676)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_ground_node_congruent count tail 8676 joint_update_expr_8676 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [joint_update_expr_8676 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8318.
   rewrite E8675.
   reflexivity.
 - intros site value Eval.
   destruct (concrete_expression_closure inputs path flat_memories left joint_update_expr_8676 (joint_update_ready_8676 left H8318 H8675) site value Eval) as [ground [bits Value]].
   subst value. exists ground. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_joint_member_8677 : List.In (8677,joint_update_expr_8677) joint_update_expected_nodes.
Proof. apply (List.nth_error_In joint_update_expected_nodes 1166%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8677_congruent inputs path left right next_left next_right :
 (exists ground bits, VM.find 8316 left = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8676 left = Some (Gval ground bits)) ->
 VM.find 8316 left = VM.find 8316 right ->
 VM.find 8676 left = VM.find 8676 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8677 next_left = VM.find 8677 next_right.
Proof.
 intros H8316 H8676 E8316 E8676 L R.
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8677 joint_update_expr_8677 joint_update_node_positions joint_update_node_safety early_control_joint_member_8677)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_ground_node_congruent count tail 8677 joint_update_expr_8677 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [joint_update_expr_8677 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8316.
   rewrite E8676.
   reflexivity.
 - intros site value Eval.
   destruct (concrete_expression_closure inputs path flat_memories left joint_update_expr_8677 (joint_update_ready_8677 left H8316 H8676) site value Eval) as [ground [bits Value]].
   subst value. exists ground. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_joint_member_8678 : List.In (8678,joint_update_expr_8678) joint_update_expected_nodes.
Proof. apply (List.nth_error_In joint_update_expected_nodes 1167%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8678_congruent inputs path left right next_left next_right :
 (exists ground bits, VM.find 8314 left = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8677 left = Some (Gval ground bits)) ->
 VM.find 8314 left = VM.find 8314 right ->
 VM.find 8677 left = VM.find 8677 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8678 next_left = VM.find 8678 next_right.
Proof.
 intros H8314 H8677 E8314 E8677 L R.
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8678 joint_update_expr_8678 joint_update_node_positions joint_update_node_safety early_control_joint_member_8678)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_ground_node_congruent count tail 8678 joint_update_expr_8678 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [joint_update_expr_8678 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8314.
   rewrite E8677.
   reflexivity.
 - intros site value Eval.
   destruct (concrete_expression_closure inputs path flat_memories left joint_update_expr_8678 (joint_update_ready_8678 left H8314 H8677) site value Eval) as [ground [bits Value]].
   subst value. exists ground. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_joint_member_8679 : List.In (8679,joint_update_expr_8679) joint_update_expected_nodes.
Proof. apply (List.nth_error_In joint_update_expected_nodes 1168%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8679_congruent inputs path left right next_left next_right :
 (exists ground bits, VM.find 8312 left = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8678 left = Some (Gval ground bits)) ->
 VM.find 8312 left = VM.find 8312 right ->
 VM.find 8678 left = VM.find 8678 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8679 next_left = VM.find 8679 next_right.
Proof.
 intros H8312 H8678 E8312 E8678 L R.
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8679 joint_update_expr_8679 joint_update_node_positions joint_update_node_safety early_control_joint_member_8679)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_ground_node_congruent count tail 8679 joint_update_expr_8679 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [joint_update_expr_8679 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8312.
   rewrite E8678.
   reflexivity.
 - intros site value Eval.
   destruct (concrete_expression_closure inputs path flat_memories left joint_update_expr_8679 (joint_update_ready_8679 left H8312 H8678) site value Eval) as [ground [bits Value]].
   subst value. exists ground. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_joint_member_8680 : List.In (8680,joint_update_expr_8680) joint_update_expected_nodes.
Proof. apply (List.nth_error_In joint_update_expected_nodes 1169%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8680_congruent inputs path left right next_left next_right :
 (exists ground bits, VM.find 8310 left = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8679 left = Some (Gval ground bits)) ->
 VM.find 8310 left = VM.find 8310 right ->
 VM.find 8679 left = VM.find 8679 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8680 next_left = VM.find 8680 next_right.
Proof.
 intros H8310 H8679 E8310 E8679 L R.
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8680 joint_update_expr_8680 joint_update_node_positions joint_update_node_safety early_control_joint_member_8680)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_ground_node_congruent count tail 8680 joint_update_expr_8680 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [joint_update_expr_8680 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8310.
   rewrite E8679.
   reflexivity.
 - intros site value Eval.
   destruct (concrete_expression_closure inputs path flat_memories left joint_update_expr_8680 (joint_update_ready_8680 left H8310 H8679) site value Eval) as [ground [bits Value]].
   subst value. exists ground. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_joint_member_8681 : List.In (8681,joint_update_expr_8681) joint_update_expected_nodes.
Proof. apply (List.nth_error_In joint_update_expected_nodes 1170%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8681_congruent inputs path left right next_left next_right :
 (exists ground bits, VM.find 8308 left = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8680 left = Some (Gval ground bits)) ->
 VM.find 8308 left = VM.find 8308 right ->
 VM.find 8680 left = VM.find 8680 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8681 next_left = VM.find 8681 next_right.
Proof.
 intros H8308 H8680 E8308 E8680 L R.
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8681 joint_update_expr_8681 joint_update_node_positions joint_update_node_safety early_control_joint_member_8681)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_ground_node_congruent count tail 8681 joint_update_expr_8681 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [joint_update_expr_8681 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8308.
   rewrite E8680.
   reflexivity.
 - intros site value Eval.
   destruct (concrete_expression_closure inputs path flat_memories left joint_update_expr_8681 (joint_update_ready_8681 left H8308 H8680) site value Eval) as [ground [bits Value]].
   subst value. exists ground. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_joint_member_8682 : List.In (8682,joint_update_expr_8682) joint_update_expected_nodes.
Proof. apply (List.nth_error_In joint_update_expected_nodes 1171%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8682_congruent inputs path left right next_left next_right :
 (exists ground bits, VM.find 8306 left = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8681 left = Some (Gval ground bits)) ->
 VM.find 8306 left = VM.find 8306 right ->
 VM.find 8681 left = VM.find 8681 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8682 next_left = VM.find 8682 next_right.
Proof.
 intros H8306 H8681 E8306 E8681 L R.
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8682 joint_update_expr_8682 joint_update_node_positions joint_update_node_safety early_control_joint_member_8682)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_ground_node_congruent count tail 8682 joint_update_expr_8682 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [joint_update_expr_8682 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8306.
   rewrite E8681.
   reflexivity.
 - intros site value Eval.
   destruct (concrete_expression_closure inputs path flat_memories left joint_update_expr_8682 (joint_update_ready_8682 left H8306 H8681) site value Eval) as [ground [bits Value]].
   subst value. exists ground. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_joint_member_8683 : List.In (8683,joint_update_expr_8683) joint_update_expected_nodes.
Proof. apply (List.nth_error_In joint_update_expected_nodes 1172%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8683_congruent inputs path left right next_left next_right :
 (exists ground bits, VM.find 8304 left = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8682 left = Some (Gval ground bits)) ->
 VM.find 8304 left = VM.find 8304 right ->
 VM.find 8682 left = VM.find 8682 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8683 next_left = VM.find 8683 next_right.
Proof.
 intros H8304 H8682 E8304 E8682 L R.
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8683 joint_update_expr_8683 joint_update_node_positions joint_update_node_safety early_control_joint_member_8683)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_ground_node_congruent count tail 8683 joint_update_expr_8683 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [joint_update_expr_8683 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8304.
   rewrite E8682.
   reflexivity.
 - intros site value Eval.
   destruct (concrete_expression_closure inputs path flat_memories left joint_update_expr_8683 (joint_update_ready_8683 left H8304 H8682) site value Eval) as [ground [bits Value]].
   subst value. exists ground. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_joint_member_8684 : List.In (8684,joint_update_expr_8684) joint_update_expected_nodes.
Proof. apply (List.nth_error_In joint_update_expected_nodes 1173%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8684_congruent inputs path left right next_left next_right :
 (exists ground bits, VM.find 8302 left = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8683 left = Some (Gval ground bits)) ->
 VM.find 8302 left = VM.find 8302 right ->
 VM.find 8683 left = VM.find 8683 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8684 next_left = VM.find 8684 next_right.
Proof.
 intros H8302 H8683 E8302 E8683 L R.
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8684 joint_update_expr_8684 joint_update_node_positions joint_update_node_safety early_control_joint_member_8684)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_ground_node_congruent count tail 8684 joint_update_expr_8684 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [joint_update_expr_8684 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8302.
   rewrite E8683.
   reflexivity.
 - intros site value Eval.
   destruct (concrete_expression_closure inputs path flat_memories left joint_update_expr_8684 (joint_update_ready_8684 left H8302 H8683) site value Eval) as [ground [bits Value]].
   subst value. exists ground. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_joint_member_8685 : List.In (8685,joint_update_expr_8685) joint_update_expected_nodes.
Proof. apply (List.nth_error_In joint_update_expected_nodes 1174%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8685_congruent inputs path left right next_left next_right :
 (exists ground bits, VM.find 8300 left = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8684 left = Some (Gval ground bits)) ->
 VM.find 8300 left = VM.find 8300 right ->
 VM.find 8684 left = VM.find 8684 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8685 next_left = VM.find 8685 next_right.
Proof.
 intros H8300 H8684 E8300 E8684 L R.
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8685 joint_update_expr_8685 joint_update_node_positions joint_update_node_safety early_control_joint_member_8685)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_ground_node_congruent count tail 8685 joint_update_expr_8685 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [joint_update_expr_8685 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8300.
   rewrite E8684.
   reflexivity.
 - intros site value Eval.
   destruct (concrete_expression_closure inputs path flat_memories left joint_update_expr_8685 (joint_update_ready_8685 left H8300 H8684) site value Eval) as [ground [bits Value]].
   subst value. exists ground. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_joint_member_8686 : List.In (8686,joint_update_expr_8686) joint_update_expected_nodes.
Proof. apply (List.nth_error_In joint_update_expected_nodes 1175%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8686_congruent inputs path left right next_left next_right :
 (exists ground bits, VM.find 8298 left = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8685 left = Some (Gval ground bits)) ->
 VM.find 8298 left = VM.find 8298 right ->
 VM.find 8685 left = VM.find 8685 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8686 next_left = VM.find 8686 next_right.
Proof.
 intros H8298 H8685 E8298 E8685 L R.
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8686 joint_update_expr_8686 joint_update_node_positions joint_update_node_safety early_control_joint_member_8686)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_ground_node_congruent count tail 8686 joint_update_expr_8686 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [joint_update_expr_8686 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8298.
   rewrite E8685.
   reflexivity.
 - intros site value Eval.
   destruct (concrete_expression_closure inputs path flat_memories left joint_update_expr_8686 (joint_update_ready_8686 left H8298 H8685) site value Eval) as [ground [bits Value]].
   subst value. exists ground. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_joint_member_8687 : List.In (8687,joint_update_expr_8687) joint_update_expected_nodes.
Proof. apply (List.nth_error_In joint_update_expected_nodes 1176%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8687_congruent inputs path left right next_left next_right :
 (exists ground bits, VM.find 8296 left = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8686 left = Some (Gval ground bits)) ->
 VM.find 8296 left = VM.find 8296 right ->
 VM.find 8686 left = VM.find 8686 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8687 next_left = VM.find 8687 next_right.
Proof.
 intros H8296 H8686 E8296 E8686 L R.
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8687 joint_update_expr_8687 joint_update_node_positions joint_update_node_safety early_control_joint_member_8687)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_ground_node_congruent count tail 8687 joint_update_expr_8687 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [joint_update_expr_8687 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8296.
   rewrite E8686.
   reflexivity.
 - intros site value Eval.
   destruct (concrete_expression_closure inputs path flat_memories left joint_update_expr_8687 (joint_update_ready_8687 left H8296 H8686) site value Eval) as [ground [bits Value]].
   subst value. exists ground. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_joint_member_8688 : List.In (8688,joint_update_expr_8688) joint_update_expected_nodes.
Proof. apply (List.nth_error_In joint_update_expected_nodes 1177%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8688_congruent inputs path left right next_left next_right :
 (exists ground bits, VM.find 8294 left = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8687 left = Some (Gval ground bits)) ->
 VM.find 8294 left = VM.find 8294 right ->
 VM.find 8687 left = VM.find 8687 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8688 next_left = VM.find 8688 next_right.
Proof.
 intros H8294 H8687 E8294 E8687 L R.
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8688 joint_update_expr_8688 joint_update_node_positions joint_update_node_safety early_control_joint_member_8688)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_ground_node_congruent count tail 8688 joint_update_expr_8688 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [joint_update_expr_8688 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8294.
   rewrite E8687.
   reflexivity.
 - intros site value Eval.
   destruct (concrete_expression_closure inputs path flat_memories left joint_update_expr_8688 (joint_update_ready_8688 left H8294 H8687) site value Eval) as [ground [bits Value]].
   subst value. exists ground. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_joint_member_8689 : List.In (8689,joint_update_expr_8689) joint_update_expected_nodes.
Proof. apply (List.nth_error_In joint_update_expected_nodes 1178%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8689_congruent inputs path left right next_left next_right :
 (exists ground bits, VM.find 8292 left = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8688 left = Some (Gval ground bits)) ->
 VM.find 8292 left = VM.find 8292 right ->
 VM.find 8688 left = VM.find 8688 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8689 next_left = VM.find 8689 next_right.
Proof.
 intros H8292 H8688 E8292 E8688 L R.
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8689 joint_update_expr_8689 joint_update_node_positions joint_update_node_safety early_control_joint_member_8689)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_ground_node_congruent count tail 8689 joint_update_expr_8689 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [joint_update_expr_8689 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8292.
   rewrite E8688.
   reflexivity.
 - intros site value Eval.
   destruct (concrete_expression_closure inputs path flat_memories left joint_update_expr_8689 (joint_update_ready_8689 left H8292 H8688) site value Eval) as [ground [bits Value]].
   subst value. exists ground. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_joint_member_8690 : List.In (8690,joint_update_expr_8690) joint_update_expected_nodes.
Proof. apply (List.nth_error_In joint_update_expected_nodes 1179%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8690_congruent inputs path left right next_left next_right :
 (exists ground bits, VM.find 8290 left = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8689 left = Some (Gval ground bits)) ->
 VM.find 8290 left = VM.find 8290 right ->
 VM.find 8689 left = VM.find 8689 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8690 next_left = VM.find 8690 next_right.
Proof.
 intros H8290 H8689 E8290 E8689 L R.
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8690 joint_update_expr_8690 joint_update_node_positions joint_update_node_safety early_control_joint_member_8690)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_ground_node_congruent count tail 8690 joint_update_expr_8690 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [joint_update_expr_8690 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8290.
   rewrite E8689.
   reflexivity.
 - intros site value Eval.
   destruct (concrete_expression_closure inputs path flat_memories left joint_update_expr_8690 (joint_update_ready_8690 left H8290 H8689) site value Eval) as [ground [bits Value]].
   subst value. exists ground. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_joint_member_8691 : List.In (8691,joint_update_expr_8691) joint_update_expected_nodes.
Proof. apply (List.nth_error_In joint_update_expected_nodes 1180%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8691_congruent inputs path left right next_left next_right :
 (exists ground bits, VM.find 8288 left = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8690 left = Some (Gval ground bits)) ->
 VM.find 8288 left = VM.find 8288 right ->
 VM.find 8690 left = VM.find 8690 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8691 next_left = VM.find 8691 next_right.
Proof.
 intros H8288 H8690 E8288 E8690 L R.
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8691 joint_update_expr_8691 joint_update_node_positions joint_update_node_safety early_control_joint_member_8691)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_ground_node_congruent count tail 8691 joint_update_expr_8691 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [joint_update_expr_8691 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8288.
   rewrite E8690.
   reflexivity.
 - intros site value Eval.
   destruct (concrete_expression_closure inputs path flat_memories left joint_update_expr_8691 (joint_update_ready_8691 left H8288 H8690) site value Eval) as [ground [bits Value]].
   subst value. exists ground. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_joint_member_8692 : List.In (8692,joint_update_expr_8692) joint_update_expected_nodes.
Proof. apply (List.nth_error_In joint_update_expected_nodes 1181%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8692_congruent inputs path left right next_left next_right :
 (exists ground bits, VM.find 8286 left = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8691 left = Some (Gval ground bits)) ->
 VM.find 8286 left = VM.find 8286 right ->
 VM.find 8691 left = VM.find 8691 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8692 next_left = VM.find 8692 next_right.
Proof.
 intros H8286 H8691 E8286 E8691 L R.
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8692 joint_update_expr_8692 joint_update_node_positions joint_update_node_safety early_control_joint_member_8692)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_ground_node_congruent count tail 8692 joint_update_expr_8692 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [joint_update_expr_8692 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8286.
   rewrite E8691.
   reflexivity.
 - intros site value Eval.
   destruct (concrete_expression_closure inputs path flat_memories left joint_update_expr_8692 (joint_update_ready_8692 left H8286 H8691) site value Eval) as [ground [bits Value]].
   subst value. exists ground. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_joint_member_8693 : List.In (8693,joint_update_expr_8693) joint_update_expected_nodes.
Proof. apply (List.nth_error_In joint_update_expected_nodes 1182%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8693_congruent inputs path left right next_left next_right :
 (exists ground bits, VM.find 8284 left = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8692 left = Some (Gval ground bits)) ->
 VM.find 8284 left = VM.find 8284 right ->
 VM.find 8692 left = VM.find 8692 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8693 next_left = VM.find 8693 next_right.
Proof.
 intros H8284 H8692 E8284 E8692 L R.
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8693 joint_update_expr_8693 joint_update_node_positions joint_update_node_safety early_control_joint_member_8693)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_ground_node_congruent count tail 8693 joint_update_expr_8693 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [joint_update_expr_8693 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8284.
   rewrite E8692.
   reflexivity.
 - intros site value Eval.
   destruct (concrete_expression_closure inputs path flat_memories left joint_update_expr_8693 (joint_update_ready_8693 left H8284 H8692) site value Eval) as [ground [bits Value]].
   subst value. exists ground. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_joint_member_8694 : List.In (8694,joint_update_expr_8694) joint_update_expected_nodes.
Proof. apply (List.nth_error_In joint_update_expected_nodes 1183%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8694_congruent inputs path left right next_left next_right :
 (exists ground bits, VM.find 8282 left = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8693 left = Some (Gval ground bits)) ->
 VM.find 8282 left = VM.find 8282 right ->
 VM.find 8693 left = VM.find 8693 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8694 next_left = VM.find 8694 next_right.
Proof.
 intros H8282 H8693 E8282 E8693 L R.
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8694 joint_update_expr_8694 joint_update_node_positions joint_update_node_safety early_control_joint_member_8694)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_ground_node_congruent count tail 8694 joint_update_expr_8694 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [joint_update_expr_8694 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8282.
   rewrite E8693.
   reflexivity.
 - intros site value Eval.
   destruct (concrete_expression_closure inputs path flat_memories left joint_update_expr_8694 (joint_update_ready_8694 left H8282 H8693) site value Eval) as [ground [bits Value]].
   subst value. exists ground. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_joint_member_8695 : List.In (8695,joint_update_expr_8695) joint_update_expected_nodes.
Proof. apply (List.nth_error_In joint_update_expected_nodes 1184%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8695_congruent inputs path left right next_left next_right :
 (exists ground bits, VM.find 8280 left = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8694 left = Some (Gval ground bits)) ->
 VM.find 8280 left = VM.find 8280 right ->
 VM.find 8694 left = VM.find 8694 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8695 next_left = VM.find 8695 next_right.
Proof.
 intros H8280 H8694 E8280 E8694 L R.
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8695 joint_update_expr_8695 joint_update_node_positions joint_update_node_safety early_control_joint_member_8695)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_ground_node_congruent count tail 8695 joint_update_expr_8695 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [joint_update_expr_8695 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8280.
   rewrite E8694.
   reflexivity.
 - intros site value Eval.
   destruct (concrete_expression_closure inputs path flat_memories left joint_update_expr_8695 (joint_update_ready_8695 left H8280 H8694) site value Eval) as [ground [bits Value]].
   subst value. exists ground. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_joint_member_8696 : List.In (8696,joint_update_expr_8696) joint_update_expected_nodes.
Proof. apply (List.nth_error_In joint_update_expected_nodes 1185%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8696_congruent inputs path left right next_left next_right :
 (exists ground bits, VM.find 8278 left = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8695 left = Some (Gval ground bits)) ->
 VM.find 8278 left = VM.find 8278 right ->
 VM.find 8695 left = VM.find 8695 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8696 next_left = VM.find 8696 next_right.
Proof.
 intros H8278 H8695 E8278 E8695 L R.
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8696 joint_update_expr_8696 joint_update_node_positions joint_update_node_safety early_control_joint_member_8696)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_ground_node_congruent count tail 8696 joint_update_expr_8696 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [joint_update_expr_8696 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8278.
   rewrite E8695.
   reflexivity.
 - intros site value Eval.
   destruct (concrete_expression_closure inputs path flat_memories left joint_update_expr_8696 (joint_update_ready_8696 left H8278 H8695) site value Eval) as [ground [bits Value]].
   subst value. exists ground. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_joint_member_8697 : List.In (8697,joint_update_expr_8697) joint_update_expected_nodes.
Proof. apply (List.nth_error_In joint_update_expected_nodes 1186%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8697_congruent inputs path left right next_left next_right :
 (exists ground bits, VM.find 8276 left = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8696 left = Some (Gval ground bits)) ->
 VM.find 8276 left = VM.find 8276 right ->
 VM.find 8696 left = VM.find 8696 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8697 next_left = VM.find 8697 next_right.
Proof.
 intros H8276 H8696 E8276 E8696 L R.
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8697 joint_update_expr_8697 joint_update_node_positions joint_update_node_safety early_control_joint_member_8697)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_ground_node_congruent count tail 8697 joint_update_expr_8697 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [joint_update_expr_8697 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8276.
   rewrite E8696.
   reflexivity.
 - intros site value Eval.
   destruct (concrete_expression_closure inputs path flat_memories left joint_update_expr_8697 (joint_update_ready_8697 left H8276 H8696) site value Eval) as [ground [bits Value]].
   subst value. exists ground. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_joint_member_8698 : List.In (8698,joint_update_expr_8698) joint_update_expected_nodes.
Proof. apply (List.nth_error_In joint_update_expected_nodes 1187%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8698_congruent inputs path left right next_left next_right :
 (exists ground bits, VM.find 8274 left = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8697 left = Some (Gval ground bits)) ->
 VM.find 8274 left = VM.find 8274 right ->
 VM.find 8697 left = VM.find 8697 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8698 next_left = VM.find 8698 next_right.
Proof.
 intros H8274 H8697 E8274 E8697 L R.
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8698 joint_update_expr_8698 joint_update_node_positions joint_update_node_safety early_control_joint_member_8698)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_ground_node_congruent count tail 8698 joint_update_expr_8698 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [joint_update_expr_8698 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8274.
   rewrite E8697.
   reflexivity.
 - intros site value Eval.
   destruct (concrete_expression_closure inputs path flat_memories left joint_update_expr_8698 (joint_update_ready_8698 left H8274 H8697) site value Eval) as [ground [bits Value]].
   subst value. exists ground. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_joint_member_8699 : List.In (8699,joint_update_expr_8699) joint_update_expected_nodes.
Proof. apply (List.nth_error_In joint_update_expected_nodes 1188%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8699_congruent inputs path left right next_left next_right :
 (exists ground bits, VM.find 8272 left = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8698 left = Some (Gval ground bits)) ->
 VM.find 8272 left = VM.find 8272 right ->
 VM.find 8698 left = VM.find 8698 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8699 next_left = VM.find 8699 next_right.
Proof.
 intros H8272 H8698 E8272 E8698 L R.
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8699 joint_update_expr_8699 joint_update_node_positions joint_update_node_safety early_control_joint_member_8699)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_ground_node_congruent count tail 8699 joint_update_expr_8699 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [joint_update_expr_8699 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8272.
   rewrite E8698.
   reflexivity.
 - intros site value Eval.
   destruct (concrete_expression_closure inputs path flat_memories left joint_update_expr_8699 (joint_update_ready_8699 left H8272 H8698) site value Eval) as [ground [bits Value]].
   subst value. exists ground. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_joint_member_8700 : List.In (8700,joint_update_expr_8700) joint_update_expected_nodes.
Proof. apply (List.nth_error_In joint_update_expected_nodes 1189%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8700_congruent inputs path left right next_left next_right :
 (exists ground bits, VM.find 8270 left = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8699 left = Some (Gval ground bits)) ->
 VM.find 8270 left = VM.find 8270 right ->
 VM.find 8699 left = VM.find 8699 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8700 next_left = VM.find 8700 next_right.
Proof.
 intros H8270 H8699 E8270 E8699 L R.
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8700 joint_update_expr_8700 joint_update_node_positions joint_update_node_safety early_control_joint_member_8700)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_ground_node_congruent count tail 8700 joint_update_expr_8700 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [joint_update_expr_8700 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8270.
   rewrite E8699.
   reflexivity.
 - intros site value Eval.
   destruct (concrete_expression_closure inputs path flat_memories left joint_update_expr_8700 (joint_update_ready_8700 left H8270 H8699) site value Eval) as [ground [bits Value]].
   subst value. exists ground. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_joint_member_8701 : List.In (8701,joint_update_expr_8701) joint_update_expected_nodes.
Proof. apply (List.nth_error_In joint_update_expected_nodes 1190%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8701_congruent inputs path left right next_left next_right :
 (exists ground bits, VM.find 8268 left = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8700 left = Some (Gval ground bits)) ->
 VM.find 8268 left = VM.find 8268 right ->
 VM.find 8700 left = VM.find 8700 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8701 next_left = VM.find 8701 next_right.
Proof.
 intros H8268 H8700 E8268 E8700 L R.
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8701 joint_update_expr_8701 joint_update_node_positions joint_update_node_safety early_control_joint_member_8701)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_ground_node_congruent count tail 8701 joint_update_expr_8701 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [joint_update_expr_8701 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8268.
   rewrite E8700.
   reflexivity.
 - intros site value Eval.
   destruct (concrete_expression_closure inputs path flat_memories left joint_update_expr_8701 (joint_update_ready_8701 left H8268 H8700) site value Eval) as [ground [bits Value]].
   subst value. exists ground. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_joint_member_8702 : List.In (8702,joint_update_expr_8702) joint_update_expected_nodes.
Proof. apply (List.nth_error_In joint_update_expected_nodes 1191%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8702_congruent inputs path left right next_left next_right :
 (exists ground bits, VM.find 8266 left = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8701 left = Some (Gval ground bits)) ->
 VM.find 8266 left = VM.find 8266 right ->
 VM.find 8701 left = VM.find 8701 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8702 next_left = VM.find 8702 next_right.
Proof.
 intros H8266 H8701 E8266 E8701 L R.
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8702 joint_update_expr_8702 joint_update_node_positions joint_update_node_safety early_control_joint_member_8702)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_ground_node_congruent count tail 8702 joint_update_expr_8702 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [joint_update_expr_8702 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8266.
   rewrite E8701.
   reflexivity.
 - intros site value Eval.
   destruct (concrete_expression_closure inputs path flat_memories left joint_update_expr_8702 (joint_update_ready_8702 left H8266 H8701) site value Eval) as [ground [bits Value]].
   subst value. exists ground. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_joint_member_8703 : List.In (8703,joint_update_expr_8703) joint_update_expected_nodes.
Proof. apply (List.nth_error_In joint_update_expected_nodes 1192%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8703_congruent inputs path left right next_left next_right :
 (exists ground bits, VM.find 8264 left = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8702 left = Some (Gval ground bits)) ->
 VM.find 8264 left = VM.find 8264 right ->
 VM.find 8702 left = VM.find 8702 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8703 next_left = VM.find 8703 next_right.
Proof.
 intros H8264 H8702 E8264 E8702 L R.
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8703 joint_update_expr_8703 joint_update_node_positions joint_update_node_safety early_control_joint_member_8703)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_ground_node_congruent count tail 8703 joint_update_expr_8703 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [joint_update_expr_8703 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8264.
   rewrite E8702.
   reflexivity.
 - intros site value Eval.
   destruct (concrete_expression_closure inputs path flat_memories left joint_update_expr_8703 (joint_update_ready_8703 left H8264 H8702) site value Eval) as [ground [bits Value]].
   subst value. exists ground. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_joint_member_8998 : List.In (8998,joint_update_expr_8998) joint_update_expected_nodes.
Proof. apply (List.nth_error_In joint_update_expected_nodes 1389%nat). vm_compute. reflexivity. Qed.
Theorem early_control_node_8998_congruent inputs path left right next_left next_right :
 (exists ground bits, VM.find 8703 left = Some (Gval ground bits)) ->
 VM.find 8703 left = VM.find 8703 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 8998 next_left = VM.find 8998 next_right.
Proof.
 intros H8703 E8703 L R.
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8998 joint_update_expr_8998 joint_update_node_positions joint_update_node_safety early_control_joint_member_8998)
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_ground_node_congruent count tail 8998 joint_update_expr_8998 (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [joint_update_expr_8998 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E8703.
   reflexivity.
 - intros site value Eval.
   destruct (concrete_expression_closure inputs path flat_memories left joint_update_expr_8998 (joint_update_ready_8998 left H8703) site value Eval) as [ground [bits Value]].
   subst value. exists ground. reflexivity.
 - exact L.
 - exact R.
Qed.
