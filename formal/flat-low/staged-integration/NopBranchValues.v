Require Import FormalDeclaredConnection JointUpdateConnectionCertificates NopBranchShapes CoreSocModel ComparisonNodes FormalTypedNodeEquation SelectedNodeSafety FormalSuccessfulNodeEvaluation JointUpdateNodePositions JointUpdateExpressionCertificates NormalizedBit.
From Coq Require Import ZArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Theorem nop_branch_zero_step_1359 invalid old current result :
 VM.find 90 old = Some (Gval (Fuint 3) [::false;false;false]) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 1359 result = Some (Gval (Fuint 3) [::false;false;false]).
Proof.
 intros H90 Step.
 apply (declared_connection_value 1437 flat_statements joint_update_connection_1359_decl joint_update_connection_1359_mid joint_update_connection_1359_tail
 1359 90 3 (Gval (Fuint 3) [::false;false;false]) (Gval (Fuint 3) [::false;false;false]) invalid flat_memories old current result
 joint_update_connection_1359_position joint_update_connection_1359_split joint_update_connection_1359_straight joint_update_connection_1359_mid_safe joint_update_connection_1359_tail_safe joint_update_connection_1359_nonregister (Logic.eq_refl _) H90);
 [reflexivity|exact Step].
Qed.
Theorem nop_branch_zero_step_1376 invalid old current result :
 VM.find 1359 old = Some (Gval (Fuint 3) [::false;false;false]) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 1376 result = Some (Gval (Fuint 1) [::false]).
Proof.
 intros H1359 Step.
 assert (Member : List.In (1376,joint_update_expr_1376) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 864%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 1376 joint_update_expr_1376 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [joint_update_expr_1376 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite H1359.
 reflexivity.
Qed.
Theorem nop_branch_zero_step_1377 invalid old current result :
 VM.find 1376 old = Some (Gval (Fuint 1) [::false]) ->
 (exists value, VM.find 1364 old = Some value /\ normalized_bit value) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 1377 result = Some (Gval (Fuint 1) [::false]).
Proof.
 intros H1376 [value [Value Normal]] Step.
 assert (Member : List.In (1377,joint_update_expr_1377) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 865%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 1377 joint_update_expr_1377 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [joint_update_expr_1377 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite H1376.
 rewrite Value. apply nop_branch_zero_and_normalized. exact Normal.
Qed.
Theorem nop_branch_zero_step_1378 invalid old current result :
 VM.find 1359 old = Some (Gval (Fuint 3) [::false;false;false]) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 1378 result = Some (Gval (Fuint 1) [::false]).
Proof.
 intros H1359 Step.
 assert (Member : List.In (1378,joint_update_expr_1378) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 866%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 1378 joint_update_expr_1378 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [joint_update_expr_1378 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite H1359.
 reflexivity.
Qed.
Theorem nop_branch_zero_step_1379 invalid old current result :
 VM.find 1378 old = Some (Gval (Fuint 1) [::false]) ->
 (exists value, VM.find 1363 old = Some value /\ normalized_bit value) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 1379 result = Some (Gval (Fuint 1) [::false]).
Proof.
 intros H1378 [value [Value Normal]] Step.
 assert (Member : List.In (1379,joint_update_expr_1379) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 867%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 1379 joint_update_expr_1379 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [joint_update_expr_1379 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite H1378.
 rewrite Value. apply nop_branch_zero_and_normalized. exact Normal.
Qed.
Theorem nop_branch_zero_step_1380 invalid old current result :
 VM.find 1377 old = Some (Gval (Fuint 1) [::false]) ->
 VM.find 1379 old = Some (Gval (Fuint 1) [::false]) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 1380 result = Some (Gval (Fuint 1) [::false]).
Proof.
 intros H1377 H1379 Step.
 assert (Member : List.In (1380,joint_update_expr_1380) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 868%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 1380 joint_update_expr_1380 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [joint_update_expr_1380 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite H1377.
 rewrite H1379.
 reflexivity.
Qed.
Theorem nop_branch_zero_step_1381 invalid old current result :
 VM.find 1359 old = Some (Gval (Fuint 3) [::false;false;false]) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 1381 result = Some (Gval (Fuint 1) [::false]).
Proof.
 intros H1359 Step.
 assert (Member : List.In (1381,joint_update_expr_1381) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 869%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 1381 joint_update_expr_1381 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [joint_update_expr_1381 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite H1359.
 reflexivity.
Qed.
Theorem nop_branch_zero_step_1382 invalid old current result :
 VM.find 1381 old = Some (Gval (Fuint 1) [::false]) ->
 (exists value, VM.find 1370 old = Some value /\ normalized_bit value) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 1382 result = Some (Gval (Fuint 1) [::false]).
Proof.
 intros H1381 [value [Value Normal]] Step.
 assert (Member : List.In (1382,joint_update_expr_1382) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 870%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 1382 joint_update_expr_1382 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [joint_update_expr_1382 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite H1381.
 rewrite Value. apply nop_branch_zero_and_normalized. exact Normal.
Qed.
Theorem nop_branch_zero_step_1383 invalid old current result :
 VM.find 1380 old = Some (Gval (Fuint 1) [::false]) ->
 VM.find 1382 old = Some (Gval (Fuint 1) [::false]) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 1383 result = Some (Gval (Fuint 1) [::false]).
Proof.
 intros H1380 H1382 Step.
 assert (Member : List.In (1383,joint_update_expr_1383) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 871%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 1383 joint_update_expr_1383 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [joint_update_expr_1383 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite H1380.
 rewrite H1382.
 reflexivity.
Qed.
Theorem nop_branch_zero_step_1384 invalid old current result :
 VM.find 1359 old = Some (Gval (Fuint 3) [::false;false;false]) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 1384 result = Some (Gval (Fuint 1) [::false]).
Proof.
 intros H1359 Step.
 assert (Member : List.In (1384,joint_update_expr_1384) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 872%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 1384 joint_update_expr_1384 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [joint_update_expr_1384 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite H1359.
 reflexivity.
Qed.
Theorem nop_branch_zero_step_1385 invalid old current result :
 VM.find 1384 old = Some (Gval (Fuint 1) [::false]) ->
 (exists value, VM.find 1374 old = Some value /\ normalized_bit value) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 1385 result = Some (Gval (Fuint 1) [::false]).
Proof.
 intros H1384 [value [Value Normal]] Step.
 assert (Member : List.In (1385,joint_update_expr_1385) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 873%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 1385 joint_update_expr_1385 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [joint_update_expr_1385 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite H1384.
 rewrite Value. apply nop_branch_zero_and_normalized. exact Normal.
Qed.
Theorem nop_branch_zero_step_1386 invalid old current result :
 VM.find 1383 old = Some (Gval (Fuint 1) [::false]) ->
 VM.find 1385 old = Some (Gval (Fuint 1) [::false]) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 1386 result = Some (Gval (Fuint 1) [::false]).
Proof.
 intros H1383 H1385 Step.
 assert (Member : List.In (1386,joint_update_expr_1386) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 874%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 1386 joint_update_expr_1386 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [joint_update_expr_1386 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite H1383.
 rewrite H1385.
 reflexivity.
Qed.
Theorem nop_branch_zero_step_1387 invalid old current result :
 VM.find 1359 old = Some (Gval (Fuint 3) [::false;false;false]) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 1387 result = Some (Gval (Fuint 1) [::false]).
Proof.
 intros H1359 Step.
 assert (Member : List.In (1387,joint_update_expr_1387) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 875%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 1387 joint_update_expr_1387 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [joint_update_expr_1387 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite H1359.
 reflexivity.
Qed.
Theorem nop_branch_zero_step_1388 invalid old current result :
 VM.find 1387 old = Some (Gval (Fuint 1) [::false]) ->
 (exists value, VM.find 1373 old = Some value /\ normalized_bit value) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 1388 result = Some (Gval (Fuint 1) [::false]).
Proof.
 intros H1387 [value [Value Normal]] Step.
 assert (Member : List.In (1388,joint_update_expr_1388) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 876%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 1388 joint_update_expr_1388 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [joint_update_expr_1388 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite H1387.
 rewrite Value. apply nop_branch_zero_and_normalized. exact Normal.
Qed.
Theorem nop_branch_zero_step_1389 invalid old current result :
 VM.find 1386 old = Some (Gval (Fuint 1) [::false]) ->
 VM.find 1388 old = Some (Gval (Fuint 1) [::false]) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 1389 result = Some (Gval (Fuint 1) [::false]).
Proof.
 intros H1386 H1388 Step.
 assert (Member : List.In (1389,joint_update_expr_1389) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 877%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 1389 joint_update_expr_1389 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [joint_update_expr_1389 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite H1386.
 rewrite H1388.
 reflexivity.
Qed.
Theorem nop_branch_zero_step_1390 invalid old current result :
 VM.find 1359 old = Some (Gval (Fuint 3) [::false;false;false]) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 1390 result = Some (Gval (Fuint 1) [::false]).
Proof.
 intros H1359 Step.
 assert (Member : List.In (1390,joint_update_expr_1390) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 878%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 1390 joint_update_expr_1390 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [joint_update_expr_1390 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite H1359.
 reflexivity.
Qed.
Theorem nop_branch_zero_step_1391 invalid old current result :
 VM.find 1390 old = Some (Gval (Fuint 1) [::false]) ->
 (exists value, VM.find 1375 old = Some value /\ normalized_bit value) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 1391 result = Some (Gval (Fuint 1) [::false]).
Proof.
 intros H1390 [value [Value Normal]] Step.
 assert (Member : List.In (1391,joint_update_expr_1391) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 879%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 1391 joint_update_expr_1391 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [joint_update_expr_1391 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite H1390.
 rewrite Value. apply nop_branch_zero_and_normalized. exact Normal.
Qed.
Theorem nop_branch_zero_step_1392 invalid old current result :
 VM.find 1389 old = Some (Gval (Fuint 1) [::false]) ->
 VM.find 1391 old = Some (Gval (Fuint 1) [::false]) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 1392 result = Some (Gval (Fuint 1) [::false]).
Proof.
 intros H1389 H1391 Step.
 assert (Member : List.In (1392,joint_update_expr_1392) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 880%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 1392 joint_update_expr_1392 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [joint_update_expr_1392 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite H1389.
 rewrite H1391.
 reflexivity.
Qed.
Theorem nop_branch_zero_step_1360 invalid old current result :
 VM.find 1392 old = Some (Gval (Fuint 1) [::false]) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 1360 result = Some (Gval (Fuint 1) [::false]).
Proof.
 intros H1392 Step.
 apply (declared_connection_value 1438 flat_statements joint_update_connection_1360_decl joint_update_connection_1360_mid joint_update_connection_1360_tail
 1360 1392 1 (Gval (Fuint 1) [::false]) (Gval (Fuint 1) [::false]) invalid flat_memories old current result
 joint_update_connection_1360_position joint_update_connection_1360_split joint_update_connection_1360_straight joint_update_connection_1360_mid_safe joint_update_connection_1360_tail_safe joint_update_connection_1360_nonregister (Logic.eq_refl _) H1392);
 [reflexivity|exact Step].
Qed.
