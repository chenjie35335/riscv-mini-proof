Require Import NopKillValues.
Require Import CoreSocModel ComparisonNodes FormalTypedNodeEquation SelectedNodeSafety FormalDeclaredConnection DataAddressPositionCertificate DataAddressSafetyCertificate DataAddressExpressionCertificates JointUpdateNodePositions JointUpdateExpressionCertificates DataAddressConnectionCertificates JointUpdateConnectionCertificates.
From Coq Require Import ZArith List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Definition nop_pc_select_value_8361 := Gval (Fuint 2) [::false;false].
Theorem nop_pc_select_step_8361 invalid old current result :
 VM.find 8360 old = Some nop_kill_value_8360 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8361 result = Some nop_pc_select_value_8361.
Proof.
 intros H8360 Step.
 assert (Member : List.In (8361,joint_update_expr_8361) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 1046%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8361 joint_update_expr_8361 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [joint_update_expr_8361 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8360.
 vm_compute. reflexivity.
Qed.
Definition nop_pc_select_value_8362 := Gval (Fuint 2) [::false;false].
Theorem nop_pc_select_step_8362 invalid old current result :
 VM.find 8358 old = Some nop_kill_value_8358 ->
 VM.find 8361 old = Some nop_pc_select_value_8361 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8362 result = Some nop_pc_select_value_8362.
Proof.
 intros H8358 H8361 Step.
 assert (Member : List.In (8362,joint_update_expr_8362) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 1047%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8362 joint_update_expr_8362 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [joint_update_expr_8362 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8358.
 rewrite H8361.
 vm_compute. reflexivity.
Qed.
Definition nop_pc_select_value_8363 := Gval (Fuint 2) [::false;false].
Theorem nop_pc_select_step_8363 invalid old current result :
 VM.find 8356 old = Some nop_kill_value_8356 ->
 VM.find 8362 old = Some nop_pc_select_value_8362 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8363 result = Some nop_pc_select_value_8363.
Proof.
 intros H8356 H8362 Step.
 assert (Member : List.In (8363,joint_update_expr_8363) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 1048%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8363 joint_update_expr_8363 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [joint_update_expr_8363 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8356.
 rewrite H8362.
 vm_compute. reflexivity.
Qed.
Definition nop_pc_select_value_8364 := Gval (Fuint 2) [::false;false].
Theorem nop_pc_select_step_8364 invalid old current result :
 VM.find 8354 old = Some nop_kill_value_8354 ->
 VM.find 8363 old = Some nop_pc_select_value_8363 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8364 result = Some nop_pc_select_value_8364.
Proof.
 intros H8354 H8363 Step.
 assert (Member : List.In (8364,joint_update_expr_8364) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 1049%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8364 joint_update_expr_8364 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [joint_update_expr_8364 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8354.
 rewrite H8363.
 vm_compute. reflexivity.
Qed.
Definition nop_pc_select_value_8365 := Gval (Fuint 2) [::false;false].
Theorem nop_pc_select_step_8365 invalid old current result :
 VM.find 8352 old = Some nop_kill_value_8352 ->
 VM.find 8364 old = Some nop_pc_select_value_8364 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8365 result = Some nop_pc_select_value_8365.
Proof.
 intros H8352 H8364 Step.
 assert (Member : List.In (8365,joint_update_expr_8365) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 1050%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8365 joint_update_expr_8365 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [joint_update_expr_8365 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8352.
 rewrite H8364.
 vm_compute. reflexivity.
Qed.
Definition nop_pc_select_value_8366 := Gval (Fuint 2) [::false;false].
Theorem nop_pc_select_step_8366 invalid old current result :
 VM.find 8350 old = Some nop_kill_value_8350 ->
 VM.find 8365 old = Some nop_pc_select_value_8365 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8366 result = Some nop_pc_select_value_8366.
Proof.
 intros H8350 H8365 Step.
 assert (Member : List.In (8366,joint_update_expr_8366) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 1051%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8366 joint_update_expr_8366 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [joint_update_expr_8366 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8350.
 rewrite H8365.
 vm_compute. reflexivity.
Qed.
Definition nop_pc_select_value_8367 := Gval (Fuint 2) [::false;false].
Theorem nop_pc_select_step_8367 invalid old current result :
 VM.find 8348 old = Some nop_kill_value_8348 ->
 VM.find 8366 old = Some nop_pc_select_value_8366 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8367 result = Some nop_pc_select_value_8367.
Proof.
 intros H8348 H8366 Step.
 assert (Member : List.In (8367,joint_update_expr_8367) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 1052%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8367 joint_update_expr_8367 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [joint_update_expr_8367 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8348.
 rewrite H8366.
 vm_compute. reflexivity.
Qed.
Definition nop_pc_select_value_8368 := Gval (Fuint 2) [::false;false].
Theorem nop_pc_select_step_8368 invalid old current result :
 VM.find 8346 old = Some nop_kill_value_8346 ->
 VM.find 8367 old = Some nop_pc_select_value_8367 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8368 result = Some nop_pc_select_value_8368.
Proof.
 intros H8346 H8367 Step.
 assert (Member : List.In (8368,joint_update_expr_8368) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 1053%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8368 joint_update_expr_8368 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [joint_update_expr_8368 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8346.
 rewrite H8367.
 vm_compute. reflexivity.
Qed.
Definition nop_pc_select_value_8369 := Gval (Fuint 2) [::false;false].
Theorem nop_pc_select_step_8369 invalid old current result :
 VM.find 8344 old = Some nop_kill_value_8344 ->
 VM.find 8368 old = Some nop_pc_select_value_8368 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8369 result = Some nop_pc_select_value_8369.
Proof.
 intros H8344 H8368 Step.
 assert (Member : List.In (8369,joint_update_expr_8369) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 1054%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8369 joint_update_expr_8369 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [joint_update_expr_8369 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8344.
 rewrite H8368.
 vm_compute. reflexivity.
Qed.
Definition nop_pc_select_value_8370 := Gval (Fuint 2) [::false;false].
Theorem nop_pc_select_step_8370 invalid old current result :
 VM.find 8342 old = Some nop_kill_value_8342 ->
 VM.find 8369 old = Some nop_pc_select_value_8369 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8370 result = Some nop_pc_select_value_8370.
Proof.
 intros H8342 H8369 Step.
 assert (Member : List.In (8370,joint_update_expr_8370) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 1055%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8370 joint_update_expr_8370 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [joint_update_expr_8370 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8342.
 rewrite H8369.
 vm_compute. reflexivity.
Qed.
Definition nop_pc_select_value_8371 := Gval (Fuint 2) [::false;false].
Theorem nop_pc_select_step_8371 invalid old current result :
 VM.find 8340 old = Some nop_kill_value_8340 ->
 VM.find 8370 old = Some nop_pc_select_value_8370 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8371 result = Some nop_pc_select_value_8371.
Proof.
 intros H8340 H8370 Step.
 assert (Member : List.In (8371,joint_update_expr_8371) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 1056%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8371 joint_update_expr_8371 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [joint_update_expr_8371 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8340.
 rewrite H8370.
 vm_compute. reflexivity.
Qed.
Definition nop_pc_select_value_8372 := Gval (Fuint 2) [::false;false].
Theorem nop_pc_select_step_8372 invalid old current result :
 VM.find 8338 old = Some nop_kill_value_8338 ->
 VM.find 8371 old = Some nop_pc_select_value_8371 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8372 result = Some nop_pc_select_value_8372.
Proof.
 intros H8338 H8371 Step.
 assert (Member : List.In (8372,joint_update_expr_8372) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 1057%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8372 joint_update_expr_8372 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [joint_update_expr_8372 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8338.
 rewrite H8371.
 vm_compute. reflexivity.
Qed.
Definition nop_pc_select_value_8373 := Gval (Fuint 2) [::false;false].
Theorem nop_pc_select_step_8373 invalid old current result :
 VM.find 8336 old = Some nop_kill_value_8336 ->
 VM.find 8372 old = Some nop_pc_select_value_8372 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8373 result = Some nop_pc_select_value_8373.
Proof.
 intros H8336 H8372 Step.
 assert (Member : List.In (8373,joint_update_expr_8373) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 1058%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8373 joint_update_expr_8373 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [joint_update_expr_8373 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8336.
 rewrite H8372.
 vm_compute. reflexivity.
Qed.
Definition nop_pc_select_value_8374 := Gval (Fuint 2) [::false;false].
Theorem nop_pc_select_step_8374 invalid old current result :
 VM.find 8334 old = Some nop_kill_value_8334 ->
 VM.find 8373 old = Some nop_pc_select_value_8373 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8374 result = Some nop_pc_select_value_8374.
Proof.
 intros H8334 H8373 Step.
 assert (Member : List.In (8374,joint_update_expr_8374) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 1059%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8374 joint_update_expr_8374 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [joint_update_expr_8374 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8334.
 rewrite H8373.
 vm_compute. reflexivity.
Qed.
Definition nop_pc_select_value_8375 := Gval (Fuint 2) [::false;false].
Theorem nop_pc_select_step_8375 invalid old current result :
 VM.find 8332 old = Some nop_kill_value_8332 ->
 VM.find 8374 old = Some nop_pc_select_value_8374 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8375 result = Some nop_pc_select_value_8375.
Proof.
 intros H8332 H8374 Step.
 assert (Member : List.In (8375,joint_update_expr_8375) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 1060%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8375 joint_update_expr_8375 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [joint_update_expr_8375 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8332.
 rewrite H8374.
 vm_compute. reflexivity.
Qed.
Definition nop_pc_select_value_8376 := Gval (Fuint 2) [::false;false].
Theorem nop_pc_select_step_8376 invalid old current result :
 VM.find 8330 old = Some nop_kill_value_8330 ->
 VM.find 8375 old = Some nop_pc_select_value_8375 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8376 result = Some nop_pc_select_value_8376.
Proof.
 intros H8330 H8375 Step.
 assert (Member : List.In (8376,joint_update_expr_8376) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 1061%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8376 joint_update_expr_8376 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [joint_update_expr_8376 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8330.
 rewrite H8375.
 vm_compute. reflexivity.
Qed.
Definition nop_pc_select_value_8377 := Gval (Fuint 2) [::false;false].
Theorem nop_pc_select_step_8377 invalid old current result :
 VM.find 8328 old = Some nop_kill_value_8328 ->
 VM.find 8376 old = Some nop_pc_select_value_8376 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8377 result = Some nop_pc_select_value_8377.
Proof.
 intros H8328 H8376 Step.
 assert (Member : List.In (8377,joint_update_expr_8377) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 1062%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8377 joint_update_expr_8377 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [joint_update_expr_8377 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8328.
 rewrite H8376.
 vm_compute. reflexivity.
Qed.
Definition nop_pc_select_value_8378 := Gval (Fuint 2) [::false;false].
Theorem nop_pc_select_step_8378 invalid old current result :
 VM.find 8326 old = Some nop_kill_value_8326 ->
 VM.find 8377 old = Some nop_pc_select_value_8377 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8378 result = Some nop_pc_select_value_8378.
Proof.
 intros H8326 H8377 Step.
 assert (Member : List.In (8378,joint_update_expr_8378) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 1063%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8378 joint_update_expr_8378 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [joint_update_expr_8378 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8326.
 rewrite H8377.
 vm_compute. reflexivity.
Qed.
Definition nop_pc_select_value_8379 := Gval (Fuint 2) [::false;false].
Theorem nop_pc_select_step_8379 invalid old current result :
 VM.find 8324 old = Some nop_kill_value_8324 ->
 VM.find 8378 old = Some nop_pc_select_value_8378 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8379 result = Some nop_pc_select_value_8379.
Proof.
 intros H8324 H8378 Step.
 assert (Member : List.In (8379,joint_update_expr_8379) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 1064%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8379 joint_update_expr_8379 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [joint_update_expr_8379 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8324.
 rewrite H8378.
 vm_compute. reflexivity.
Qed.
Definition nop_pc_select_value_8380 := Gval (Fuint 2) [::false;false].
Theorem nop_pc_select_step_8380 invalid old current result :
 VM.find 8322 old = Some nop_kill_value_8322 ->
 VM.find 8379 old = Some nop_pc_select_value_8379 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8380 result = Some nop_pc_select_value_8380.
Proof.
 intros H8322 H8379 Step.
 assert (Member : List.In (8380,joint_update_expr_8380) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 1065%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8380 joint_update_expr_8380 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [joint_update_expr_8380 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8322.
 rewrite H8379.
 vm_compute. reflexivity.
Qed.
Definition nop_pc_select_value_8381 := Gval (Fuint 2) [::false;false].
Theorem nop_pc_select_step_8381 invalid old current result :
 VM.find 8320 old = Some nop_kill_value_8320 ->
 VM.find 8380 old = Some nop_pc_select_value_8380 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8381 result = Some nop_pc_select_value_8381.
Proof.
 intros H8320 H8380 Step.
 assert (Member : List.In (8381,joint_update_expr_8381) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 1066%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8381 joint_update_expr_8381 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [joint_update_expr_8381 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8320.
 rewrite H8380.
 vm_compute. reflexivity.
Qed.
Definition nop_pc_select_value_8382 := Gval (Fuint 2) [::false;false].
Theorem nop_pc_select_step_8382 invalid old current result :
 VM.find 8318 old = Some nop_kill_value_8318 ->
 VM.find 8381 old = Some nop_pc_select_value_8381 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8382 result = Some nop_pc_select_value_8382.
Proof.
 intros H8318 H8381 Step.
 assert (Member : List.In (8382,joint_update_expr_8382) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 1067%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8382 joint_update_expr_8382 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [joint_update_expr_8382 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8318.
 rewrite H8381.
 vm_compute. reflexivity.
Qed.
Definition nop_pc_select_value_8383 := Gval (Fuint 2) [::false;false].
Theorem nop_pc_select_step_8383 invalid old current result :
 VM.find 8316 old = Some nop_kill_value_8316 ->
 VM.find 8382 old = Some nop_pc_select_value_8382 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8383 result = Some nop_pc_select_value_8383.
Proof.
 intros H8316 H8382 Step.
 assert (Member : List.In (8383,joint_update_expr_8383) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 1068%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8383 joint_update_expr_8383 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [joint_update_expr_8383 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8316.
 rewrite H8382.
 vm_compute. reflexivity.
Qed.
Definition nop_pc_select_value_8384 := Gval (Fuint 2) [::false;false].
Theorem nop_pc_select_step_8384 invalid old current result :
 VM.find 8314 old = Some nop_kill_value_8314 ->
 VM.find 8383 old = Some nop_pc_select_value_8383 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8384 result = Some nop_pc_select_value_8384.
Proof.
 intros H8314 H8383 Step.
 assert (Member : List.In (8384,joint_update_expr_8384) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 1069%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8384 joint_update_expr_8384 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [joint_update_expr_8384 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8314.
 rewrite H8383.
 vm_compute. reflexivity.
Qed.
Definition nop_pc_select_value_8385 := Gval (Fuint 2) [::false;false].
Theorem nop_pc_select_step_8385 invalid old current result :
 VM.find 8312 old = Some nop_kill_value_8312 ->
 VM.find 8384 old = Some nop_pc_select_value_8384 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8385 result = Some nop_pc_select_value_8385.
Proof.
 intros H8312 H8384 Step.
 assert (Member : List.In (8385,joint_update_expr_8385) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 1070%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8385 joint_update_expr_8385 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [joint_update_expr_8385 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8312.
 rewrite H8384.
 vm_compute. reflexivity.
Qed.
Definition nop_pc_select_value_8386 := Gval (Fuint 2) [::false;false].
Theorem nop_pc_select_step_8386 invalid old current result :
 VM.find 8310 old = Some nop_kill_value_8310 ->
 VM.find 8385 old = Some nop_pc_select_value_8385 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8386 result = Some nop_pc_select_value_8386.
Proof.
 intros H8310 H8385 Step.
 assert (Member : List.In (8386,joint_update_expr_8386) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 1071%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8386 joint_update_expr_8386 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [joint_update_expr_8386 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8310.
 rewrite H8385.
 vm_compute. reflexivity.
Qed.
Definition nop_pc_select_value_8387 := Gval (Fuint 2) [::false;false].
Theorem nop_pc_select_step_8387 invalid old current result :
 VM.find 8308 old = Some nop_kill_value_8308 ->
 VM.find 8386 old = Some nop_pc_select_value_8386 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8387 result = Some nop_pc_select_value_8387.
Proof.
 intros H8308 H8386 Step.
 assert (Member : List.In (8387,joint_update_expr_8387) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 1072%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8387 joint_update_expr_8387 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [joint_update_expr_8387 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8308.
 rewrite H8386.
 vm_compute. reflexivity.
Qed.
Definition nop_pc_select_value_8388 := Gval (Fuint 2) [::false;false].
Theorem nop_pc_select_step_8388 invalid old current result :
 VM.find 8306 old = Some nop_kill_value_8306 ->
 VM.find 8387 old = Some nop_pc_select_value_8387 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8388 result = Some nop_pc_select_value_8388.
Proof.
 intros H8306 H8387 Step.
 assert (Member : List.In (8388,joint_update_expr_8388) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 1073%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8388 joint_update_expr_8388 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [joint_update_expr_8388 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8306.
 rewrite H8387.
 vm_compute. reflexivity.
Qed.
Definition nop_pc_select_value_8389 := Gval (Fuint 2) [::false;false].
Theorem nop_pc_select_step_8389 invalid old current result :
 VM.find 8304 old = Some nop_kill_value_8304 ->
 VM.find 8388 old = Some nop_pc_select_value_8388 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8389 result = Some nop_pc_select_value_8389.
Proof.
 intros H8304 H8388 Step.
 assert (Member : List.In (8389,joint_update_expr_8389) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 1074%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8389 joint_update_expr_8389 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [joint_update_expr_8389 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8304.
 rewrite H8388.
 vm_compute. reflexivity.
Qed.
Definition nop_pc_select_value_8390 := Gval (Fuint 2) [::false;false].
Theorem nop_pc_select_step_8390 invalid old current result :
 VM.find 8302 old = Some nop_kill_value_8302 ->
 VM.find 8389 old = Some nop_pc_select_value_8389 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8390 result = Some nop_pc_select_value_8390.
Proof.
 intros H8302 H8389 Step.
 assert (Member : List.In (8390,joint_update_expr_8390) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 1075%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8390 joint_update_expr_8390 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [joint_update_expr_8390 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8302.
 rewrite H8389.
 vm_compute. reflexivity.
Qed.
Definition nop_pc_select_value_8391 := Gval (Fuint 2) [::false;false].
Theorem nop_pc_select_step_8391 invalid old current result :
 VM.find 8300 old = Some nop_kill_value_8300 ->
 VM.find 8390 old = Some nop_pc_select_value_8390 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8391 result = Some nop_pc_select_value_8391.
Proof.
 intros H8300 H8390 Step.
 assert (Member : List.In (8391,joint_update_expr_8391) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 1076%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8391 joint_update_expr_8391 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [joint_update_expr_8391 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8300.
 rewrite H8390.
 vm_compute. reflexivity.
Qed.
Definition nop_pc_select_value_8392 := Gval (Fuint 2) [::false;false].
Theorem nop_pc_select_step_8392 invalid old current result :
 VM.find 8298 old = Some nop_kill_value_8298 ->
 VM.find 8391 old = Some nop_pc_select_value_8391 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8392 result = Some nop_pc_select_value_8392.
Proof.
 intros H8298 H8391 Step.
 assert (Member : List.In (8392,joint_update_expr_8392) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 1077%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8392 joint_update_expr_8392 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [joint_update_expr_8392 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8298.
 rewrite H8391.
 vm_compute. reflexivity.
Qed.
Definition nop_pc_select_value_8393 := Gval (Fuint 2) [::false;false].
Theorem nop_pc_select_step_8393 invalid old current result :
 VM.find 8296 old = Some nop_kill_value_8296 ->
 VM.find 8392 old = Some nop_pc_select_value_8392 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8393 result = Some nop_pc_select_value_8393.
Proof.
 intros H8296 H8392 Step.
 assert (Member : List.In (8393,joint_update_expr_8393) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 1078%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8393 joint_update_expr_8393 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [joint_update_expr_8393 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8296.
 rewrite H8392.
 vm_compute. reflexivity.
Qed.
Definition nop_pc_select_value_8394 := Gval (Fuint 2) [::false;false].
Theorem nop_pc_select_step_8394 invalid old current result :
 VM.find 8294 old = Some nop_kill_value_8294 ->
 VM.find 8393 old = Some nop_pc_select_value_8393 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8394 result = Some nop_pc_select_value_8394.
Proof.
 intros H8294 H8393 Step.
 assert (Member : List.In (8394,joint_update_expr_8394) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 1079%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8394 joint_update_expr_8394 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [joint_update_expr_8394 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8294.
 rewrite H8393.
 vm_compute. reflexivity.
Qed.
Definition nop_pc_select_value_8395 := Gval (Fuint 2) [::false;false].
Theorem nop_pc_select_step_8395 invalid old current result :
 VM.find 8292 old = Some nop_kill_value_8292 ->
 VM.find 8394 old = Some nop_pc_select_value_8394 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8395 result = Some nop_pc_select_value_8395.
Proof.
 intros H8292 H8394 Step.
 assert (Member : List.In (8395,joint_update_expr_8395) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 1080%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8395 joint_update_expr_8395 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [joint_update_expr_8395 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8292.
 rewrite H8394.
 vm_compute. reflexivity.
Qed.
Definition nop_pc_select_value_8396 := Gval (Fuint 2) [::false;false].
Theorem nop_pc_select_step_8396 invalid old current result :
 VM.find 8290 old = Some nop_kill_value_8290 ->
 VM.find 8395 old = Some nop_pc_select_value_8395 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8396 result = Some nop_pc_select_value_8396.
Proof.
 intros H8290 H8395 Step.
 assert (Member : List.In (8396,joint_update_expr_8396) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 1081%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8396 joint_update_expr_8396 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [joint_update_expr_8396 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8290.
 rewrite H8395.
 vm_compute. reflexivity.
Qed.
Definition nop_pc_select_value_8397 := Gval (Fuint 2) [::false;false].
Theorem nop_pc_select_step_8397 invalid old current result :
 VM.find 8288 old = Some nop_kill_value_8288 ->
 VM.find 8396 old = Some nop_pc_select_value_8396 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8397 result = Some nop_pc_select_value_8397.
Proof.
 intros H8288 H8396 Step.
 assert (Member : List.In (8397,joint_update_expr_8397) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 1082%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8397 joint_update_expr_8397 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [joint_update_expr_8397 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8288.
 rewrite H8396.
 vm_compute. reflexivity.
Qed.
Definition nop_pc_select_value_8398 := Gval (Fuint 2) [::false;false].
Theorem nop_pc_select_step_8398 invalid old current result :
 VM.find 8286 old = Some nop_kill_value_8286 ->
 VM.find 8397 old = Some nop_pc_select_value_8397 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8398 result = Some nop_pc_select_value_8398.
Proof.
 intros H8286 H8397 Step.
 assert (Member : List.In (8398,joint_update_expr_8398) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 1083%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8398 joint_update_expr_8398 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [joint_update_expr_8398 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8286.
 rewrite H8397.
 vm_compute. reflexivity.
Qed.
Definition nop_pc_select_value_8399 := Gval (Fuint 2) [::false;false].
Theorem nop_pc_select_step_8399 invalid old current result :
 VM.find 8284 old = Some nop_kill_value_8284 ->
 VM.find 8398 old = Some nop_pc_select_value_8398 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8399 result = Some nop_pc_select_value_8399.
Proof.
 intros H8284 H8398 Step.
 assert (Member : List.In (8399,joint_update_expr_8399) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 1084%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8399 joint_update_expr_8399 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [joint_update_expr_8399 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8284.
 rewrite H8398.
 vm_compute. reflexivity.
Qed.
Definition nop_pc_select_value_8400 := Gval (Fuint 2) [::false;false].
Theorem nop_pc_select_step_8400 invalid old current result :
 VM.find 8282 old = Some nop_kill_value_8282 ->
 VM.find 8399 old = Some nop_pc_select_value_8399 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8400 result = Some nop_pc_select_value_8400.
Proof.
 intros H8282 H8399 Step.
 assert (Member : List.In (8400,joint_update_expr_8400) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 1085%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8400 joint_update_expr_8400 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [joint_update_expr_8400 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8282.
 rewrite H8399.
 vm_compute. reflexivity.
Qed.
Definition nop_pc_select_value_8401 := Gval (Fuint 2) [::false;false].
Theorem nop_pc_select_step_8401 invalid old current result :
 VM.find 8280 old = Some nop_kill_value_8280 ->
 VM.find 8400 old = Some nop_pc_select_value_8400 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8401 result = Some nop_pc_select_value_8401.
Proof.
 intros H8280 H8400 Step.
 assert (Member : List.In (8401,joint_update_expr_8401) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 1086%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8401 joint_update_expr_8401 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [joint_update_expr_8401 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8280.
 rewrite H8400.
 vm_compute. reflexivity.
Qed.
Definition nop_pc_select_value_8402 := Gval (Fuint 2) [::false;false].
Theorem nop_pc_select_step_8402 invalid old current result :
 VM.find 8278 old = Some nop_kill_value_8278 ->
 VM.find 8401 old = Some nop_pc_select_value_8401 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8402 result = Some nop_pc_select_value_8402.
Proof.
 intros H8278 H8401 Step.
 assert (Member : List.In (8402,joint_update_expr_8402) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 1087%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8402 joint_update_expr_8402 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [joint_update_expr_8402 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8278.
 rewrite H8401.
 vm_compute. reflexivity.
Qed.
Definition nop_pc_select_value_8403 := Gval (Fuint 2) [::false;false].
Theorem nop_pc_select_step_8403 invalid old current result :
 VM.find 8276 old = Some nop_kill_value_8276 ->
 VM.find 8402 old = Some nop_pc_select_value_8402 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8403 result = Some nop_pc_select_value_8403.
Proof.
 intros H8276 H8402 Step.
 assert (Member : List.In (8403,joint_update_expr_8403) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 1088%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8403 joint_update_expr_8403 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [joint_update_expr_8403 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8276.
 rewrite H8402.
 vm_compute. reflexivity.
Qed.
Definition nop_pc_select_value_8404 := Gval (Fuint 2) [::false;false].
Theorem nop_pc_select_step_8404 invalid old current result :
 VM.find 8274 old = Some nop_kill_value_8274 ->
 VM.find 8403 old = Some nop_pc_select_value_8403 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8404 result = Some nop_pc_select_value_8404.
Proof.
 intros H8274 H8403 Step.
 assert (Member : List.In (8404,joint_update_expr_8404) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 1089%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8404 joint_update_expr_8404 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [joint_update_expr_8404 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8274.
 rewrite H8403.
 vm_compute. reflexivity.
Qed.
Definition nop_pc_select_value_8405 := Gval (Fuint 2) [::false;false].
Theorem nop_pc_select_step_8405 invalid old current result :
 VM.find 8272 old = Some nop_kill_value_8272 ->
 VM.find 8404 old = Some nop_pc_select_value_8404 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8405 result = Some nop_pc_select_value_8405.
Proof.
 intros H8272 H8404 Step.
 assert (Member : List.In (8405,joint_update_expr_8405) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 1090%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8405 joint_update_expr_8405 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [joint_update_expr_8405 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8272.
 rewrite H8404.
 vm_compute. reflexivity.
Qed.
Definition nop_pc_select_value_8406 := Gval (Fuint 2) [::false;false].
Theorem nop_pc_select_step_8406 invalid old current result :
 VM.find 8270 old = Some nop_kill_value_8270 ->
 VM.find 8405 old = Some nop_pc_select_value_8405 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8406 result = Some nop_pc_select_value_8406.
Proof.
 intros H8270 H8405 Step.
 assert (Member : List.In (8406,joint_update_expr_8406) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 1091%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8406 joint_update_expr_8406 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [joint_update_expr_8406 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8270.
 rewrite H8405.
 vm_compute. reflexivity.
Qed.
Definition nop_pc_select_value_8407 := Gval (Fuint 2) [::false;false].
Theorem nop_pc_select_step_8407 invalid old current result :
 VM.find 8268 old = Some nop_kill_value_8268 ->
 VM.find 8406 old = Some nop_pc_select_value_8406 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8407 result = Some nop_pc_select_value_8407.
Proof.
 intros H8268 H8406 Step.
 assert (Member : List.In (8407,joint_update_expr_8407) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 1092%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8407 joint_update_expr_8407 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [joint_update_expr_8407 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8268.
 rewrite H8406.
 vm_compute. reflexivity.
Qed.
Definition nop_pc_select_value_8408 := Gval (Fuint 2) [::false;false].
Theorem nop_pc_select_step_8408 invalid old current result :
 VM.find 8266 old = Some nop_kill_value_8266 ->
 VM.find 8407 old = Some nop_pc_select_value_8407 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8408 result = Some nop_pc_select_value_8408.
Proof.
 intros H8266 H8407 Step.
 assert (Member : List.In (8408,joint_update_expr_8408) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 1093%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8408 joint_update_expr_8408 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [joint_update_expr_8408 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8266.
 rewrite H8407.
 vm_compute. reflexivity.
Qed.
Definition nop_pc_select_value_8409 := Gval (Fuint 2) [::false;false].
Theorem nop_pc_select_step_8409 invalid old current result :
 VM.find 8264 old = Some nop_kill_value_8264 ->
 VM.find 8408 old = Some nop_pc_select_value_8408 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8409 result = Some nop_pc_select_value_8409.
Proof.
 intros H8264 H8408 Step.
 assert (Member : List.In (8409,joint_update_expr_8409) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 1094%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8409 joint_update_expr_8409 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [joint_update_expr_8409 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8264.
 rewrite H8408.
 vm_compute. reflexivity.
Qed.
Definition nop_pc_select_value_8250 := Gval (Fuint 2) [::false;false].
Theorem nop_pc_select_step_8250 invalid old current result :
 VM.find 8409 old = Some nop_pc_select_value_8409 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8250 result = Some nop_pc_select_value_8250.
Proof.
 intros H8409 Step.
 apply (declared_connection_value 9010 flat_statements joint_update_connection_8250_decl joint_update_connection_8250_mid joint_update_connection_8250_tail
 8250 8409 2 nop_pc_select_value_8409 nop_pc_select_value_8250 invalid flat_memories old current result
 joint_update_connection_8250_position joint_update_connection_8250_split joint_update_connection_8250_straight joint_update_connection_8250_mid_safe joint_update_connection_8250_tail_safe joint_update_connection_8250_nonregister (Logic.eq_refl _) H8409);
 [vm_compute;reflexivity|exact Step].
Qed.
Definition nop_pc_select_value_84 := Gval (Fuint 2) [::false;false].
Theorem nop_pc_select_step_84 invalid old current result :
 VM.find 8250 old = Some nop_pc_select_value_8250 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 84 result = Some nop_pc_select_value_84.
Proof.
 intros H8250 Step.
 apply (declared_connection_value 61 flat_statements joint_update_connection_84_decl joint_update_connection_84_mid joint_update_connection_84_tail
 84 8250 2 nop_pc_select_value_8250 nop_pc_select_value_84 invalid flat_memories old current result
 joint_update_connection_84_position joint_update_connection_84_split joint_update_connection_84_straight joint_update_connection_84_mid_safe joint_update_connection_84_tail_safe joint_update_connection_84_nonregister (Logic.eq_refl _) H8250);
 [vm_compute;reflexivity|exact Step].
Qed.
Definition nop_pc_select_value_7771 := Gval (Fuint 1) [::false].
Theorem nop_pc_select_step_7771 invalid old current result :
 VM.find 84 old = Some nop_pc_select_value_84 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 7771 result = Some nop_pc_select_value_7771.
Proof.
 intros H84 Step.
 assert (Member : List.In (7771,joint_update_expr_7771) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 886%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 7771 joint_update_expr_7771 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [joint_update_expr_7771 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H84.
 vm_compute. reflexivity.
Qed.
Definition nop_pc_select_value_7772 := Gval (Fuint 1) [::false].
Theorem nop_pc_select_step_7772 invalid old current result :
 VM.find 84 old = Some nop_pc_select_value_84 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 7772 result = Some nop_pc_select_value_7772.
Proof.
 intros H84 Step.
 assert (Member : List.In (7772,joint_update_expr_7772) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 887%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 7772 joint_update_expr_7772 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [joint_update_expr_7772 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H84.
 vm_compute. reflexivity.
Qed.
Definition nop_pc_select_value_7776 := Gval (Fuint 1) [::false].
Theorem nop_pc_select_step_7776 invalid old current result :
 VM.find 84 old = Some nop_pc_select_value_84 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 7776 result = Some nop_pc_select_value_7776.
Proof.
 intros H84 Step.
 assert (Member : List.In (7776,joint_update_expr_7776) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 891%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 7776 joint_update_expr_7776 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [joint_update_expr_7776 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H84.
 vm_compute. reflexivity.
Qed.
Print Assumptions nop_pc_select_step_84.
Print Assumptions nop_pc_select_step_7771.
