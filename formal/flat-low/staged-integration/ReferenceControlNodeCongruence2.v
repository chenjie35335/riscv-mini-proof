Require Import CoreSocModel ComparisonNodes ReferenceControlExpressions ReferenceControlGroundOperations ReferenceControlGroundExpressions ReferenceControlNodeGeneric SelectedNodeSafety.
From Coq Require Import ZArith List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Require Import ReferenceControlNodeCertificates2.
Lemma reference_control_ready_2483 old :
 reference_control_ready old reference_control_expr_2483.
Proof.
 unfold reference_control_expr_2483.
apply rc_binary.
Qed.
Lemma reference_control_member_2483 : List.In (2483,reference_control_expr_2483) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 0%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2483_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2483 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2483 reference_control_expr_2483 reference_control_2_positions reference_control_2_safety reference_control_member_2483) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2483 reference_control_expr_2483 inputs path old current result Position Safe Nonreg (reference_control_ready_2483 old ) Step).
Qed.
Theorem reference_control_node_2483_congruent inputs path left right next_left next_right :
 VM.find 2480 left = VM.find 2480 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2483 next_left = VM.find 2483 next_right.
Proof.
 intros  E2480 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2483 reference_control_expr_2483 reference_control_2_positions reference_control_2_safety reference_control_member_2483) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2483 reference_control_expr_2483 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2483 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2483 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2480.
 reflexivity.
Qed.
Lemma reference_control_ready_2484 old :
 reference_control_ready old reference_control_expr_2484.
Proof.
 unfold reference_control_expr_2484.
apply rc_unary.
Qed.
Lemma reference_control_member_2484 : List.In (2484,reference_control_expr_2484) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 1%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2484_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2484 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2484 reference_control_expr_2484 reference_control_2_positions reference_control_2_safety reference_control_member_2484) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2484 reference_control_expr_2484 inputs path old current result Position Safe Nonreg (reference_control_ready_2484 old ) Step).
Qed.
Theorem reference_control_node_2484_congruent inputs path left right next_left next_right :
 VM.find 2483 left = VM.find 2483 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2484 next_left = VM.find 2484 next_right.
Proof.
 intros  E2483 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2484 reference_control_expr_2484 reference_control_2_positions reference_control_2_safety reference_control_member_2484) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2484 reference_control_expr_2484 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2484 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2484 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2483.
 reflexivity.
Qed.
Lemma reference_control_ready_2485 old :
 reference_control_ready old reference_control_expr_2485.
Proof.
 unfold reference_control_expr_2485.
apply rc_unary.
Qed.
Lemma reference_control_member_2485 : List.In (2485,reference_control_expr_2485) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 2%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2485_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2485 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2485 reference_control_expr_2485 reference_control_2_positions reference_control_2_safety reference_control_member_2485) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2485 reference_control_expr_2485 inputs path old current result Position Safe Nonreg (reference_control_ready_2485 old ) Step).
Qed.
Theorem reference_control_node_2485_congruent inputs path left right next_left next_right :
 VM.find 2248 left = VM.find 2248 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2485 next_left = VM.find 2485 next_right.
Proof.
 intros  E2248 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2485 reference_control_expr_2485 reference_control_2_positions reference_control_2_safety reference_control_member_2485) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2485 reference_control_expr_2485 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2485 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2485 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2248.
 reflexivity.
Qed.
Lemma reference_control_ready_2486 old :
 reference_control_ready old reference_control_expr_2486.
Proof.
 unfold reference_control_expr_2486.
apply rc_unary.
Qed.
Lemma reference_control_member_2486 : List.In (2486,reference_control_expr_2486) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 3%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2486_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2486 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2486 reference_control_expr_2486 reference_control_2_positions reference_control_2_safety reference_control_member_2486) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2486 reference_control_expr_2486 inputs path old current result Position Safe Nonreg (reference_control_ready_2486 old ) Step).
Qed.
Theorem reference_control_node_2486_congruent inputs path left right next_left next_right :
 VM.find 2485 left = VM.find 2485 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2486 next_left = VM.find 2486 next_right.
Proof.
 intros  E2485 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2486 reference_control_expr_2486 reference_control_2_positions reference_control_2_safety reference_control_member_2486) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2486 reference_control_expr_2486 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2486 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2486 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2485.
 reflexivity.
Qed.
Lemma reference_control_ready_2487 old :
 reference_control_ready old reference_control_expr_2487.
Proof.
 unfold reference_control_expr_2487.
apply rc_mux.
{ apply rc_const.
}
{ apply rc_const.
}
Qed.
Lemma reference_control_member_2487 : List.In (2487,reference_control_expr_2487) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 4%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2487_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2487 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2487 reference_control_expr_2487 reference_control_2_positions reference_control_2_safety reference_control_member_2487) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2487 reference_control_expr_2487 inputs path old current result Position Safe Nonreg (reference_control_ready_2487 old ) Step).
Qed.
Theorem reference_control_node_2487_congruent inputs path left right next_left next_right :
 VM.find 2486 left = VM.find 2486 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2487 next_left = VM.find 2487 next_right.
Proof.
 intros  E2486 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2487 reference_control_expr_2487 reference_control_2_positions reference_control_2_safety reference_control_member_2487) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2487 reference_control_expr_2487 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2487 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2487 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2486.
 reflexivity.
Qed.
Lemma reference_control_ready_2488 old :
 reference_control_ready old reference_control_expr_2488.
Proof.
 unfold reference_control_expr_2488.
apply rc_binary.
Qed.
Lemma reference_control_member_2488 : List.In (2488,reference_control_expr_2488) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 5%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2488_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2488 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2488 reference_control_expr_2488 reference_control_2_positions reference_control_2_safety reference_control_member_2488) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2488 reference_control_expr_2488 inputs path old current result Position Safe Nonreg (reference_control_ready_2488 old ) Step).
Qed.
Theorem reference_control_node_2488_congruent inputs path left right next_left next_right :
 VM.find 2248 left = VM.find 2248 right ->
 VM.find 2487 left = VM.find 2487 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2488 next_left = VM.find 2488 next_right.
Proof.
 intros  E2248 E2487 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2488 reference_control_expr_2488 reference_control_2_positions reference_control_2_safety reference_control_member_2488) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2488 reference_control_expr_2488 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2488 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2488 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2248.
 rewrite E2487.
 reflexivity.
Qed.
Lemma reference_control_ready_2489 old :
 reference_control_ready old reference_control_expr_2489.
Proof.
 unfold reference_control_expr_2489.
apply rc_unary.
Qed.
Lemma reference_control_member_2489 : List.In (2489,reference_control_expr_2489) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 6%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2489_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2489 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2489 reference_control_expr_2489 reference_control_2_positions reference_control_2_safety reference_control_member_2489) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2489 reference_control_expr_2489 inputs path old current result Position Safe Nonreg (reference_control_ready_2489 old ) Step).
Qed.
Theorem reference_control_node_2489_congruent inputs path left right next_left next_right :
 VM.find 2248 left = VM.find 2248 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2489 next_left = VM.find 2489 next_right.
Proof.
 intros  E2248 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2489 reference_control_expr_2489 reference_control_2_positions reference_control_2_safety reference_control_member_2489) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2489 reference_control_expr_2489 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2489 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2489 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2248.
 reflexivity.
Qed.
Lemma reference_control_ready_2490 old :
 reference_control_ready old reference_control_expr_2490.
Proof.
 unfold reference_control_expr_2490.
apply rc_unary.
Qed.
Lemma reference_control_member_2490 : List.In (2490,reference_control_expr_2490) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 7%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2490_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2490 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2490 reference_control_expr_2490 reference_control_2_positions reference_control_2_safety reference_control_member_2490) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2490 reference_control_expr_2490 inputs path old current result Position Safe Nonreg (reference_control_ready_2490 old ) Step).
Qed.
Theorem reference_control_node_2490_congruent inputs path left right next_left next_right :
 VM.find 2489 left = VM.find 2489 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2490 next_left = VM.find 2490 next_right.
Proof.
 intros  E2489 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2490 reference_control_expr_2490 reference_control_2_positions reference_control_2_safety reference_control_member_2490) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2490 reference_control_expr_2490 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2490 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2490 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2489.
 reflexivity.
Qed.
Lemma reference_control_ready_2491 old :
 reference_control_ready old reference_control_expr_2491.
Proof.
 unfold reference_control_expr_2491.
apply rc_mux.
{ apply rc_const.
}
{ apply rc_const.
}
Qed.
Lemma reference_control_member_2491 : List.In (2491,reference_control_expr_2491) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 8%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2491_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2491 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2491 reference_control_expr_2491 reference_control_2_positions reference_control_2_safety reference_control_member_2491) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2491 reference_control_expr_2491 inputs path old current result Position Safe Nonreg (reference_control_ready_2491 old ) Step).
Qed.
Theorem reference_control_node_2491_congruent inputs path left right next_left next_right :
 VM.find 2490 left = VM.find 2490 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2491 next_left = VM.find 2491 next_right.
Proof.
 intros  E2490 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2491 reference_control_expr_2491 reference_control_2_positions reference_control_2_safety reference_control_member_2491) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2491 reference_control_expr_2491 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2491 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2491 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2490.
 reflexivity.
Qed.
Lemma reference_control_ready_2492 old :
 reference_control_ready old reference_control_expr_2492.
Proof.
 unfold reference_control_expr_2492.
apply rc_binary.
Qed.
Lemma reference_control_member_2492 : List.In (2492,reference_control_expr_2492) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 9%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2492_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2492 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2492 reference_control_expr_2492 reference_control_2_positions reference_control_2_safety reference_control_member_2492) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2492 reference_control_expr_2492 inputs path old current result Position Safe Nonreg (reference_control_ready_2492 old ) Step).
Qed.
Theorem reference_control_node_2492_congruent inputs path left right next_left next_right :
 VM.find 2248 left = VM.find 2248 right ->
 VM.find 2491 left = VM.find 2491 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2492 next_left = VM.find 2492 next_right.
Proof.
 intros  E2248 E2491 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2492 reference_control_expr_2492 reference_control_2_positions reference_control_2_safety reference_control_member_2492) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2492 reference_control_expr_2492 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2492 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2492 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2248.
 rewrite E2491.
 reflexivity.
Qed.
Lemma reference_control_ready_2493 old :
 reference_control_ready old reference_control_expr_2493.
Proof.
 unfold reference_control_expr_2493.
apply rc_unary.
Qed.
Lemma reference_control_member_2493 : List.In (2493,reference_control_expr_2493) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 10%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2493_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2493 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2493 reference_control_expr_2493 reference_control_2_positions reference_control_2_safety reference_control_member_2493) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2493 reference_control_expr_2493 inputs path old current result Position Safe Nonreg (reference_control_ready_2493 old ) Step).
Qed.
Theorem reference_control_node_2493_congruent inputs path left right next_left next_right :
 VM.find 2248 left = VM.find 2248 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2493 next_left = VM.find 2493 next_right.
Proof.
 intros  E2248 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2493 reference_control_expr_2493 reference_control_2_positions reference_control_2_safety reference_control_member_2493) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2493 reference_control_expr_2493 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2493 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2493 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2248.
 reflexivity.
Qed.
Lemma reference_control_ready_2494 old :
 reference_control_ready old reference_control_expr_2494.
Proof.
 unfold reference_control_expr_2494.
apply rc_unary.
Qed.
Lemma reference_control_member_2494 : List.In (2494,reference_control_expr_2494) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 11%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2494_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2494 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2494 reference_control_expr_2494 reference_control_2_positions reference_control_2_safety reference_control_member_2494) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2494 reference_control_expr_2494 inputs path old current result Position Safe Nonreg (reference_control_ready_2494 old ) Step).
Qed.
Theorem reference_control_node_2494_congruent inputs path left right next_left next_right :
 VM.find 2493 left = VM.find 2493 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2494 next_left = VM.find 2494 next_right.
Proof.
 intros  E2493 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2494 reference_control_expr_2494 reference_control_2_positions reference_control_2_safety reference_control_member_2494) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2494 reference_control_expr_2494 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2494 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2494 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2493.
 reflexivity.
Qed.
Lemma reference_control_ready_2495 old :
 reference_control_ready old reference_control_expr_2495.
Proof.
 unfold reference_control_expr_2495.
apply rc_mux.
{ apply rc_const.
}
{ apply rc_const.
}
Qed.
Lemma reference_control_member_2495 : List.In (2495,reference_control_expr_2495) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 12%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2495_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2495 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2495 reference_control_expr_2495 reference_control_2_positions reference_control_2_safety reference_control_member_2495) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2495 reference_control_expr_2495 inputs path old current result Position Safe Nonreg (reference_control_ready_2495 old ) Step).
Qed.
Theorem reference_control_node_2495_congruent inputs path left right next_left next_right :
 VM.find 2494 left = VM.find 2494 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2495 next_left = VM.find 2495 next_right.
Proof.
 intros  E2494 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2495 reference_control_expr_2495 reference_control_2_positions reference_control_2_safety reference_control_member_2495) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2495 reference_control_expr_2495 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2495 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2495 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2494.
 reflexivity.
Qed.
Lemma reference_control_ready_2496 old :
 reference_control_ready old reference_control_expr_2496.
Proof.
 unfold reference_control_expr_2496.
apply rc_binary.
Qed.
Lemma reference_control_member_2496 : List.In (2496,reference_control_expr_2496) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 13%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2496_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2496 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2496 reference_control_expr_2496 reference_control_2_positions reference_control_2_safety reference_control_member_2496) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2496 reference_control_expr_2496 inputs path old current result Position Safe Nonreg (reference_control_ready_2496 old ) Step).
Qed.
Theorem reference_control_node_2496_congruent inputs path left right next_left next_right :
 VM.find 2248 left = VM.find 2248 right ->
 VM.find 2495 left = VM.find 2495 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2496 next_left = VM.find 2496 next_right.
Proof.
 intros  E2248 E2495 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2496 reference_control_expr_2496 reference_control_2_positions reference_control_2_safety reference_control_member_2496) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2496 reference_control_expr_2496 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2496 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2496 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2248.
 rewrite E2495.
 reflexivity.
Qed.
Lemma reference_control_ready_2497 old :
 reference_control_ready old reference_control_expr_2497.
Proof.
 unfold reference_control_expr_2497.
apply rc_unary.
Qed.
Lemma reference_control_member_2497 : List.In (2497,reference_control_expr_2497) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 14%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2497_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2497 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2497 reference_control_expr_2497 reference_control_2_positions reference_control_2_safety reference_control_member_2497) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2497 reference_control_expr_2497 inputs path old current result Position Safe Nonreg (reference_control_ready_2497 old ) Step).
Qed.
Theorem reference_control_node_2497_congruent inputs path left right next_left next_right :
 VM.find 2248 left = VM.find 2248 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2497 next_left = VM.find 2497 next_right.
Proof.
 intros  E2248 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2497 reference_control_expr_2497 reference_control_2_positions reference_control_2_safety reference_control_member_2497) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2497 reference_control_expr_2497 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2497 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2497 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2248.
 reflexivity.
Qed.
Lemma reference_control_ready_2498 old :
 reference_control_ready old reference_control_expr_2498.
Proof.
 unfold reference_control_expr_2498.
apply rc_unary.
Qed.
Lemma reference_control_member_2498 : List.In (2498,reference_control_expr_2498) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 15%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2498_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2498 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2498 reference_control_expr_2498 reference_control_2_positions reference_control_2_safety reference_control_member_2498) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2498 reference_control_expr_2498 inputs path old current result Position Safe Nonreg (reference_control_ready_2498 old ) Step).
Qed.
Theorem reference_control_node_2498_congruent inputs path left right next_left next_right :
 VM.find 2497 left = VM.find 2497 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2498 next_left = VM.find 2498 next_right.
Proof.
 intros  E2497 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2498 reference_control_expr_2498 reference_control_2_positions reference_control_2_safety reference_control_member_2498) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2498 reference_control_expr_2498 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2498 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2498 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2497.
 reflexivity.
Qed.
Lemma reference_control_ready_2499 old :
 reference_control_ready old reference_control_expr_2499.
Proof.
 unfold reference_control_expr_2499.
apply rc_mux.
{ apply rc_const.
}
{ apply rc_const.
}
Qed.
Lemma reference_control_member_2499 : List.In (2499,reference_control_expr_2499) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 16%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2499_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2499 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2499 reference_control_expr_2499 reference_control_2_positions reference_control_2_safety reference_control_member_2499) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2499 reference_control_expr_2499 inputs path old current result Position Safe Nonreg (reference_control_ready_2499 old ) Step).
Qed.
Theorem reference_control_node_2499_congruent inputs path left right next_left next_right :
 VM.find 2498 left = VM.find 2498 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2499 next_left = VM.find 2499 next_right.
Proof.
 intros  E2498 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2499 reference_control_expr_2499 reference_control_2_positions reference_control_2_safety reference_control_member_2499) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2499 reference_control_expr_2499 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2499 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2499 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2498.
 reflexivity.
Qed.
Lemma reference_control_ready_2500 old :
 reference_control_ready old reference_control_expr_2500.
Proof.
 unfold reference_control_expr_2500.
apply rc_binary.
Qed.
Lemma reference_control_member_2500 : List.In (2500,reference_control_expr_2500) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 17%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2500_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2500 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2500 reference_control_expr_2500 reference_control_2_positions reference_control_2_safety reference_control_member_2500) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2500 reference_control_expr_2500 inputs path old current result Position Safe Nonreg (reference_control_ready_2500 old ) Step).
Qed.
Theorem reference_control_node_2500_congruent inputs path left right next_left next_right :
 VM.find 2248 left = VM.find 2248 right ->
 VM.find 2499 left = VM.find 2499 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2500 next_left = VM.find 2500 next_right.
Proof.
 intros  E2248 E2499 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2500 reference_control_expr_2500 reference_control_2_positions reference_control_2_safety reference_control_member_2500) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2500 reference_control_expr_2500 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2500 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2500 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2248.
 rewrite E2499.
 reflexivity.
Qed.
Lemma reference_control_ready_2501 old :
 reference_control_ready old reference_control_expr_2501.
Proof.
 unfold reference_control_expr_2501.
apply rc_unary.
Qed.
Lemma reference_control_member_2501 : List.In (2501,reference_control_expr_2501) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 18%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2501_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2501 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2501 reference_control_expr_2501 reference_control_2_positions reference_control_2_safety reference_control_member_2501) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2501 reference_control_expr_2501 inputs path old current result Position Safe Nonreg (reference_control_ready_2501 old ) Step).
Qed.
Theorem reference_control_node_2501_congruent inputs path left right next_left next_right :
 VM.find 2248 left = VM.find 2248 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2501 next_left = VM.find 2501 next_right.
Proof.
 intros  E2248 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2501 reference_control_expr_2501 reference_control_2_positions reference_control_2_safety reference_control_member_2501) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2501 reference_control_expr_2501 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2501 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2501 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2248.
 reflexivity.
Qed.
Lemma reference_control_ready_2502 old :
 reference_control_ready old reference_control_expr_2502.
Proof.
 unfold reference_control_expr_2502.
apply rc_unary.
Qed.
Lemma reference_control_member_2502 : List.In (2502,reference_control_expr_2502) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 19%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2502_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2502 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2502 reference_control_expr_2502 reference_control_2_positions reference_control_2_safety reference_control_member_2502) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2502 reference_control_expr_2502 inputs path old current result Position Safe Nonreg (reference_control_ready_2502 old ) Step).
Qed.
Theorem reference_control_node_2502_congruent inputs path left right next_left next_right :
 VM.find 2501 left = VM.find 2501 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2502 next_left = VM.find 2502 next_right.
Proof.
 intros  E2501 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2502 reference_control_expr_2502 reference_control_2_positions reference_control_2_safety reference_control_member_2502) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2502 reference_control_expr_2502 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2502 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2502 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2501.
 reflexivity.
Qed.
Lemma reference_control_ready_2503 old :
 reference_control_ready old reference_control_expr_2503.
Proof.
 unfold reference_control_expr_2503.
apply rc_mux.
{ apply rc_const.
}
{ apply rc_const.
}
Qed.
Lemma reference_control_member_2503 : List.In (2503,reference_control_expr_2503) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 20%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2503_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2503 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2503 reference_control_expr_2503 reference_control_2_positions reference_control_2_safety reference_control_member_2503) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2503 reference_control_expr_2503 inputs path old current result Position Safe Nonreg (reference_control_ready_2503 old ) Step).
Qed.
Theorem reference_control_node_2503_congruent inputs path left right next_left next_right :
 VM.find 2502 left = VM.find 2502 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2503 next_left = VM.find 2503 next_right.
Proof.
 intros  E2502 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2503 reference_control_expr_2503 reference_control_2_positions reference_control_2_safety reference_control_member_2503) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2503 reference_control_expr_2503 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2503 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2503 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2502.
 reflexivity.
Qed.
Lemma reference_control_ready_2504 old :
 reference_control_ready old reference_control_expr_2504.
Proof.
 unfold reference_control_expr_2504.
apply rc_binary.
Qed.
Lemma reference_control_member_2504 : List.In (2504,reference_control_expr_2504) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 21%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2504_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2504 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2504 reference_control_expr_2504 reference_control_2_positions reference_control_2_safety reference_control_member_2504) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2504 reference_control_expr_2504 inputs path old current result Position Safe Nonreg (reference_control_ready_2504 old ) Step).
Qed.
Theorem reference_control_node_2504_congruent inputs path left right next_left next_right :
 VM.find 2248 left = VM.find 2248 right ->
 VM.find 2503 left = VM.find 2503 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2504 next_left = VM.find 2504 next_right.
Proof.
 intros  E2248 E2503 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2504 reference_control_expr_2504 reference_control_2_positions reference_control_2_safety reference_control_member_2504) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2504 reference_control_expr_2504 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2504 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2504 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2248.
 rewrite E2503.
 reflexivity.
Qed.
Lemma reference_control_ready_2505 old :
 reference_control_ready old reference_control_expr_2505.
Proof.
 unfold reference_control_expr_2505.
apply rc_unary.
Qed.
Lemma reference_control_member_2505 : List.In (2505,reference_control_expr_2505) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 22%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2505_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2505 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2505 reference_control_expr_2505 reference_control_2_positions reference_control_2_safety reference_control_member_2505) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2505 reference_control_expr_2505 inputs path old current result Position Safe Nonreg (reference_control_ready_2505 old ) Step).
Qed.
Theorem reference_control_node_2505_congruent inputs path left right next_left next_right :
 VM.find 2248 left = VM.find 2248 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2505 next_left = VM.find 2505 next_right.
Proof.
 intros  E2248 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2505 reference_control_expr_2505 reference_control_2_positions reference_control_2_safety reference_control_member_2505) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2505 reference_control_expr_2505 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2505 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2505 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2248.
 reflexivity.
Qed.
Lemma reference_control_ready_2506 old :
 reference_control_ready old reference_control_expr_2506.
Proof.
 unfold reference_control_expr_2506.
apply rc_unary.
Qed.
Lemma reference_control_member_2506 : List.In (2506,reference_control_expr_2506) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 23%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2506_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2506 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2506 reference_control_expr_2506 reference_control_2_positions reference_control_2_safety reference_control_member_2506) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2506 reference_control_expr_2506 inputs path old current result Position Safe Nonreg (reference_control_ready_2506 old ) Step).
Qed.
Theorem reference_control_node_2506_congruent inputs path left right next_left next_right :
 VM.find 2505 left = VM.find 2505 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2506 next_left = VM.find 2506 next_right.
Proof.
 intros  E2505 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2506 reference_control_expr_2506 reference_control_2_positions reference_control_2_safety reference_control_member_2506) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2506 reference_control_expr_2506 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2506 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2506 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2505.
 reflexivity.
Qed.
Lemma reference_control_ready_2507 old :
 reference_control_ready old reference_control_expr_2507.
Proof.
 unfold reference_control_expr_2507.
apply rc_mux.
{ apply rc_const.
}
{ apply rc_const.
}
Qed.
Lemma reference_control_member_2507 : List.In (2507,reference_control_expr_2507) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 24%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2507_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2507 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2507 reference_control_expr_2507 reference_control_2_positions reference_control_2_safety reference_control_member_2507) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2507 reference_control_expr_2507 inputs path old current result Position Safe Nonreg (reference_control_ready_2507 old ) Step).
Qed.
Theorem reference_control_node_2507_congruent inputs path left right next_left next_right :
 VM.find 2506 left = VM.find 2506 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2507 next_left = VM.find 2507 next_right.
Proof.
 intros  E2506 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2507 reference_control_expr_2507 reference_control_2_positions reference_control_2_safety reference_control_member_2507) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2507 reference_control_expr_2507 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2507 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2507 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2506.
 reflexivity.
Qed.
Lemma reference_control_ready_2508 old :
 reference_control_ready old reference_control_expr_2508.
Proof.
 unfold reference_control_expr_2508.
apply rc_binary.
Qed.
Lemma reference_control_member_2508 : List.In (2508,reference_control_expr_2508) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 25%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2508_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2508 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2508 reference_control_expr_2508 reference_control_2_positions reference_control_2_safety reference_control_member_2508) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2508 reference_control_expr_2508 inputs path old current result Position Safe Nonreg (reference_control_ready_2508 old ) Step).
Qed.
Theorem reference_control_node_2508_congruent inputs path left right next_left next_right :
 VM.find 2248 left = VM.find 2248 right ->
 VM.find 2507 left = VM.find 2507 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2508 next_left = VM.find 2508 next_right.
Proof.
 intros  E2248 E2507 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2508 reference_control_expr_2508 reference_control_2_positions reference_control_2_safety reference_control_member_2508) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2508 reference_control_expr_2508 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2508 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2508 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2248.
 rewrite E2507.
 reflexivity.
Qed.
Lemma reference_control_ready_2509 old :
 reference_control_ready old reference_control_expr_2509.
Proof.
 unfold reference_control_expr_2509.
apply rc_unary.
Qed.
Lemma reference_control_member_2509 : List.In (2509,reference_control_expr_2509) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 26%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2509_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2509 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2509 reference_control_expr_2509 reference_control_2_positions reference_control_2_safety reference_control_member_2509) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2509 reference_control_expr_2509 inputs path old current result Position Safe Nonreg (reference_control_ready_2509 old ) Step).
Qed.
Theorem reference_control_node_2509_congruent inputs path left right next_left next_right :
 VM.find 2248 left = VM.find 2248 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2509 next_left = VM.find 2509 next_right.
Proof.
 intros  E2248 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2509 reference_control_expr_2509 reference_control_2_positions reference_control_2_safety reference_control_member_2509) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2509 reference_control_expr_2509 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2509 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2509 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2248.
 reflexivity.
Qed.
Lemma reference_control_ready_2510 old :
 reference_control_ready old reference_control_expr_2510.
Proof.
 unfold reference_control_expr_2510.
apply rc_unary.
Qed.
Lemma reference_control_member_2510 : List.In (2510,reference_control_expr_2510) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 27%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2510_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2510 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2510 reference_control_expr_2510 reference_control_2_positions reference_control_2_safety reference_control_member_2510) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2510 reference_control_expr_2510 inputs path old current result Position Safe Nonreg (reference_control_ready_2510 old ) Step).
Qed.
Theorem reference_control_node_2510_congruent inputs path left right next_left next_right :
 VM.find 2509 left = VM.find 2509 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2510 next_left = VM.find 2510 next_right.
Proof.
 intros  E2509 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2510 reference_control_expr_2510 reference_control_2_positions reference_control_2_safety reference_control_member_2510) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2510 reference_control_expr_2510 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2510 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2510 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2509.
 reflexivity.
Qed.
Lemma reference_control_ready_2511 old :
 reference_control_ready old reference_control_expr_2511.
Proof.
 unfold reference_control_expr_2511.
apply rc_mux.
{ apply rc_const.
}
{ apply rc_const.
}
Qed.
Lemma reference_control_member_2511 : List.In (2511,reference_control_expr_2511) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 28%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2511_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2511 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2511 reference_control_expr_2511 reference_control_2_positions reference_control_2_safety reference_control_member_2511) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2511 reference_control_expr_2511 inputs path old current result Position Safe Nonreg (reference_control_ready_2511 old ) Step).
Qed.
Theorem reference_control_node_2511_congruent inputs path left right next_left next_right :
 VM.find 2510 left = VM.find 2510 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2511 next_left = VM.find 2511 next_right.
Proof.
 intros  E2510 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2511 reference_control_expr_2511 reference_control_2_positions reference_control_2_safety reference_control_member_2511) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2511 reference_control_expr_2511 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2511 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2511 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2510.
 reflexivity.
Qed.
Lemma reference_control_ready_2512 old :
 reference_control_ready old reference_control_expr_2512.
Proof.
 unfold reference_control_expr_2512.
apply rc_binary.
Qed.
Lemma reference_control_member_2512 : List.In (2512,reference_control_expr_2512) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 29%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2512_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2512 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2512 reference_control_expr_2512 reference_control_2_positions reference_control_2_safety reference_control_member_2512) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2512 reference_control_expr_2512 inputs path old current result Position Safe Nonreg (reference_control_ready_2512 old ) Step).
Qed.
Theorem reference_control_node_2512_congruent inputs path left right next_left next_right :
 VM.find 2248 left = VM.find 2248 right ->
 VM.find 2511 left = VM.find 2511 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2512 next_left = VM.find 2512 next_right.
Proof.
 intros  E2248 E2511 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2512 reference_control_expr_2512 reference_control_2_positions reference_control_2_safety reference_control_member_2512) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2512 reference_control_expr_2512 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2512 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2512 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2248.
 rewrite E2511.
 reflexivity.
Qed.
Lemma reference_control_ready_2513 old :
 reference_control_ready old reference_control_expr_2513.
Proof.
 unfold reference_control_expr_2513.
apply rc_unary.
Qed.
Lemma reference_control_member_2513 : List.In (2513,reference_control_expr_2513) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 30%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2513_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2513 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2513 reference_control_expr_2513 reference_control_2_positions reference_control_2_safety reference_control_member_2513) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2513 reference_control_expr_2513 inputs path old current result Position Safe Nonreg (reference_control_ready_2513 old ) Step).
Qed.
Theorem reference_control_node_2513_congruent inputs path left right next_left next_right :
 VM.find 2248 left = VM.find 2248 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2513 next_left = VM.find 2513 next_right.
Proof.
 intros  E2248 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2513 reference_control_expr_2513 reference_control_2_positions reference_control_2_safety reference_control_member_2513) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2513 reference_control_expr_2513 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2513 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2513 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2248.
 reflexivity.
Qed.
Lemma reference_control_ready_2514 old :
 reference_control_ready old reference_control_expr_2514.
Proof.
 unfold reference_control_expr_2514.
apply rc_unary.
Qed.
Lemma reference_control_member_2514 : List.In (2514,reference_control_expr_2514) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 31%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2514_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2514 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2514 reference_control_expr_2514 reference_control_2_positions reference_control_2_safety reference_control_member_2514) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2514 reference_control_expr_2514 inputs path old current result Position Safe Nonreg (reference_control_ready_2514 old ) Step).
Qed.
Theorem reference_control_node_2514_congruent inputs path left right next_left next_right :
 VM.find 2513 left = VM.find 2513 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2514 next_left = VM.find 2514 next_right.
Proof.
 intros  E2513 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2514 reference_control_expr_2514 reference_control_2_positions reference_control_2_safety reference_control_member_2514) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2514 reference_control_expr_2514 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2514 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2514 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2513.
 reflexivity.
Qed.
Lemma reference_control_ready_2515 old :
 reference_control_ready old reference_control_expr_2515.
Proof.
 unfold reference_control_expr_2515.
apply rc_mux.
{ apply rc_const.
}
{ apply rc_const.
}
Qed.
Lemma reference_control_member_2515 : List.In (2515,reference_control_expr_2515) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 32%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2515_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2515 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2515 reference_control_expr_2515 reference_control_2_positions reference_control_2_safety reference_control_member_2515) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2515 reference_control_expr_2515 inputs path old current result Position Safe Nonreg (reference_control_ready_2515 old ) Step).
Qed.
Theorem reference_control_node_2515_congruent inputs path left right next_left next_right :
 VM.find 2514 left = VM.find 2514 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2515 next_left = VM.find 2515 next_right.
Proof.
 intros  E2514 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2515 reference_control_expr_2515 reference_control_2_positions reference_control_2_safety reference_control_member_2515) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2515 reference_control_expr_2515 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2515 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2515 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2514.
 reflexivity.
Qed.
Lemma reference_control_ready_2516 old :
 reference_control_ready old reference_control_expr_2516.
Proof.
 unfold reference_control_expr_2516.
apply rc_binary.
Qed.
Lemma reference_control_member_2516 : List.In (2516,reference_control_expr_2516) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 33%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2516_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2516 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2516 reference_control_expr_2516 reference_control_2_positions reference_control_2_safety reference_control_member_2516) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2516 reference_control_expr_2516 inputs path old current result Position Safe Nonreg (reference_control_ready_2516 old ) Step).
Qed.
Theorem reference_control_node_2516_congruent inputs path left right next_left next_right :
 VM.find 2248 left = VM.find 2248 right ->
 VM.find 2515 left = VM.find 2515 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2516 next_left = VM.find 2516 next_right.
Proof.
 intros  E2248 E2515 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2516 reference_control_expr_2516 reference_control_2_positions reference_control_2_safety reference_control_member_2516) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2516 reference_control_expr_2516 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2516 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2516 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2248.
 rewrite E2515.
 reflexivity.
Qed.
Lemma reference_control_ready_2517 old :
 reference_control_ready old reference_control_expr_2517.
Proof.
 unfold reference_control_expr_2517.
apply rc_unary.
Qed.
Lemma reference_control_member_2517 : List.In (2517,reference_control_expr_2517) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 34%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2517_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2517 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2517 reference_control_expr_2517 reference_control_2_positions reference_control_2_safety reference_control_member_2517) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2517 reference_control_expr_2517 inputs path old current result Position Safe Nonreg (reference_control_ready_2517 old ) Step).
Qed.
Theorem reference_control_node_2517_congruent inputs path left right next_left next_right :
 VM.find 2248 left = VM.find 2248 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2517 next_left = VM.find 2517 next_right.
Proof.
 intros  E2248 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2517 reference_control_expr_2517 reference_control_2_positions reference_control_2_safety reference_control_member_2517) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2517 reference_control_expr_2517 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2517 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2517 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2248.
 reflexivity.
Qed.
Lemma reference_control_ready_2518 old :
 reference_control_ready old reference_control_expr_2518.
Proof.
 unfold reference_control_expr_2518.
apply rc_unary.
Qed.
Lemma reference_control_member_2518 : List.In (2518,reference_control_expr_2518) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 35%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2518_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2518 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2518 reference_control_expr_2518 reference_control_2_positions reference_control_2_safety reference_control_member_2518) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2518 reference_control_expr_2518 inputs path old current result Position Safe Nonreg (reference_control_ready_2518 old ) Step).
Qed.
Theorem reference_control_node_2518_congruent inputs path left right next_left next_right :
 VM.find 2517 left = VM.find 2517 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2518 next_left = VM.find 2518 next_right.
Proof.
 intros  E2517 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2518 reference_control_expr_2518 reference_control_2_positions reference_control_2_safety reference_control_member_2518) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2518 reference_control_expr_2518 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2518 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2518 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2517.
 reflexivity.
Qed.
Lemma reference_control_ready_2519 old :
 reference_control_ready old reference_control_expr_2519.
Proof.
 unfold reference_control_expr_2519.
apply rc_mux.
{ apply rc_const.
}
{ apply rc_const.
}
Qed.
Lemma reference_control_member_2519 : List.In (2519,reference_control_expr_2519) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 36%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2519_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2519 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2519 reference_control_expr_2519 reference_control_2_positions reference_control_2_safety reference_control_member_2519) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2519 reference_control_expr_2519 inputs path old current result Position Safe Nonreg (reference_control_ready_2519 old ) Step).
Qed.
Theorem reference_control_node_2519_congruent inputs path left right next_left next_right :
 VM.find 2518 left = VM.find 2518 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2519 next_left = VM.find 2519 next_right.
Proof.
 intros  E2518 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2519 reference_control_expr_2519 reference_control_2_positions reference_control_2_safety reference_control_member_2519) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2519 reference_control_expr_2519 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2519 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2519 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2518.
 reflexivity.
Qed.
Lemma reference_control_ready_2520 old :
 reference_control_ready old reference_control_expr_2520.
Proof.
 unfold reference_control_expr_2520.
apply rc_binary.
Qed.
Lemma reference_control_member_2520 : List.In (2520,reference_control_expr_2520) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 37%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2520_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2520 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2520 reference_control_expr_2520 reference_control_2_positions reference_control_2_safety reference_control_member_2520) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2520 reference_control_expr_2520 inputs path old current result Position Safe Nonreg (reference_control_ready_2520 old ) Step).
Qed.
Theorem reference_control_node_2520_congruent inputs path left right next_left next_right :
 VM.find 2248 left = VM.find 2248 right ->
 VM.find 2519 left = VM.find 2519 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2520 next_left = VM.find 2520 next_right.
Proof.
 intros  E2248 E2519 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2520 reference_control_expr_2520 reference_control_2_positions reference_control_2_safety reference_control_member_2520) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2520 reference_control_expr_2520 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2520 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2520 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2248.
 rewrite E2519.
 reflexivity.
Qed.
Lemma reference_control_ready_2521 old :
 (exists value ground, VM.find 2520 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2521.
Proof.
 intros H2520.
 destruct H2520 as [v2520 [G2520 [V2520 T2520]]].
 unfold reference_control_expr_2521.
apply rc_mux.
{ eapply rc_ref; [exact V2520|exists G2520; exact T2520].
}
{ apply rc_const.
}
Qed.
Lemma reference_control_member_2521 : List.In (2521,reference_control_expr_2521) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 38%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2521_ground inputs path old current result :
 (exists value ground, VM.find 2520 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2521 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2520 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2521 reference_control_expr_2521 reference_control_2_positions reference_control_2_safety reference_control_member_2521) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2521 reference_control_expr_2521 inputs path old current result Position Safe Nonreg (reference_control_ready_2521 old H2520) Step).
Qed.
Theorem reference_control_node_2521_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2520 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2096 left = VM.find 2096 right ->
 VM.find 2520 left = VM.find 2520 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2521 next_left = VM.find 2521 next_right.
Proof.
 intros H2520 E2096 E2520 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2521 reference_control_expr_2521 reference_control_2_positions reference_control_2_safety reference_control_member_2521) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2521 reference_control_expr_2521 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2521 left H2520)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2521 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2096.
 rewrite E2520.
 reflexivity.
Qed.
Lemma reference_control_ready_2522 old :
 (exists value ground, VM.find 2516 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2521 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2522.
Proof.
 intros H2516 H2521.
 destruct H2516 as [v2516 [G2516 [V2516 T2516]]].
 destruct H2521 as [v2521 [G2521 [V2521 T2521]]].
 unfold reference_control_expr_2522.
apply rc_mux.
{ eapply rc_ref; [exact V2516|exists G2516; exact T2516].
}
{ eapply rc_ref; [exact V2521|exists G2521; exact T2521].
}
Qed.
Lemma reference_control_member_2522 : List.In (2522,reference_control_expr_2522) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 39%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2522_ground inputs path old current result :
 (exists value ground, VM.find 2516 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2521 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2522 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2516 H2521 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2522 reference_control_expr_2522 reference_control_2_positions reference_control_2_safety reference_control_member_2522) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2522 reference_control_expr_2522 inputs path old current result Position Safe Nonreg (reference_control_ready_2522 old H2516 H2521) Step).
Qed.
Theorem reference_control_node_2522_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2516 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2521 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2092 left = VM.find 2092 right ->
 VM.find 2516 left = VM.find 2516 right ->
 VM.find 2521 left = VM.find 2521 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2522 next_left = VM.find 2522 next_right.
Proof.
 intros H2516 H2521 E2092 E2516 E2521 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2522 reference_control_expr_2522 reference_control_2_positions reference_control_2_safety reference_control_member_2522) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2522 reference_control_expr_2522 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2522 left H2516 H2521)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2522 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2092.
 rewrite E2516.
 rewrite E2521.
 reflexivity.
Qed.
Lemma reference_control_ready_2523 old :
 (exists value ground, VM.find 2512 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2522 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2523.
Proof.
 intros H2512 H2522.
 destruct H2512 as [v2512 [G2512 [V2512 T2512]]].
 destruct H2522 as [v2522 [G2522 [V2522 T2522]]].
 unfold reference_control_expr_2523.
apply rc_mux.
{ eapply rc_ref; [exact V2512|exists G2512; exact T2512].
}
{ eapply rc_ref; [exact V2522|exists G2522; exact T2522].
}
Qed.
Lemma reference_control_member_2523 : List.In (2523,reference_control_expr_2523) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 40%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2523_ground inputs path old current result :
 (exists value ground, VM.find 2512 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2522 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2523 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2512 H2522 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2523 reference_control_expr_2523 reference_control_2_positions reference_control_2_safety reference_control_member_2523) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2523 reference_control_expr_2523 inputs path old current result Position Safe Nonreg (reference_control_ready_2523 old H2512 H2522) Step).
Qed.
Theorem reference_control_node_2523_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2512 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2522 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2088 left = VM.find 2088 right ->
 VM.find 2512 left = VM.find 2512 right ->
 VM.find 2522 left = VM.find 2522 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2523 next_left = VM.find 2523 next_right.
Proof.
 intros H2512 H2522 E2088 E2512 E2522 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2523 reference_control_expr_2523 reference_control_2_positions reference_control_2_safety reference_control_member_2523) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2523 reference_control_expr_2523 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2523 left H2512 H2522)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2523 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2088.
 rewrite E2512.
 rewrite E2522.
 reflexivity.
Qed.
Lemma reference_control_ready_2524 old :
 (exists value ground, VM.find 2508 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2523 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2524.
Proof.
 intros H2508 H2523.
 destruct H2508 as [v2508 [G2508 [V2508 T2508]]].
 destruct H2523 as [v2523 [G2523 [V2523 T2523]]].
 unfold reference_control_expr_2524.
apply rc_mux.
{ eapply rc_ref; [exact V2508|exists G2508; exact T2508].
}
{ eapply rc_ref; [exact V2523|exists G2523; exact T2523].
}
Qed.
Lemma reference_control_member_2524 : List.In (2524,reference_control_expr_2524) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 41%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2524_ground inputs path old current result :
 (exists value ground, VM.find 2508 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2523 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2524 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2508 H2523 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2524 reference_control_expr_2524 reference_control_2_positions reference_control_2_safety reference_control_member_2524) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2524 reference_control_expr_2524 inputs path old current result Position Safe Nonreg (reference_control_ready_2524 old H2508 H2523) Step).
Qed.
Theorem reference_control_node_2524_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2508 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2523 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2084 left = VM.find 2084 right ->
 VM.find 2508 left = VM.find 2508 right ->
 VM.find 2523 left = VM.find 2523 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2524 next_left = VM.find 2524 next_right.
Proof.
 intros H2508 H2523 E2084 E2508 E2523 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2524 reference_control_expr_2524 reference_control_2_positions reference_control_2_safety reference_control_member_2524) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2524 reference_control_expr_2524 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2524 left H2508 H2523)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2524 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2084.
 rewrite E2508.
 rewrite E2523.
 reflexivity.
Qed.
Lemma reference_control_ready_2525 old :
 (exists value ground, VM.find 2504 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2524 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2525.
Proof.
 intros H2504 H2524.
 destruct H2504 as [v2504 [G2504 [V2504 T2504]]].
 destruct H2524 as [v2524 [G2524 [V2524 T2524]]].
 unfold reference_control_expr_2525.
apply rc_mux.
{ eapply rc_ref; [exact V2504|exists G2504; exact T2504].
}
{ eapply rc_ref; [exact V2524|exists G2524; exact T2524].
}
Qed.
Lemma reference_control_member_2525 : List.In (2525,reference_control_expr_2525) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 42%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2525_ground inputs path old current result :
 (exists value ground, VM.find 2504 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2524 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2525 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2504 H2524 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2525 reference_control_expr_2525 reference_control_2_positions reference_control_2_safety reference_control_member_2525) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2525 reference_control_expr_2525 inputs path old current result Position Safe Nonreg (reference_control_ready_2525 old H2504 H2524) Step).
Qed.
Theorem reference_control_node_2525_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2504 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2524 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2080 left = VM.find 2080 right ->
 VM.find 2504 left = VM.find 2504 right ->
 VM.find 2524 left = VM.find 2524 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2525 next_left = VM.find 2525 next_right.
Proof.
 intros H2504 H2524 E2080 E2504 E2524 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2525 reference_control_expr_2525 reference_control_2_positions reference_control_2_safety reference_control_member_2525) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2525 reference_control_expr_2525 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2525 left H2504 H2524)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2525 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2080.
 rewrite E2504.
 rewrite E2524.
 reflexivity.
Qed.
Lemma reference_control_ready_2526 old :
 (exists value ground, VM.find 2500 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2525 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2526.
Proof.
 intros H2500 H2525.
 destruct H2500 as [v2500 [G2500 [V2500 T2500]]].
 destruct H2525 as [v2525 [G2525 [V2525 T2525]]].
 unfold reference_control_expr_2526.
apply rc_mux.
{ eapply rc_ref; [exact V2500|exists G2500; exact T2500].
}
{ eapply rc_ref; [exact V2525|exists G2525; exact T2525].
}
Qed.
Lemma reference_control_member_2526 : List.In (2526,reference_control_expr_2526) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 43%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2526_ground inputs path old current result :
 (exists value ground, VM.find 2500 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2525 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2526 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2500 H2525 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2526 reference_control_expr_2526 reference_control_2_positions reference_control_2_safety reference_control_member_2526) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2526 reference_control_expr_2526 inputs path old current result Position Safe Nonreg (reference_control_ready_2526 old H2500 H2525) Step).
Qed.
Theorem reference_control_node_2526_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2500 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2525 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2076 left = VM.find 2076 right ->
 VM.find 2500 left = VM.find 2500 right ->
 VM.find 2525 left = VM.find 2525 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2526 next_left = VM.find 2526 next_right.
Proof.
 intros H2500 H2525 E2076 E2500 E2525 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2526 reference_control_expr_2526 reference_control_2_positions reference_control_2_safety reference_control_member_2526) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2526 reference_control_expr_2526 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2526 left H2500 H2525)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2526 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2076.
 rewrite E2500.
 rewrite E2525.
 reflexivity.
Qed.
Lemma reference_control_ready_2527 old :
 (exists value ground, VM.find 2496 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2526 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2527.
Proof.
 intros H2496 H2526.
 destruct H2496 as [v2496 [G2496 [V2496 T2496]]].
 destruct H2526 as [v2526 [G2526 [V2526 T2526]]].
 unfold reference_control_expr_2527.
apply rc_mux.
{ eapply rc_ref; [exact V2496|exists G2496; exact T2496].
}
{ eapply rc_ref; [exact V2526|exists G2526; exact T2526].
}
Qed.
Lemma reference_control_member_2527 : List.In (2527,reference_control_expr_2527) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 44%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2527_ground inputs path old current result :
 (exists value ground, VM.find 2496 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2526 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2527 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2496 H2526 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2527 reference_control_expr_2527 reference_control_2_positions reference_control_2_safety reference_control_member_2527) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2527 reference_control_expr_2527 inputs path old current result Position Safe Nonreg (reference_control_ready_2527 old H2496 H2526) Step).
Qed.
Theorem reference_control_node_2527_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2496 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2526 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2072 left = VM.find 2072 right ->
 VM.find 2496 left = VM.find 2496 right ->
 VM.find 2526 left = VM.find 2526 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2527 next_left = VM.find 2527 next_right.
Proof.
 intros H2496 H2526 E2072 E2496 E2526 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2527 reference_control_expr_2527 reference_control_2_positions reference_control_2_safety reference_control_member_2527) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2527 reference_control_expr_2527 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2527 left H2496 H2526)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2527 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2072.
 rewrite E2496.
 rewrite E2526.
 reflexivity.
Qed.
Lemma reference_control_ready_2528 old :
 (exists value ground, VM.find 2492 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2527 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2528.
Proof.
 intros H2492 H2527.
 destruct H2492 as [v2492 [G2492 [V2492 T2492]]].
 destruct H2527 as [v2527 [G2527 [V2527 T2527]]].
 unfold reference_control_expr_2528.
apply rc_mux.
{ eapply rc_ref; [exact V2492|exists G2492; exact T2492].
}
{ eapply rc_ref; [exact V2527|exists G2527; exact T2527].
}
Qed.
Lemma reference_control_member_2528 : List.In (2528,reference_control_expr_2528) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 45%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2528_ground inputs path old current result :
 (exists value ground, VM.find 2492 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2527 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2528 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2492 H2527 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2528 reference_control_expr_2528 reference_control_2_positions reference_control_2_safety reference_control_member_2528) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2528 reference_control_expr_2528 inputs path old current result Position Safe Nonreg (reference_control_ready_2528 old H2492 H2527) Step).
Qed.
Theorem reference_control_node_2528_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2492 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2527 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2068 left = VM.find 2068 right ->
 VM.find 2492 left = VM.find 2492 right ->
 VM.find 2527 left = VM.find 2527 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2528 next_left = VM.find 2528 next_right.
Proof.
 intros H2492 H2527 E2068 E2492 E2527 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2528 reference_control_expr_2528 reference_control_2_positions reference_control_2_safety reference_control_member_2528) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2528 reference_control_expr_2528 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2528 left H2492 H2527)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2528 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2068.
 rewrite E2492.
 rewrite E2527.
 reflexivity.
Qed.
Lemma reference_control_ready_2529 old :
 (exists value ground, VM.find 2488 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2528 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2529.
Proof.
 intros H2488 H2528.
 destruct H2488 as [v2488 [G2488 [V2488 T2488]]].
 destruct H2528 as [v2528 [G2528 [V2528 T2528]]].
 unfold reference_control_expr_2529.
apply rc_mux.
{ eapply rc_ref; [exact V2488|exists G2488; exact T2488].
}
{ eapply rc_ref; [exact V2528|exists G2528; exact T2528].
}
Qed.
Lemma reference_control_member_2529 : List.In (2529,reference_control_expr_2529) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 46%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2529_ground inputs path old current result :
 (exists value ground, VM.find 2488 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2528 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2529 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2488 H2528 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2529 reference_control_expr_2529 reference_control_2_positions reference_control_2_safety reference_control_member_2529) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2529 reference_control_expr_2529 inputs path old current result Position Safe Nonreg (reference_control_ready_2529 old H2488 H2528) Step).
Qed.
Theorem reference_control_node_2529_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2488 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2528 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2064 left = VM.find 2064 right ->
 VM.find 2488 left = VM.find 2488 right ->
 VM.find 2528 left = VM.find 2528 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2529 next_left = VM.find 2529 next_right.
Proof.
 intros H2488 H2528 E2064 E2488 E2528 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2529 reference_control_expr_2529 reference_control_2_positions reference_control_2_safety reference_control_member_2529) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2529 reference_control_expr_2529 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2529 left H2488 H2528)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2529 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2064.
 rewrite E2488.
 rewrite E2528.
 reflexivity.
Qed.
Lemma reference_control_ready_2530 old :
 (exists value ground, VM.find 2484 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2529 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2530.
Proof.
 intros H2484 H2529.
 destruct H2484 as [v2484 [G2484 [V2484 T2484]]].
 destruct H2529 as [v2529 [G2529 [V2529 T2529]]].
 unfold reference_control_expr_2530.
apply rc_mux.
{ eapply rc_ref; [exact V2484|exists G2484; exact T2484].
}
{ eapply rc_ref; [exact V2529|exists G2529; exact T2529].
}
Qed.
Lemma reference_control_member_2530 : List.In (2530,reference_control_expr_2530) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 47%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2530_ground inputs path old current result :
 (exists value ground, VM.find 2484 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2529 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2530 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2484 H2529 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2530 reference_control_expr_2530 reference_control_2_positions reference_control_2_safety reference_control_member_2530) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2530 reference_control_expr_2530 inputs path old current result Position Safe Nonreg (reference_control_ready_2530 old H2484 H2529) Step).
Qed.
Theorem reference_control_node_2530_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2484 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2529 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2475 left = VM.find 2475 right ->
 VM.find 2484 left = VM.find 2484 right ->
 VM.find 2529 left = VM.find 2529 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2530 next_left = VM.find 2530 next_right.
Proof.
 intros H2484 H2529 E2475 E2484 E2529 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2530 reference_control_expr_2530 reference_control_2_positions reference_control_2_safety reference_control_member_2530) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2530 reference_control_expr_2530 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2530 left H2484 H2529)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2530 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2475.
 rewrite E2484.
 rewrite E2529.
 reflexivity.
Qed.
Lemma reference_control_ready_2531 old :
 (exists value ground, VM.find 2482 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2530 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2531.
Proof.
 intros H2482 H2530.
 destruct H2482 as [v2482 [G2482 [V2482 T2482]]].
 destruct H2530 as [v2530 [G2530 [V2530 T2530]]].
 unfold reference_control_expr_2531.
apply rc_mux.
{ eapply rc_ref; [exact V2482|exists G2482; exact T2482].
}
{ eapply rc_ref; [exact V2530|exists G2530; exact T2530].
}
Qed.
Lemma reference_control_member_2531 : List.In (2531,reference_control_expr_2531) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 48%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2531_ground inputs path old current result :
 (exists value ground, VM.find 2482 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2530 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2531 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2482 H2530 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2531 reference_control_expr_2531 reference_control_2_positions reference_control_2_safety reference_control_member_2531) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2531 reference_control_expr_2531 inputs path old current result Position Safe Nonreg (reference_control_ready_2531 old H2482 H2530) Step).
Qed.
Theorem reference_control_node_2531_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2482 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2530 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2472 left = VM.find 2472 right ->
 VM.find 2482 left = VM.find 2482 right ->
 VM.find 2530 left = VM.find 2530 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2531 next_left = VM.find 2531 next_right.
Proof.
 intros H2482 H2530 E2472 E2482 E2530 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2531 reference_control_expr_2531 reference_control_2_positions reference_control_2_safety reference_control_member_2531) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2531 reference_control_expr_2531 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2531 left H2482 H2530)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2531 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2472.
 rewrite E2482.
 rewrite E2530.
 reflexivity.
Qed.
Lemma reference_control_ready_2532 old :
 (exists value ground, VM.find 2470 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2531 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2532.
Proof.
 intros H2470 H2531.
 destruct H2470 as [v2470 [G2470 [V2470 T2470]]].
 destruct H2531 as [v2531 [G2531 [V2531 T2531]]].
 unfold reference_control_expr_2532.
apply rc_mux.
{ eapply rc_ref; [exact V2470|exists G2470; exact T2470].
}
{ eapply rc_ref; [exact V2531|exists G2531; exact T2531].
}
Qed.
Lemma reference_control_member_2532 : List.In (2532,reference_control_expr_2532) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 49%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2532_ground inputs path old current result :
 (exists value ground, VM.find 2470 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2531 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2532 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2470 H2531 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2532 reference_control_expr_2532 reference_control_2_positions reference_control_2_safety reference_control_member_2532) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2532 reference_control_expr_2532 inputs path old current result Position Safe Nonreg (reference_control_ready_2532 old H2470 H2531) Step).
Qed.
Theorem reference_control_node_2532_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2470 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2531 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2357 left = VM.find 2357 right ->
 VM.find 2470 left = VM.find 2470 right ->
 VM.find 2531 left = VM.find 2531 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2532 next_left = VM.find 2532 next_right.
Proof.
 intros H2470 H2531 E2357 E2470 E2531 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2532 reference_control_expr_2532 reference_control_2_positions reference_control_2_safety reference_control_member_2532) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2532 reference_control_expr_2532 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2532 left H2470 H2531)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2532 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2357.
 rewrite E2470.
 rewrite E2531.
 reflexivity.
Qed.
Lemma reference_control_ready_2533 old :
 (exists value ground, VM.find 2449 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2532 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2533.
Proof.
 intros H2449 H2532.
 destruct H2449 as [v2449 [G2449 [V2449 T2449]]].
 destruct H2532 as [v2532 [G2532 [V2532 T2532]]].
 unfold reference_control_expr_2533.
apply rc_mux.
{ eapply rc_ref; [exact V2449|exists G2449; exact T2449].
}
{ eapply rc_ref; [exact V2532|exists G2532; exact T2532].
}
Qed.
Lemma reference_control_member_2533 : List.In (2533,reference_control_expr_2533) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 50%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2533_ground inputs path old current result :
 (exists value ground, VM.find 2449 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2532 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2533 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2449 H2532 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2533 reference_control_expr_2533 reference_control_2_positions reference_control_2_safety reference_control_member_2533) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2533 reference_control_expr_2533 inputs path old current result Position Safe Nonreg (reference_control_ready_2533 old H2449 H2532) Step).
Qed.
Theorem reference_control_node_2533_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2449 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2532 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2010 left = VM.find 2010 right ->
 VM.find 2449 left = VM.find 2449 right ->
 VM.find 2532 left = VM.find 2532 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2533 next_left = VM.find 2533 next_right.
Proof.
 intros H2449 H2532 E2010 E2449 E2532 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2533 reference_control_expr_2533 reference_control_2_positions reference_control_2_safety reference_control_member_2533) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2533 reference_control_expr_2533 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2533 left H2449 H2532)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2533 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2010.
 rewrite E2449.
 rewrite E2532.
 reflexivity.
Qed.
Lemma reference_control_ready_2534 old :
 (exists value ground, VM.find 2445 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2533 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2534.
Proof.
 intros H2445 H2533.
 destruct H2445 as [v2445 [G2445 [V2445 T2445]]].
 destruct H2533 as [v2533 [G2533 [V2533 T2533]]].
 unfold reference_control_expr_2534.
apply rc_mux.
{ eapply rc_ref; [exact V2445|exists G2445; exact T2445].
}
{ eapply rc_ref; [exact V2533|exists G2533; exact T2533].
}
Qed.
Lemma reference_control_member_2534 : List.In (2534,reference_control_expr_2534) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 51%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2534_ground inputs path old current result :
 (exists value ground, VM.find 2445 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2533 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2534 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2445 H2533 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2534 reference_control_expr_2534 reference_control_2_positions reference_control_2_safety reference_control_member_2534) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2534 reference_control_expr_2534 inputs path old current result Position Safe Nonreg (reference_control_ready_2534 old H2445 H2533) Step).
Qed.
Theorem reference_control_node_2534_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2445 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2533 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2004 left = VM.find 2004 right ->
 VM.find 2445 left = VM.find 2445 right ->
 VM.find 2533 left = VM.find 2533 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2534 next_left = VM.find 2534 next_right.
Proof.
 intros H2445 H2533 E2004 E2445 E2533 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2534 reference_control_expr_2534 reference_control_2_positions reference_control_2_safety reference_control_member_2534) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2534 reference_control_expr_2534 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2534 left H2445 H2533)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2534 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2004.
 rewrite E2445.
 rewrite E2533.
 reflexivity.
Qed.
Lemma reference_control_ready_2535 old :
 (exists value ground, VM.find 2437 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2534 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2535.
Proof.
 intros H2437 H2534.
 destruct H2437 as [v2437 [G2437 [V2437 T2437]]].
 destruct H2534 as [v2534 [G2534 [V2534 T2534]]].
 unfold reference_control_expr_2535.
apply rc_mux.
{ eapply rc_ref; [exact V2437|exists G2437; exact T2437].
}
{ eapply rc_ref; [exact V2534|exists G2534; exact T2534].
}
Qed.
Lemma reference_control_member_2535 : List.In (2535,reference_control_expr_2535) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 52%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2535_ground inputs path old current result :
 (exists value ground, VM.find 2437 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2534 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2535 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2437 H2534 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2535 reference_control_expr_2535 reference_control_2_positions reference_control_2_safety reference_control_member_2535) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2535 reference_control_expr_2535 inputs path old current result Position Safe Nonreg (reference_control_ready_2535 old H2437 H2534) Step).
Qed.
Theorem reference_control_node_2535_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2437 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2534 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1998 left = VM.find 1998 right ->
 VM.find 2437 left = VM.find 2437 right ->
 VM.find 2534 left = VM.find 2534 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2535 next_left = VM.find 2535 next_right.
Proof.
 intros H2437 H2534 E1998 E2437 E2534 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2535 reference_control_expr_2535 reference_control_2_positions reference_control_2_safety reference_control_member_2535) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2535 reference_control_expr_2535 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2535 left H2437 H2534)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2535 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1998.
 rewrite E2437.
 rewrite E2534.
 reflexivity.
Qed.
Lemma reference_control_ready_2536 old :
 (exists value ground, VM.find 2429 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2535 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2536.
Proof.
 intros H2429 H2535.
 destruct H2429 as [v2429 [G2429 [V2429 T2429]]].
 destruct H2535 as [v2535 [G2535 [V2535 T2535]]].
 unfold reference_control_expr_2536.
apply rc_mux.
{ eapply rc_ref; [exact V2429|exists G2429; exact T2429].
}
{ eapply rc_ref; [exact V2535|exists G2535; exact T2535].
}
Qed.
Lemma reference_control_member_2536 : List.In (2536,reference_control_expr_2536) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 53%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2536_ground inputs path old current result :
 (exists value ground, VM.find 2429 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2535 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2536 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2429 H2535 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2536 reference_control_expr_2536 reference_control_2_positions reference_control_2_safety reference_control_member_2536) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2536 reference_control_expr_2536 inputs path old current result Position Safe Nonreg (reference_control_ready_2536 old H2429 H2535) Step).
Qed.
Theorem reference_control_node_2536_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2429 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2535 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1992 left = VM.find 1992 right ->
 VM.find 2429 left = VM.find 2429 right ->
 VM.find 2535 left = VM.find 2535 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2536 next_left = VM.find 2536 next_right.
Proof.
 intros H2429 H2535 E1992 E2429 E2535 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2536 reference_control_expr_2536 reference_control_2_positions reference_control_2_safety reference_control_member_2536) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2536 reference_control_expr_2536 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2536 left H2429 H2535)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2536 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1992.
 rewrite E2429.
 rewrite E2535.
 reflexivity.
Qed.
Lemma reference_control_ready_2537 old :
 (exists value ground, VM.find 2421 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2536 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2537.
Proof.
 intros H2421 H2536.
 destruct H2421 as [v2421 [G2421 [V2421 T2421]]].
 destruct H2536 as [v2536 [G2536 [V2536 T2536]]].
 unfold reference_control_expr_2537.
apply rc_mux.
{ eapply rc_ref; [exact V2421|exists G2421; exact T2421].
}
{ eapply rc_ref; [exact V2536|exists G2536; exact T2536].
}
Qed.
Lemma reference_control_member_2537 : List.In (2537,reference_control_expr_2537) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 54%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2537_ground inputs path old current result :
 (exists value ground, VM.find 2421 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2536 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2537 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2421 H2536 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2537 reference_control_expr_2537 reference_control_2_positions reference_control_2_safety reference_control_member_2537) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2537 reference_control_expr_2537 inputs path old current result Position Safe Nonreg (reference_control_ready_2537 old H2421 H2536) Step).
Qed.
Theorem reference_control_node_2537_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2421 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2536 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1986 left = VM.find 1986 right ->
 VM.find 2421 left = VM.find 2421 right ->
 VM.find 2536 left = VM.find 2536 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2537 next_left = VM.find 2537 next_right.
Proof.
 intros H2421 H2536 E1986 E2421 E2536 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2537 reference_control_expr_2537 reference_control_2_positions reference_control_2_safety reference_control_member_2537) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2537 reference_control_expr_2537 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2537 left H2421 H2536)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2537 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1986.
 rewrite E2421.
 rewrite E2536.
 reflexivity.
Qed.
Lemma reference_control_ready_2538 old :
 (exists value ground, VM.find 2413 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2537 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2538.
Proof.
 intros H2413 H2537.
 destruct H2413 as [v2413 [G2413 [V2413 T2413]]].
 destruct H2537 as [v2537 [G2537 [V2537 T2537]]].
 unfold reference_control_expr_2538.
apply rc_mux.
{ eapply rc_ref; [exact V2413|exists G2413; exact T2413].
}
{ eapply rc_ref; [exact V2537|exists G2537; exact T2537].
}
Qed.
Lemma reference_control_member_2538 : List.In (2538,reference_control_expr_2538) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 55%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2538_ground inputs path old current result :
 (exists value ground, VM.find 2413 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2537 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2538 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2413 H2537 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2538 reference_control_expr_2538 reference_control_2_positions reference_control_2_safety reference_control_member_2538) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2538 reference_control_expr_2538 inputs path old current result Position Safe Nonreg (reference_control_ready_2538 old H2413 H2537) Step).
Qed.
Theorem reference_control_node_2538_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2413 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2537 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1980 left = VM.find 1980 right ->
 VM.find 2413 left = VM.find 2413 right ->
 VM.find 2537 left = VM.find 2537 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2538 next_left = VM.find 2538 next_right.
Proof.
 intros H2413 H2537 E1980 E2413 E2537 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2538 reference_control_expr_2538 reference_control_2_positions reference_control_2_safety reference_control_member_2538) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2538 reference_control_expr_2538 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2538 left H2413 H2537)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2538 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1980.
 rewrite E2413.
 rewrite E2537.
 reflexivity.
Qed.
Lemma reference_control_ready_2539 old :
 (exists value ground, VM.find 2405 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2538 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2539.
Proof.
 intros H2405 H2538.
 destruct H2405 as [v2405 [G2405 [V2405 T2405]]].
 destruct H2538 as [v2538 [G2538 [V2538 T2538]]].
 unfold reference_control_expr_2539.
apply rc_mux.
{ eapply rc_ref; [exact V2405|exists G2405; exact T2405].
}
{ eapply rc_ref; [exact V2538|exists G2538; exact T2538].
}
Qed.
Lemma reference_control_member_2539 : List.In (2539,reference_control_expr_2539) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 56%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2539_ground inputs path old current result :
 (exists value ground, VM.find 2405 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2538 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2539 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2405 H2538 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2539 reference_control_expr_2539 reference_control_2_positions reference_control_2_safety reference_control_member_2539) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2539 reference_control_expr_2539 inputs path old current result Position Safe Nonreg (reference_control_ready_2539 old H2405 H2538) Step).
Qed.
Theorem reference_control_node_2539_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2405 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2538 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1974 left = VM.find 1974 right ->
 VM.find 2405 left = VM.find 2405 right ->
 VM.find 2538 left = VM.find 2538 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2539 next_left = VM.find 2539 next_right.
Proof.
 intros H2405 H2538 E1974 E2405 E2538 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2539 reference_control_expr_2539 reference_control_2_positions reference_control_2_safety reference_control_member_2539) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2539 reference_control_expr_2539 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2539 left H2405 H2538)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2539 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1974.
 rewrite E2405.
 rewrite E2538.
 reflexivity.
Qed.
Lemma reference_control_ready_2540 old :
 (exists value ground, VM.find 2317 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2539 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2540.
Proof.
 intros H2317 H2539.
 destruct H2317 as [v2317 [G2317 [V2317 T2317]]].
 destruct H2539 as [v2539 [G2539 [V2539 T2539]]].
 unfold reference_control_expr_2540.
apply rc_mux.
{ eapply rc_ref; [exact V2317|exists G2317; exact T2317].
}
{ eapply rc_ref; [exact V2539|exists G2539; exact T2539].
}
Qed.
Lemma reference_control_member_2540 : List.In (2540,reference_control_expr_2540) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 57%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2540_ground inputs path old current result :
 (exists value ground, VM.find 2317 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2539 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2540 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2317 H2539 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2540 reference_control_expr_2540 reference_control_2_positions reference_control_2_safety reference_control_member_2540) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2540 reference_control_expr_2540 inputs path old current result Position Safe Nonreg (reference_control_ready_2540 old H2317 H2539) Step).
Qed.
Theorem reference_control_node_2540_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2317 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2539 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1970 left = VM.find 1970 right ->
 VM.find 2317 left = VM.find 2317 right ->
 VM.find 2539 left = VM.find 2539 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2540 next_left = VM.find 2540 next_right.
Proof.
 intros H2317 H2539 E1970 E2317 E2539 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2540 reference_control_expr_2540 reference_control_2_positions reference_control_2_safety reference_control_member_2540) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2540 reference_control_expr_2540 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2540 left H2317 H2539)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2540 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1970.
 rewrite E2317.
 rewrite E2539.
 reflexivity.
Qed.
Lemma reference_control_ready_2541 old :
 (exists value ground, VM.find 2313 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2540 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2541.
Proof.
 intros H2313 H2540.
 destruct H2313 as [v2313 [G2313 [V2313 T2313]]].
 destruct H2540 as [v2540 [G2540 [V2540 T2540]]].
 unfold reference_control_expr_2541.
apply rc_mux.
{ eapply rc_ref; [exact V2313|exists G2313; exact T2313].
}
{ eapply rc_ref; [exact V2540|exists G2540; exact T2540].
}
Qed.
Lemma reference_control_member_2541 : List.In (2541,reference_control_expr_2541) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 58%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2541_ground inputs path old current result :
 (exists value ground, VM.find 2313 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2540 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2541 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2313 H2540 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2541 reference_control_expr_2541 reference_control_2_positions reference_control_2_safety reference_control_member_2541) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2541 reference_control_expr_2541 inputs path old current result Position Safe Nonreg (reference_control_ready_2541 old H2313 H2540) Step).
Qed.
Theorem reference_control_node_2541_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2313 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2540 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1966 left = VM.find 1966 right ->
 VM.find 2313 left = VM.find 2313 right ->
 VM.find 2540 left = VM.find 2540 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2541 next_left = VM.find 2541 next_right.
Proof.
 intros H2313 H2540 E1966 E2313 E2540 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2541 reference_control_expr_2541 reference_control_2_positions reference_control_2_safety reference_control_member_2541) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2541 reference_control_expr_2541 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2541 left H2313 H2540)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2541 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1966.
 rewrite E2313.
 rewrite E2540.
 reflexivity.
Qed.
Lemma reference_control_ready_2542 old :
 (exists value ground, VM.find 2309 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2541 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2542.
Proof.
 intros H2309 H2541.
 destruct H2309 as [v2309 [G2309 [V2309 T2309]]].
 destruct H2541 as [v2541 [G2541 [V2541 T2541]]].
 unfold reference_control_expr_2542.
apply rc_mux.
{ eapply rc_ref; [exact V2309|exists G2309; exact T2309].
}
{ eapply rc_ref; [exact V2541|exists G2541; exact T2541].
}
Qed.
Lemma reference_control_member_2542 : List.In (2542,reference_control_expr_2542) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 59%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2542_ground inputs path old current result :
 (exists value ground, VM.find 2309 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2541 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2542 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2309 H2541 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2542 reference_control_expr_2542 reference_control_2_positions reference_control_2_safety reference_control_member_2542) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2542 reference_control_expr_2542 inputs path old current result Position Safe Nonreg (reference_control_ready_2542 old H2309 H2541) Step).
Qed.
Theorem reference_control_node_2542_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2309 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2541 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1962 left = VM.find 1962 right ->
 VM.find 2309 left = VM.find 2309 right ->
 VM.find 2541 left = VM.find 2541 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2542 next_left = VM.find 2542 next_right.
Proof.
 intros H2309 H2541 E1962 E2309 E2541 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2542 reference_control_expr_2542 reference_control_2_positions reference_control_2_safety reference_control_member_2542) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2542 reference_control_expr_2542 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2542 left H2309 H2541)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2542 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1962.
 rewrite E2309.
 rewrite E2541.
 reflexivity.
Qed.
Lemma reference_control_ready_2543 old :
 (exists value ground, VM.find 2305 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2542 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2543.
Proof.
 intros H2305 H2542.
 destruct H2305 as [v2305 [G2305 [V2305 T2305]]].
 destruct H2542 as [v2542 [G2542 [V2542 T2542]]].
 unfold reference_control_expr_2543.
apply rc_mux.
{ eapply rc_ref; [exact V2305|exists G2305; exact T2305].
}
{ eapply rc_ref; [exact V2542|exists G2542; exact T2542].
}
Qed.
Lemma reference_control_member_2543 : List.In (2543,reference_control_expr_2543) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 60%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2543_ground inputs path old current result :
 (exists value ground, VM.find 2305 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2542 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2543 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2305 H2542 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2543 reference_control_expr_2543 reference_control_2_positions reference_control_2_safety reference_control_member_2543) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2543 reference_control_expr_2543 inputs path old current result Position Safe Nonreg (reference_control_ready_2543 old H2305 H2542) Step).
Qed.
Theorem reference_control_node_2543_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2305 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2542 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1958 left = VM.find 1958 right ->
 VM.find 2305 left = VM.find 2305 right ->
 VM.find 2542 left = VM.find 2542 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2543 next_left = VM.find 2543 next_right.
Proof.
 intros H2305 H2542 E1958 E2305 E2542 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2543 reference_control_expr_2543 reference_control_2_positions reference_control_2_safety reference_control_member_2543) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2543 reference_control_expr_2543 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2543 left H2305 H2542)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2543 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1958.
 rewrite E2305.
 rewrite E2542.
 reflexivity.
Qed.
Lemma reference_control_ready_2544 old :
 (exists value ground, VM.find 2301 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2543 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2544.
Proof.
 intros H2301 H2543.
 destruct H2301 as [v2301 [G2301 [V2301 T2301]]].
 destruct H2543 as [v2543 [G2543 [V2543 T2543]]].
 unfold reference_control_expr_2544.
apply rc_mux.
{ eapply rc_ref; [exact V2301|exists G2301; exact T2301].
}
{ eapply rc_ref; [exact V2543|exists G2543; exact T2543].
}
Qed.
Lemma reference_control_member_2544 : List.In (2544,reference_control_expr_2544) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 61%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2544_ground inputs path old current result :
 (exists value ground, VM.find 2301 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2543 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2544 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2301 H2543 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2544 reference_control_expr_2544 reference_control_2_positions reference_control_2_safety reference_control_member_2544) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2544 reference_control_expr_2544 inputs path old current result Position Safe Nonreg (reference_control_ready_2544 old H2301 H2543) Step).
Qed.
Theorem reference_control_node_2544_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2301 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2543 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1886 left = VM.find 1886 right ->
 VM.find 2301 left = VM.find 2301 right ->
 VM.find 2543 left = VM.find 2543 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2544 next_left = VM.find 2544 next_right.
Proof.
 intros H2301 H2543 E1886 E2301 E2543 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2544 reference_control_expr_2544 reference_control_2_positions reference_control_2_safety reference_control_member_2544) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2544 reference_control_expr_2544 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2544 left H2301 H2543)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2544 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1886.
 rewrite E2301.
 rewrite E2543.
 reflexivity.
Qed.
Lemma reference_control_ready_2545 old :
 (exists value ground, VM.find 2297 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2544 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2545.
Proof.
 intros H2297 H2544.
 destruct H2297 as [v2297 [G2297 [V2297 T2297]]].
 destruct H2544 as [v2544 [G2544 [V2544 T2544]]].
 unfold reference_control_expr_2545.
apply rc_mux.
{ eapply rc_ref; [exact V2297|exists G2297; exact T2297].
}
{ eapply rc_ref; [exact V2544|exists G2544; exact T2544].
}
Qed.
Lemma reference_control_member_2545 : List.In (2545,reference_control_expr_2545) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 62%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2545_ground inputs path old current result :
 (exists value ground, VM.find 2297 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2544 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2545 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2297 H2544 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2545 reference_control_expr_2545 reference_control_2_positions reference_control_2_safety reference_control_member_2545) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2545 reference_control_expr_2545 inputs path old current result Position Safe Nonreg (reference_control_ready_2545 old H2297 H2544) Step).
Qed.
Theorem reference_control_node_2545_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2297 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2544 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1951 left = VM.find 1951 right ->
 VM.find 2297 left = VM.find 2297 right ->
 VM.find 2544 left = VM.find 2544 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2545 next_left = VM.find 2545 next_right.
Proof.
 intros H2297 H2544 E1951 E2297 E2544 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2545 reference_control_expr_2545 reference_control_2_positions reference_control_2_safety reference_control_member_2545) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2545 reference_control_expr_2545 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2545 left H2297 H2544)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2545 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1951.
 rewrite E2297.
 rewrite E2544.
 reflexivity.
Qed.
Lemma reference_control_ready_2546 old :
 (exists value ground, VM.find 2292 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2545 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2546.
Proof.
 intros H2292 H2545.
 destruct H2292 as [v2292 [G2292 [V2292 T2292]]].
 destruct H2545 as [v2545 [G2545 [V2545 T2545]]].
 unfold reference_control_expr_2546.
apply rc_mux.
{ eapply rc_ref; [exact V2292|exists G2292; exact T2292].
}
{ eapply rc_ref; [exact V2545|exists G2545; exact T2545].
}
Qed.
Lemma reference_control_member_2546 : List.In (2546,reference_control_expr_2546) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 63%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2546_ground inputs path old current result :
 (exists value ground, VM.find 2292 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2545 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2546 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2292 H2545 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2546 reference_control_expr_2546 reference_control_2_positions reference_control_2_safety reference_control_member_2546) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2546 reference_control_expr_2546 inputs path old current result Position Safe Nonreg (reference_control_ready_2546 old H2292 H2545) Step).
Qed.
Theorem reference_control_node_2546_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2292 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2545 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1946 left = VM.find 1946 right ->
 VM.find 2292 left = VM.find 2292 right ->
 VM.find 2545 left = VM.find 2545 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2546 next_left = VM.find 2546 next_right.
Proof.
 intros H2292 H2545 E1946 E2292 E2545 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2546 reference_control_expr_2546 reference_control_2_positions reference_control_2_safety reference_control_member_2546) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2546 reference_control_expr_2546 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2546 left H2292 H2545)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2546 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1946.
 rewrite E2292.
 rewrite E2545.
 reflexivity.
Qed.
Lemma reference_control_ready_2547 old :
 (exists value ground, VM.find 2287 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2546 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2547.
Proof.
 intros H2287 H2546.
 destruct H2287 as [v2287 [G2287 [V2287 T2287]]].
 destruct H2546 as [v2546 [G2546 [V2546 T2546]]].
 unfold reference_control_expr_2547.
apply rc_mux.
{ eapply rc_ref; [exact V2287|exists G2287; exact T2287].
}
{ eapply rc_ref; [exact V2546|exists G2546; exact T2546].
}
Qed.
Lemma reference_control_member_2547 : List.In (2547,reference_control_expr_2547) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 64%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2547_ground inputs path old current result :
 (exists value ground, VM.find 2287 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2546 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2547 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2287 H2546 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2547 reference_control_expr_2547 reference_control_2_positions reference_control_2_safety reference_control_member_2547) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2547 reference_control_expr_2547 inputs path old current result Position Safe Nonreg (reference_control_ready_2547 old H2287 H2546) Step).
Qed.
Theorem reference_control_node_2547_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2287 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2546 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1941 left = VM.find 1941 right ->
 VM.find 2287 left = VM.find 2287 right ->
 VM.find 2546 left = VM.find 2546 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2547 next_left = VM.find 2547 next_right.
Proof.
 intros H2287 H2546 E1941 E2287 E2546 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2547 reference_control_expr_2547 reference_control_2_positions reference_control_2_safety reference_control_member_2547) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2547 reference_control_expr_2547 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2547 left H2287 H2546)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2547 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1941.
 rewrite E2287.
 rewrite E2546.
 reflexivity.
Qed.
Lemma reference_control_ready_2548 old :
 (exists value ground, VM.find 2260 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2547 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2548.
Proof.
 intros H2260 H2547.
 destruct H2260 as [v2260 [G2260 [V2260 T2260]]].
 destruct H2547 as [v2547 [G2547 [V2547 T2547]]].
 unfold reference_control_expr_2548.
apply rc_mux.
{ eapply rc_ref; [exact V2260|exists G2260; exact T2260].
}
{ eapply rc_ref; [exact V2547|exists G2547; exact T2547].
}
Qed.
Lemma reference_control_member_2548 : List.In (2548,reference_control_expr_2548) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 65%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2548_ground inputs path old current result :
 (exists value ground, VM.find 2260 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2547 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2548 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2260 H2547 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2548 reference_control_expr_2548 reference_control_2_positions reference_control_2_safety reference_control_member_2548) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2548 reference_control_expr_2548 inputs path old current result Position Safe Nonreg (reference_control_ready_2548 old H2260 H2547) Step).
Qed.
Theorem reference_control_node_2548_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2260 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2547 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1937 left = VM.find 1937 right ->
 VM.find 2260 left = VM.find 2260 right ->
 VM.find 2547 left = VM.find 2547 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2548 next_left = VM.find 2548 next_right.
Proof.
 intros H2260 H2547 E1937 E2260 E2547 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2548 reference_control_expr_2548 reference_control_2_positions reference_control_2_safety reference_control_member_2548) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2548 reference_control_expr_2548 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2548 left H2260 H2547)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2548 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1937.
 rewrite E2260.
 rewrite E2547.
 reflexivity.
Qed.
Lemma reference_control_ready_2549 old :
 (exists value ground, VM.find 2256 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2548 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2549.
Proof.
 intros H2256 H2548.
 destruct H2256 as [v2256 [G2256 [V2256 T2256]]].
 destruct H2548 as [v2548 [G2548 [V2548 T2548]]].
 unfold reference_control_expr_2549.
apply rc_mux.
{ eapply rc_ref; [exact V2256|exists G2256; exact T2256].
}
{ eapply rc_ref; [exact V2548|exists G2548; exact T2548].
}
Qed.
Lemma reference_control_member_2549 : List.In (2549,reference_control_expr_2549) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 66%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2549_ground inputs path old current result :
 (exists value ground, VM.find 2256 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2548 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2549 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2256 H2548 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2549 reference_control_expr_2549 reference_control_2_positions reference_control_2_safety reference_control_member_2549) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2549 reference_control_expr_2549 inputs path old current result Position Safe Nonreg (reference_control_ready_2549 old H2256 H2548) Step).
Qed.
Theorem reference_control_node_2549_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2256 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2548 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1933 left = VM.find 1933 right ->
 VM.find 2256 left = VM.find 2256 right ->
 VM.find 2548 left = VM.find 2548 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2549 next_left = VM.find 2549 next_right.
Proof.
 intros H2256 H2548 E1933 E2256 E2548 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2549 reference_control_expr_2549 reference_control_2_positions reference_control_2_safety reference_control_member_2549) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2549 reference_control_expr_2549 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2549 left H2256 H2548)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2549 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1933.
 rewrite E2256.
 rewrite E2548.
 reflexivity.
Qed.
Lemma reference_control_ready_2550 old :
 (exists value ground, VM.find 2252 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2549 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2550.
Proof.
 intros H2252 H2549.
 destruct H2252 as [v2252 [G2252 [V2252 T2252]]].
 destruct H2549 as [v2549 [G2549 [V2549 T2549]]].
 unfold reference_control_expr_2550.
apply rc_mux.
{ eapply rc_ref; [exact V2252|exists G2252; exact T2252].
}
{ eapply rc_ref; [exact V2549|exists G2549; exact T2549].
}
Qed.
Lemma reference_control_member_2550 : List.In (2550,reference_control_expr_2550) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 67%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2550_ground inputs path old current result :
 (exists value ground, VM.find 2252 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2549 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2550 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2252 H2549 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2550 reference_control_expr_2550 reference_control_2_positions reference_control_2_safety reference_control_member_2550) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2550 reference_control_expr_2550 inputs path old current result Position Safe Nonreg (reference_control_ready_2550 old H2252 H2549) Step).
Qed.
Theorem reference_control_node_2550_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2252 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2549 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1929 left = VM.find 1929 right ->
 VM.find 2252 left = VM.find 2252 right ->
 VM.find 2549 left = VM.find 2549 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2550 next_left = VM.find 2550 next_right.
Proof.
 intros H2252 H2549 E1929 E2252 E2549 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2550 reference_control_expr_2550 reference_control_2_positions reference_control_2_safety reference_control_member_2550) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2550 reference_control_expr_2550 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2550 left H2252 H2549)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2550 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1929.
 rewrite E2252.
 rewrite E2549.
 reflexivity.
Qed.
Lemma reference_control_ready_2551 old :
 (exists value ground, VM.find 2550 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2551.
Proof.
 intros H2550.
 destruct H2550 as [v2550 [G2550 [V2550 T2550]]].
 unfold reference_control_expr_2551.
apply rc_mux.
{ eapply rc_ref; [exact V2550|exists G2550; exact T2550].
}
{ apply rc_const.
}
Qed.
Lemma reference_control_member_2551 : List.In (2551,reference_control_expr_2551) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 68%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2551_ground inputs path old current result :
 (exists value ground, VM.find 2550 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2551 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2550 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2551 reference_control_expr_2551 reference_control_2_positions reference_control_2_safety reference_control_member_2551) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2551 reference_control_expr_2551 inputs path old current result Position Safe Nonreg (reference_control_ready_2551 old H2550) Step).
Qed.
Theorem reference_control_node_2551_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2550 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1707 left = VM.find 1707 right ->
 VM.find 2550 left = VM.find 2550 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2551 next_left = VM.find 2551 next_right.
Proof.
 intros H2550 E1707 E2550 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2551 reference_control_expr_2551 reference_control_2_positions reference_control_2_safety reference_control_member_2551) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2551 reference_control_expr_2551 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2551 left H2550)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2551 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1707.
 rewrite E2550.
 reflexivity.
Qed.
Lemma reference_control_ready_2552 old :
 (exists value ground, VM.find 2551 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2552.
Proof.
 intros H2551.
 destruct H2551 as [v2551 [G2551 [V2551 T2551]]].
 unfold reference_control_expr_2552.
eapply rc_ref; [exact V2551|exists G2551; exact T2551].
Qed.
Lemma reference_control_member_2552 : List.In (2552,reference_control_expr_2552) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 69%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2552_ground inputs path old current result :
 (exists value ground, VM.find 2551 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2552 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2551 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2552 reference_control_expr_2552 reference_control_2_positions reference_control_2_safety reference_control_member_2552) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2552 reference_control_expr_2552 inputs path old current result Position Safe Nonreg (reference_control_ready_2552 old H2551) Step).
Qed.
Theorem reference_control_node_2552_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2551 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2551 left = VM.find 2551 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2552 next_left = VM.find 2552 next_right.
Proof.
 intros H2551 E2551 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2552 reference_control_expr_2552 reference_control_2_positions reference_control_2_safety reference_control_member_2552) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2552 reference_control_expr_2552 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2552 left H2551)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2552 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2551.
 reflexivity.
Qed.
Lemma reference_control_ready_2553 old :
 reference_control_ready old reference_control_expr_2553.
Proof.
 unfold reference_control_expr_2553.
apply rc_binary.
Qed.
Lemma reference_control_member_2553 : List.In (2553,reference_control_expr_2553) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 70%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2553_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2553 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2553 reference_control_expr_2553 reference_control_2_positions reference_control_2_safety reference_control_member_2553) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2553 reference_control_expr_2553 inputs path old current result Position Safe Nonreg (reference_control_ready_2553 old ) Step).
Qed.
Theorem reference_control_node_2553_congruent inputs path left right next_left next_right :
 VM.find 2210 left = VM.find 2210 right ->
 VM.find 2552 left = VM.find 2552 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2553 next_left = VM.find 2553 next_right.
Proof.
 intros  E2210 E2552 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2553 reference_control_expr_2553 reference_control_2_positions reference_control_2_safety reference_control_member_2553) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2553 reference_control_expr_2553 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2553 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2553 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2210.
 rewrite E2552.
 reflexivity.
Qed.
Lemma reference_control_ready_2554 old :
 reference_control_ready old reference_control_expr_2554.
Proof.
 unfold reference_control_expr_2554.
apply rc_unary.
Qed.
Lemma reference_control_member_2554 : List.In (2554,reference_control_expr_2554) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 71%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2554_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2554 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2554 reference_control_expr_2554 reference_control_2_positions reference_control_2_safety reference_control_member_2554) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2554 reference_control_expr_2554 inputs path old current result Position Safe Nonreg (reference_control_ready_2554 old ) Step).
Qed.
Theorem reference_control_node_2554_congruent inputs path left right next_left next_right :
 VM.find 2553 left = VM.find 2553 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2554 next_left = VM.find 2554 next_right.
Proof.
 intros  E2553 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2554 reference_control_expr_2554 reference_control_2_positions reference_control_2_safety reference_control_member_2554) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2554 reference_control_expr_2554 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2554 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2554 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2553.
 reflexivity.
Qed.
Lemma reference_control_ready_2555 old :
 reference_control_ready old reference_control_expr_2555.
Proof.
 unfold reference_control_expr_2555.
apply rc_unary.
Qed.
Lemma reference_control_member_2555 : List.In (2555,reference_control_expr_2555) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 72%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2555_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2555 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2555 reference_control_expr_2555 reference_control_2_positions reference_control_2_safety reference_control_member_2555) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2555 reference_control_expr_2555 inputs path old current result Position Safe Nonreg (reference_control_ready_2555 old ) Step).
Qed.
Theorem reference_control_node_2555_congruent inputs path left right next_left next_right :
 VM.find 2554 left = VM.find 2554 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2555 next_left = VM.find 2555 next_right.
Proof.
 intros  E2554 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2555 reference_control_expr_2555 reference_control_2_positions reference_control_2_safety reference_control_member_2555) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2555 reference_control_expr_2555 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2555 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2555 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2554.
 reflexivity.
Qed.
Lemma reference_control_ready_2556 old :
 reference_control_ready old reference_control_expr_2556.
Proof.
 unfold reference_control_expr_2556.
apply rc_binary.
Qed.
Lemma reference_control_member_2556 : List.In (2556,reference_control_expr_2556) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 73%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2556_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2556 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2556 reference_control_expr_2556 reference_control_2_positions reference_control_2_safety reference_control_member_2556) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2556 reference_control_expr_2556 inputs path old current result Position Safe Nonreg (reference_control_ready_2556 old ) Step).
Qed.
Theorem reference_control_node_2556_congruent inputs path left right next_left next_right :
 VM.find 2555 left = VM.find 2555 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2556 next_left = VM.find 2556 next_right.
Proof.
 intros  E2555 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2556 reference_control_expr_2556 reference_control_2_positions reference_control_2_safety reference_control_member_2556) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2556 reference_control_expr_2556 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2556 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2556 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2555.
 reflexivity.
Qed.
Lemma reference_control_ready_2557 old :
 reference_control_ready old reference_control_expr_2557.
Proof.
 unfold reference_control_expr_2557.
apply rc_binary.
Qed.
Lemma reference_control_member_2557 : List.In (2557,reference_control_expr_2557) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 74%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2557_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2557 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2557 reference_control_expr_2557 reference_control_2_positions reference_control_2_safety reference_control_member_2557) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2557 reference_control_expr_2557 inputs path old current result Position Safe Nonreg (reference_control_ready_2557 old ) Step).
Qed.
Theorem reference_control_node_2557_congruent inputs path left right next_left next_right :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2557 next_left = VM.find 2557 next_right.
Proof.
 intros   L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2557 reference_control_expr_2557 reference_control_2_positions reference_control_2_safety reference_control_member_2557) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2557 reference_control_expr_2557 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2557 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2557 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 reflexivity.
Qed.
Lemma reference_control_ready_2558 old :
 reference_control_ready old reference_control_expr_2558.
Proof.
 unfold reference_control_expr_2558.
apply rc_unary.
Qed.
Lemma reference_control_member_2558 : List.In (2558,reference_control_expr_2558) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 75%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2558_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2558 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2558 reference_control_expr_2558 reference_control_2_positions reference_control_2_safety reference_control_member_2558) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2558 reference_control_expr_2558 inputs path old current result Position Safe Nonreg (reference_control_ready_2558 old ) Step).
Qed.
Theorem reference_control_node_2558_congruent inputs path left right next_left next_right :
 VM.find 2554 left = VM.find 2554 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2558 next_left = VM.find 2558 next_right.
Proof.
 intros  E2554 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2558 reference_control_expr_2558 reference_control_2_positions reference_control_2_safety reference_control_member_2558) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2558 reference_control_expr_2558 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2558 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2558 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2554.
 reflexivity.
Qed.
Lemma reference_control_ready_2559 old :
 reference_control_ready old reference_control_expr_2559.
Proof.
 unfold reference_control_expr_2559.
apply rc_binary.
Qed.
Lemma reference_control_member_2559 : List.In (2559,reference_control_expr_2559) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 76%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2559_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2559 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2559 reference_control_expr_2559 reference_control_2_positions reference_control_2_safety reference_control_member_2559) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2559 reference_control_expr_2559 inputs path old current result Position Safe Nonreg (reference_control_ready_2559 old ) Step).
Qed.
Theorem reference_control_node_2559_congruent inputs path left right next_left next_right :
 VM.find 2558 left = VM.find 2558 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2559 next_left = VM.find 2559 next_right.
Proof.
 intros  E2558 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2559 reference_control_expr_2559 reference_control_2_positions reference_control_2_safety reference_control_member_2559) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2559 reference_control_expr_2559 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2559 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2559 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2558.
 reflexivity.
Qed.
Lemma reference_control_ready_2560 old :
 reference_control_ready old reference_control_expr_2560.
Proof.
 unfold reference_control_expr_2560.
apply rc_binary.
Qed.
Lemma reference_control_member_2560 : List.In (2560,reference_control_expr_2560) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 77%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2560_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2560 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2560 reference_control_expr_2560 reference_control_2_positions reference_control_2_safety reference_control_member_2560) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2560 reference_control_expr_2560 inputs path old current result Position Safe Nonreg (reference_control_ready_2560 old ) Step).
Qed.
Theorem reference_control_node_2560_congruent inputs path left right next_left next_right :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2560 next_left = VM.find 2560 next_right.
Proof.
 intros   L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2560 reference_control_expr_2560 reference_control_2_positions reference_control_2_safety reference_control_member_2560) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2560 reference_control_expr_2560 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2560 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2560 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 reflexivity.
Qed.
Lemma reference_control_ready_2561 old :
 reference_control_ready old reference_control_expr_2561.
Proof.
 unfold reference_control_expr_2561.
apply rc_unary.
Qed.
Lemma reference_control_member_2561 : List.In (2561,reference_control_expr_2561) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 78%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2561_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2561 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2561 reference_control_expr_2561 reference_control_2_positions reference_control_2_safety reference_control_member_2561) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2561 reference_control_expr_2561 inputs path old current result Position Safe Nonreg (reference_control_ready_2561 old ) Step).
Qed.
Theorem reference_control_node_2561_congruent inputs path left right next_left next_right :
 VM.find 2554 left = VM.find 2554 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2561 next_left = VM.find 2561 next_right.
Proof.
 intros  E2554 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2561 reference_control_expr_2561 reference_control_2_positions reference_control_2_safety reference_control_member_2561) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2561 reference_control_expr_2561 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2561 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2561 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2554.
 reflexivity.
Qed.
Lemma reference_control_ready_2562 old :
 reference_control_ready old reference_control_expr_2562.
Proof.
 unfold reference_control_expr_2562.
apply rc_binary.
Qed.
Lemma reference_control_member_2562 : List.In (2562,reference_control_expr_2562) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 79%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2562_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2562 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2562 reference_control_expr_2562 reference_control_2_positions reference_control_2_safety reference_control_member_2562) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2562 reference_control_expr_2562 inputs path old current result Position Safe Nonreg (reference_control_ready_2562 old ) Step).
Qed.
Theorem reference_control_node_2562_congruent inputs path left right next_left next_right :
 VM.find 2561 left = VM.find 2561 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2562 next_left = VM.find 2562 next_right.
Proof.
 intros  E2561 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2562 reference_control_expr_2562 reference_control_2_positions reference_control_2_safety reference_control_member_2562) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2562 reference_control_expr_2562 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2562 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2562 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2561.
 reflexivity.
Qed.
Lemma reference_control_ready_2563 old :
 (exists value ground, VM.find 2562 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2563.
Proof.
 intros H2562.
 destruct H2562 as [v2562 [G2562 [V2562 T2562]]].
 unfold reference_control_expr_2563.
apply rc_mux.
{ eapply rc_ref; [exact V2562|exists G2562; exact T2562].
}
{ apply rc_const.
}
Qed.
Lemma reference_control_member_2563 : List.In (2563,reference_control_expr_2563) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 80%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2563_ground inputs path old current result :
 (exists value ground, VM.find 2562 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2563 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2562 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2563 reference_control_expr_2563 reference_control_2_positions reference_control_2_safety reference_control_member_2563) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2563 reference_control_expr_2563 inputs path old current result Position Safe Nonreg (reference_control_ready_2563 old H2562) Step).
Qed.
Theorem reference_control_node_2563_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2562 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2560 left = VM.find 2560 right ->
 VM.find 2562 left = VM.find 2562 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2563 next_left = VM.find 2563 next_right.
Proof.
 intros H2562 E2560 E2562 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2563 reference_control_expr_2563 reference_control_2_positions reference_control_2_safety reference_control_member_2563) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2563 reference_control_expr_2563 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2563 left H2562)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2563 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2560.
 rewrite E2562.
 reflexivity.
Qed.
Lemma reference_control_ready_2564 old :
 (exists value ground, VM.find 2559 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2563 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2564.
Proof.
 intros H2559 H2563.
 destruct H2559 as [v2559 [G2559 [V2559 T2559]]].
 destruct H2563 as [v2563 [G2563 [V2563 T2563]]].
 unfold reference_control_expr_2564.
apply rc_mux.
{ eapply rc_ref; [exact V2559|exists G2559; exact T2559].
}
{ eapply rc_ref; [exact V2563|exists G2563; exact T2563].
}
Qed.
Lemma reference_control_member_2564 : List.In (2564,reference_control_expr_2564) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 81%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2564_ground inputs path old current result :
 (exists value ground, VM.find 2559 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2563 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2564 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2559 H2563 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2564 reference_control_expr_2564 reference_control_2_positions reference_control_2_safety reference_control_member_2564) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2564 reference_control_expr_2564 inputs path old current result Position Safe Nonreg (reference_control_ready_2564 old H2559 H2563) Step).
Qed.
Theorem reference_control_node_2564_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2559 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2563 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2557 left = VM.find 2557 right ->
 VM.find 2559 left = VM.find 2559 right ->
 VM.find 2563 left = VM.find 2563 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2564 next_left = VM.find 2564 next_right.
Proof.
 intros H2559 H2563 E2557 E2559 E2563 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2564 reference_control_expr_2564 reference_control_2_positions reference_control_2_safety reference_control_member_2564) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2564 reference_control_expr_2564 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2564 left H2559 H2563)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2564 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2557.
 rewrite E2559.
 rewrite E2563.
 reflexivity.
Qed.
Lemma reference_control_ready_2565 old :
 (exists value ground, VM.find 2556 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2564 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2565.
Proof.
 intros H2556 H2564.
 destruct H2556 as [v2556 [G2556 [V2556 T2556]]].
 destruct H2564 as [v2564 [G2564 [V2564 T2564]]].
 unfold reference_control_expr_2565.
apply rc_mux.
{ eapply rc_ref; [exact V2556|exists G2556; exact T2556].
}
{ eapply rc_ref; [exact V2564|exists G2564; exact T2564].
}
Qed.
Lemma reference_control_member_2565 : List.In (2565,reference_control_expr_2565) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 82%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2565_ground inputs path old current result :
 (exists value ground, VM.find 2556 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2564 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2565 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2556 H2564 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2565 reference_control_expr_2565 reference_control_2_positions reference_control_2_safety reference_control_member_2565) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2565 reference_control_expr_2565 inputs path old current result Position Safe Nonreg (reference_control_ready_2565 old H2556 H2564) Step).
Qed.
Theorem reference_control_node_2565_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2556 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2564 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1887 left = VM.find 1887 right ->
 VM.find 2556 left = VM.find 2556 right ->
 VM.find 2564 left = VM.find 2564 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2565 next_left = VM.find 2565 next_right.
Proof.
 intros H2556 H2564 E1887 E2556 E2564 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2565 reference_control_expr_2565 reference_control_2_positions reference_control_2_safety reference_control_member_2565) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2565 reference_control_expr_2565 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2565 left H2556 H2564)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2565 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1887.
 rewrite E2556.
 rewrite E2564.
 reflexivity.
Qed.
Lemma reference_control_ready_2566 old :
 reference_control_ready old reference_control_expr_2566.
Proof.
 unfold reference_control_expr_2566.
apply rc_binary.
Qed.
Lemma reference_control_member_2566 : List.In (2566,reference_control_expr_2566) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 83%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2566_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2566 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2566 reference_control_expr_2566 reference_control_2_positions reference_control_2_safety reference_control_member_2566) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2566 reference_control_expr_2566 inputs path old current result Position Safe Nonreg (reference_control_ready_2566 old ) Step).
Qed.
Theorem reference_control_node_2566_congruent inputs path left right next_left next_right :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2566 next_left = VM.find 2566 next_right.
Proof.
 intros   L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2566 reference_control_expr_2566 reference_control_2_positions reference_control_2_safety reference_control_member_2566) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2566 reference_control_expr_2566 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2566 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2566 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 reflexivity.
Qed.
Lemma reference_control_ready_2567 old :
 reference_control_ready old reference_control_expr_2567.
Proof.
 unfold reference_control_expr_2567.
apply rc_unary.
Qed.
Lemma reference_control_member_2567 : List.In (2567,reference_control_expr_2567) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 84%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2567_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2567 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2567 reference_control_expr_2567 reference_control_2_positions reference_control_2_safety reference_control_member_2567) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2567 reference_control_expr_2567 inputs path old current result Position Safe Nonreg (reference_control_ready_2567 old ) Step).
Qed.
Theorem reference_control_node_2567_congruent inputs path left right next_left next_right :
 VM.find 1890 left = VM.find 1890 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2567 next_left = VM.find 2567 next_right.
Proof.
 intros  E1890 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2567 reference_control_expr_2567 reference_control_2_positions reference_control_2_safety reference_control_member_2567) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2567 reference_control_expr_2567 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2567 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2567 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1890.
 reflexivity.
Qed.
Lemma reference_control_ready_2568 old :
 reference_control_ready old reference_control_expr_2568.
Proof.
 unfold reference_control_expr_2568.
apply rc_unary.
Qed.
Lemma reference_control_member_2568 : List.In (2568,reference_control_expr_2568) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 85%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2568_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2568 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2568 reference_control_expr_2568 reference_control_2_positions reference_control_2_safety reference_control_member_2568) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2568 reference_control_expr_2568 inputs path old current result Position Safe Nonreg (reference_control_ready_2568 old ) Step).
Qed.
Theorem reference_control_node_2568_congruent inputs path left right next_left next_right :
 VM.find 1895 left = VM.find 1895 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2568 next_left = VM.find 2568 next_right.
Proof.
 intros  E1895 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2568 reference_control_expr_2568 reference_control_2_positions reference_control_2_safety reference_control_member_2568) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2568 reference_control_expr_2568 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2568 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2568 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1895.
 reflexivity.
Qed.
Lemma reference_control_ready_2569 old :
 reference_control_ready old reference_control_expr_2569.
Proof.
 unfold reference_control_expr_2569.
apply rc_unary.
Qed.
Lemma reference_control_member_2569 : List.In (2569,reference_control_expr_2569) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 86%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2569_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2569 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2569 reference_control_expr_2569 reference_control_2_positions reference_control_2_safety reference_control_member_2569) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2569 reference_control_expr_2569 inputs path old current result Position Safe Nonreg (reference_control_ready_2569 old ) Step).
Qed.
Theorem reference_control_node_2569_congruent inputs path left right next_left next_right :
 VM.find 1900 left = VM.find 1900 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2569 next_left = VM.find 2569 next_right.
Proof.
 intros  E1900 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2569 reference_control_expr_2569 reference_control_2_positions reference_control_2_safety reference_control_member_2569) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2569 reference_control_expr_2569 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2569 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2569 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1900.
 reflexivity.
Qed.
Lemma reference_control_ready_2570 old :
 reference_control_ready old reference_control_expr_2570.
Proof.
 unfold reference_control_expr_2570.
apply rc_unary.
Qed.
Lemma reference_control_member_2570 : List.In (2570,reference_control_expr_2570) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 87%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2570_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2570 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2570 reference_control_expr_2570 reference_control_2_positions reference_control_2_safety reference_control_member_2570) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2570 reference_control_expr_2570 inputs path old current result Position Safe Nonreg (reference_control_ready_2570 old ) Step).
Qed.
Theorem reference_control_node_2570_congruent inputs path left right next_left next_right :
 VM.find 1905 left = VM.find 1905 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2570 next_left = VM.find 2570 next_right.
Proof.
 intros  E1905 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2570 reference_control_expr_2570 reference_control_2_positions reference_control_2_safety reference_control_member_2570) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2570 reference_control_expr_2570 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2570 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2570 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1905.
 reflexivity.
Qed.
Lemma reference_control_ready_2571 old :
 reference_control_ready old reference_control_expr_2571.
Proof.
 unfold reference_control_expr_2571.
apply rc_unary.
Qed.
Lemma reference_control_member_2571 : List.In (2571,reference_control_expr_2571) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 88%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2571_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2571 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2571 reference_control_expr_2571 reference_control_2_positions reference_control_2_safety reference_control_member_2571) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2571 reference_control_expr_2571 inputs path old current result Position Safe Nonreg (reference_control_ready_2571 old ) Step).
Qed.
Theorem reference_control_node_2571_congruent inputs path left right next_left next_right :
 VM.find 1910 left = VM.find 1910 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2571 next_left = VM.find 2571 next_right.
Proof.
 intros  E1910 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2571 reference_control_expr_2571 reference_control_2_positions reference_control_2_safety reference_control_member_2571) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2571 reference_control_expr_2571 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2571 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2571 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1910.
 reflexivity.
Qed.
Lemma reference_control_ready_2572 old :
 reference_control_ready old reference_control_expr_2572.
Proof.
 unfold reference_control_expr_2572.
apply rc_unary.
Qed.
Lemma reference_control_member_2572 : List.In (2572,reference_control_expr_2572) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 89%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2572_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2572 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2572 reference_control_expr_2572 reference_control_2_positions reference_control_2_safety reference_control_member_2572) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2572 reference_control_expr_2572 inputs path old current result Position Safe Nonreg (reference_control_ready_2572 old ) Step).
Qed.
Theorem reference_control_node_2572_congruent inputs path left right next_left next_right :
 VM.find 1915 left = VM.find 1915 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2572 next_left = VM.find 2572 next_right.
Proof.
 intros  E1915 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2572 reference_control_expr_2572 reference_control_2_positions reference_control_2_safety reference_control_member_2572) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2572 reference_control_expr_2572 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2572 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2572 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1915.
 reflexivity.
Qed.
Lemma reference_control_ready_2573 old :
 reference_control_ready old reference_control_expr_2573.
Proof.
 unfold reference_control_expr_2573.
apply rc_unary.
Qed.
Lemma reference_control_member_2573 : List.In (2573,reference_control_expr_2573) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 90%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2573_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2573 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2573 reference_control_expr_2573 reference_control_2_positions reference_control_2_safety reference_control_member_2573) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2573 reference_control_expr_2573 inputs path old current result Position Safe Nonreg (reference_control_ready_2573 old ) Step).
Qed.
Theorem reference_control_node_2573_congruent inputs path left right next_left next_right :
 VM.find 1920 left = VM.find 1920 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2573 next_left = VM.find 2573 next_right.
Proof.
 intros  E1920 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2573 reference_control_expr_2573 reference_control_2_positions reference_control_2_safety reference_control_member_2573) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2573 reference_control_expr_2573 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2573 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2573 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1920.
 reflexivity.
Qed.
Lemma reference_control_ready_2574 old :
 reference_control_ready old reference_control_expr_2574.
Proof.
 unfold reference_control_expr_2574.
apply rc_unary.
Qed.
Lemma reference_control_member_2574 : List.In (2574,reference_control_expr_2574) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 91%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2574_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2574 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2574 reference_control_expr_2574 reference_control_2_positions reference_control_2_safety reference_control_member_2574) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2574 reference_control_expr_2574 inputs path old current result Position Safe Nonreg (reference_control_ready_2574 old ) Step).
Qed.
Theorem reference_control_node_2574_congruent inputs path left right next_left next_right :
 VM.find 1925 left = VM.find 1925 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2574 next_left = VM.find 2574 next_right.
Proof.
 intros  E1925 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2574 reference_control_expr_2574 reference_control_2_positions reference_control_2_safety reference_control_member_2574) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2574 reference_control_expr_2574 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2574 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2574 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1925.
 reflexivity.
Qed.
Lemma reference_control_ready_2575 old :
 reference_control_ready old reference_control_expr_2575.
Proof.
 unfold reference_control_expr_2575.
apply rc_unary.
Qed.
Lemma reference_control_member_2575 : List.In (2575,reference_control_expr_2575) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 92%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2575_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2575 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2575 reference_control_expr_2575 reference_control_2_positions reference_control_2_safety reference_control_member_2575) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2575 reference_control_expr_2575 inputs path old current result Position Safe Nonreg (reference_control_ready_2575 old ) Step).
Qed.
Theorem reference_control_node_2575_congruent inputs path left right next_left next_right :
 VM.find 1942 left = VM.find 1942 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2575 next_left = VM.find 2575 next_right.
Proof.
 intros  E1942 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2575 reference_control_expr_2575 reference_control_2_positions reference_control_2_safety reference_control_member_2575) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2575 reference_control_expr_2575 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2575 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2575 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1942.
 reflexivity.
Qed.
Lemma reference_control_ready_2576 old :
 reference_control_ready old reference_control_expr_2576.
Proof.
 unfold reference_control_expr_2576.
apply rc_unary.
Qed.
Lemma reference_control_member_2576 : List.In (2576,reference_control_expr_2576) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 93%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2576_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2576 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2576 reference_control_expr_2576 reference_control_2_positions reference_control_2_safety reference_control_member_2576) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2576 reference_control_expr_2576 inputs path old current result Position Safe Nonreg (reference_control_ready_2576 old ) Step).
Qed.
Theorem reference_control_node_2576_congruent inputs path left right next_left next_right :
 VM.find 1947 left = VM.find 1947 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2576 next_left = VM.find 2576 next_right.
Proof.
 intros  E1947 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2576 reference_control_expr_2576 reference_control_2_positions reference_control_2_safety reference_control_member_2576) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2576 reference_control_expr_2576 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2576 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2576 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1947.
 reflexivity.
Qed.
Lemma reference_control_ready_2577 old :
 reference_control_ready old reference_control_expr_2577.
Proof.
 unfold reference_control_expr_2577.
apply rc_unary.
Qed.
Lemma reference_control_member_2577 : List.In (2577,reference_control_expr_2577) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 94%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2577_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2577 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2577 reference_control_expr_2577 reference_control_2_positions reference_control_2_safety reference_control_member_2577) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2577 reference_control_expr_2577 inputs path old current result Position Safe Nonreg (reference_control_ready_2577 old ) Step).
Qed.
Theorem reference_control_node_2577_congruent inputs path left right next_left next_right :
 VM.find 1952 left = VM.find 1952 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2577 next_left = VM.find 2577 next_right.
Proof.
 intros  E1952 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2577 reference_control_expr_2577 reference_control_2_positions reference_control_2_safety reference_control_member_2577) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2577 reference_control_expr_2577 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2577 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2577 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1952.
 reflexivity.
Qed.
Lemma reference_control_ready_2578 old :
 reference_control_ready old reference_control_expr_2578.
Proof.
 unfold reference_control_expr_2578.
apply rc_unary.
Qed.
Lemma reference_control_member_2578 : List.In (2578,reference_control_expr_2578) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 95%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2578_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2578 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2578 reference_control_expr_2578 reference_control_2_positions reference_control_2_safety reference_control_member_2578) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2578 reference_control_expr_2578 inputs path old current result Position Safe Nonreg (reference_control_ready_2578 old ) Step).
Qed.
Theorem reference_control_node_2578_congruent inputs path left right next_left next_right :
 VM.find 1976 left = VM.find 1976 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2578 next_left = VM.find 2578 next_right.
Proof.
 intros  E1976 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2578 reference_control_expr_2578 reference_control_2_positions reference_control_2_safety reference_control_member_2578) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2578 reference_control_expr_2578 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2578 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2578 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1976.
 reflexivity.
Qed.
Lemma reference_control_ready_2579 old :
 reference_control_ready old reference_control_expr_2579.
Proof.
 unfold reference_control_expr_2579.
apply rc_unary.
Qed.
Lemma reference_control_member_2579 : List.In (2579,reference_control_expr_2579) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 96%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2579_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2579 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2579 reference_control_expr_2579 reference_control_2_positions reference_control_2_safety reference_control_member_2579) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2579 reference_control_expr_2579 inputs path old current result Position Safe Nonreg (reference_control_ready_2579 old ) Step).
Qed.
Theorem reference_control_node_2579_congruent inputs path left right next_left next_right :
 VM.find 1982 left = VM.find 1982 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2579 next_left = VM.find 2579 next_right.
Proof.
 intros  E1982 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2579 reference_control_expr_2579 reference_control_2_positions reference_control_2_safety reference_control_member_2579) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2579 reference_control_expr_2579 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2579 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2579 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1982.
 reflexivity.
Qed.
Lemma reference_control_ready_2580 old :
 reference_control_ready old reference_control_expr_2580.
Proof.
 unfold reference_control_expr_2580.
apply rc_unary.
Qed.
Lemma reference_control_member_2580 : List.In (2580,reference_control_expr_2580) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 97%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2580_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2580 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2580 reference_control_expr_2580 reference_control_2_positions reference_control_2_safety reference_control_member_2580) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2580 reference_control_expr_2580 inputs path old current result Position Safe Nonreg (reference_control_ready_2580 old ) Step).
Qed.
Theorem reference_control_node_2580_congruent inputs path left right next_left next_right :
 VM.find 1988 left = VM.find 1988 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2580 next_left = VM.find 2580 next_right.
Proof.
 intros  E1988 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2580 reference_control_expr_2580 reference_control_2_positions reference_control_2_safety reference_control_member_2580) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2580 reference_control_expr_2580 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2580 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2580 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1988.
 reflexivity.
Qed.
Lemma reference_control_ready_2581 old :
 reference_control_ready old reference_control_expr_2581.
Proof.
 unfold reference_control_expr_2581.
apply rc_unary.
Qed.
Lemma reference_control_member_2581 : List.In (2581,reference_control_expr_2581) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 98%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2581_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2581 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2581 reference_control_expr_2581 reference_control_2_positions reference_control_2_safety reference_control_member_2581) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2581 reference_control_expr_2581 inputs path old current result Position Safe Nonreg (reference_control_ready_2581 old ) Step).
Qed.
Theorem reference_control_node_2581_congruent inputs path left right next_left next_right :
 VM.find 1994 left = VM.find 1994 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2581 next_left = VM.find 2581 next_right.
Proof.
 intros  E1994 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2581 reference_control_expr_2581 reference_control_2_positions reference_control_2_safety reference_control_member_2581) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2581 reference_control_expr_2581 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2581 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2581 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1994.
 reflexivity.
Qed.
Lemma reference_control_ready_2582 old :
 reference_control_ready old reference_control_expr_2582.
Proof.
 unfold reference_control_expr_2582.
apply rc_unary.
Qed.
Lemma reference_control_member_2582 : List.In (2582,reference_control_expr_2582) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 99%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2582_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2582 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2582 reference_control_expr_2582 reference_control_2_positions reference_control_2_safety reference_control_member_2582) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2582 reference_control_expr_2582 inputs path old current result Position Safe Nonreg (reference_control_ready_2582 old ) Step).
Qed.
Theorem reference_control_node_2582_congruent inputs path left right next_left next_right :
 VM.find 2000 left = VM.find 2000 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2582 next_left = VM.find 2582 next_right.
Proof.
 intros  E2000 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2582 reference_control_expr_2582 reference_control_2_positions reference_control_2_safety reference_control_member_2582) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2582 reference_control_expr_2582 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2582 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2582 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2000.
 reflexivity.
Qed.
Lemma reference_control_ready_2583 old :
 reference_control_ready old reference_control_expr_2583.
Proof.
 unfold reference_control_expr_2583.
apply rc_unary.
Qed.
Lemma reference_control_member_2583 : List.In (2583,reference_control_expr_2583) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 100%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2583_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2583 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2583 reference_control_expr_2583 reference_control_2_positions reference_control_2_safety reference_control_member_2583) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2583 reference_control_expr_2583 inputs path old current result Position Safe Nonreg (reference_control_ready_2583 old ) Step).
Qed.
Theorem reference_control_node_2583_congruent inputs path left right next_left next_right :
 VM.find 2006 left = VM.find 2006 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2583 next_left = VM.find 2583 next_right.
Proof.
 intros  E2006 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2583 reference_control_expr_2583 reference_control_2_positions reference_control_2_safety reference_control_member_2583) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2583 reference_control_expr_2583 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2583 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2583 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2006.
 reflexivity.
Qed.
Lemma reference_control_ready_2584 old :
 reference_control_ready old reference_control_expr_2584.
Proof.
 unfold reference_control_expr_2584.
apply rc_unary.
Qed.
Lemma reference_control_member_2584 : List.In (2584,reference_control_expr_2584) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 101%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2584_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2584 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2584 reference_control_expr_2584 reference_control_2_positions reference_control_2_safety reference_control_member_2584) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2584 reference_control_expr_2584 inputs path old current result Position Safe Nonreg (reference_control_ready_2584 old ) Step).
Qed.
Theorem reference_control_node_2584_congruent inputs path left right next_left next_right :
 VM.find 2015 left = VM.find 2015 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2584 next_left = VM.find 2584 next_right.
Proof.
 intros  E2015 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2584 reference_control_expr_2584 reference_control_2_positions reference_control_2_safety reference_control_member_2584) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2584 reference_control_expr_2584 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2584 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2584 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2015.
 reflexivity.
Qed.
Lemma reference_control_ready_2585 old :
 reference_control_ready old reference_control_expr_2585.
Proof.
 unfold reference_control_expr_2585.
apply rc_unary.
Qed.
Lemma reference_control_member_2585 : List.In (2585,reference_control_expr_2585) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 102%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2585_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2585 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2585 reference_control_expr_2585 reference_control_2_positions reference_control_2_safety reference_control_member_2585) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2585 reference_control_expr_2585 inputs path old current result Position Safe Nonreg (reference_control_ready_2585 old ) Step).
Qed.
Theorem reference_control_node_2585_congruent inputs path left right next_left next_right :
 VM.find 2020 left = VM.find 2020 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2585 next_left = VM.find 2585 next_right.
Proof.
 intros  E2020 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2585 reference_control_expr_2585 reference_control_2_positions reference_control_2_safety reference_control_member_2585) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2585 reference_control_expr_2585 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2585 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2585 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2020.
 reflexivity.
Qed.
Lemma reference_control_ready_2586 old :
 reference_control_ready old reference_control_expr_2586.
Proof.
 unfold reference_control_expr_2586.
apply rc_unary.
Qed.
Lemma reference_control_member_2586 : List.In (2586,reference_control_expr_2586) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 103%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2586_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2586 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2586 reference_control_expr_2586 reference_control_2_positions reference_control_2_safety reference_control_member_2586) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2586 reference_control_expr_2586 inputs path old current result Position Safe Nonreg (reference_control_ready_2586 old ) Step).
Qed.
Theorem reference_control_node_2586_congruent inputs path left right next_left next_right :
 VM.find 2025 left = VM.find 2025 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2586 next_left = VM.find 2586 next_right.
Proof.
 intros  E2025 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2586 reference_control_expr_2586 reference_control_2_positions reference_control_2_safety reference_control_member_2586) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2586 reference_control_expr_2586 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2586 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2586 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2025.
 reflexivity.
Qed.
Lemma reference_control_ready_2587 old :
 reference_control_ready old reference_control_expr_2587.
Proof.
 unfold reference_control_expr_2587.
apply rc_unary.
Qed.
Lemma reference_control_member_2587 : List.In (2587,reference_control_expr_2587) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 104%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2587_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2587 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2587 reference_control_expr_2587 reference_control_2_positions reference_control_2_safety reference_control_member_2587) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2587 reference_control_expr_2587 inputs path old current result Position Safe Nonreg (reference_control_ready_2587 old ) Step).
Qed.
Theorem reference_control_node_2587_congruent inputs path left right next_left next_right :
 VM.find 2030 left = VM.find 2030 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2587 next_left = VM.find 2587 next_right.
Proof.
 intros  E2030 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2587 reference_control_expr_2587 reference_control_2_positions reference_control_2_safety reference_control_member_2587) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2587 reference_control_expr_2587 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2587 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2587 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2030.
 reflexivity.
Qed.
Lemma reference_control_ready_2588 old :
 reference_control_ready old reference_control_expr_2588.
Proof.
 unfold reference_control_expr_2588.
apply rc_unary.
Qed.
Lemma reference_control_member_2588 : List.In (2588,reference_control_expr_2588) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 105%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2588_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2588 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2588 reference_control_expr_2588 reference_control_2_positions reference_control_2_safety reference_control_member_2588) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2588 reference_control_expr_2588 inputs path old current result Position Safe Nonreg (reference_control_ready_2588 old ) Step).
Qed.
Theorem reference_control_node_2588_congruent inputs path left right next_left next_right :
 VM.find 2035 left = VM.find 2035 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2588 next_left = VM.find 2588 next_right.
Proof.
 intros  E2035 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2588 reference_control_expr_2588 reference_control_2_positions reference_control_2_safety reference_control_member_2588) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2588 reference_control_expr_2588 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2588 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2588 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2035.
 reflexivity.
Qed.
Lemma reference_control_ready_2589 old :
 reference_control_ready old reference_control_expr_2589.
Proof.
 unfold reference_control_expr_2589.
apply rc_unary.
Qed.
Lemma reference_control_member_2589 : List.In (2589,reference_control_expr_2589) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 106%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2589_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2589 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2589 reference_control_expr_2589 reference_control_2_positions reference_control_2_safety reference_control_member_2589) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2589 reference_control_expr_2589 inputs path old current result Position Safe Nonreg (reference_control_ready_2589 old ) Step).
Qed.
Theorem reference_control_node_2589_congruent inputs path left right next_left next_right :
 VM.find 2040 left = VM.find 2040 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2589 next_left = VM.find 2589 next_right.
Proof.
 intros  E2040 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2589 reference_control_expr_2589 reference_control_2_positions reference_control_2_safety reference_control_member_2589) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2589 reference_control_expr_2589 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2589 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2589 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2040.
 reflexivity.
Qed.
Lemma reference_control_ready_2590 old :
 reference_control_ready old reference_control_expr_2590.
Proof.
 unfold reference_control_expr_2590.
apply rc_unary.
Qed.
Lemma reference_control_member_2590 : List.In (2590,reference_control_expr_2590) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 107%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2590_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2590 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2590 reference_control_expr_2590 reference_control_2_positions reference_control_2_safety reference_control_member_2590) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2590 reference_control_expr_2590 inputs path old current result Position Safe Nonreg (reference_control_ready_2590 old ) Step).
Qed.
Theorem reference_control_node_2590_congruent inputs path left right next_left next_right :
 VM.find 2045 left = VM.find 2045 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2590 next_left = VM.find 2590 next_right.
Proof.
 intros  E2045 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2590 reference_control_expr_2590 reference_control_2_positions reference_control_2_safety reference_control_member_2590) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2590 reference_control_expr_2590 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2590 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2590 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2045.
 reflexivity.
Qed.
Lemma reference_control_ready_2591 old :
 reference_control_ready old reference_control_expr_2591.
Proof.
 unfold reference_control_expr_2591.
apply rc_unary.
Qed.
Lemma reference_control_member_2591 : List.In (2591,reference_control_expr_2591) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 108%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2591_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2591 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2591 reference_control_expr_2591 reference_control_2_positions reference_control_2_safety reference_control_member_2591) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2591 reference_control_expr_2591 inputs path old current result Position Safe Nonreg (reference_control_ready_2591 old ) Step).
Qed.
Theorem reference_control_node_2591_congruent inputs path left right next_left next_right :
 VM.find 2050 left = VM.find 2050 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2591 next_left = VM.find 2591 next_right.
Proof.
 intros  E2050 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2591 reference_control_expr_2591 reference_control_2_positions reference_control_2_safety reference_control_member_2591) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2591 reference_control_expr_2591 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2591 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2591 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2050.
 reflexivity.
Qed.
Lemma reference_control_ready_2592 old :
 reference_control_ready old reference_control_expr_2592.
Proof.
 unfold reference_control_expr_2592.
apply rc_unary.
Qed.
Lemma reference_control_member_2592 : List.In (2592,reference_control_expr_2592) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 109%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2592_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2592 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2592 reference_control_expr_2592 reference_control_2_positions reference_control_2_safety reference_control_member_2592) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2592 reference_control_expr_2592 inputs path old current result Position Safe Nonreg (reference_control_ready_2592 old ) Step).
Qed.
Theorem reference_control_node_2592_congruent inputs path left right next_left next_right :
 VM.find 2055 left = VM.find 2055 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2592 next_left = VM.find 2592 next_right.
Proof.
 intros  E2055 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2592 reference_control_expr_2592 reference_control_2_positions reference_control_2_safety reference_control_member_2592) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2592 reference_control_expr_2592 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2592 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2592 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2055.
 reflexivity.
Qed.
Lemma reference_control_ready_2593 old :
 reference_control_ready old reference_control_expr_2593.
Proof.
 unfold reference_control_expr_2593.
apply rc_unary.
Qed.
Lemma reference_control_member_2593 : List.In (2593,reference_control_expr_2593) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 110%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2593_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2593 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2593 reference_control_expr_2593 reference_control_2_positions reference_control_2_safety reference_control_member_2593) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2593 reference_control_expr_2593 inputs path old current result Position Safe Nonreg (reference_control_ready_2593 old ) Step).
Qed.
Theorem reference_control_node_2593_congruent inputs path left right next_left next_right :
 VM.find 2060 left = VM.find 2060 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2593 next_left = VM.find 2593 next_right.
Proof.
 intros  E2060 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2593 reference_control_expr_2593 reference_control_2_positions reference_control_2_safety reference_control_member_2593) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2593 reference_control_expr_2593 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2593 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2593 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2060.
 reflexivity.
Qed.
Lemma reference_control_ready_2594 old :
 (exists value ground, VM.find 2593 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2594.
Proof.
 intros H2593.
 destruct H2593 as [v2593 [G2593 [V2593 T2593]]].
 unfold reference_control_expr_2594.
apply rc_mux.
{ eapply rc_ref; [exact V2593|exists G2593; exact T2593].
}
{ apply rc_const.
}
Qed.
Lemma reference_control_member_2594 : List.In (2594,reference_control_expr_2594) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 111%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2594_ground inputs path old current result :
 (exists value ground, VM.find 2593 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2594 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2593 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2594 reference_control_expr_2594 reference_control_2_positions reference_control_2_safety reference_control_member_2594) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2594 reference_control_expr_2594 inputs path old current result Position Safe Nonreg (reference_control_ready_2594 old H2593) Step).
Qed.
Theorem reference_control_node_2594_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2593 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2059 left = VM.find 2059 right ->
 VM.find 2593 left = VM.find 2593 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2594 next_left = VM.find 2594 next_right.
Proof.
 intros H2593 E2059 E2593 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2594 reference_control_expr_2594 reference_control_2_positions reference_control_2_safety reference_control_member_2594) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2594 reference_control_expr_2594 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2594 left H2593)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2594 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2059.
 rewrite E2593.
 reflexivity.
Qed.
Lemma reference_control_ready_2595 old :
 (exists value ground, VM.find 2592 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2594 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2595.
Proof.
 intros H2592 H2594.
 destruct H2592 as [v2592 [G2592 [V2592 T2592]]].
 destruct H2594 as [v2594 [G2594 [V2594 T2594]]].
 unfold reference_control_expr_2595.
apply rc_mux.
{ eapply rc_ref; [exact V2592|exists G2592; exact T2592].
}
{ eapply rc_ref; [exact V2594|exists G2594; exact T2594].
}
Qed.
Lemma reference_control_member_2595 : List.In (2595,reference_control_expr_2595) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 112%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2595_ground inputs path old current result :
 (exists value ground, VM.find 2592 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2594 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2595 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2592 H2594 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2595 reference_control_expr_2595 reference_control_2_positions reference_control_2_safety reference_control_member_2595) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2595 reference_control_expr_2595 inputs path old current result Position Safe Nonreg (reference_control_ready_2595 old H2592 H2594) Step).
Qed.
Theorem reference_control_node_2595_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2592 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2594 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2054 left = VM.find 2054 right ->
 VM.find 2592 left = VM.find 2592 right ->
 VM.find 2594 left = VM.find 2594 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2595 next_left = VM.find 2595 next_right.
Proof.
 intros H2592 H2594 E2054 E2592 E2594 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2595 reference_control_expr_2595 reference_control_2_positions reference_control_2_safety reference_control_member_2595) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2595 reference_control_expr_2595 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2595 left H2592 H2594)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2595 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2054.
 rewrite E2592.
 rewrite E2594.
 reflexivity.
Qed.
Lemma reference_control_ready_2596 old :
 (exists value ground, VM.find 2591 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2595 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2596.
Proof.
 intros H2591 H2595.
 destruct H2591 as [v2591 [G2591 [V2591 T2591]]].
 destruct H2595 as [v2595 [G2595 [V2595 T2595]]].
 unfold reference_control_expr_2596.
apply rc_mux.
{ eapply rc_ref; [exact V2591|exists G2591; exact T2591].
}
{ eapply rc_ref; [exact V2595|exists G2595; exact T2595].
}
Qed.
Lemma reference_control_member_2596 : List.In (2596,reference_control_expr_2596) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 113%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2596_ground inputs path old current result :
 (exists value ground, VM.find 2591 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2595 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2596 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2591 H2595 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2596 reference_control_expr_2596 reference_control_2_positions reference_control_2_safety reference_control_member_2596) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2596 reference_control_expr_2596 inputs path old current result Position Safe Nonreg (reference_control_ready_2596 old H2591 H2595) Step).
Qed.
Theorem reference_control_node_2596_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2591 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2595 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2049 left = VM.find 2049 right ->
 VM.find 2591 left = VM.find 2591 right ->
 VM.find 2595 left = VM.find 2595 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2596 next_left = VM.find 2596 next_right.
Proof.
 intros H2591 H2595 E2049 E2591 E2595 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2596 reference_control_expr_2596 reference_control_2_positions reference_control_2_safety reference_control_member_2596) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2596 reference_control_expr_2596 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2596 left H2591 H2595)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2596 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2049.
 rewrite E2591.
 rewrite E2595.
 reflexivity.
Qed.
Lemma reference_control_ready_2597 old :
 (exists value ground, VM.find 2590 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2596 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2597.
Proof.
 intros H2590 H2596.
 destruct H2590 as [v2590 [G2590 [V2590 T2590]]].
 destruct H2596 as [v2596 [G2596 [V2596 T2596]]].
 unfold reference_control_expr_2597.
apply rc_mux.
{ eapply rc_ref; [exact V2590|exists G2590; exact T2590].
}
{ eapply rc_ref; [exact V2596|exists G2596; exact T2596].
}
Qed.
Lemma reference_control_member_2597 : List.In (2597,reference_control_expr_2597) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 114%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2597_ground inputs path old current result :
 (exists value ground, VM.find 2590 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2596 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2597 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2590 H2596 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2597 reference_control_expr_2597 reference_control_2_positions reference_control_2_safety reference_control_member_2597) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2597 reference_control_expr_2597 inputs path old current result Position Safe Nonreg (reference_control_ready_2597 old H2590 H2596) Step).
Qed.
Theorem reference_control_node_2597_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2590 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2596 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2044 left = VM.find 2044 right ->
 VM.find 2590 left = VM.find 2590 right ->
 VM.find 2596 left = VM.find 2596 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2597 next_left = VM.find 2597 next_right.
Proof.
 intros H2590 H2596 E2044 E2590 E2596 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2597 reference_control_expr_2597 reference_control_2_positions reference_control_2_safety reference_control_member_2597) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2597 reference_control_expr_2597 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2597 left H2590 H2596)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2597 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2044.
 rewrite E2590.
 rewrite E2596.
 reflexivity.
Qed.
Lemma reference_control_ready_2598 old :
 (exists value ground, VM.find 2589 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2597 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2598.
Proof.
 intros H2589 H2597.
 destruct H2589 as [v2589 [G2589 [V2589 T2589]]].
 destruct H2597 as [v2597 [G2597 [V2597 T2597]]].
 unfold reference_control_expr_2598.
apply rc_mux.
{ eapply rc_ref; [exact V2589|exists G2589; exact T2589].
}
{ eapply rc_ref; [exact V2597|exists G2597; exact T2597].
}
Qed.
Lemma reference_control_member_2598 : List.In (2598,reference_control_expr_2598) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 115%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2598_ground inputs path old current result :
 (exists value ground, VM.find 2589 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2597 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2598 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2589 H2597 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2598 reference_control_expr_2598 reference_control_2_positions reference_control_2_safety reference_control_member_2598) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2598 reference_control_expr_2598 inputs path old current result Position Safe Nonreg (reference_control_ready_2598 old H2589 H2597) Step).
Qed.
Theorem reference_control_node_2598_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2589 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2597 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2039 left = VM.find 2039 right ->
 VM.find 2589 left = VM.find 2589 right ->
 VM.find 2597 left = VM.find 2597 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2598 next_left = VM.find 2598 next_right.
Proof.
 intros H2589 H2597 E2039 E2589 E2597 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2598 reference_control_expr_2598 reference_control_2_positions reference_control_2_safety reference_control_member_2598) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2598 reference_control_expr_2598 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2598 left H2589 H2597)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2598 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2039.
 rewrite E2589.
 rewrite E2597.
 reflexivity.
Qed.
Lemma reference_control_ready_2599 old :
 (exists value ground, VM.find 2588 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2598 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2599.
Proof.
 intros H2588 H2598.
 destruct H2588 as [v2588 [G2588 [V2588 T2588]]].
 destruct H2598 as [v2598 [G2598 [V2598 T2598]]].
 unfold reference_control_expr_2599.
apply rc_mux.
{ eapply rc_ref; [exact V2588|exists G2588; exact T2588].
}
{ eapply rc_ref; [exact V2598|exists G2598; exact T2598].
}
Qed.
Lemma reference_control_member_2599 : List.In (2599,reference_control_expr_2599) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 116%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2599_ground inputs path old current result :
 (exists value ground, VM.find 2588 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2598 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2599 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2588 H2598 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2599 reference_control_expr_2599 reference_control_2_positions reference_control_2_safety reference_control_member_2599) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2599 reference_control_expr_2599 inputs path old current result Position Safe Nonreg (reference_control_ready_2599 old H2588 H2598) Step).
Qed.
Theorem reference_control_node_2599_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2588 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2598 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2034 left = VM.find 2034 right ->
 VM.find 2588 left = VM.find 2588 right ->
 VM.find 2598 left = VM.find 2598 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2599 next_left = VM.find 2599 next_right.
Proof.
 intros H2588 H2598 E2034 E2588 E2598 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2599 reference_control_expr_2599 reference_control_2_positions reference_control_2_safety reference_control_member_2599) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2599 reference_control_expr_2599 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2599 left H2588 H2598)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2599 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2034.
 rewrite E2588.
 rewrite E2598.
 reflexivity.
Qed.
Lemma reference_control_ready_2600 old :
 (exists value ground, VM.find 2587 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2599 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2600.
Proof.
 intros H2587 H2599.
 destruct H2587 as [v2587 [G2587 [V2587 T2587]]].
 destruct H2599 as [v2599 [G2599 [V2599 T2599]]].
 unfold reference_control_expr_2600.
apply rc_mux.
{ eapply rc_ref; [exact V2587|exists G2587; exact T2587].
}
{ eapply rc_ref; [exact V2599|exists G2599; exact T2599].
}
Qed.
Lemma reference_control_member_2600 : List.In (2600,reference_control_expr_2600) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 117%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2600_ground inputs path old current result :
 (exists value ground, VM.find 2587 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2599 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2600 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2587 H2599 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2600 reference_control_expr_2600 reference_control_2_positions reference_control_2_safety reference_control_member_2600) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2600 reference_control_expr_2600 inputs path old current result Position Safe Nonreg (reference_control_ready_2600 old H2587 H2599) Step).
Qed.
Theorem reference_control_node_2600_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2587 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2599 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2029 left = VM.find 2029 right ->
 VM.find 2587 left = VM.find 2587 right ->
 VM.find 2599 left = VM.find 2599 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2600 next_left = VM.find 2600 next_right.
Proof.
 intros H2587 H2599 E2029 E2587 E2599 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2600 reference_control_expr_2600 reference_control_2_positions reference_control_2_safety reference_control_member_2600) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2600 reference_control_expr_2600 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2600 left H2587 H2599)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2600 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2029.
 rewrite E2587.
 rewrite E2599.
 reflexivity.
Qed.
Lemma reference_control_ready_2601 old :
 (exists value ground, VM.find 2586 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2600 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2601.
Proof.
 intros H2586 H2600.
 destruct H2586 as [v2586 [G2586 [V2586 T2586]]].
 destruct H2600 as [v2600 [G2600 [V2600 T2600]]].
 unfold reference_control_expr_2601.
apply rc_mux.
{ eapply rc_ref; [exact V2586|exists G2586; exact T2586].
}
{ eapply rc_ref; [exact V2600|exists G2600; exact T2600].
}
Qed.
Lemma reference_control_member_2601 : List.In (2601,reference_control_expr_2601) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 118%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2601_ground inputs path old current result :
 (exists value ground, VM.find 2586 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2600 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2601 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2586 H2600 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2601 reference_control_expr_2601 reference_control_2_positions reference_control_2_safety reference_control_member_2601) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2601 reference_control_expr_2601 inputs path old current result Position Safe Nonreg (reference_control_ready_2601 old H2586 H2600) Step).
Qed.
Theorem reference_control_node_2601_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2586 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2600 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2024 left = VM.find 2024 right ->
 VM.find 2586 left = VM.find 2586 right ->
 VM.find 2600 left = VM.find 2600 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2601 next_left = VM.find 2601 next_right.
Proof.
 intros H2586 H2600 E2024 E2586 E2600 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2601 reference_control_expr_2601 reference_control_2_positions reference_control_2_safety reference_control_member_2601) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2601 reference_control_expr_2601 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2601 left H2586 H2600)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2601 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2024.
 rewrite E2586.
 rewrite E2600.
 reflexivity.
Qed.
Lemma reference_control_ready_2602 old :
 (exists value ground, VM.find 2585 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2601 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2602.
Proof.
 intros H2585 H2601.
 destruct H2585 as [v2585 [G2585 [V2585 T2585]]].
 destruct H2601 as [v2601 [G2601 [V2601 T2601]]].
 unfold reference_control_expr_2602.
apply rc_mux.
{ eapply rc_ref; [exact V2585|exists G2585; exact T2585].
}
{ eapply rc_ref; [exact V2601|exists G2601; exact T2601].
}
Qed.
Lemma reference_control_member_2602 : List.In (2602,reference_control_expr_2602) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 119%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2602_ground inputs path old current result :
 (exists value ground, VM.find 2585 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2601 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2602 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2585 H2601 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2602 reference_control_expr_2602 reference_control_2_positions reference_control_2_safety reference_control_member_2602) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2602 reference_control_expr_2602 inputs path old current result Position Safe Nonreg (reference_control_ready_2602 old H2585 H2601) Step).
Qed.
Theorem reference_control_node_2602_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2585 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2601 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2019 left = VM.find 2019 right ->
 VM.find 2585 left = VM.find 2585 right ->
 VM.find 2601 left = VM.find 2601 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2602 next_left = VM.find 2602 next_right.
Proof.
 intros H2585 H2601 E2019 E2585 E2601 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2602 reference_control_expr_2602 reference_control_2_positions reference_control_2_safety reference_control_member_2602) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2602 reference_control_expr_2602 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2602 left H2585 H2601)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2602 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2019.
 rewrite E2585.
 rewrite E2601.
 reflexivity.
Qed.
Lemma reference_control_ready_2603 old :
 (exists value ground, VM.find 2584 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2602 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2603.
Proof.
 intros H2584 H2602.
 destruct H2584 as [v2584 [G2584 [V2584 T2584]]].
 destruct H2602 as [v2602 [G2602 [V2602 T2602]]].
 unfold reference_control_expr_2603.
apply rc_mux.
{ eapply rc_ref; [exact V2584|exists G2584; exact T2584].
}
{ eapply rc_ref; [exact V2602|exists G2602; exact T2602].
}
Qed.
Lemma reference_control_member_2603 : List.In (2603,reference_control_expr_2603) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 120%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2603_ground inputs path old current result :
 (exists value ground, VM.find 2584 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2602 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2603 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2584 H2602 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2603 reference_control_expr_2603 reference_control_2_positions reference_control_2_safety reference_control_member_2603) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2603 reference_control_expr_2603 inputs path old current result Position Safe Nonreg (reference_control_ready_2603 old H2584 H2602) Step).
Qed.
Theorem reference_control_node_2603_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2584 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2602 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2014 left = VM.find 2014 right ->
 VM.find 2584 left = VM.find 2584 right ->
 VM.find 2602 left = VM.find 2602 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2603 next_left = VM.find 2603 next_right.
Proof.
 intros H2584 H2602 E2014 E2584 E2602 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2603 reference_control_expr_2603 reference_control_2_positions reference_control_2_safety reference_control_member_2603) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2603 reference_control_expr_2603 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2603 left H2584 H2602)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2603 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2014.
 rewrite E2584.
 rewrite E2602.
 reflexivity.
Qed.
Lemma reference_control_ready_2604 old :
 (exists value ground, VM.find 2583 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2603 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2604.
Proof.
 intros H2583 H2603.
 destruct H2583 as [v2583 [G2583 [V2583 T2583]]].
 destruct H2603 as [v2603 [G2603 [V2603 T2603]]].
 unfold reference_control_expr_2604.
apply rc_mux.
{ eapply rc_ref; [exact V2583|exists G2583; exact T2583].
}
{ eapply rc_ref; [exact V2603|exists G2603; exact T2603].
}
Qed.
Lemma reference_control_member_2604 : List.In (2604,reference_control_expr_2604) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 121%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2604_ground inputs path old current result :
 (exists value ground, VM.find 2583 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2603 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2604 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2583 H2603 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2604 reference_control_expr_2604 reference_control_2_positions reference_control_2_safety reference_control_member_2604) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2604 reference_control_expr_2604 inputs path old current result Position Safe Nonreg (reference_control_ready_2604 old H2583 H2603) Step).
Qed.
Theorem reference_control_node_2604_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2583 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2603 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2004 left = VM.find 2004 right ->
 VM.find 2583 left = VM.find 2583 right ->
 VM.find 2603 left = VM.find 2603 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2604 next_left = VM.find 2604 next_right.
Proof.
 intros H2583 H2603 E2004 E2583 E2603 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2604 reference_control_expr_2604 reference_control_2_positions reference_control_2_safety reference_control_member_2604) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2604 reference_control_expr_2604 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2604 left H2583 H2603)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2604 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2004.
 rewrite E2583.
 rewrite E2603.
 reflexivity.
Qed.
Lemma reference_control_ready_2605 old :
 (exists value ground, VM.find 2582 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2604 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2605.
Proof.
 intros H2582 H2604.
 destruct H2582 as [v2582 [G2582 [V2582 T2582]]].
 destruct H2604 as [v2604 [G2604 [V2604 T2604]]].
 unfold reference_control_expr_2605.
apply rc_mux.
{ eapply rc_ref; [exact V2582|exists G2582; exact T2582].
}
{ eapply rc_ref; [exact V2604|exists G2604; exact T2604].
}
Qed.
Lemma reference_control_member_2605 : List.In (2605,reference_control_expr_2605) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 122%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2605_ground inputs path old current result :
 (exists value ground, VM.find 2582 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2604 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2605 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2582 H2604 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2605 reference_control_expr_2605 reference_control_2_positions reference_control_2_safety reference_control_member_2605) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2605 reference_control_expr_2605 inputs path old current result Position Safe Nonreg (reference_control_ready_2605 old H2582 H2604) Step).
Qed.
Theorem reference_control_node_2605_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2582 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2604 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1998 left = VM.find 1998 right ->
 VM.find 2582 left = VM.find 2582 right ->
 VM.find 2604 left = VM.find 2604 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2605 next_left = VM.find 2605 next_right.
Proof.
 intros H2582 H2604 E1998 E2582 E2604 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2605 reference_control_expr_2605 reference_control_2_positions reference_control_2_safety reference_control_member_2605) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2605 reference_control_expr_2605 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2605 left H2582 H2604)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2605 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1998.
 rewrite E2582.
 rewrite E2604.
 reflexivity.
Qed.
Lemma reference_control_ready_2606 old :
 (exists value ground, VM.find 2581 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2605 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2606.
Proof.
 intros H2581 H2605.
 destruct H2581 as [v2581 [G2581 [V2581 T2581]]].
 destruct H2605 as [v2605 [G2605 [V2605 T2605]]].
 unfold reference_control_expr_2606.
apply rc_mux.
{ eapply rc_ref; [exact V2581|exists G2581; exact T2581].
}
{ eapply rc_ref; [exact V2605|exists G2605; exact T2605].
}
Qed.
Lemma reference_control_member_2606 : List.In (2606,reference_control_expr_2606) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 123%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2606_ground inputs path old current result :
 (exists value ground, VM.find 2581 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2605 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2606 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2581 H2605 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2606 reference_control_expr_2606 reference_control_2_positions reference_control_2_safety reference_control_member_2606) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2606 reference_control_expr_2606 inputs path old current result Position Safe Nonreg (reference_control_ready_2606 old H2581 H2605) Step).
Qed.
Theorem reference_control_node_2606_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2581 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2605 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1992 left = VM.find 1992 right ->
 VM.find 2581 left = VM.find 2581 right ->
 VM.find 2605 left = VM.find 2605 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2606 next_left = VM.find 2606 next_right.
Proof.
 intros H2581 H2605 E1992 E2581 E2605 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2606 reference_control_expr_2606 reference_control_2_positions reference_control_2_safety reference_control_member_2606) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2606 reference_control_expr_2606 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2606 left H2581 H2605)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2606 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1992.
 rewrite E2581.
 rewrite E2605.
 reflexivity.
Qed.
Lemma reference_control_ready_2607 old :
 (exists value ground, VM.find 2580 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2606 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2607.
Proof.
 intros H2580 H2606.
 destruct H2580 as [v2580 [G2580 [V2580 T2580]]].
 destruct H2606 as [v2606 [G2606 [V2606 T2606]]].
 unfold reference_control_expr_2607.
apply rc_mux.
{ eapply rc_ref; [exact V2580|exists G2580; exact T2580].
}
{ eapply rc_ref; [exact V2606|exists G2606; exact T2606].
}
Qed.
Lemma reference_control_member_2607 : List.In (2607,reference_control_expr_2607) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 124%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2607_ground inputs path old current result :
 (exists value ground, VM.find 2580 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2606 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2607 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2580 H2606 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2607 reference_control_expr_2607 reference_control_2_positions reference_control_2_safety reference_control_member_2607) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2607 reference_control_expr_2607 inputs path old current result Position Safe Nonreg (reference_control_ready_2607 old H2580 H2606) Step).
Qed.
Theorem reference_control_node_2607_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2580 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2606 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1986 left = VM.find 1986 right ->
 VM.find 2580 left = VM.find 2580 right ->
 VM.find 2606 left = VM.find 2606 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2607 next_left = VM.find 2607 next_right.
Proof.
 intros H2580 H2606 E1986 E2580 E2606 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2607 reference_control_expr_2607 reference_control_2_positions reference_control_2_safety reference_control_member_2607) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2607 reference_control_expr_2607 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2607 left H2580 H2606)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2607 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1986.
 rewrite E2580.
 rewrite E2606.
 reflexivity.
Qed.
Lemma reference_control_ready_2608 old :
 (exists value ground, VM.find 2579 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2607 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2608.
Proof.
 intros H2579 H2607.
 destruct H2579 as [v2579 [G2579 [V2579 T2579]]].
 destruct H2607 as [v2607 [G2607 [V2607 T2607]]].
 unfold reference_control_expr_2608.
apply rc_mux.
{ eapply rc_ref; [exact V2579|exists G2579; exact T2579].
}
{ eapply rc_ref; [exact V2607|exists G2607; exact T2607].
}
Qed.
Lemma reference_control_member_2608 : List.In (2608,reference_control_expr_2608) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 125%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2608_ground inputs path old current result :
 (exists value ground, VM.find 2579 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2607 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2608 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2579 H2607 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2608 reference_control_expr_2608 reference_control_2_positions reference_control_2_safety reference_control_member_2608) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2608 reference_control_expr_2608 inputs path old current result Position Safe Nonreg (reference_control_ready_2608 old H2579 H2607) Step).
Qed.
Theorem reference_control_node_2608_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2579 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2607 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1980 left = VM.find 1980 right ->
 VM.find 2579 left = VM.find 2579 right ->
 VM.find 2607 left = VM.find 2607 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2608 next_left = VM.find 2608 next_right.
Proof.
 intros H2579 H2607 E1980 E2579 E2607 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2608 reference_control_expr_2608 reference_control_2_positions reference_control_2_safety reference_control_member_2608) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2608 reference_control_expr_2608 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2608 left H2579 H2607)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2608 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1980.
 rewrite E2579.
 rewrite E2607.
 reflexivity.
Qed.
Lemma reference_control_ready_2609 old :
 (exists value ground, VM.find 2578 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2608 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2609.
Proof.
 intros H2578 H2608.
 destruct H2578 as [v2578 [G2578 [V2578 T2578]]].
 destruct H2608 as [v2608 [G2608 [V2608 T2608]]].
 unfold reference_control_expr_2609.
apply rc_mux.
{ eapply rc_ref; [exact V2578|exists G2578; exact T2578].
}
{ eapply rc_ref; [exact V2608|exists G2608; exact T2608].
}
Qed.
Lemma reference_control_member_2609 : List.In (2609,reference_control_expr_2609) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 126%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2609_ground inputs path old current result :
 (exists value ground, VM.find 2578 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2608 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2609 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2578 H2608 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2609 reference_control_expr_2609 reference_control_2_positions reference_control_2_safety reference_control_member_2609) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2609 reference_control_expr_2609 inputs path old current result Position Safe Nonreg (reference_control_ready_2609 old H2578 H2608) Step).
Qed.
Theorem reference_control_node_2609_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2578 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2608 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1974 left = VM.find 1974 right ->
 VM.find 2578 left = VM.find 2578 right ->
 VM.find 2608 left = VM.find 2608 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2609 next_left = VM.find 2609 next_right.
Proof.
 intros H2578 H2608 E1974 E2578 E2608 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2609 reference_control_expr_2609 reference_control_2_positions reference_control_2_safety reference_control_member_2609) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2609 reference_control_expr_2609 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2609 left H2578 H2608)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2609 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1974.
 rewrite E2578.
 rewrite E2608.
 reflexivity.
Qed.
Lemma reference_control_ready_2610 old :
 (exists value ground, VM.find 2577 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2609 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2610.
Proof.
 intros H2577 H2609.
 destruct H2577 as [v2577 [G2577 [V2577 T2577]]].
 destruct H2609 as [v2609 [G2609 [V2609 T2609]]].
 unfold reference_control_expr_2610.
apply rc_mux.
{ eapply rc_ref; [exact V2577|exists G2577; exact T2577].
}
{ eapply rc_ref; [exact V2609|exists G2609; exact T2609].
}
Qed.
Lemma reference_control_member_2610 : List.In (2610,reference_control_expr_2610) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 127%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2610_ground inputs path old current result :
 (exists value ground, VM.find 2577 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2609 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2610 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2577 H2609 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2610 reference_control_expr_2610 reference_control_2_positions reference_control_2_safety reference_control_member_2610) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2610 reference_control_expr_2610 inputs path old current result Position Safe Nonreg (reference_control_ready_2610 old H2577 H2609) Step).
Qed.
Theorem reference_control_node_2610_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2577 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2609 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1951 left = VM.find 1951 right ->
 VM.find 2577 left = VM.find 2577 right ->
 VM.find 2609 left = VM.find 2609 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2610 next_left = VM.find 2610 next_right.
Proof.
 intros H2577 H2609 E1951 E2577 E2609 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2610 reference_control_expr_2610 reference_control_2_positions reference_control_2_safety reference_control_member_2610) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2610 reference_control_expr_2610 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2610 left H2577 H2609)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2610 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1951.
 rewrite E2577.
 rewrite E2609.
 reflexivity.
Qed.
Lemma reference_control_ready_2611 old :
 (exists value ground, VM.find 2576 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2610 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2611.
Proof.
 intros H2576 H2610.
 destruct H2576 as [v2576 [G2576 [V2576 T2576]]].
 destruct H2610 as [v2610 [G2610 [V2610 T2610]]].
 unfold reference_control_expr_2611.
apply rc_mux.
{ eapply rc_ref; [exact V2576|exists G2576; exact T2576].
}
{ eapply rc_ref; [exact V2610|exists G2610; exact T2610].
}
Qed.
Lemma reference_control_member_2611 : List.In (2611,reference_control_expr_2611) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 128%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2611_ground inputs path old current result :
 (exists value ground, VM.find 2576 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2610 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2611 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2576 H2610 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2611 reference_control_expr_2611 reference_control_2_positions reference_control_2_safety reference_control_member_2611) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2611 reference_control_expr_2611 inputs path old current result Position Safe Nonreg (reference_control_ready_2611 old H2576 H2610) Step).
Qed.
Theorem reference_control_node_2611_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2576 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2610 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1946 left = VM.find 1946 right ->
 VM.find 2576 left = VM.find 2576 right ->
 VM.find 2610 left = VM.find 2610 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2611 next_left = VM.find 2611 next_right.
Proof.
 intros H2576 H2610 E1946 E2576 E2610 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2611 reference_control_expr_2611 reference_control_2_positions reference_control_2_safety reference_control_member_2611) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2611 reference_control_expr_2611 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2611 left H2576 H2610)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2611 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1946.
 rewrite E2576.
 rewrite E2610.
 reflexivity.
Qed.
Lemma reference_control_ready_2612 old :
 (exists value ground, VM.find 2575 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2611 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2612.
Proof.
 intros H2575 H2611.
 destruct H2575 as [v2575 [G2575 [V2575 T2575]]].
 destruct H2611 as [v2611 [G2611 [V2611 T2611]]].
 unfold reference_control_expr_2612.
apply rc_mux.
{ eapply rc_ref; [exact V2575|exists G2575; exact T2575].
}
{ eapply rc_ref; [exact V2611|exists G2611; exact T2611].
}
Qed.
Lemma reference_control_member_2612 : List.In (2612,reference_control_expr_2612) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 129%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2612_ground inputs path old current result :
 (exists value ground, VM.find 2575 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2611 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2612 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2575 H2611 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2612 reference_control_expr_2612 reference_control_2_positions reference_control_2_safety reference_control_member_2612) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2612 reference_control_expr_2612 inputs path old current result Position Safe Nonreg (reference_control_ready_2612 old H2575 H2611) Step).
Qed.
Theorem reference_control_node_2612_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2575 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2611 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1941 left = VM.find 1941 right ->
 VM.find 2575 left = VM.find 2575 right ->
 VM.find 2611 left = VM.find 2611 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2612 next_left = VM.find 2612 next_right.
Proof.
 intros H2575 H2611 E1941 E2575 E2611 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2612 reference_control_expr_2612 reference_control_2_positions reference_control_2_safety reference_control_member_2612) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2612 reference_control_expr_2612 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2612 left H2575 H2611)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2612 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1941.
 rewrite E2575.
 rewrite E2611.
 reflexivity.
Qed.
Lemma reference_control_ready_2613 old :
 (exists value ground, VM.find 2574 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2612 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2613.
Proof.
 intros H2574 H2612.
 destruct H2574 as [v2574 [G2574 [V2574 T2574]]].
 destruct H2612 as [v2612 [G2612 [V2612 T2612]]].
 unfold reference_control_expr_2613.
apply rc_mux.
{ eapply rc_ref; [exact V2574|exists G2574; exact T2574].
}
{ eapply rc_ref; [exact V2612|exists G2612; exact T2612].
}
Qed.
Lemma reference_control_member_2613 : List.In (2613,reference_control_expr_2613) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 130%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2613_ground inputs path old current result :
 (exists value ground, VM.find 2574 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2612 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2613 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2574 H2612 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2613 reference_control_expr_2613 reference_control_2_positions reference_control_2_safety reference_control_member_2613) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2613 reference_control_expr_2613 inputs path old current result Position Safe Nonreg (reference_control_ready_2613 old H2574 H2612) Step).
Qed.
Theorem reference_control_node_2613_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2574 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2612 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1924 left = VM.find 1924 right ->
 VM.find 2574 left = VM.find 2574 right ->
 VM.find 2612 left = VM.find 2612 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2613 next_left = VM.find 2613 next_right.
Proof.
 intros H2574 H2612 E1924 E2574 E2612 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2613 reference_control_expr_2613 reference_control_2_positions reference_control_2_safety reference_control_member_2613) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2613 reference_control_expr_2613 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2613 left H2574 H2612)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2613 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1924.
 rewrite E2574.
 rewrite E2612.
 reflexivity.
Qed.
Lemma reference_control_ready_2614 old :
 (exists value ground, VM.find 2573 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2613 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2614.
Proof.
 intros H2573 H2613.
 destruct H2573 as [v2573 [G2573 [V2573 T2573]]].
 destruct H2613 as [v2613 [G2613 [V2613 T2613]]].
 unfold reference_control_expr_2614.
apply rc_mux.
{ eapply rc_ref; [exact V2573|exists G2573; exact T2573].
}
{ eapply rc_ref; [exact V2613|exists G2613; exact T2613].
}
Qed.
Lemma reference_control_member_2614 : List.In (2614,reference_control_expr_2614) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 131%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2614_ground inputs path old current result :
 (exists value ground, VM.find 2573 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2613 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2614 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2573 H2613 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2614 reference_control_expr_2614 reference_control_2_positions reference_control_2_safety reference_control_member_2614) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2614 reference_control_expr_2614 inputs path old current result Position Safe Nonreg (reference_control_ready_2614 old H2573 H2613) Step).
Qed.
Theorem reference_control_node_2614_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2573 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2613 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1919 left = VM.find 1919 right ->
 VM.find 2573 left = VM.find 2573 right ->
 VM.find 2613 left = VM.find 2613 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2614 next_left = VM.find 2614 next_right.
Proof.
 intros H2573 H2613 E1919 E2573 E2613 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2614 reference_control_expr_2614 reference_control_2_positions reference_control_2_safety reference_control_member_2614) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2614 reference_control_expr_2614 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2614 left H2573 H2613)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2614 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1919.
 rewrite E2573.
 rewrite E2613.
 reflexivity.
Qed.
Lemma reference_control_ready_2615 old :
 (exists value ground, VM.find 2572 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2614 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2615.
Proof.
 intros H2572 H2614.
 destruct H2572 as [v2572 [G2572 [V2572 T2572]]].
 destruct H2614 as [v2614 [G2614 [V2614 T2614]]].
 unfold reference_control_expr_2615.
apply rc_mux.
{ eapply rc_ref; [exact V2572|exists G2572; exact T2572].
}
{ eapply rc_ref; [exact V2614|exists G2614; exact T2614].
}
Qed.
Lemma reference_control_member_2615 : List.In (2615,reference_control_expr_2615) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 132%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2615_ground inputs path old current result :
 (exists value ground, VM.find 2572 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2614 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2615 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2572 H2614 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2615 reference_control_expr_2615 reference_control_2_positions reference_control_2_safety reference_control_member_2615) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2615 reference_control_expr_2615 inputs path old current result Position Safe Nonreg (reference_control_ready_2615 old H2572 H2614) Step).
Qed.
Theorem reference_control_node_2615_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2572 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2614 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1914 left = VM.find 1914 right ->
 VM.find 2572 left = VM.find 2572 right ->
 VM.find 2614 left = VM.find 2614 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2615 next_left = VM.find 2615 next_right.
Proof.
 intros H2572 H2614 E1914 E2572 E2614 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2615 reference_control_expr_2615 reference_control_2_positions reference_control_2_safety reference_control_member_2615) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2615 reference_control_expr_2615 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2615 left H2572 H2614)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2615 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1914.
 rewrite E2572.
 rewrite E2614.
 reflexivity.
Qed.
Lemma reference_control_ready_2616 old :
 (exists value ground, VM.find 2571 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2615 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2616.
Proof.
 intros H2571 H2615.
 destruct H2571 as [v2571 [G2571 [V2571 T2571]]].
 destruct H2615 as [v2615 [G2615 [V2615 T2615]]].
 unfold reference_control_expr_2616.
apply rc_mux.
{ eapply rc_ref; [exact V2571|exists G2571; exact T2571].
}
{ eapply rc_ref; [exact V2615|exists G2615; exact T2615].
}
Qed.
Lemma reference_control_member_2616 : List.In (2616,reference_control_expr_2616) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 133%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2616_ground inputs path old current result :
 (exists value ground, VM.find 2571 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2615 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2616 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2571 H2615 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2616 reference_control_expr_2616 reference_control_2_positions reference_control_2_safety reference_control_member_2616) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2616 reference_control_expr_2616 inputs path old current result Position Safe Nonreg (reference_control_ready_2616 old H2571 H2615) Step).
Qed.
Theorem reference_control_node_2616_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2571 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2615 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1909 left = VM.find 1909 right ->
 VM.find 2571 left = VM.find 2571 right ->
 VM.find 2615 left = VM.find 2615 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2616 next_left = VM.find 2616 next_right.
Proof.
 intros H2571 H2615 E1909 E2571 E2615 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2616 reference_control_expr_2616 reference_control_2_positions reference_control_2_safety reference_control_member_2616) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2616 reference_control_expr_2616 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2616 left H2571 H2615)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2616 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1909.
 rewrite E2571.
 rewrite E2615.
 reflexivity.
Qed.
Lemma reference_control_ready_2617 old :
 (exists value ground, VM.find 2570 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2616 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2617.
Proof.
 intros H2570 H2616.
 destruct H2570 as [v2570 [G2570 [V2570 T2570]]].
 destruct H2616 as [v2616 [G2616 [V2616 T2616]]].
 unfold reference_control_expr_2617.
apply rc_mux.
{ eapply rc_ref; [exact V2570|exists G2570; exact T2570].
}
{ eapply rc_ref; [exact V2616|exists G2616; exact T2616].
}
Qed.
Lemma reference_control_member_2617 : List.In (2617,reference_control_expr_2617) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 134%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2617_ground inputs path old current result :
 (exists value ground, VM.find 2570 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2616 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2617 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2570 H2616 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2617 reference_control_expr_2617 reference_control_2_positions reference_control_2_safety reference_control_member_2617) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2617 reference_control_expr_2617 inputs path old current result Position Safe Nonreg (reference_control_ready_2617 old H2570 H2616) Step).
Qed.
Theorem reference_control_node_2617_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2570 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2616 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1904 left = VM.find 1904 right ->
 VM.find 2570 left = VM.find 2570 right ->
 VM.find 2616 left = VM.find 2616 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2617 next_left = VM.find 2617 next_right.
Proof.
 intros H2570 H2616 E1904 E2570 E2616 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2617 reference_control_expr_2617 reference_control_2_positions reference_control_2_safety reference_control_member_2617) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2617 reference_control_expr_2617 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2617 left H2570 H2616)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2617 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1904.
 rewrite E2570.
 rewrite E2616.
 reflexivity.
Qed.
Lemma reference_control_ready_2618 old :
 (exists value ground, VM.find 2569 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2617 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2618.
Proof.
 intros H2569 H2617.
 destruct H2569 as [v2569 [G2569 [V2569 T2569]]].
 destruct H2617 as [v2617 [G2617 [V2617 T2617]]].
 unfold reference_control_expr_2618.
apply rc_mux.
{ eapply rc_ref; [exact V2569|exists G2569; exact T2569].
}
{ eapply rc_ref; [exact V2617|exists G2617; exact T2617].
}
Qed.
Lemma reference_control_member_2618 : List.In (2618,reference_control_expr_2618) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 135%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2618_ground inputs path old current result :
 (exists value ground, VM.find 2569 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2617 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2618 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2569 H2617 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2618 reference_control_expr_2618 reference_control_2_positions reference_control_2_safety reference_control_member_2618) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2618 reference_control_expr_2618 inputs path old current result Position Safe Nonreg (reference_control_ready_2618 old H2569 H2617) Step).
Qed.
Theorem reference_control_node_2618_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2569 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2617 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1899 left = VM.find 1899 right ->
 VM.find 2569 left = VM.find 2569 right ->
 VM.find 2617 left = VM.find 2617 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2618 next_left = VM.find 2618 next_right.
Proof.
 intros H2569 H2617 E1899 E2569 E2617 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2618 reference_control_expr_2618 reference_control_2_positions reference_control_2_safety reference_control_member_2618) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2618 reference_control_expr_2618 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2618 left H2569 H2617)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2618 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1899.
 rewrite E2569.
 rewrite E2617.
 reflexivity.
Qed.
Lemma reference_control_ready_2619 old :
 (exists value ground, VM.find 2568 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2618 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2619.
Proof.
 intros H2568 H2618.
 destruct H2568 as [v2568 [G2568 [V2568 T2568]]].
 destruct H2618 as [v2618 [G2618 [V2618 T2618]]].
 unfold reference_control_expr_2619.
apply rc_mux.
{ eapply rc_ref; [exact V2568|exists G2568; exact T2568].
}
{ eapply rc_ref; [exact V2618|exists G2618; exact T2618].
}
Qed.
Lemma reference_control_member_2619 : List.In (2619,reference_control_expr_2619) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 136%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2619_ground inputs path old current result :
 (exists value ground, VM.find 2568 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2618 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2619 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2568 H2618 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2619 reference_control_expr_2619 reference_control_2_positions reference_control_2_safety reference_control_member_2619) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2619 reference_control_expr_2619 inputs path old current result Position Safe Nonreg (reference_control_ready_2619 old H2568 H2618) Step).
Qed.
Theorem reference_control_node_2619_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2568 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2618 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1894 left = VM.find 1894 right ->
 VM.find 2568 left = VM.find 2568 right ->
 VM.find 2618 left = VM.find 2618 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2619 next_left = VM.find 2619 next_right.
Proof.
 intros H2568 H2618 E1894 E2568 E2618 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2619 reference_control_expr_2619 reference_control_2_positions reference_control_2_safety reference_control_member_2619) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2619 reference_control_expr_2619 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2619 left H2568 H2618)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2619 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1894.
 rewrite E2568.
 rewrite E2618.
 reflexivity.
Qed.
Lemma reference_control_ready_2620 old :
 (exists value ground, VM.find 2567 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2619 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2620.
Proof.
 intros H2567 H2619.
 destruct H2567 as [v2567 [G2567 [V2567 T2567]]].
 destruct H2619 as [v2619 [G2619 [V2619 T2619]]].
 unfold reference_control_expr_2620.
apply rc_mux.
{ eapply rc_ref; [exact V2567|exists G2567; exact T2567].
}
{ eapply rc_ref; [exact V2619|exists G2619; exact T2619].
}
Qed.
Lemma reference_control_member_2620 : List.In (2620,reference_control_expr_2620) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 137%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2620_ground inputs path old current result :
 (exists value ground, VM.find 2567 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2619 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2620 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2567 H2619 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2620 reference_control_expr_2620 reference_control_2_positions reference_control_2_safety reference_control_member_2620) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2620 reference_control_expr_2620 inputs path old current result Position Safe Nonreg (reference_control_ready_2620 old H2567 H2619) Step).
Qed.
Theorem reference_control_node_2620_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2567 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2619 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1889 left = VM.find 1889 right ->
 VM.find 2567 left = VM.find 2567 right ->
 VM.find 2619 left = VM.find 2619 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2620 next_left = VM.find 2620 next_right.
Proof.
 intros H2567 H2619 E1889 E2567 E2619 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2620 reference_control_expr_2620 reference_control_2_positions reference_control_2_safety reference_control_member_2620) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2620 reference_control_expr_2620 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2620 left H2567 H2619)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2620 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1889.
 rewrite E2567.
 rewrite E2619.
 reflexivity.
Qed.
Lemma reference_control_ready_2621 old :
 (exists value ground, VM.find 2620 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2621.
Proof.
 intros H2620.
 destruct H2620 as [v2620 [G2620 [V2620 T2620]]].
 unfold reference_control_expr_2621.
apply rc_mux.
{ eapply rc_ref; [exact V2620|exists G2620; exact T2620].
}
{ apply rc_const.
}
Qed.
Lemma reference_control_member_2621 : List.In (2621,reference_control_expr_2621) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 138%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2621_ground inputs path old current result :
 (exists value ground, VM.find 2620 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2621 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2620 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2621 reference_control_expr_2621 reference_control_2_positions reference_control_2_safety reference_control_member_2621) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2621 reference_control_expr_2621 inputs path old current result Position Safe Nonreg (reference_control_ready_2621 old H2620) Step).
Qed.
Theorem reference_control_node_2621_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2620 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1707 left = VM.find 1707 right ->
 VM.find 2620 left = VM.find 2620 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2621 next_left = VM.find 2621 next_right.
Proof.
 intros H2620 E1707 E2620 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2621 reference_control_expr_2621 reference_control_2_positions reference_control_2_safety reference_control_member_2621) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2621 reference_control_expr_2621 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2621 left H2620)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2621 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1707.
 rewrite E2620.
 reflexivity.
Qed.
Lemma reference_control_ready_2622 old :
 (exists value ground, VM.find 2621 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2622.
Proof.
 intros H2621.
 destruct H2621 as [v2621 [G2621 [V2621 T2621]]].
 unfold reference_control_expr_2622.
eapply rc_ref; [exact V2621|exists G2621; exact T2621].
Qed.
Lemma reference_control_member_2622 : List.In (2622,reference_control_expr_2622) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 139%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2622_ground inputs path old current result :
 (exists value ground, VM.find 2621 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2622 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2621 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2622 reference_control_expr_2622 reference_control_2_positions reference_control_2_safety reference_control_member_2622) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2622 reference_control_expr_2622 inputs path old current result Position Safe Nonreg (reference_control_ready_2622 old H2621) Step).
Qed.
Theorem reference_control_node_2622_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2621 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2621 left = VM.find 2621 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2622 next_left = VM.find 2622 next_right.
Proof.
 intros H2621 E2621 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2622 reference_control_expr_2622 reference_control_2_positions reference_control_2_safety reference_control_member_2622) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2622 reference_control_expr_2622 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2622 left H2621)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2622 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2621.
 reflexivity.
Qed.
Lemma reference_control_ready_2623 old :
 reference_control_ready old reference_control_expr_2623.
Proof.
 unfold reference_control_expr_2623.
apply rc_unary.
Qed.
Lemma reference_control_member_2623 : List.In (2623,reference_control_expr_2623) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 140%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2623_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2623 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2623 reference_control_expr_2623 reference_control_2_positions reference_control_2_safety reference_control_member_2623) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2623 reference_control_expr_2623 inputs path old current result Position Safe Nonreg (reference_control_ready_2623 old ) Step).
Qed.
Theorem reference_control_node_2623_congruent inputs path left right next_left next_right :
 VM.find 2622 left = VM.find 2622 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2623 next_left = VM.find 2623 next_right.
Proof.
 intros  E2622 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2623 reference_control_expr_2623 reference_control_2_positions reference_control_2_safety reference_control_member_2623) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2623 reference_control_expr_2623 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2623 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2623 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2622.
 reflexivity.
Qed.
Lemma reference_control_ready_2624 old :
 reference_control_ready old reference_control_expr_2624.
Proof.
 unfold reference_control_expr_2624.
apply rc_binary.
Qed.
Lemma reference_control_member_2624 : List.In (2624,reference_control_expr_2624) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 141%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2624_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2624 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2624 reference_control_expr_2624 reference_control_2_positions reference_control_2_safety reference_control_member_2624) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2624 reference_control_expr_2624 inputs path old current result Position Safe Nonreg (reference_control_ready_2624 old ) Step).
Qed.
Theorem reference_control_node_2624_congruent inputs path left right next_left next_right :
 VM.find 2623 left = VM.find 2623 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2624 next_left = VM.find 2624 next_right.
Proof.
 intros  E2623 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2624 reference_control_expr_2624 reference_control_2_positions reference_control_2_safety reference_control_member_2624) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2624 reference_control_expr_2624 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2624 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2624 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2623.
 reflexivity.
Qed.
Lemma reference_control_ready_2625 old :
 reference_control_ready old reference_control_expr_2625.
Proof.
 unfold reference_control_expr_2625.
apply rc_binary.
Qed.
Lemma reference_control_member_2625 : List.In (2625,reference_control_expr_2625) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 142%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2625_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2625 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2625 reference_control_expr_2625 reference_control_2_positions reference_control_2_safety reference_control_member_2625) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2625 reference_control_expr_2625 inputs path old current result Position Safe Nonreg (reference_control_ready_2625 old ) Step).
Qed.
Theorem reference_control_node_2625_congruent inputs path left right next_left next_right :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2625 next_left = VM.find 2625 next_right.
Proof.
 intros   L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2625 reference_control_expr_2625 reference_control_2_positions reference_control_2_safety reference_control_member_2625) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2625 reference_control_expr_2625 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2625 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2625 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 reflexivity.
Qed.
Lemma reference_control_ready_2626 old :
 reference_control_ready old reference_control_expr_2626.
Proof.
 unfold reference_control_expr_2626.
apply rc_unary.
Qed.
Lemma reference_control_member_2626 : List.In (2626,reference_control_expr_2626) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 143%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2626_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2626 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2626 reference_control_expr_2626 reference_control_2_positions reference_control_2_safety reference_control_member_2626) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2626 reference_control_expr_2626 inputs path old current result Position Safe Nonreg (reference_control_ready_2626 old ) Step).
Qed.
Theorem reference_control_node_2626_congruent inputs path left right next_left next_right :
 VM.find 2622 left = VM.find 2622 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2626 next_left = VM.find 2626 next_right.
Proof.
 intros  E2622 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2626 reference_control_expr_2626 reference_control_2_positions reference_control_2_safety reference_control_member_2626) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2626 reference_control_expr_2626 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2626 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2626 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2622.
 reflexivity.
Qed.
Lemma reference_control_ready_2627 old :
 reference_control_ready old reference_control_expr_2627.
Proof.
 unfold reference_control_expr_2627.
apply rc_binary.
Qed.
Lemma reference_control_member_2627 : List.In (2627,reference_control_expr_2627) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 144%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2627_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2627 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2627 reference_control_expr_2627 reference_control_2_positions reference_control_2_safety reference_control_member_2627) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2627 reference_control_expr_2627 inputs path old current result Position Safe Nonreg (reference_control_ready_2627 old ) Step).
Qed.
Theorem reference_control_node_2627_congruent inputs path left right next_left next_right :
 VM.find 2626 left = VM.find 2626 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2627 next_left = VM.find 2627 next_right.
Proof.
 intros  E2626 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2627 reference_control_expr_2627 reference_control_2_positions reference_control_2_safety reference_control_member_2627) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2627 reference_control_expr_2627 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2627 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2627 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2626.
 reflexivity.
Qed.
Lemma reference_control_ready_2628 old :
 reference_control_ready old reference_control_expr_2628.
Proof.
 unfold reference_control_expr_2628.
apply rc_binary.
Qed.
Lemma reference_control_member_2628 : List.In (2628,reference_control_expr_2628) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 145%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2628_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2628 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2628 reference_control_expr_2628 reference_control_2_positions reference_control_2_safety reference_control_member_2628) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2628 reference_control_expr_2628 inputs path old current result Position Safe Nonreg (reference_control_ready_2628 old ) Step).
Qed.
Theorem reference_control_node_2628_congruent inputs path left right next_left next_right :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2628 next_left = VM.find 2628 next_right.
Proof.
 intros   L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2628 reference_control_expr_2628 reference_control_2_positions reference_control_2_safety reference_control_member_2628) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2628 reference_control_expr_2628 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2628 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2628 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 reflexivity.
Qed.
Lemma reference_control_ready_2629 old :
 reference_control_ready old reference_control_expr_2629.
Proof.
 unfold reference_control_expr_2629.
apply rc_unary.
Qed.
Lemma reference_control_member_2629 : List.In (2629,reference_control_expr_2629) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 146%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2629_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2629 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2629 reference_control_expr_2629 reference_control_2_positions reference_control_2_safety reference_control_member_2629) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2629 reference_control_expr_2629 inputs path old current result Position Safe Nonreg (reference_control_ready_2629 old ) Step).
Qed.
Theorem reference_control_node_2629_congruent inputs path left right next_left next_right :
 VM.find 2622 left = VM.find 2622 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2629 next_left = VM.find 2629 next_right.
Proof.
 intros  E2622 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2629 reference_control_expr_2629 reference_control_2_positions reference_control_2_safety reference_control_member_2629) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2629 reference_control_expr_2629 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2629 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2629 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2622.
 reflexivity.
Qed.
Lemma reference_control_ready_2630 old :
 reference_control_ready old reference_control_expr_2630.
Proof.
 unfold reference_control_expr_2630.
apply rc_binary.
Qed.
Lemma reference_control_member_2630 : List.In (2630,reference_control_expr_2630) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 147%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2630_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2630 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2630 reference_control_expr_2630 reference_control_2_positions reference_control_2_safety reference_control_member_2630) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2630 reference_control_expr_2630 inputs path old current result Position Safe Nonreg (reference_control_ready_2630 old ) Step).
Qed.
Theorem reference_control_node_2630_congruent inputs path left right next_left next_right :
 VM.find 2629 left = VM.find 2629 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2630 next_left = VM.find 2630 next_right.
Proof.
 intros  E2629 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2630 reference_control_expr_2630 reference_control_2_positions reference_control_2_safety reference_control_member_2630) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2630 reference_control_expr_2630 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2630 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2630 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2629.
 reflexivity.
Qed.
Lemma reference_control_ready_2631 old :
 (exists value ground, VM.find 2630 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2631.
Proof.
 intros H2630.
 destruct H2630 as [v2630 [G2630 [V2630 T2630]]].
 unfold reference_control_expr_2631.
apply rc_mux.
{ eapply rc_ref; [exact V2630|exists G2630; exact T2630].
}
{ apply rc_const.
}
Qed.
Lemma reference_control_member_2631 : List.In (2631,reference_control_expr_2631) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 148%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2631_ground inputs path old current result :
 (exists value ground, VM.find 2630 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2631 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2630 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2631 reference_control_expr_2631 reference_control_2_positions reference_control_2_safety reference_control_member_2631) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2631 reference_control_expr_2631 inputs path old current result Position Safe Nonreg (reference_control_ready_2631 old H2630) Step).
Qed.
Theorem reference_control_node_2631_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2630 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2628 left = VM.find 2628 right ->
 VM.find 2630 left = VM.find 2630 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2631 next_left = VM.find 2631 next_right.
Proof.
 intros H2630 E2628 E2630 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2631 reference_control_expr_2631 reference_control_2_positions reference_control_2_safety reference_control_member_2631) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2631 reference_control_expr_2631 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2631 left H2630)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2631 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2628.
 rewrite E2630.
 reflexivity.
Qed.
Lemma reference_control_ready_2632 old :
 (exists value ground, VM.find 2627 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2631 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2632.
Proof.
 intros H2627 H2631.
 destruct H2627 as [v2627 [G2627 [V2627 T2627]]].
 destruct H2631 as [v2631 [G2631 [V2631 T2631]]].
 unfold reference_control_expr_2632.
apply rc_mux.
{ eapply rc_ref; [exact V2627|exists G2627; exact T2627].
}
{ eapply rc_ref; [exact V2631|exists G2631; exact T2631].
}
Qed.
Lemma reference_control_member_2632 : List.In (2632,reference_control_expr_2632) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 149%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2632_ground inputs path old current result :
 (exists value ground, VM.find 2627 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2631 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2632 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2627 H2631 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2632 reference_control_expr_2632 reference_control_2_positions reference_control_2_safety reference_control_member_2632) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2632 reference_control_expr_2632 inputs path old current result Position Safe Nonreg (reference_control_ready_2632 old H2627 H2631) Step).
Qed.
Theorem reference_control_node_2632_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2627 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2631 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2625 left = VM.find 2625 right ->
 VM.find 2627 left = VM.find 2627 right ->
 VM.find 2631 left = VM.find 2631 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2632 next_left = VM.find 2632 next_right.
Proof.
 intros H2627 H2631 E2625 E2627 E2631 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2632 reference_control_expr_2632 reference_control_2_positions reference_control_2_safety reference_control_member_2632) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2632 reference_control_expr_2632 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2632 left H2627 H2631)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2632 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2625.
 rewrite E2627.
 rewrite E2631.
 reflexivity.
Qed.
Lemma reference_control_ready_2633 old :
 (exists value ground, VM.find 2624 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2632 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2633.
Proof.
 intros H2624 H2632.
 destruct H2624 as [v2624 [G2624 [V2624 T2624]]].
 destruct H2632 as [v2632 [G2632 [V2632 T2632]]].
 unfold reference_control_expr_2633.
apply rc_mux.
{ eapply rc_ref; [exact V2624|exists G2624; exact T2624].
}
{ eapply rc_ref; [exact V2632|exists G2632; exact T2632].
}
Qed.
Lemma reference_control_member_2633 : List.In (2633,reference_control_expr_2633) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 150%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2633_ground inputs path old current result :
 (exists value ground, VM.find 2624 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2632 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2633 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2624 H2632 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2633 reference_control_expr_2633 reference_control_2_positions reference_control_2_safety reference_control_member_2633) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2633 reference_control_expr_2633 inputs path old current result Position Safe Nonreg (reference_control_ready_2633 old H2624 H2632) Step).
Qed.
Theorem reference_control_node_2633_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2624 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2632 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2566 left = VM.find 2566 right ->
 VM.find 2624 left = VM.find 2624 right ->
 VM.find 2632 left = VM.find 2632 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2633 next_left = VM.find 2633 next_right.
Proof.
 intros H2624 H2632 E2566 E2624 E2632 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2633 reference_control_expr_2633 reference_control_2_positions reference_control_2_safety reference_control_member_2633) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2633 reference_control_expr_2633 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2633 left H2624 H2632)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2633 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2566.
 rewrite E2624.
 rewrite E2632.
 reflexivity.
Qed.
Lemma reference_control_ready_2634 old :
 reference_control_ready old reference_control_expr_2634.
Proof.
 unfold reference_control_expr_2634.
apply rc_binary.
Qed.
Lemma reference_control_member_2634 : List.In (2634,reference_control_expr_2634) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 151%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2634_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2634 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2634 reference_control_expr_2634 reference_control_2_positions reference_control_2_safety reference_control_member_2634) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2634 reference_control_expr_2634 inputs path old current result Position Safe Nonreg (reference_control_ready_2634 old ) Step).
Qed.
Theorem reference_control_node_2634_congruent inputs path left right next_left next_right :
 VM.find 2633 left = VM.find 2633 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2634 next_left = VM.find 2634 next_right.
Proof.
 intros  E2633 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2634 reference_control_expr_2634 reference_control_2_positions reference_control_2_safety reference_control_member_2634) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2634 reference_control_expr_2634 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2634 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2634 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2633.
 reflexivity.
Qed.
Lemma reference_control_ready_2635 old :
 reference_control_ready old reference_control_expr_2635.
Proof.
 unfold reference_control_expr_2635.
apply rc_binary.
Qed.
Lemma reference_control_member_2635 : List.In (2635,reference_control_expr_2635) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 152%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2635_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2635 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2635 reference_control_expr_2635 reference_control_2_positions reference_control_2_safety reference_control_member_2635) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2635 reference_control_expr_2635 inputs path old current result Position Safe Nonreg (reference_control_ready_2635 old ) Step).
Qed.
Theorem reference_control_node_2635_congruent inputs path left right next_left next_right :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2635 next_left = VM.find 2635 next_right.
Proof.
 intros   L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2635 reference_control_expr_2635 reference_control_2_positions reference_control_2_safety reference_control_member_2635) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2635 reference_control_expr_2635 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2635 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2635 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 reflexivity.
Qed.
Lemma reference_control_ready_2636 old :
 (exists value ground, VM.find 2209 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2636.
Proof.
 intros H2209.
 destruct H2209 as [v2209 [G2209 [V2209 T2209]]].
 unfold reference_control_expr_2636.
eapply rc_ref; [exact V2209|exists G2209; exact T2209].
Qed.
Lemma reference_control_member_2636 : List.In (2636,reference_control_expr_2636) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 153%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2636_ground inputs path old current result :
 (exists value ground, VM.find 2209 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2636 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2209 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2636 reference_control_expr_2636 reference_control_2_positions reference_control_2_safety reference_control_member_2636) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2636 reference_control_expr_2636 inputs path old current result Position Safe Nonreg (reference_control_ready_2636 old H2209) Step).
Qed.
Theorem reference_control_node_2636_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2209 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2209 left = VM.find 2209 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2636 next_left = VM.find 2636 next_right.
Proof.
 intros H2209 E2209 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2636 reference_control_expr_2636 reference_control_2_positions reference_control_2_safety reference_control_member_2636) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2636 reference_control_expr_2636 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2636 left H2209)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2636 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2209.
 reflexivity.
Qed.
Lemma reference_control_ready_2637 old :
 reference_control_ready old reference_control_expr_2637.
Proof.
 unfold reference_control_expr_2637.
apply rc_binary.
Qed.
Lemma reference_control_member_2637 : List.In (2637,reference_control_expr_2637) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 154%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2637_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2637 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2637 reference_control_expr_2637 reference_control_2_positions reference_control_2_safety reference_control_member_2637) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2637 reference_control_expr_2637 inputs path old current result Position Safe Nonreg (reference_control_ready_2637 old ) Step).
Qed.
Theorem reference_control_node_2637_congruent inputs path left right next_left next_right :
 VM.find 2552 left = VM.find 2552 right ->
 VM.find 2636 left = VM.find 2636 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2637 next_left = VM.find 2637 next_right.
Proof.
 intros  E2552 E2636 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2637 reference_control_expr_2637 reference_control_2_positions reference_control_2_safety reference_control_member_2637) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2637 reference_control_expr_2637 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2637 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2637 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2552.
 rewrite E2636.
 reflexivity.
Qed.
Lemma reference_control_ready_2638 old :
 reference_control_ready old reference_control_expr_2638.
Proof.
 unfold reference_control_expr_2638.
apply rc_unary.
Qed.
Lemma reference_control_member_2638 : List.In (2638,reference_control_expr_2638) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 155%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2638_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2638 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2638 reference_control_expr_2638 reference_control_2_positions reference_control_2_safety reference_control_member_2638) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2638 reference_control_expr_2638 inputs path old current result Position Safe Nonreg (reference_control_ready_2638 old ) Step).
Qed.
Theorem reference_control_node_2638_congruent inputs path left right next_left next_right :
 VM.find 2637 left = VM.find 2637 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2638 next_left = VM.find 2638 next_right.
Proof.
 intros  E2637 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2638 reference_control_expr_2638 reference_control_2_positions reference_control_2_safety reference_control_member_2638) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2638 reference_control_expr_2638 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2638 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2638 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2637.
 reflexivity.
Qed.
Lemma reference_control_ready_2639 old :
 reference_control_ready old reference_control_expr_2639.
Proof.
 unfold reference_control_expr_2639.
apply rc_unary.
Qed.
Lemma reference_control_member_2639 : List.In (2639,reference_control_expr_2639) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 156%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2639_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2639 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2639 reference_control_expr_2639 reference_control_2_positions reference_control_2_safety reference_control_member_2639) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2639 reference_control_expr_2639 inputs path old current result Position Safe Nonreg (reference_control_ready_2639 old ) Step).
Qed.
Theorem reference_control_node_2639_congruent inputs path left right next_left next_right :
 VM.find 2638 left = VM.find 2638 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2639 next_left = VM.find 2639 next_right.
Proof.
 intros  E2638 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2639 reference_control_expr_2639 reference_control_2_positions reference_control_2_safety reference_control_member_2639) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2639 reference_control_expr_2639 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2639 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2639 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2638.
 reflexivity.
Qed.
Lemma reference_control_ready_2640 old :
 reference_control_ready old reference_control_expr_2640.
Proof.
 unfold reference_control_expr_2640.
apply rc_binary.
Qed.
Lemma reference_control_member_2640 : List.In (2640,reference_control_expr_2640) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 157%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2640_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2640 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2640 reference_control_expr_2640 reference_control_2_positions reference_control_2_safety reference_control_member_2640) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2640 reference_control_expr_2640 inputs path old current result Position Safe Nonreg (reference_control_ready_2640 old ) Step).
Qed.
Theorem reference_control_node_2640_congruent inputs path left right next_left next_right :
 VM.find 2639 left = VM.find 2639 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2640 next_left = VM.find 2640 next_right.
Proof.
 intros  E2639 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2640 reference_control_expr_2640 reference_control_2_positions reference_control_2_safety reference_control_member_2640) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2640 reference_control_expr_2640 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2640 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2640 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2639.
 reflexivity.
Qed.
Lemma reference_control_ready_2641 old :
 reference_control_ready old reference_control_expr_2641.
Proof.
 unfold reference_control_expr_2641.
apply rc_binary.
Qed.
Lemma reference_control_member_2641 : List.In (2641,reference_control_expr_2641) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 158%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2641_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2641 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2641 reference_control_expr_2641 reference_control_2_positions reference_control_2_safety reference_control_member_2641) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2641 reference_control_expr_2641 inputs path old current result Position Safe Nonreg (reference_control_ready_2641 old ) Step).
Qed.
Theorem reference_control_node_2641_congruent inputs path left right next_left next_right :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2641 next_left = VM.find 2641 next_right.
Proof.
 intros   L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2641 reference_control_expr_2641 reference_control_2_positions reference_control_2_safety reference_control_member_2641) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2641 reference_control_expr_2641 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2641 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2641 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 reflexivity.
Qed.
Lemma reference_control_ready_2642 old :
 reference_control_ready old reference_control_expr_2642.
Proof.
 unfold reference_control_expr_2642.
apply rc_unary.
Qed.
Lemma reference_control_member_2642 : List.In (2642,reference_control_expr_2642) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 159%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2642_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2642 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2642 reference_control_expr_2642 reference_control_2_positions reference_control_2_safety reference_control_member_2642) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2642 reference_control_expr_2642 inputs path old current result Position Safe Nonreg (reference_control_ready_2642 old ) Step).
Qed.
Theorem reference_control_node_2642_congruent inputs path left right next_left next_right :
 VM.find 2638 left = VM.find 2638 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2642 next_left = VM.find 2642 next_right.
Proof.
 intros  E2638 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2642 reference_control_expr_2642 reference_control_2_positions reference_control_2_safety reference_control_member_2642) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2642 reference_control_expr_2642 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2642 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2642 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2638.
 reflexivity.
Qed.
Lemma reference_control_ready_2643 old :
 reference_control_ready old reference_control_expr_2643.
Proof.
 unfold reference_control_expr_2643.
apply rc_binary.
Qed.
Lemma reference_control_member_2643 : List.In (2643,reference_control_expr_2643) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 160%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2643_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2643 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2643 reference_control_expr_2643 reference_control_2_positions reference_control_2_safety reference_control_member_2643) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2643 reference_control_expr_2643 inputs path old current result Position Safe Nonreg (reference_control_ready_2643 old ) Step).
Qed.
Theorem reference_control_node_2643_congruent inputs path left right next_left next_right :
 VM.find 2642 left = VM.find 2642 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2643 next_left = VM.find 2643 next_right.
Proof.
 intros  E2642 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2643 reference_control_expr_2643 reference_control_2_positions reference_control_2_safety reference_control_member_2643) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2643 reference_control_expr_2643 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2643 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2643 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2642.
 reflexivity.
Qed.
Lemma reference_control_ready_2644 old :
 reference_control_ready old reference_control_expr_2644.
Proof.
 unfold reference_control_expr_2644.
apply rc_binary.
Qed.
Lemma reference_control_member_2644 : List.In (2644,reference_control_expr_2644) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 161%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2644_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2644 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2644 reference_control_expr_2644 reference_control_2_positions reference_control_2_safety reference_control_member_2644) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2644 reference_control_expr_2644 inputs path old current result Position Safe Nonreg (reference_control_ready_2644 old ) Step).
Qed.
Theorem reference_control_node_2644_congruent inputs path left right next_left next_right :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2644 next_left = VM.find 2644 next_right.
Proof.
 intros   L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2644 reference_control_expr_2644 reference_control_2_positions reference_control_2_safety reference_control_member_2644) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2644 reference_control_expr_2644 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2644 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2644 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 reflexivity.
Qed.
Lemma reference_control_ready_2645 old :
 reference_control_ready old reference_control_expr_2645.
Proof.
 unfold reference_control_expr_2645.
apply rc_unary.
Qed.
Lemma reference_control_member_2645 : List.In (2645,reference_control_expr_2645) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 162%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2645_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2645 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2645 reference_control_expr_2645 reference_control_2_positions reference_control_2_safety reference_control_member_2645) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2645 reference_control_expr_2645 inputs path old current result Position Safe Nonreg (reference_control_ready_2645 old ) Step).
Qed.
Theorem reference_control_node_2645_congruent inputs path left right next_left next_right :
 VM.find 2638 left = VM.find 2638 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2645 next_left = VM.find 2645 next_right.
Proof.
 intros  E2638 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2645 reference_control_expr_2645 reference_control_2_positions reference_control_2_safety reference_control_member_2645) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2645 reference_control_expr_2645 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2645 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2645 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2638.
 reflexivity.
Qed.
Lemma reference_control_ready_2646 old :
 reference_control_ready old reference_control_expr_2646.
Proof.
 unfold reference_control_expr_2646.
apply rc_binary.
Qed.
Lemma reference_control_member_2646 : List.In (2646,reference_control_expr_2646) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 163%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2646_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2646 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2646 reference_control_expr_2646 reference_control_2_positions reference_control_2_safety reference_control_member_2646) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2646 reference_control_expr_2646 inputs path old current result Position Safe Nonreg (reference_control_ready_2646 old ) Step).
Qed.
Theorem reference_control_node_2646_congruent inputs path left right next_left next_right :
 VM.find 2645 left = VM.find 2645 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2646 next_left = VM.find 2646 next_right.
Proof.
 intros  E2645 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2646 reference_control_expr_2646 reference_control_2_positions reference_control_2_safety reference_control_member_2646) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2646 reference_control_expr_2646 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2646 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2646 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2645.
 reflexivity.
Qed.
Lemma reference_control_ready_2647 old :
 (exists value ground, VM.find 2646 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2647.
Proof.
 intros H2646.
 destruct H2646 as [v2646 [G2646 [V2646 T2646]]].
 unfold reference_control_expr_2647.
apply rc_mux.
{ eapply rc_ref; [exact V2646|exists G2646; exact T2646].
}
{ apply rc_const.
}
Qed.
Lemma reference_control_member_2647 : List.In (2647,reference_control_expr_2647) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 164%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2647_ground inputs path old current result :
 (exists value ground, VM.find 2646 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2647 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2646 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2647 reference_control_expr_2647 reference_control_2_positions reference_control_2_safety reference_control_member_2647) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2647 reference_control_expr_2647 inputs path old current result Position Safe Nonreg (reference_control_ready_2647 old H2646) Step).
Qed.
Theorem reference_control_node_2647_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2646 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2644 left = VM.find 2644 right ->
 VM.find 2646 left = VM.find 2646 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2647 next_left = VM.find 2647 next_right.
Proof.
 intros H2646 E2644 E2646 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2647 reference_control_expr_2647 reference_control_2_positions reference_control_2_safety reference_control_member_2647) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2647 reference_control_expr_2647 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2647 left H2646)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2647 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2644.
 rewrite E2646.
 reflexivity.
Qed.
Lemma reference_control_ready_2648 old :
 (exists value ground, VM.find 2643 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2647 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2648.
Proof.
 intros H2643 H2647.
 destruct H2643 as [v2643 [G2643 [V2643 T2643]]].
 destruct H2647 as [v2647 [G2647 [V2647 T2647]]].
 unfold reference_control_expr_2648.
apply rc_mux.
{ eapply rc_ref; [exact V2643|exists G2643; exact T2643].
}
{ eapply rc_ref; [exact V2647|exists G2647; exact T2647].
}
Qed.
Lemma reference_control_member_2648 : List.In (2648,reference_control_expr_2648) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 165%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2648_ground inputs path old current result :
 (exists value ground, VM.find 2643 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2647 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2648 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2643 H2647 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2648 reference_control_expr_2648 reference_control_2_positions reference_control_2_safety reference_control_member_2648) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2648 reference_control_expr_2648 inputs path old current result Position Safe Nonreg (reference_control_ready_2648 old H2643 H2647) Step).
Qed.
Theorem reference_control_node_2648_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2643 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2647 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2641 left = VM.find 2641 right ->
 VM.find 2643 left = VM.find 2643 right ->
 VM.find 2647 left = VM.find 2647 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2648 next_left = VM.find 2648 next_right.
Proof.
 intros H2643 H2647 E2641 E2643 E2647 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2648 reference_control_expr_2648 reference_control_2_positions reference_control_2_safety reference_control_member_2648) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2648 reference_control_expr_2648 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2648 left H2643 H2647)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2648 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2641.
 rewrite E2643.
 rewrite E2647.
 reflexivity.
Qed.
Lemma reference_control_ready_2649 old :
 (exists value ground, VM.find 2640 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2648 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2649.
Proof.
 intros H2640 H2648.
 destruct H2640 as [v2640 [G2640 [V2640 T2640]]].
 destruct H2648 as [v2648 [G2648 [V2648 T2648]]].
 unfold reference_control_expr_2649.
apply rc_mux.
{ eapply rc_ref; [exact V2640|exists G2640; exact T2640].
}
{ eapply rc_ref; [exact V2648|exists G2648; exact T2648].
}
Qed.
Lemma reference_control_member_2649 : List.In (2649,reference_control_expr_2649) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 166%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2649_ground inputs path old current result :
 (exists value ground, VM.find 2640 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2648 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2649 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2640 H2648 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2649 reference_control_expr_2649 reference_control_2_positions reference_control_2_safety reference_control_member_2649) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2649 reference_control_expr_2649 inputs path old current result Position Safe Nonreg (reference_control_ready_2649 old H2640 H2648) Step).
Qed.
Theorem reference_control_node_2649_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2640 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2648 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2635 left = VM.find 2635 right ->
 VM.find 2640 left = VM.find 2640 right ->
 VM.find 2648 left = VM.find 2648 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2649 next_left = VM.find 2649 next_right.
Proof.
 intros H2640 H2648 E2635 E2640 E2648 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2649 reference_control_expr_2649 reference_control_2_positions reference_control_2_safety reference_control_member_2649) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2649 reference_control_expr_2649 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2649 left H2640 H2648)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2649 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2635.
 rewrite E2640.
 rewrite E2648.
 reflexivity.
Qed.
Lemma reference_control_ready_2650 old :
 reference_control_ready old reference_control_expr_2650.
Proof.
 unfold reference_control_expr_2650.
apply rc_binary.
Qed.
Lemma reference_control_member_2650 : List.In (2650,reference_control_expr_2650) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 167%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2650_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2650 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2650 reference_control_expr_2650 reference_control_2_positions reference_control_2_safety reference_control_member_2650) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2650 reference_control_expr_2650 inputs path old current result Position Safe Nonreg (reference_control_ready_2650 old ) Step).
Qed.
Theorem reference_control_node_2650_congruent inputs path left right next_left next_right :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2650 next_left = VM.find 2650 next_right.
Proof.
 intros   L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2650 reference_control_expr_2650 reference_control_2_positions reference_control_2_safety reference_control_member_2650) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2650 reference_control_expr_2650 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2650 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2650 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 reflexivity.
Qed.
Lemma reference_control_ready_2651 old :
 (exists value ground, VM.find 2209 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2651.
Proof.
 intros H2209.
 destruct H2209 as [v2209 [G2209 [V2209 T2209]]].
 unfold reference_control_expr_2651.
eapply rc_ref; [exact V2209|exists G2209; exact T2209].
Qed.
Lemma reference_control_member_2651 : List.In (2651,reference_control_expr_2651) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 168%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2651_ground inputs path old current result :
 (exists value ground, VM.find 2209 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2651 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2209 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2651 reference_control_expr_2651 reference_control_2_positions reference_control_2_safety reference_control_member_2651) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2651 reference_control_expr_2651 inputs path old current result Position Safe Nonreg (reference_control_ready_2651 old H2209) Step).
Qed.
Theorem reference_control_node_2651_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2209 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2209 left = VM.find 2209 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2651 next_left = VM.find 2651 next_right.
Proof.
 intros H2209 E2209 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2651 reference_control_expr_2651 reference_control_2_positions reference_control_2_safety reference_control_member_2651) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2651 reference_control_expr_2651 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2651 left H2209)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2651 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2209.
 reflexivity.
Qed.
Lemma reference_control_ready_2652 old :
 reference_control_ready old reference_control_expr_2652.
Proof.
 unfold reference_control_expr_2652.
apply rc_binary.
Qed.
Lemma reference_control_member_2652 : List.In (2652,reference_control_expr_2652) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 169%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2652_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2652 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2652 reference_control_expr_2652 reference_control_2_positions reference_control_2_safety reference_control_member_2652) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2652 reference_control_expr_2652 inputs path old current result Position Safe Nonreg (reference_control_ready_2652 old ) Step).
Qed.
Theorem reference_control_node_2652_congruent inputs path left right next_left next_right :
 VM.find 2552 left = VM.find 2552 right ->
 VM.find 2651 left = VM.find 2651 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2652 next_left = VM.find 2652 next_right.
Proof.
 intros  E2552 E2651 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2652 reference_control_expr_2652 reference_control_2_positions reference_control_2_safety reference_control_member_2652) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2652 reference_control_expr_2652 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2652 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2652 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2552.
 rewrite E2651.
 reflexivity.
Qed.
Lemma reference_control_ready_2653 old :
 reference_control_ready old reference_control_expr_2653.
Proof.
 unfold reference_control_expr_2653.
apply rc_unary.
Qed.
Lemma reference_control_member_2653 : List.In (2653,reference_control_expr_2653) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 170%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2653_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2653 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2653 reference_control_expr_2653 reference_control_2_positions reference_control_2_safety reference_control_member_2653) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2653 reference_control_expr_2653 inputs path old current result Position Safe Nonreg (reference_control_ready_2653 old ) Step).
Qed.
Theorem reference_control_node_2653_congruent inputs path left right next_left next_right :
 VM.find 2652 left = VM.find 2652 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2653 next_left = VM.find 2653 next_right.
Proof.
 intros  E2652 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2653 reference_control_expr_2653 reference_control_2_positions reference_control_2_safety reference_control_member_2653) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2653 reference_control_expr_2653 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2653 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2653 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2652.
 reflexivity.
Qed.
Lemma reference_control_ready_2654 old :
 reference_control_ready old reference_control_expr_2654.
Proof.
 unfold reference_control_expr_2654.
apply rc_unary.
Qed.
Lemma reference_control_member_2654 : List.In (2654,reference_control_expr_2654) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 171%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2654_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2654 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2654 reference_control_expr_2654 reference_control_2_positions reference_control_2_safety reference_control_member_2654) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2654 reference_control_expr_2654 inputs path old current result Position Safe Nonreg (reference_control_ready_2654 old ) Step).
Qed.
Theorem reference_control_node_2654_congruent inputs path left right next_left next_right :
 VM.find 2653 left = VM.find 2653 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2654 next_left = VM.find 2654 next_right.
Proof.
 intros  E2653 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2654 reference_control_expr_2654 reference_control_2_positions reference_control_2_safety reference_control_member_2654) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2654 reference_control_expr_2654 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2654 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2654 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2653.
 reflexivity.
Qed.
Lemma reference_control_ready_2655 old :
 reference_control_ready old reference_control_expr_2655.
Proof.
 unfold reference_control_expr_2655.
apply rc_binary.
Qed.
Lemma reference_control_member_2655 : List.In (2655,reference_control_expr_2655) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 172%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2655_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2655 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2655 reference_control_expr_2655 reference_control_2_positions reference_control_2_safety reference_control_member_2655) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2655 reference_control_expr_2655 inputs path old current result Position Safe Nonreg (reference_control_ready_2655 old ) Step).
Qed.
Theorem reference_control_node_2655_congruent inputs path left right next_left next_right :
 VM.find 2654 left = VM.find 2654 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2655 next_left = VM.find 2655 next_right.
Proof.
 intros  E2654 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2655 reference_control_expr_2655 reference_control_2_positions reference_control_2_safety reference_control_member_2655) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2655 reference_control_expr_2655 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2655 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2655 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2654.
 reflexivity.
Qed.
Lemma reference_control_ready_2656 old :
 reference_control_ready old reference_control_expr_2656.
Proof.
 unfold reference_control_expr_2656.
apply rc_binary.
Qed.
Lemma reference_control_member_2656 : List.In (2656,reference_control_expr_2656) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 173%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2656_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2656 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2656 reference_control_expr_2656 reference_control_2_positions reference_control_2_safety reference_control_member_2656) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2656 reference_control_expr_2656 inputs path old current result Position Safe Nonreg (reference_control_ready_2656 old ) Step).
Qed.
Theorem reference_control_node_2656_congruent inputs path left right next_left next_right :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2656 next_left = VM.find 2656 next_right.
Proof.
 intros   L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2656 reference_control_expr_2656 reference_control_2_positions reference_control_2_safety reference_control_member_2656) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2656 reference_control_expr_2656 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2656 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2656 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 reflexivity.
Qed.
Lemma reference_control_ready_2657 old :
 reference_control_ready old reference_control_expr_2657.
Proof.
 unfold reference_control_expr_2657.
apply rc_unary.
Qed.
Lemma reference_control_member_2657 : List.In (2657,reference_control_expr_2657) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 174%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2657_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2657 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2657 reference_control_expr_2657 reference_control_2_positions reference_control_2_safety reference_control_member_2657) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2657 reference_control_expr_2657 inputs path old current result Position Safe Nonreg (reference_control_ready_2657 old ) Step).
Qed.
Theorem reference_control_node_2657_congruent inputs path left right next_left next_right :
 VM.find 2653 left = VM.find 2653 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2657 next_left = VM.find 2657 next_right.
Proof.
 intros  E2653 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2657 reference_control_expr_2657 reference_control_2_positions reference_control_2_safety reference_control_member_2657) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2657 reference_control_expr_2657 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2657 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2657 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2653.
 reflexivity.
Qed.
Lemma reference_control_ready_2658 old :
 reference_control_ready old reference_control_expr_2658.
Proof.
 unfold reference_control_expr_2658.
apply rc_binary.
Qed.
Lemma reference_control_member_2658 : List.In (2658,reference_control_expr_2658) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 175%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2658_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2658 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2658 reference_control_expr_2658 reference_control_2_positions reference_control_2_safety reference_control_member_2658) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2658 reference_control_expr_2658 inputs path old current result Position Safe Nonreg (reference_control_ready_2658 old ) Step).
Qed.
Theorem reference_control_node_2658_congruent inputs path left right next_left next_right :
 VM.find 2657 left = VM.find 2657 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2658 next_left = VM.find 2658 next_right.
Proof.
 intros  E2657 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2658 reference_control_expr_2658 reference_control_2_positions reference_control_2_safety reference_control_member_2658) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2658 reference_control_expr_2658 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2658 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2658 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2657.
 reflexivity.
Qed.
Lemma reference_control_ready_2659 old :
 reference_control_ready old reference_control_expr_2659.
Proof.
 unfold reference_control_expr_2659.
apply rc_binary.
Qed.
Lemma reference_control_member_2659 : List.In (2659,reference_control_expr_2659) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 176%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2659_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2659 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2659 reference_control_expr_2659 reference_control_2_positions reference_control_2_safety reference_control_member_2659) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2659 reference_control_expr_2659 inputs path old current result Position Safe Nonreg (reference_control_ready_2659 old ) Step).
Qed.
Theorem reference_control_node_2659_congruent inputs path left right next_left next_right :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2659 next_left = VM.find 2659 next_right.
Proof.
 intros   L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2659 reference_control_expr_2659 reference_control_2_positions reference_control_2_safety reference_control_member_2659) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2659 reference_control_expr_2659 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2659 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2659 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 reflexivity.
Qed.
Lemma reference_control_ready_2660 old :
 reference_control_ready old reference_control_expr_2660.
Proof.
 unfold reference_control_expr_2660.
apply rc_unary.
Qed.
Lemma reference_control_member_2660 : List.In (2660,reference_control_expr_2660) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 177%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2660_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2660 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2660 reference_control_expr_2660 reference_control_2_positions reference_control_2_safety reference_control_member_2660) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2660 reference_control_expr_2660 inputs path old current result Position Safe Nonreg (reference_control_ready_2660 old ) Step).
Qed.
Theorem reference_control_node_2660_congruent inputs path left right next_left next_right :
 VM.find 2653 left = VM.find 2653 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2660 next_left = VM.find 2660 next_right.
Proof.
 intros  E2653 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2660 reference_control_expr_2660 reference_control_2_positions reference_control_2_safety reference_control_member_2660) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2660 reference_control_expr_2660 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2660 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2660 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2653.
 reflexivity.
Qed.
Lemma reference_control_ready_2661 old :
 reference_control_ready old reference_control_expr_2661.
Proof.
 unfold reference_control_expr_2661.
apply rc_binary.
Qed.
Lemma reference_control_member_2661 : List.In (2661,reference_control_expr_2661) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 178%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2661_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2661 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2661 reference_control_expr_2661 reference_control_2_positions reference_control_2_safety reference_control_member_2661) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2661 reference_control_expr_2661 inputs path old current result Position Safe Nonreg (reference_control_ready_2661 old ) Step).
Qed.
Theorem reference_control_node_2661_congruent inputs path left right next_left next_right :
 VM.find 2660 left = VM.find 2660 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2661 next_left = VM.find 2661 next_right.
Proof.
 intros  E2660 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2661 reference_control_expr_2661 reference_control_2_positions reference_control_2_safety reference_control_member_2661) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2661 reference_control_expr_2661 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2661 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2661 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2660.
 reflexivity.
Qed.
Lemma reference_control_ready_2662 old :
 (exists value ground, VM.find 2661 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2662.
Proof.
 intros H2661.
 destruct H2661 as [v2661 [G2661 [V2661 T2661]]].
 unfold reference_control_expr_2662.
apply rc_mux.
{ eapply rc_ref; [exact V2661|exists G2661; exact T2661].
}
{ apply rc_const.
}
Qed.
Lemma reference_control_member_2662 : List.In (2662,reference_control_expr_2662) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 179%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2662_ground inputs path old current result :
 (exists value ground, VM.find 2661 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2662 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2661 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2662 reference_control_expr_2662 reference_control_2_positions reference_control_2_safety reference_control_member_2662) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2662 reference_control_expr_2662 inputs path old current result Position Safe Nonreg (reference_control_ready_2662 old H2661) Step).
Qed.
Theorem reference_control_node_2662_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2661 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2659 left = VM.find 2659 right ->
 VM.find 2661 left = VM.find 2661 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2662 next_left = VM.find 2662 next_right.
Proof.
 intros H2661 E2659 E2661 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2662 reference_control_expr_2662 reference_control_2_positions reference_control_2_safety reference_control_member_2662) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2662 reference_control_expr_2662 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2662 left H2661)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2662 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2659.
 rewrite E2661.
 reflexivity.
Qed.
Lemma reference_control_ready_2663 old :
 (exists value ground, VM.find 2658 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2662 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2663.
Proof.
 intros H2658 H2662.
 destruct H2658 as [v2658 [G2658 [V2658 T2658]]].
 destruct H2662 as [v2662 [G2662 [V2662 T2662]]].
 unfold reference_control_expr_2663.
apply rc_mux.
{ eapply rc_ref; [exact V2658|exists G2658; exact T2658].
}
{ eapply rc_ref; [exact V2662|exists G2662; exact T2662].
}
Qed.
Lemma reference_control_member_2663 : List.In (2663,reference_control_expr_2663) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 180%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2663_ground inputs path old current result :
 (exists value ground, VM.find 2658 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2662 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2663 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2658 H2662 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2663 reference_control_expr_2663 reference_control_2_positions reference_control_2_safety reference_control_member_2663) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2663 reference_control_expr_2663 inputs path old current result Position Safe Nonreg (reference_control_ready_2663 old H2658 H2662) Step).
Qed.
Theorem reference_control_node_2663_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2658 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2662 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2656 left = VM.find 2656 right ->
 VM.find 2658 left = VM.find 2658 right ->
 VM.find 2662 left = VM.find 2662 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2663 next_left = VM.find 2663 next_right.
Proof.
 intros H2658 H2662 E2656 E2658 E2662 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2663 reference_control_expr_2663 reference_control_2_positions reference_control_2_safety reference_control_member_2663) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2663 reference_control_expr_2663 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2663 left H2658 H2662)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2663 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2656.
 rewrite E2658.
 rewrite E2662.
 reflexivity.
Qed.
Lemma reference_control_ready_2664 old :
 (exists value ground, VM.find 2655 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2663 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2664.
Proof.
 intros H2655 H2663.
 destruct H2655 as [v2655 [G2655 [V2655 T2655]]].
 destruct H2663 as [v2663 [G2663 [V2663 T2663]]].
 unfold reference_control_expr_2664.
apply rc_mux.
{ eapply rc_ref; [exact V2655|exists G2655; exact T2655].
}
{ eapply rc_ref; [exact V2663|exists G2663; exact T2663].
}
Qed.
Lemma reference_control_member_2664 : List.In (2664,reference_control_expr_2664) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 181%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2664_ground inputs path old current result :
 (exists value ground, VM.find 2655 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2663 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2664 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2655 H2663 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2664 reference_control_expr_2664 reference_control_2_positions reference_control_2_safety reference_control_member_2664) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2664 reference_control_expr_2664 inputs path old current result Position Safe Nonreg (reference_control_ready_2664 old H2655 H2663) Step).
Qed.
Theorem reference_control_node_2664_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2655 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2663 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2650 left = VM.find 2650 right ->
 VM.find 2655 left = VM.find 2655 right ->
 VM.find 2663 left = VM.find 2663 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2664 next_left = VM.find 2664 next_right.
Proof.
 intros H2655 H2663 E2650 E2655 E2663 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2664 reference_control_expr_2664 reference_control_2_positions reference_control_2_safety reference_control_member_2664) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2664 reference_control_expr_2664 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2664 left H2655 H2663)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2664 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2650.
 rewrite E2655.
 rewrite E2663.
 reflexivity.
Qed.
Lemma reference_control_ready_2665 old :
 reference_control_ready old reference_control_expr_2665.
Proof.
 unfold reference_control_expr_2665.
apply rc_binary.
Qed.
Lemma reference_control_member_2665 : List.In (2665,reference_control_expr_2665) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 182%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2665_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2665 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2665 reference_control_expr_2665 reference_control_2_positions reference_control_2_safety reference_control_member_2665) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2665 reference_control_expr_2665 inputs path old current result Position Safe Nonreg (reference_control_ready_2665 old ) Step).
Qed.
Theorem reference_control_node_2665_congruent inputs path left right next_left next_right :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2665 next_left = VM.find 2665 next_right.
Proof.
 intros   L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2665 reference_control_expr_2665 reference_control_2_positions reference_control_2_safety reference_control_member_2665) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2665 reference_control_expr_2665 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2665 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2665 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 reflexivity.
Qed.
Lemma reference_control_ready_2666 old :
 (exists value ground, VM.find 2209 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2666.
Proof.
 intros H2209.
 destruct H2209 as [v2209 [G2209 [V2209 T2209]]].
 unfold reference_control_expr_2666.
eapply rc_ref; [exact V2209|exists G2209; exact T2209].
Qed.
Lemma reference_control_member_2666 : List.In (2666,reference_control_expr_2666) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 183%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2666_ground inputs path old current result :
 (exists value ground, VM.find 2209 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2666 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2209 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2666 reference_control_expr_2666 reference_control_2_positions reference_control_2_safety reference_control_member_2666) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2666 reference_control_expr_2666 inputs path old current result Position Safe Nonreg (reference_control_ready_2666 old H2209) Step).
Qed.
Theorem reference_control_node_2666_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2209 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2209 left = VM.find 2209 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2666 next_left = VM.find 2666 next_right.
Proof.
 intros H2209 E2209 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2666 reference_control_expr_2666 reference_control_2_positions reference_control_2_safety reference_control_member_2666) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2666 reference_control_expr_2666 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2666 left H2209)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2666 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2209.
 reflexivity.
Qed.
Lemma reference_control_ready_2667 old :
 reference_control_ready old reference_control_expr_2667.
Proof.
 unfold reference_control_expr_2667.
apply rc_binary.
Qed.
Lemma reference_control_member_2667 : List.In (2667,reference_control_expr_2667) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 184%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2667_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2667 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2667 reference_control_expr_2667 reference_control_2_positions reference_control_2_safety reference_control_member_2667) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2667 reference_control_expr_2667 inputs path old current result Position Safe Nonreg (reference_control_ready_2667 old ) Step).
Qed.
Theorem reference_control_node_2667_congruent inputs path left right next_left next_right :
 VM.find 2552 left = VM.find 2552 right ->
 VM.find 2666 left = VM.find 2666 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2667 next_left = VM.find 2667 next_right.
Proof.
 intros  E2552 E2666 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2667 reference_control_expr_2667 reference_control_2_positions reference_control_2_safety reference_control_member_2667) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2667 reference_control_expr_2667 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2667 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2667 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2552.
 rewrite E2666.
 reflexivity.
Qed.
Lemma reference_control_ready_2668 old :
 reference_control_ready old reference_control_expr_2668.
Proof.
 unfold reference_control_expr_2668.
apply rc_unary.
Qed.
Lemma reference_control_member_2668 : List.In (2668,reference_control_expr_2668) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 185%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2668_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2668 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2668 reference_control_expr_2668 reference_control_2_positions reference_control_2_safety reference_control_member_2668) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2668 reference_control_expr_2668 inputs path old current result Position Safe Nonreg (reference_control_ready_2668 old ) Step).
Qed.
Theorem reference_control_node_2668_congruent inputs path left right next_left next_right :
 VM.find 2667 left = VM.find 2667 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2668 next_left = VM.find 2668 next_right.
Proof.
 intros  E2667 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2668 reference_control_expr_2668 reference_control_2_positions reference_control_2_safety reference_control_member_2668) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2668 reference_control_expr_2668 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2668 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2668 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2667.
 reflexivity.
Qed.
Lemma reference_control_ready_2669 old :
 reference_control_ready old reference_control_expr_2669.
Proof.
 unfold reference_control_expr_2669.
apply rc_unary.
Qed.
Lemma reference_control_member_2669 : List.In (2669,reference_control_expr_2669) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 186%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2669_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2669 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2669 reference_control_expr_2669 reference_control_2_positions reference_control_2_safety reference_control_member_2669) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2669 reference_control_expr_2669 inputs path old current result Position Safe Nonreg (reference_control_ready_2669 old ) Step).
Qed.
Theorem reference_control_node_2669_congruent inputs path left right next_left next_right :
 VM.find 2668 left = VM.find 2668 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2669 next_left = VM.find 2669 next_right.
Proof.
 intros  E2668 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2669 reference_control_expr_2669 reference_control_2_positions reference_control_2_safety reference_control_member_2669) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2669 reference_control_expr_2669 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2669 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2669 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2668.
 reflexivity.
Qed.
Lemma reference_control_ready_2670 old :
 reference_control_ready old reference_control_expr_2670.
Proof.
 unfold reference_control_expr_2670.
apply rc_binary.
Qed.
Lemma reference_control_member_2670 : List.In (2670,reference_control_expr_2670) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 187%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2670_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2670 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2670 reference_control_expr_2670 reference_control_2_positions reference_control_2_safety reference_control_member_2670) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2670 reference_control_expr_2670 inputs path old current result Position Safe Nonreg (reference_control_ready_2670 old ) Step).
Qed.
Theorem reference_control_node_2670_congruent inputs path left right next_left next_right :
 VM.find 2669 left = VM.find 2669 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2670 next_left = VM.find 2670 next_right.
Proof.
 intros  E2669 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2670 reference_control_expr_2670 reference_control_2_positions reference_control_2_safety reference_control_member_2670) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2670 reference_control_expr_2670 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2670 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2670 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2669.
 reflexivity.
Qed.
Lemma reference_control_ready_2671 old :
 reference_control_ready old reference_control_expr_2671.
Proof.
 unfold reference_control_expr_2671.
apply rc_binary.
Qed.
Lemma reference_control_member_2671 : List.In (2671,reference_control_expr_2671) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 188%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2671_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2671 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2671 reference_control_expr_2671 reference_control_2_positions reference_control_2_safety reference_control_member_2671) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2671 reference_control_expr_2671 inputs path old current result Position Safe Nonreg (reference_control_ready_2671 old ) Step).
Qed.
Theorem reference_control_node_2671_congruent inputs path left right next_left next_right :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2671 next_left = VM.find 2671 next_right.
Proof.
 intros   L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2671 reference_control_expr_2671 reference_control_2_positions reference_control_2_safety reference_control_member_2671) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2671 reference_control_expr_2671 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2671 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2671 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 reflexivity.
Qed.
Lemma reference_control_ready_2672 old :
 reference_control_ready old reference_control_expr_2672.
Proof.
 unfold reference_control_expr_2672.
apply rc_unary.
Qed.
Lemma reference_control_member_2672 : List.In (2672,reference_control_expr_2672) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 189%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2672_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2672 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2672 reference_control_expr_2672 reference_control_2_positions reference_control_2_safety reference_control_member_2672) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2672 reference_control_expr_2672 inputs path old current result Position Safe Nonreg (reference_control_ready_2672 old ) Step).
Qed.
Theorem reference_control_node_2672_congruent inputs path left right next_left next_right :
 VM.find 2668 left = VM.find 2668 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2672 next_left = VM.find 2672 next_right.
Proof.
 intros  E2668 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2672 reference_control_expr_2672 reference_control_2_positions reference_control_2_safety reference_control_member_2672) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2672 reference_control_expr_2672 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2672 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2672 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2668.
 reflexivity.
Qed.
Lemma reference_control_ready_2673 old :
 reference_control_ready old reference_control_expr_2673.
Proof.
 unfold reference_control_expr_2673.
apply rc_binary.
Qed.
Lemma reference_control_member_2673 : List.In (2673,reference_control_expr_2673) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 190%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2673_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2673 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2673 reference_control_expr_2673 reference_control_2_positions reference_control_2_safety reference_control_member_2673) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2673 reference_control_expr_2673 inputs path old current result Position Safe Nonreg (reference_control_ready_2673 old ) Step).
Qed.
Theorem reference_control_node_2673_congruent inputs path left right next_left next_right :
 VM.find 2672 left = VM.find 2672 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2673 next_left = VM.find 2673 next_right.
Proof.
 intros  E2672 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2673 reference_control_expr_2673 reference_control_2_positions reference_control_2_safety reference_control_member_2673) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2673 reference_control_expr_2673 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2673 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2673 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2672.
 reflexivity.
Qed.
Lemma reference_control_ready_2674 old :
 reference_control_ready old reference_control_expr_2674.
Proof.
 unfold reference_control_expr_2674.
apply rc_binary.
Qed.
Lemma reference_control_member_2674 : List.In (2674,reference_control_expr_2674) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 191%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2674_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2674 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2674 reference_control_expr_2674 reference_control_2_positions reference_control_2_safety reference_control_member_2674) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2674 reference_control_expr_2674 inputs path old current result Position Safe Nonreg (reference_control_ready_2674 old ) Step).
Qed.
Theorem reference_control_node_2674_congruent inputs path left right next_left next_right :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2674 next_left = VM.find 2674 next_right.
Proof.
 intros   L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2674 reference_control_expr_2674 reference_control_2_positions reference_control_2_safety reference_control_member_2674) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2674 reference_control_expr_2674 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2674 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2674 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 reflexivity.
Qed.
Lemma reference_control_ready_2675 old :
 reference_control_ready old reference_control_expr_2675.
Proof.
 unfold reference_control_expr_2675.
apply rc_unary.
Qed.
Lemma reference_control_member_2675 : List.In (2675,reference_control_expr_2675) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 192%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2675_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2675 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2675 reference_control_expr_2675 reference_control_2_positions reference_control_2_safety reference_control_member_2675) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2675 reference_control_expr_2675 inputs path old current result Position Safe Nonreg (reference_control_ready_2675 old ) Step).
Qed.
Theorem reference_control_node_2675_congruent inputs path left right next_left next_right :
 VM.find 2668 left = VM.find 2668 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2675 next_left = VM.find 2675 next_right.
Proof.
 intros  E2668 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2675 reference_control_expr_2675 reference_control_2_positions reference_control_2_safety reference_control_member_2675) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2675 reference_control_expr_2675 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2675 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2675 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2668.
 reflexivity.
Qed.
Lemma reference_control_ready_2676 old :
 reference_control_ready old reference_control_expr_2676.
Proof.
 unfold reference_control_expr_2676.
apply rc_binary.
Qed.
Lemma reference_control_member_2676 : List.In (2676,reference_control_expr_2676) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 193%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2676_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2676 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2676 reference_control_expr_2676 reference_control_2_positions reference_control_2_safety reference_control_member_2676) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2676 reference_control_expr_2676 inputs path old current result Position Safe Nonreg (reference_control_ready_2676 old ) Step).
Qed.
Theorem reference_control_node_2676_congruent inputs path left right next_left next_right :
 VM.find 2675 left = VM.find 2675 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2676 next_left = VM.find 2676 next_right.
Proof.
 intros  E2675 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2676 reference_control_expr_2676 reference_control_2_positions reference_control_2_safety reference_control_member_2676) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2676 reference_control_expr_2676 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2676 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2676 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2675.
 reflexivity.
Qed.
Lemma reference_control_ready_2677 old :
 (exists value ground, VM.find 2676 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2677.
Proof.
 intros H2676.
 destruct H2676 as [v2676 [G2676 [V2676 T2676]]].
 unfold reference_control_expr_2677.
apply rc_mux.
{ eapply rc_ref; [exact V2676|exists G2676; exact T2676].
}
{ apply rc_const.
}
Qed.
Lemma reference_control_member_2677 : List.In (2677,reference_control_expr_2677) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 194%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2677_ground inputs path old current result :
 (exists value ground, VM.find 2676 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2677 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2676 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2677 reference_control_expr_2677 reference_control_2_positions reference_control_2_safety reference_control_member_2677) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2677 reference_control_expr_2677 inputs path old current result Position Safe Nonreg (reference_control_ready_2677 old H2676) Step).
Qed.
Theorem reference_control_node_2677_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2676 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2674 left = VM.find 2674 right ->
 VM.find 2676 left = VM.find 2676 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2677 next_left = VM.find 2677 next_right.
Proof.
 intros H2676 E2674 E2676 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2677 reference_control_expr_2677 reference_control_2_positions reference_control_2_safety reference_control_member_2677) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2677 reference_control_expr_2677 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2677 left H2676)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2677 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2674.
 rewrite E2676.
 reflexivity.
Qed.
Lemma reference_control_ready_2678 old :
 (exists value ground, VM.find 2673 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2677 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2678.
Proof.
 intros H2673 H2677.
 destruct H2673 as [v2673 [G2673 [V2673 T2673]]].
 destruct H2677 as [v2677 [G2677 [V2677 T2677]]].
 unfold reference_control_expr_2678.
apply rc_mux.
{ eapply rc_ref; [exact V2673|exists G2673; exact T2673].
}
{ eapply rc_ref; [exact V2677|exists G2677; exact T2677].
}
Qed.
Lemma reference_control_member_2678 : List.In (2678,reference_control_expr_2678) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 195%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2678_ground inputs path old current result :
 (exists value ground, VM.find 2673 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2677 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2678 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2673 H2677 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2678 reference_control_expr_2678 reference_control_2_positions reference_control_2_safety reference_control_member_2678) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2678 reference_control_expr_2678 inputs path old current result Position Safe Nonreg (reference_control_ready_2678 old H2673 H2677) Step).
Qed.
Theorem reference_control_node_2678_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2673 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2677 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2671 left = VM.find 2671 right ->
 VM.find 2673 left = VM.find 2673 right ->
 VM.find 2677 left = VM.find 2677 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2678 next_left = VM.find 2678 next_right.
Proof.
 intros H2673 H2677 E2671 E2673 E2677 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2678 reference_control_expr_2678 reference_control_2_positions reference_control_2_safety reference_control_member_2678) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2678 reference_control_expr_2678 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2678 left H2673 H2677)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2678 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2671.
 rewrite E2673.
 rewrite E2677.
 reflexivity.
Qed.
Lemma reference_control_ready_2679 old :
 (exists value ground, VM.find 2670 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2678 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2679.
Proof.
 intros H2670 H2678.
 destruct H2670 as [v2670 [G2670 [V2670 T2670]]].
 destruct H2678 as [v2678 [G2678 [V2678 T2678]]].
 unfold reference_control_expr_2679.
apply rc_mux.
{ eapply rc_ref; [exact V2670|exists G2670; exact T2670].
}
{ eapply rc_ref; [exact V2678|exists G2678; exact T2678].
}
Qed.
Lemma reference_control_member_2679 : List.In (2679,reference_control_expr_2679) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 196%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2679_ground inputs path old current result :
 (exists value ground, VM.find 2670 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2678 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2679 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2670 H2678 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2679 reference_control_expr_2679 reference_control_2_positions reference_control_2_safety reference_control_member_2679) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2679 reference_control_expr_2679 inputs path old current result Position Safe Nonreg (reference_control_ready_2679 old H2670 H2678) Step).
Qed.
Theorem reference_control_node_2679_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2670 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2678 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2665 left = VM.find 2665 right ->
 VM.find 2670 left = VM.find 2670 right ->
 VM.find 2678 left = VM.find 2678 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2679 next_left = VM.find 2679 next_right.
Proof.
 intros H2670 H2678 E2665 E2670 E2678 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2679 reference_control_expr_2679 reference_control_2_positions reference_control_2_safety reference_control_member_2679) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2679 reference_control_expr_2679 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2679 left H2670 H2678)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2679 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2665.
 rewrite E2670.
 rewrite E2678.
 reflexivity.
Qed.
Lemma reference_control_ready_2694 old :
 reference_control_ready old reference_control_expr_2694.
Proof.
 unfold reference_control_expr_2694.
apply rc_binary.
Qed.
Lemma reference_control_member_2694 : List.In (2694,reference_control_expr_2694) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 197%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2694_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2694 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2694 reference_control_expr_2694 reference_control_2_positions reference_control_2_safety reference_control_member_2694) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2694 reference_control_expr_2694 inputs path old current result Position Safe Nonreg (reference_control_ready_2694 old ) Step).
Qed.
Theorem reference_control_node_2694_congruent inputs path left right next_left next_right :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2694 next_left = VM.find 2694 next_right.
Proof.
 intros   L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2694 reference_control_expr_2694 reference_control_2_positions reference_control_2_safety reference_control_member_2694) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2694 reference_control_expr_2694 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2694 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2694 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 reflexivity.
Qed.
Lemma reference_control_ready_2695 old :
 (exists value ground, VM.find 2209 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2695.
Proof.
 intros H2209.
 destruct H2209 as [v2209 [G2209 [V2209 T2209]]].
 unfold reference_control_expr_2695.
eapply rc_ref; [exact V2209|exists G2209; exact T2209].
Qed.
Lemma reference_control_member_2695 : List.In (2695,reference_control_expr_2695) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 198%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2695_ground inputs path old current result :
 (exists value ground, VM.find 2209 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2695 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2209 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2695 reference_control_expr_2695 reference_control_2_positions reference_control_2_safety reference_control_member_2695) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2695 reference_control_expr_2695 inputs path old current result Position Safe Nonreg (reference_control_ready_2695 old H2209) Step).
Qed.
Theorem reference_control_node_2695_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2209 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2209 left = VM.find 2209 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2695 next_left = VM.find 2695 next_right.
Proof.
 intros H2209 E2209 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2695 reference_control_expr_2695 reference_control_2_positions reference_control_2_safety reference_control_member_2695) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2695 reference_control_expr_2695 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2695 left H2209)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2695 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2209.
 reflexivity.
Qed.
Lemma reference_control_ready_2696 old :
 reference_control_ready old reference_control_expr_2696.
Proof.
 unfold reference_control_expr_2696.
apply rc_binary.
Qed.
Lemma reference_control_member_2696 : List.In (2696,reference_control_expr_2696) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 199%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2696_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2696 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2696 reference_control_expr_2696 reference_control_2_positions reference_control_2_safety reference_control_member_2696) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2696 reference_control_expr_2696 inputs path old current result Position Safe Nonreg (reference_control_ready_2696 old ) Step).
Qed.
Theorem reference_control_node_2696_congruent inputs path left right next_left next_right :
 VM.find 2552 left = VM.find 2552 right ->
 VM.find 2695 left = VM.find 2695 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2696 next_left = VM.find 2696 next_right.
Proof.
 intros  E2552 E2695 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2696 reference_control_expr_2696 reference_control_2_positions reference_control_2_safety reference_control_member_2696) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2696 reference_control_expr_2696 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2696 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2696 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2552.
 rewrite E2695.
 reflexivity.
Qed.
Lemma reference_control_ready_2697 old :
 reference_control_ready old reference_control_expr_2697.
Proof.
 unfold reference_control_expr_2697.
apply rc_unary.
Qed.
Lemma reference_control_member_2697 : List.In (2697,reference_control_expr_2697) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 200%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2697_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2697 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2697 reference_control_expr_2697 reference_control_2_positions reference_control_2_safety reference_control_member_2697) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2697 reference_control_expr_2697 inputs path old current result Position Safe Nonreg (reference_control_ready_2697 old ) Step).
Qed.
Theorem reference_control_node_2697_congruent inputs path left right next_left next_right :
 VM.find 2696 left = VM.find 2696 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2697 next_left = VM.find 2697 next_right.
Proof.
 intros  E2696 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2697 reference_control_expr_2697 reference_control_2_positions reference_control_2_safety reference_control_member_2697) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2697 reference_control_expr_2697 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2697 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2697 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2696.
 reflexivity.
Qed.
Lemma reference_control_ready_2698 old :
 reference_control_ready old reference_control_expr_2698.
Proof.
 unfold reference_control_expr_2698.
apply rc_unary.
Qed.
Lemma reference_control_member_2698 : List.In (2698,reference_control_expr_2698) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 201%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2698_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2698 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2698 reference_control_expr_2698 reference_control_2_positions reference_control_2_safety reference_control_member_2698) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2698 reference_control_expr_2698 inputs path old current result Position Safe Nonreg (reference_control_ready_2698 old ) Step).
Qed.
Theorem reference_control_node_2698_congruent inputs path left right next_left next_right :
 VM.find 2697 left = VM.find 2697 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2698 next_left = VM.find 2698 next_right.
Proof.
 intros  E2697 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2698 reference_control_expr_2698 reference_control_2_positions reference_control_2_safety reference_control_member_2698) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2698 reference_control_expr_2698 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2698 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2698 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2697.
 reflexivity.
Qed.
Lemma reference_control_ready_2699 old :
 reference_control_ready old reference_control_expr_2699.
Proof.
 unfold reference_control_expr_2699.
apply rc_binary.
Qed.
Lemma reference_control_member_2699 : List.In (2699,reference_control_expr_2699) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 202%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2699_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2699 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2699 reference_control_expr_2699 reference_control_2_positions reference_control_2_safety reference_control_member_2699) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2699 reference_control_expr_2699 inputs path old current result Position Safe Nonreg (reference_control_ready_2699 old ) Step).
Qed.
Theorem reference_control_node_2699_congruent inputs path left right next_left next_right :
 VM.find 2698 left = VM.find 2698 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2699 next_left = VM.find 2699 next_right.
Proof.
 intros  E2698 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2699 reference_control_expr_2699 reference_control_2_positions reference_control_2_safety reference_control_member_2699) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2699 reference_control_expr_2699 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2699 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2699 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2698.
 reflexivity.
Qed.
Lemma reference_control_ready_2700 old :
 reference_control_ready old reference_control_expr_2700.
Proof.
 unfold reference_control_expr_2700.
apply rc_binary.
Qed.
Lemma reference_control_member_2700 : List.In (2700,reference_control_expr_2700) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 203%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2700_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2700 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2700 reference_control_expr_2700 reference_control_2_positions reference_control_2_safety reference_control_member_2700) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2700 reference_control_expr_2700 inputs path old current result Position Safe Nonreg (reference_control_ready_2700 old ) Step).
Qed.
Theorem reference_control_node_2700_congruent inputs path left right next_left next_right :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2700 next_left = VM.find 2700 next_right.
Proof.
 intros   L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2700 reference_control_expr_2700 reference_control_2_positions reference_control_2_safety reference_control_member_2700) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2700 reference_control_expr_2700 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2700 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2700 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 reflexivity.
Qed.
Lemma reference_control_ready_2701 old :
 reference_control_ready old reference_control_expr_2701.
Proof.
 unfold reference_control_expr_2701.
apply rc_unary.
Qed.
Lemma reference_control_member_2701 : List.In (2701,reference_control_expr_2701) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 204%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2701_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2701 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2701 reference_control_expr_2701 reference_control_2_positions reference_control_2_safety reference_control_member_2701) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2701 reference_control_expr_2701 inputs path old current result Position Safe Nonreg (reference_control_ready_2701 old ) Step).
Qed.
Theorem reference_control_node_2701_congruent inputs path left right next_left next_right :
 VM.find 2697 left = VM.find 2697 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2701 next_left = VM.find 2701 next_right.
Proof.
 intros  E2697 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2701 reference_control_expr_2701 reference_control_2_positions reference_control_2_safety reference_control_member_2701) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2701 reference_control_expr_2701 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2701 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2701 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2697.
 reflexivity.
Qed.
Lemma reference_control_ready_2702 old :
 reference_control_ready old reference_control_expr_2702.
Proof.
 unfold reference_control_expr_2702.
apply rc_binary.
Qed.
Lemma reference_control_member_2702 : List.In (2702,reference_control_expr_2702) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 205%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2702_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2702 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2702 reference_control_expr_2702 reference_control_2_positions reference_control_2_safety reference_control_member_2702) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2702 reference_control_expr_2702 inputs path old current result Position Safe Nonreg (reference_control_ready_2702 old ) Step).
Qed.
Theorem reference_control_node_2702_congruent inputs path left right next_left next_right :
 VM.find 2701 left = VM.find 2701 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2702 next_left = VM.find 2702 next_right.
Proof.
 intros  E2701 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2702 reference_control_expr_2702 reference_control_2_positions reference_control_2_safety reference_control_member_2702) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2702 reference_control_expr_2702 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2702 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2702 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2701.
 reflexivity.
Qed.
Lemma reference_control_ready_2703 old :
 reference_control_ready old reference_control_expr_2703.
Proof.
 unfold reference_control_expr_2703.
apply rc_binary.
Qed.
Lemma reference_control_member_2703 : List.In (2703,reference_control_expr_2703) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 206%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2703_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2703 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2703 reference_control_expr_2703 reference_control_2_positions reference_control_2_safety reference_control_member_2703) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2703 reference_control_expr_2703 inputs path old current result Position Safe Nonreg (reference_control_ready_2703 old ) Step).
Qed.
Theorem reference_control_node_2703_congruent inputs path left right next_left next_right :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2703 next_left = VM.find 2703 next_right.
Proof.
 intros   L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2703 reference_control_expr_2703 reference_control_2_positions reference_control_2_safety reference_control_member_2703) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2703 reference_control_expr_2703 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2703 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2703 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 reflexivity.
Qed.
Lemma reference_control_ready_2704 old :
 reference_control_ready old reference_control_expr_2704.
Proof.
 unfold reference_control_expr_2704.
apply rc_unary.
Qed.
Lemma reference_control_member_2704 : List.In (2704,reference_control_expr_2704) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 207%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2704_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2704 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2704 reference_control_expr_2704 reference_control_2_positions reference_control_2_safety reference_control_member_2704) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2704 reference_control_expr_2704 inputs path old current result Position Safe Nonreg (reference_control_ready_2704 old ) Step).
Qed.
Theorem reference_control_node_2704_congruent inputs path left right next_left next_right :
 VM.find 2697 left = VM.find 2697 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2704 next_left = VM.find 2704 next_right.
Proof.
 intros  E2697 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2704 reference_control_expr_2704 reference_control_2_positions reference_control_2_safety reference_control_member_2704) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2704 reference_control_expr_2704 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2704 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2704 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2697.
 reflexivity.
Qed.
Lemma reference_control_ready_2705 old :
 reference_control_ready old reference_control_expr_2705.
Proof.
 unfold reference_control_expr_2705.
apply rc_binary.
Qed.
Lemma reference_control_member_2705 : List.In (2705,reference_control_expr_2705) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 208%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2705_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2705 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2705 reference_control_expr_2705 reference_control_2_positions reference_control_2_safety reference_control_member_2705) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2705 reference_control_expr_2705 inputs path old current result Position Safe Nonreg (reference_control_ready_2705 old ) Step).
Qed.
Theorem reference_control_node_2705_congruent inputs path left right next_left next_right :
 VM.find 2704 left = VM.find 2704 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2705 next_left = VM.find 2705 next_right.
Proof.
 intros  E2704 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2705 reference_control_expr_2705 reference_control_2_positions reference_control_2_safety reference_control_member_2705) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2705 reference_control_expr_2705 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2705 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2705 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2704.
 reflexivity.
Qed.
Lemma reference_control_ready_2706 old :
 (exists value ground, VM.find 2705 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2706.
Proof.
 intros H2705.
 destruct H2705 as [v2705 [G2705 [V2705 T2705]]].
 unfold reference_control_expr_2706.
apply rc_mux.
{ eapply rc_ref; [exact V2705|exists G2705; exact T2705].
}
{ apply rc_const.
}
Qed.
Lemma reference_control_member_2706 : List.In (2706,reference_control_expr_2706) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 209%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2706_ground inputs path old current result :
 (exists value ground, VM.find 2705 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2706 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2705 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2706 reference_control_expr_2706 reference_control_2_positions reference_control_2_safety reference_control_member_2706) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2706 reference_control_expr_2706 inputs path old current result Position Safe Nonreg (reference_control_ready_2706 old H2705) Step).
Qed.
Theorem reference_control_node_2706_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2705 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2703 left = VM.find 2703 right ->
 VM.find 2705 left = VM.find 2705 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2706 next_left = VM.find 2706 next_right.
Proof.
 intros H2705 E2703 E2705 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2706 reference_control_expr_2706 reference_control_2_positions reference_control_2_safety reference_control_member_2706) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2706 reference_control_expr_2706 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2706 left H2705)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2706 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2703.
 rewrite E2705.
 reflexivity.
Qed.
Lemma reference_control_ready_2707 old :
 (exists value ground, VM.find 2702 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2706 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2707.
Proof.
 intros H2702 H2706.
 destruct H2702 as [v2702 [G2702 [V2702 T2702]]].
 destruct H2706 as [v2706 [G2706 [V2706 T2706]]].
 unfold reference_control_expr_2707.
apply rc_mux.
{ eapply rc_ref; [exact V2702|exists G2702; exact T2702].
}
{ eapply rc_ref; [exact V2706|exists G2706; exact T2706].
}
Qed.
Lemma reference_control_member_2707 : List.In (2707,reference_control_expr_2707) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 210%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2707_ground inputs path old current result :
 (exists value ground, VM.find 2702 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2706 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2707 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2702 H2706 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2707 reference_control_expr_2707 reference_control_2_positions reference_control_2_safety reference_control_member_2707) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2707 reference_control_expr_2707 inputs path old current result Position Safe Nonreg (reference_control_ready_2707 old H2702 H2706) Step).
Qed.
Theorem reference_control_node_2707_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2702 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2706 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2700 left = VM.find 2700 right ->
 VM.find 2702 left = VM.find 2702 right ->
 VM.find 2706 left = VM.find 2706 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2707 next_left = VM.find 2707 next_right.
Proof.
 intros H2702 H2706 E2700 E2702 E2706 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2707 reference_control_expr_2707 reference_control_2_positions reference_control_2_safety reference_control_member_2707) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2707 reference_control_expr_2707 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2707 left H2702 H2706)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2707 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2700.
 rewrite E2702.
 rewrite E2706.
 reflexivity.
Qed.
Lemma reference_control_ready_2708 old :
 (exists value ground, VM.find 2699 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2707 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2708.
Proof.
 intros H2699 H2707.
 destruct H2699 as [v2699 [G2699 [V2699 T2699]]].
 destruct H2707 as [v2707 [G2707 [V2707 T2707]]].
 unfold reference_control_expr_2708.
apply rc_mux.
{ eapply rc_ref; [exact V2699|exists G2699; exact T2699].
}
{ eapply rc_ref; [exact V2707|exists G2707; exact T2707].
}
Qed.
Lemma reference_control_member_2708 : List.In (2708,reference_control_expr_2708) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 211%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2708_ground inputs path old current result :
 (exists value ground, VM.find 2699 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2707 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2708 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2699 H2707 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2708 reference_control_expr_2708 reference_control_2_positions reference_control_2_safety reference_control_member_2708) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2708 reference_control_expr_2708 inputs path old current result Position Safe Nonreg (reference_control_ready_2708 old H2699 H2707) Step).
Qed.
Theorem reference_control_node_2708_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2699 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2707 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2694 left = VM.find 2694 right ->
 VM.find 2699 left = VM.find 2699 right ->
 VM.find 2707 left = VM.find 2707 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2708 next_left = VM.find 2708 next_right.
Proof.
 intros H2699 H2707 E2694 E2699 E2707 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2708 reference_control_expr_2708 reference_control_2_positions reference_control_2_safety reference_control_member_2708) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2708 reference_control_expr_2708 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2708 left H2699 H2707)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2708 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2694.
 rewrite E2699.
 rewrite E2707.
 reflexivity.
Qed.
Lemma reference_control_ready_2709 old :
 reference_control_ready old reference_control_expr_2709.
Proof.
 unfold reference_control_expr_2709.
apply rc_binary.
Qed.
Lemma reference_control_member_2709 : List.In (2709,reference_control_expr_2709) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 212%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2709_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2709 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2709 reference_control_expr_2709 reference_control_2_positions reference_control_2_safety reference_control_member_2709) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2709 reference_control_expr_2709 inputs path old current result Position Safe Nonreg (reference_control_ready_2709 old ) Step).
Qed.
Theorem reference_control_node_2709_congruent inputs path left right next_left next_right :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2709 next_left = VM.find 2709 next_right.
Proof.
 intros   L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2709 reference_control_expr_2709 reference_control_2_positions reference_control_2_safety reference_control_member_2709) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2709 reference_control_expr_2709 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2709 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2709 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 reflexivity.
Qed.
Lemma reference_control_ready_2710 old :
 (exists value ground, VM.find 2209 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2710.
Proof.
 intros H2209.
 destruct H2209 as [v2209 [G2209 [V2209 T2209]]].
 unfold reference_control_expr_2710.
eapply rc_ref; [exact V2209|exists G2209; exact T2209].
Qed.
Lemma reference_control_member_2710 : List.In (2710,reference_control_expr_2710) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 213%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2710_ground inputs path old current result :
 (exists value ground, VM.find 2209 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2710 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2209 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2710 reference_control_expr_2710 reference_control_2_positions reference_control_2_safety reference_control_member_2710) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2710 reference_control_expr_2710 inputs path old current result Position Safe Nonreg (reference_control_ready_2710 old H2209) Step).
Qed.
Theorem reference_control_node_2710_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2209 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2209 left = VM.find 2209 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2710 next_left = VM.find 2710 next_right.
Proof.
 intros H2209 E2209 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2710 reference_control_expr_2710 reference_control_2_positions reference_control_2_safety reference_control_member_2710) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2710 reference_control_expr_2710 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2710 left H2209)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2710 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2209.
 reflexivity.
Qed.
Lemma reference_control_ready_2711 old :
 reference_control_ready old reference_control_expr_2711.
Proof.
 unfold reference_control_expr_2711.
apply rc_binary.
Qed.
Lemma reference_control_member_2711 : List.In (2711,reference_control_expr_2711) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 214%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2711_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2711 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2711 reference_control_expr_2711 reference_control_2_positions reference_control_2_safety reference_control_member_2711) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2711 reference_control_expr_2711 inputs path old current result Position Safe Nonreg (reference_control_ready_2711 old ) Step).
Qed.
Theorem reference_control_node_2711_congruent inputs path left right next_left next_right :
 VM.find 2552 left = VM.find 2552 right ->
 VM.find 2710 left = VM.find 2710 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2711 next_left = VM.find 2711 next_right.
Proof.
 intros  E2552 E2710 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2711 reference_control_expr_2711 reference_control_2_positions reference_control_2_safety reference_control_member_2711) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2711 reference_control_expr_2711 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2711 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2711 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2552.
 rewrite E2710.
 reflexivity.
Qed.
Lemma reference_control_ready_2712 old :
 reference_control_ready old reference_control_expr_2712.
Proof.
 unfold reference_control_expr_2712.
apply rc_unary.
Qed.
Lemma reference_control_member_2712 : List.In (2712,reference_control_expr_2712) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 215%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2712_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2712 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2712 reference_control_expr_2712 reference_control_2_positions reference_control_2_safety reference_control_member_2712) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2712 reference_control_expr_2712 inputs path old current result Position Safe Nonreg (reference_control_ready_2712 old ) Step).
Qed.
Theorem reference_control_node_2712_congruent inputs path left right next_left next_right :
 VM.find 2711 left = VM.find 2711 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2712 next_left = VM.find 2712 next_right.
Proof.
 intros  E2711 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2712 reference_control_expr_2712 reference_control_2_positions reference_control_2_safety reference_control_member_2712) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2712 reference_control_expr_2712 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2712 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2712 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2711.
 reflexivity.
Qed.
Lemma reference_control_ready_2713 old :
 reference_control_ready old reference_control_expr_2713.
Proof.
 unfold reference_control_expr_2713.
apply rc_unary.
Qed.
Lemma reference_control_member_2713 : List.In (2713,reference_control_expr_2713) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 216%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2713_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2713 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2713 reference_control_expr_2713 reference_control_2_positions reference_control_2_safety reference_control_member_2713) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2713 reference_control_expr_2713 inputs path old current result Position Safe Nonreg (reference_control_ready_2713 old ) Step).
Qed.
Theorem reference_control_node_2713_congruent inputs path left right next_left next_right :
 VM.find 2712 left = VM.find 2712 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2713 next_left = VM.find 2713 next_right.
Proof.
 intros  E2712 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2713 reference_control_expr_2713 reference_control_2_positions reference_control_2_safety reference_control_member_2713) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2713 reference_control_expr_2713 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2713 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2713 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2712.
 reflexivity.
Qed.
Lemma reference_control_ready_2714 old :
 reference_control_ready old reference_control_expr_2714.
Proof.
 unfold reference_control_expr_2714.
apply rc_binary.
Qed.
Lemma reference_control_member_2714 : List.In (2714,reference_control_expr_2714) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 217%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2714_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2714 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2714 reference_control_expr_2714 reference_control_2_positions reference_control_2_safety reference_control_member_2714) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2714 reference_control_expr_2714 inputs path old current result Position Safe Nonreg (reference_control_ready_2714 old ) Step).
Qed.
Theorem reference_control_node_2714_congruent inputs path left right next_left next_right :
 VM.find 2713 left = VM.find 2713 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2714 next_left = VM.find 2714 next_right.
Proof.
 intros  E2713 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2714 reference_control_expr_2714 reference_control_2_positions reference_control_2_safety reference_control_member_2714) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2714 reference_control_expr_2714 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2714 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2714 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2713.
 reflexivity.
Qed.
Lemma reference_control_ready_2715 old :
 reference_control_ready old reference_control_expr_2715.
Proof.
 unfold reference_control_expr_2715.
apply rc_binary.
Qed.
Lemma reference_control_member_2715 : List.In (2715,reference_control_expr_2715) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 218%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2715_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2715 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2715 reference_control_expr_2715 reference_control_2_positions reference_control_2_safety reference_control_member_2715) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2715 reference_control_expr_2715 inputs path old current result Position Safe Nonreg (reference_control_ready_2715 old ) Step).
Qed.
Theorem reference_control_node_2715_congruent inputs path left right next_left next_right :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2715 next_left = VM.find 2715 next_right.
Proof.
 intros   L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2715 reference_control_expr_2715 reference_control_2_positions reference_control_2_safety reference_control_member_2715) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2715 reference_control_expr_2715 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2715 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2715 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 reflexivity.
Qed.
Lemma reference_control_ready_2716 old :
 reference_control_ready old reference_control_expr_2716.
Proof.
 unfold reference_control_expr_2716.
apply rc_unary.
Qed.
Lemma reference_control_member_2716 : List.In (2716,reference_control_expr_2716) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 219%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2716_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2716 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2716 reference_control_expr_2716 reference_control_2_positions reference_control_2_safety reference_control_member_2716) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2716 reference_control_expr_2716 inputs path old current result Position Safe Nonreg (reference_control_ready_2716 old ) Step).
Qed.
Theorem reference_control_node_2716_congruent inputs path left right next_left next_right :
 VM.find 2712 left = VM.find 2712 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2716 next_left = VM.find 2716 next_right.
Proof.
 intros  E2712 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2716 reference_control_expr_2716 reference_control_2_positions reference_control_2_safety reference_control_member_2716) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2716 reference_control_expr_2716 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2716 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2716 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2712.
 reflexivity.
Qed.
Lemma reference_control_ready_2717 old :
 reference_control_ready old reference_control_expr_2717.
Proof.
 unfold reference_control_expr_2717.
apply rc_binary.
Qed.
Lemma reference_control_member_2717 : List.In (2717,reference_control_expr_2717) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 220%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2717_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2717 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2717 reference_control_expr_2717 reference_control_2_positions reference_control_2_safety reference_control_member_2717) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2717 reference_control_expr_2717 inputs path old current result Position Safe Nonreg (reference_control_ready_2717 old ) Step).
Qed.
Theorem reference_control_node_2717_congruent inputs path left right next_left next_right :
 VM.find 2716 left = VM.find 2716 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2717 next_left = VM.find 2717 next_right.
Proof.
 intros  E2716 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2717 reference_control_expr_2717 reference_control_2_positions reference_control_2_safety reference_control_member_2717) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2717 reference_control_expr_2717 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2717 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2717 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2716.
 reflexivity.
Qed.
Lemma reference_control_ready_2718 old :
 reference_control_ready old reference_control_expr_2718.
Proof.
 unfold reference_control_expr_2718.
apply rc_binary.
Qed.
Lemma reference_control_member_2718 : List.In (2718,reference_control_expr_2718) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 221%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2718_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2718 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2718 reference_control_expr_2718 reference_control_2_positions reference_control_2_safety reference_control_member_2718) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2718 reference_control_expr_2718 inputs path old current result Position Safe Nonreg (reference_control_ready_2718 old ) Step).
Qed.
Theorem reference_control_node_2718_congruent inputs path left right next_left next_right :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2718 next_left = VM.find 2718 next_right.
Proof.
 intros   L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2718 reference_control_expr_2718 reference_control_2_positions reference_control_2_safety reference_control_member_2718) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2718 reference_control_expr_2718 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2718 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2718 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 reflexivity.
Qed.
Lemma reference_control_ready_2719 old :
 reference_control_ready old reference_control_expr_2719.
Proof.
 unfold reference_control_expr_2719.
apply rc_unary.
Qed.
Lemma reference_control_member_2719 : List.In (2719,reference_control_expr_2719) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 222%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2719_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2719 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2719 reference_control_expr_2719 reference_control_2_positions reference_control_2_safety reference_control_member_2719) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2719 reference_control_expr_2719 inputs path old current result Position Safe Nonreg (reference_control_ready_2719 old ) Step).
Qed.
Theorem reference_control_node_2719_congruent inputs path left right next_left next_right :
 VM.find 2712 left = VM.find 2712 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2719 next_left = VM.find 2719 next_right.
Proof.
 intros  E2712 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2719 reference_control_expr_2719 reference_control_2_positions reference_control_2_safety reference_control_member_2719) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2719 reference_control_expr_2719 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2719 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2719 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2712.
 reflexivity.
Qed.
Lemma reference_control_ready_2720 old :
 reference_control_ready old reference_control_expr_2720.
Proof.
 unfold reference_control_expr_2720.
apply rc_binary.
Qed.
Lemma reference_control_member_2720 : List.In (2720,reference_control_expr_2720) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 223%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2720_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2720 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2720 reference_control_expr_2720 reference_control_2_positions reference_control_2_safety reference_control_member_2720) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2720 reference_control_expr_2720 inputs path old current result Position Safe Nonreg (reference_control_ready_2720 old ) Step).
Qed.
Theorem reference_control_node_2720_congruent inputs path left right next_left next_right :
 VM.find 2719 left = VM.find 2719 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2720 next_left = VM.find 2720 next_right.
Proof.
 intros  E2719 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2720 reference_control_expr_2720 reference_control_2_positions reference_control_2_safety reference_control_member_2720) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2720 reference_control_expr_2720 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2720 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2720 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2719.
 reflexivity.
Qed.
Lemma reference_control_ready_2721 old :
 (exists value ground, VM.find 2720 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2721.
Proof.
 intros H2720.
 destruct H2720 as [v2720 [G2720 [V2720 T2720]]].
 unfold reference_control_expr_2721.
apply rc_mux.
{ eapply rc_ref; [exact V2720|exists G2720; exact T2720].
}
{ apply rc_const.
}
Qed.
Lemma reference_control_member_2721 : List.In (2721,reference_control_expr_2721) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 224%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2721_ground inputs path old current result :
 (exists value ground, VM.find 2720 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2721 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2720 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2721 reference_control_expr_2721 reference_control_2_positions reference_control_2_safety reference_control_member_2721) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2721 reference_control_expr_2721 inputs path old current result Position Safe Nonreg (reference_control_ready_2721 old H2720) Step).
Qed.
Theorem reference_control_node_2721_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2720 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2718 left = VM.find 2718 right ->
 VM.find 2720 left = VM.find 2720 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2721 next_left = VM.find 2721 next_right.
Proof.
 intros H2720 E2718 E2720 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2721 reference_control_expr_2721 reference_control_2_positions reference_control_2_safety reference_control_member_2721) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2721 reference_control_expr_2721 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2721 left H2720)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2721 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2718.
 rewrite E2720.
 reflexivity.
Qed.
Lemma reference_control_ready_2722 old :
 (exists value ground, VM.find 2717 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2721 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2722.
Proof.
 intros H2717 H2721.
 destruct H2717 as [v2717 [G2717 [V2717 T2717]]].
 destruct H2721 as [v2721 [G2721 [V2721 T2721]]].
 unfold reference_control_expr_2722.
apply rc_mux.
{ eapply rc_ref; [exact V2717|exists G2717; exact T2717].
}
{ eapply rc_ref; [exact V2721|exists G2721; exact T2721].
}
Qed.
Lemma reference_control_member_2722 : List.In (2722,reference_control_expr_2722) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 225%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2722_ground inputs path old current result :
 (exists value ground, VM.find 2717 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2721 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2722 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2717 H2721 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2722 reference_control_expr_2722 reference_control_2_positions reference_control_2_safety reference_control_member_2722) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2722 reference_control_expr_2722 inputs path old current result Position Safe Nonreg (reference_control_ready_2722 old H2717 H2721) Step).
Qed.
Theorem reference_control_node_2722_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2717 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2721 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2715 left = VM.find 2715 right ->
 VM.find 2717 left = VM.find 2717 right ->
 VM.find 2721 left = VM.find 2721 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2722 next_left = VM.find 2722 next_right.
Proof.
 intros H2717 H2721 E2715 E2717 E2721 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2722 reference_control_expr_2722 reference_control_2_positions reference_control_2_safety reference_control_member_2722) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2722 reference_control_expr_2722 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2722 left H2717 H2721)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2722 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2715.
 rewrite E2717.
 rewrite E2721.
 reflexivity.
Qed.
Lemma reference_control_ready_2723 old :
 (exists value ground, VM.find 2714 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2722 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2723.
Proof.
 intros H2714 H2722.
 destruct H2714 as [v2714 [G2714 [V2714 T2714]]].
 destruct H2722 as [v2722 [G2722 [V2722 T2722]]].
 unfold reference_control_expr_2723.
apply rc_mux.
{ eapply rc_ref; [exact V2714|exists G2714; exact T2714].
}
{ eapply rc_ref; [exact V2722|exists G2722; exact T2722].
}
Qed.
Lemma reference_control_member_2723 : List.In (2723,reference_control_expr_2723) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 226%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2723_ground inputs path old current result :
 (exists value ground, VM.find 2714 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2722 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2723 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2714 H2722 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2723 reference_control_expr_2723 reference_control_2_positions reference_control_2_safety reference_control_member_2723) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2723 reference_control_expr_2723 inputs path old current result Position Safe Nonreg (reference_control_ready_2723 old H2714 H2722) Step).
Qed.
Theorem reference_control_node_2723_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2714 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2722 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2709 left = VM.find 2709 right ->
 VM.find 2714 left = VM.find 2714 right ->
 VM.find 2722 left = VM.find 2722 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2723 next_left = VM.find 2723 next_right.
Proof.
 intros H2714 H2722 E2709 E2714 E2722 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2723 reference_control_expr_2723 reference_control_2_positions reference_control_2_safety reference_control_member_2723) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2723 reference_control_expr_2723 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2723 left H2714 H2722)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2723 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2709.
 rewrite E2714.
 rewrite E2722.
 reflexivity.
Qed.
Lemma reference_control_ready_2724 old :
 reference_control_ready old reference_control_expr_2724.
Proof.
 unfold reference_control_expr_2724.
apply rc_binary.
Qed.
Lemma reference_control_member_2724 : List.In (2724,reference_control_expr_2724) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 227%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2724_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2724 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2724 reference_control_expr_2724 reference_control_2_positions reference_control_2_safety reference_control_member_2724) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2724 reference_control_expr_2724 inputs path old current result Position Safe Nonreg (reference_control_ready_2724 old ) Step).
Qed.
Theorem reference_control_node_2724_congruent inputs path left right next_left next_right :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2724 next_left = VM.find 2724 next_right.
Proof.
 intros   L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2724 reference_control_expr_2724 reference_control_2_positions reference_control_2_safety reference_control_member_2724) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2724 reference_control_expr_2724 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2724 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2724 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 reflexivity.
Qed.
Lemma reference_control_ready_2725 old :
 reference_control_ready old reference_control_expr_2725.
Proof.
 unfold reference_control_expr_2725.
apply rc_unary.
Qed.
Lemma reference_control_member_2725 : List.In (2725,reference_control_expr_2725) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 228%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2725_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2725 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2725 reference_control_expr_2725 reference_control_2_positions reference_control_2_safety reference_control_member_2725) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2725 reference_control_expr_2725 inputs path old current result Position Safe Nonreg (reference_control_ready_2725 old ) Step).
Qed.
Theorem reference_control_node_2725_congruent inputs path left right next_left next_right :
 VM.find 2622 left = VM.find 2622 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2725 next_left = VM.find 2725 next_right.
Proof.
 intros  E2622 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2725 reference_control_expr_2725 reference_control_2_positions reference_control_2_safety reference_control_member_2725) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2725 reference_control_expr_2725 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2725 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2725 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2622.
 reflexivity.
Qed.
Lemma reference_control_ready_2726 old :
 reference_control_ready old reference_control_expr_2726.
Proof.
 unfold reference_control_expr_2726.
apply rc_binary.
Qed.
Lemma reference_control_member_2726 : List.In (2726,reference_control_expr_2726) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 229%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2726_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2726 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2726 reference_control_expr_2726 reference_control_2_positions reference_control_2_safety reference_control_member_2726) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2726 reference_control_expr_2726 inputs path old current result Position Safe Nonreg (reference_control_ready_2726 old ) Step).
Qed.
Theorem reference_control_node_2726_congruent inputs path left right next_left next_right :
 VM.find 2725 left = VM.find 2725 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2726 next_left = VM.find 2726 next_right.
Proof.
 intros  E2725 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2726 reference_control_expr_2726 reference_control_2_positions reference_control_2_safety reference_control_member_2726) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2726 reference_control_expr_2726 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2726 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2726 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2725.
 reflexivity.
Qed.
Lemma reference_control_ready_2727 old :
 reference_control_ready old reference_control_expr_2727.
Proof.
 unfold reference_control_expr_2727.
apply rc_binary.
Qed.
Lemma reference_control_member_2727 : List.In (2727,reference_control_expr_2727) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 230%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2727_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2727 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2727 reference_control_expr_2727 reference_control_2_positions reference_control_2_safety reference_control_member_2727) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2727 reference_control_expr_2727 inputs path old current result Position Safe Nonreg (reference_control_ready_2727 old ) Step).
Qed.
Theorem reference_control_node_2727_congruent inputs path left right next_left next_right :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2727 next_left = VM.find 2727 next_right.
Proof.
 intros   L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2727 reference_control_expr_2727 reference_control_2_positions reference_control_2_safety reference_control_member_2727) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2727 reference_control_expr_2727 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2727 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2727 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 reflexivity.
Qed.
Lemma reference_control_ready_2728 old :
 reference_control_ready old reference_control_expr_2728.
Proof.
 unfold reference_control_expr_2728.
apply rc_unary.
Qed.
Lemma reference_control_member_2728 : List.In (2728,reference_control_expr_2728) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 231%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2728_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2728 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2728 reference_control_expr_2728 reference_control_2_positions reference_control_2_safety reference_control_member_2728) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2728 reference_control_expr_2728 inputs path old current result Position Safe Nonreg (reference_control_ready_2728 old ) Step).
Qed.
Theorem reference_control_node_2728_congruent inputs path left right next_left next_right :
 VM.find 2622 left = VM.find 2622 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2728 next_left = VM.find 2728 next_right.
Proof.
 intros  E2622 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2728 reference_control_expr_2728 reference_control_2_positions reference_control_2_safety reference_control_member_2728) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2728 reference_control_expr_2728 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2728 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2728 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2622.
 reflexivity.
Qed.
Lemma reference_control_ready_2729 old :
 reference_control_ready old reference_control_expr_2729.
Proof.
 unfold reference_control_expr_2729.
apply rc_binary.
Qed.
Lemma reference_control_member_2729 : List.In (2729,reference_control_expr_2729) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 232%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2729_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2729 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2729 reference_control_expr_2729 reference_control_2_positions reference_control_2_safety reference_control_member_2729) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2729 reference_control_expr_2729 inputs path old current result Position Safe Nonreg (reference_control_ready_2729 old ) Step).
Qed.
Theorem reference_control_node_2729_congruent inputs path left right next_left next_right :
 VM.find 2728 left = VM.find 2728 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2729 next_left = VM.find 2729 next_right.
Proof.
 intros  E2728 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2729 reference_control_expr_2729 reference_control_2_positions reference_control_2_safety reference_control_member_2729) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2729 reference_control_expr_2729 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2729 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2729 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2728.
 reflexivity.
Qed.
Lemma reference_control_ready_2730 old :
 reference_control_ready old reference_control_expr_2730.
Proof.
 unfold reference_control_expr_2730.
apply rc_binary.
Qed.
Lemma reference_control_member_2730 : List.In (2730,reference_control_expr_2730) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 233%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2730_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2730 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2730 reference_control_expr_2730 reference_control_2_positions reference_control_2_safety reference_control_member_2730) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2730 reference_control_expr_2730 inputs path old current result Position Safe Nonreg (reference_control_ready_2730 old ) Step).
Qed.
Theorem reference_control_node_2730_congruent inputs path left right next_left next_right :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2730 next_left = VM.find 2730 next_right.
Proof.
 intros   L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2730 reference_control_expr_2730 reference_control_2_positions reference_control_2_safety reference_control_member_2730) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2730 reference_control_expr_2730 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2730 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2730 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 reflexivity.
Qed.
Lemma reference_control_ready_2731 old :
 reference_control_ready old reference_control_expr_2731.
Proof.
 unfold reference_control_expr_2731.
apply rc_unary.
Qed.
Lemma reference_control_member_2731 : List.In (2731,reference_control_expr_2731) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 234%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2731_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2731 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2731 reference_control_expr_2731 reference_control_2_positions reference_control_2_safety reference_control_member_2731) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2731 reference_control_expr_2731 inputs path old current result Position Safe Nonreg (reference_control_ready_2731 old ) Step).
Qed.
Theorem reference_control_node_2731_congruent inputs path left right next_left next_right :
 VM.find 2622 left = VM.find 2622 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2731 next_left = VM.find 2731 next_right.
Proof.
 intros  E2622 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2731 reference_control_expr_2731 reference_control_2_positions reference_control_2_safety reference_control_member_2731) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2731 reference_control_expr_2731 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2731 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2731 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2622.
 reflexivity.
Qed.
Lemma reference_control_ready_2732 old :
 reference_control_ready old reference_control_expr_2732.
Proof.
 unfold reference_control_expr_2732.
apply rc_binary.
Qed.
Lemma reference_control_member_2732 : List.In (2732,reference_control_expr_2732) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 235%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2732_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2732 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2732 reference_control_expr_2732 reference_control_2_positions reference_control_2_safety reference_control_member_2732) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2732 reference_control_expr_2732 inputs path old current result Position Safe Nonreg (reference_control_ready_2732 old ) Step).
Qed.
Theorem reference_control_node_2732_congruent inputs path left right next_left next_right :
 VM.find 2731 left = VM.find 2731 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2732 next_left = VM.find 2732 next_right.
Proof.
 intros  E2731 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2732 reference_control_expr_2732 reference_control_2_positions reference_control_2_safety reference_control_member_2732) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2732 reference_control_expr_2732 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2732 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2732 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2731.
 reflexivity.
Qed.
Lemma reference_control_ready_2733 old :
 (exists value ground, VM.find 2732 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2733.
Proof.
 intros H2732.
 destruct H2732 as [v2732 [G2732 [V2732 T2732]]].
 unfold reference_control_expr_2733.
apply rc_mux.
{ eapply rc_ref; [exact V2732|exists G2732; exact T2732].
}
{ apply rc_const.
}
Qed.
Lemma reference_control_member_2733 : List.In (2733,reference_control_expr_2733) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 236%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2733_ground inputs path old current result :
 (exists value ground, VM.find 2732 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2733 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2732 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2733 reference_control_expr_2733 reference_control_2_positions reference_control_2_safety reference_control_member_2733) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2733 reference_control_expr_2733 inputs path old current result Position Safe Nonreg (reference_control_ready_2733 old H2732) Step).
Qed.
Theorem reference_control_node_2733_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2732 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2730 left = VM.find 2730 right ->
 VM.find 2732 left = VM.find 2732 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2733 next_left = VM.find 2733 next_right.
Proof.
 intros H2732 E2730 E2732 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2733 reference_control_expr_2733 reference_control_2_positions reference_control_2_safety reference_control_member_2733) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2733 reference_control_expr_2733 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2733 left H2732)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2733 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2730.
 rewrite E2732.
 reflexivity.
Qed.
Lemma reference_control_ready_2734 old :
 (exists value ground, VM.find 2729 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2733 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2734.
Proof.
 intros H2729 H2733.
 destruct H2729 as [v2729 [G2729 [V2729 T2729]]].
 destruct H2733 as [v2733 [G2733 [V2733 T2733]]].
 unfold reference_control_expr_2734.
apply rc_mux.
{ eapply rc_ref; [exact V2729|exists G2729; exact T2729].
}
{ eapply rc_ref; [exact V2733|exists G2733; exact T2733].
}
Qed.
Lemma reference_control_member_2734 : List.In (2734,reference_control_expr_2734) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 237%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2734_ground inputs path old current result :
 (exists value ground, VM.find 2729 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2733 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2734 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2729 H2733 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2734 reference_control_expr_2734 reference_control_2_positions reference_control_2_safety reference_control_member_2734) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2734 reference_control_expr_2734 inputs path old current result Position Safe Nonreg (reference_control_ready_2734 old H2729 H2733) Step).
Qed.
Theorem reference_control_node_2734_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2729 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2733 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2727 left = VM.find 2727 right ->
 VM.find 2729 left = VM.find 2729 right ->
 VM.find 2733 left = VM.find 2733 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2734 next_left = VM.find 2734 next_right.
Proof.
 intros H2729 H2733 E2727 E2729 E2733 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2734 reference_control_expr_2734 reference_control_2_positions reference_control_2_safety reference_control_member_2734) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2734 reference_control_expr_2734 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2734 left H2729 H2733)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2734 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2727.
 rewrite E2729.
 rewrite E2733.
 reflexivity.
Qed.
Lemma reference_control_ready_2735 old :
 (exists value ground, VM.find 2726 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2734 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2735.
Proof.
 intros H2726 H2734.
 destruct H2726 as [v2726 [G2726 [V2726 T2726]]].
 destruct H2734 as [v2734 [G2734 [V2734 T2734]]].
 unfold reference_control_expr_2735.
apply rc_mux.
{ eapply rc_ref; [exact V2726|exists G2726; exact T2726].
}
{ eapply rc_ref; [exact V2734|exists G2734; exact T2734].
}
Qed.
Lemma reference_control_member_2735 : List.In (2735,reference_control_expr_2735) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 238%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2735_ground inputs path old current result :
 (exists value ground, VM.find 2726 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2734 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2735 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2726 H2734 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2735 reference_control_expr_2735 reference_control_2_positions reference_control_2_safety reference_control_member_2735) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2735 reference_control_expr_2735 inputs path old current result Position Safe Nonreg (reference_control_ready_2735 old H2726 H2734) Step).
Qed.
Theorem reference_control_node_2735_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2726 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2734 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2724 left = VM.find 2724 right ->
 VM.find 2726 left = VM.find 2726 right ->
 VM.find 2734 left = VM.find 2734 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2735 next_left = VM.find 2735 next_right.
Proof.
 intros H2726 H2734 E2724 E2726 E2734 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2735 reference_control_expr_2735 reference_control_2_positions reference_control_2_safety reference_control_member_2735) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2735 reference_control_expr_2735 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2735 left H2726 H2734)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2735 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2724.
 rewrite E2726.
 rewrite E2734.
 reflexivity.
Qed.
Lemma reference_control_ready_2736 old :
 reference_control_ready old reference_control_expr_2736.
Proof.
 unfold reference_control_expr_2736.
apply rc_binary.
Qed.
Lemma reference_control_member_2736 : List.In (2736,reference_control_expr_2736) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 239%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2736_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2736 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2736 reference_control_expr_2736 reference_control_2_positions reference_control_2_safety reference_control_member_2736) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2736 reference_control_expr_2736 inputs path old current result Position Safe Nonreg (reference_control_ready_2736 old ) Step).
Qed.
Theorem reference_control_node_2736_congruent inputs path left right next_left next_right :
 VM.find 2735 left = VM.find 2735 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2736 next_left = VM.find 2736 next_right.
Proof.
 intros  E2735 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2736 reference_control_expr_2736 reference_control_2_positions reference_control_2_safety reference_control_member_2736) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2736 reference_control_expr_2736 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2736 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2736 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2735.
 reflexivity.
Qed.
Lemma reference_control_ready_2747 old :
 (exists value ground, VM.find 1786 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2747.
Proof.
 intros H1786.
 destruct H1786 as [v1786 [G1786 [V1786 T1786]]].
 unfold reference_control_expr_2747.
eapply rc_ref; [exact V1786|exists G1786; exact T1786].
Qed.
Lemma reference_control_member_2747 : List.In (2747,reference_control_expr_2747) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 240%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2747_ground inputs path old current result :
 (exists value ground, VM.find 1786 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2747 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H1786 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2747 reference_control_expr_2747 reference_control_2_positions reference_control_2_safety reference_control_member_2747) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2747 reference_control_expr_2747 inputs path old current result Position Safe Nonreg (reference_control_ready_2747 old H1786) Step).
Qed.
Theorem reference_control_node_2747_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 1786 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1786 left = VM.find 1786 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2747 next_left = VM.find 2747 next_right.
Proof.
 intros H1786 E1786 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2747 reference_control_expr_2747 reference_control_2_positions reference_control_2_safety reference_control_member_2747) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2747 reference_control_expr_2747 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2747 left H1786)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2747 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1786.
 reflexivity.
Qed.
Lemma reference_control_ready_2748 old :
 reference_control_ready old reference_control_expr_2748.
Proof.
 unfold reference_control_expr_2748.
apply rc_binary.
Qed.
Lemma reference_control_member_2748 : List.In (2748,reference_control_expr_2748) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 241%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2748_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2748 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2748 reference_control_expr_2748 reference_control_2_positions reference_control_2_safety reference_control_member_2748) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2748 reference_control_expr_2748 inputs path old current result Position Safe Nonreg (reference_control_ready_2748 old ) Step).
Qed.
Theorem reference_control_node_2748_congruent inputs path left right next_left next_right :
 VM.find 2747 left = VM.find 2747 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2748 next_left = VM.find 2748 next_right.
Proof.
 intros  E2747 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2748 reference_control_expr_2748 reference_control_2_positions reference_control_2_safety reference_control_member_2748) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2748 reference_control_expr_2748 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2748 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2748 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2747.
 reflexivity.
Qed.
Lemma reference_control_ready_2750 old :
 reference_control_ready old reference_control_expr_2750.
Proof.
 unfold reference_control_expr_2750.
apply rc_binary.
Qed.
Lemma reference_control_member_2750 : List.In (2750,reference_control_expr_2750) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 242%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2750_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2750 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2750 reference_control_expr_2750 reference_control_2_positions reference_control_2_safety reference_control_member_2750) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2750 reference_control_expr_2750 inputs path old current result Position Safe Nonreg (reference_control_ready_2750 old ) Step).
Qed.
Theorem reference_control_node_2750_congruent inputs path left right next_left next_right :
 VM.find 2747 left = VM.find 2747 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2750 next_left = VM.find 2750 next_right.
Proof.
 intros  E2747 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2750 reference_control_expr_2750 reference_control_2_positions reference_control_2_safety reference_control_member_2750) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2750 reference_control_expr_2750 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2750 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2750 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2747.
 reflexivity.
Qed.
Lemma reference_control_ready_2751 old :
 reference_control_ready old reference_control_expr_2751.
Proof.
 unfold reference_control_expr_2751.
apply rc_binary.
Qed.
Lemma reference_control_member_2751 : List.In (2751,reference_control_expr_2751) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 243%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2751_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2751 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2751 reference_control_expr_2751 reference_control_2_positions reference_control_2_safety reference_control_member_2751) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2751 reference_control_expr_2751 inputs path old current result Position Safe Nonreg (reference_control_ready_2751 old ) Step).
Qed.
Theorem reference_control_node_2751_congruent inputs path left right next_left next_right :
 VM.find 2747 left = VM.find 2747 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2751 next_left = VM.find 2751 next_right.
Proof.
 intros  E2747 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2751 reference_control_expr_2751 reference_control_2_positions reference_control_2_safety reference_control_member_2751) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2751 reference_control_expr_2751 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2751 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2751 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2747.
 reflexivity.
Qed.
Lemma reference_control_ready_2772 old :
 (exists value ground, VM.find 2209 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2772.
Proof.
 intros H2209.
 destruct H2209 as [v2209 [G2209 [V2209 T2209]]].
 unfold reference_control_expr_2772.
eapply rc_ref; [exact V2209|exists G2209; exact T2209].
Qed.
Lemma reference_control_member_2772 : List.In (2772,reference_control_expr_2772) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 244%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2772_ground inputs path old current result :
 (exists value ground, VM.find 2209 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2772 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2209 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2772 reference_control_expr_2772 reference_control_2_positions reference_control_2_safety reference_control_member_2772) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2772 reference_control_expr_2772 inputs path old current result Position Safe Nonreg (reference_control_ready_2772 old H2209) Step).
Qed.
Theorem reference_control_node_2772_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2209 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2209 left = VM.find 2209 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2772 next_left = VM.find 2772 next_right.
Proof.
 intros H2209 E2209 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2772 reference_control_expr_2772 reference_control_2_positions reference_control_2_safety reference_control_member_2772) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2772 reference_control_expr_2772 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2772 left H2209)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2772 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2209.
 reflexivity.
Qed.
Lemma reference_control_ready_2773 old :
 (exists value ground, VM.find 2177 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2773.
Proof.
 intros H2177.
 destruct H2177 as [v2177 [G2177 [V2177 T2177]]].
 unfold reference_control_expr_2773.
apply rc_validif.
eapply rc_ref; [exact V2177|exists G2177; exact T2177].
Qed.
Lemma reference_control_member_2773 : List.In (2773,reference_control_expr_2773) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 245%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2773_ground inputs path old current result :
 (exists value ground, VM.find 2177 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2773 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2177 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2773 reference_control_expr_2773 reference_control_2_positions reference_control_2_safety reference_control_member_2773) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2773 reference_control_expr_2773 inputs path old current result Position Safe Nonreg (reference_control_ready_2773 old H2177) Step).
Qed.
Theorem reference_control_node_2773_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2177 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2177 left = VM.find 2177 right ->
 VM.find 2622 left = VM.find 2622 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2773 next_left = VM.find 2773 next_right.
Proof.
 intros H2177 E2177 E2622 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2773 reference_control_expr_2773 reference_control_2_positions reference_control_2_safety reference_control_member_2773) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2773 reference_control_expr_2773 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2773 left H2177)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2773 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2177.
 rewrite E2622.
 reflexivity.
Qed.
Lemma reference_control_ready_2774 old :
 (exists value ground, VM.find 2176 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2773 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2774.
Proof.
 intros H2176 H2773.
 destruct H2176 as [v2176 [G2176 [V2176 T2176]]].
 destruct H2773 as [v2773 [G2773 [V2773 T2773]]].
 unfold reference_control_expr_2774.
apply rc_mux.
{ eapply rc_ref; [exact V2176|exists G2176; exact T2176].
}
{ eapply rc_ref; [exact V2773|exists G2773; exact T2773].
}
Qed.
Lemma reference_control_member_2774 : List.In (2774,reference_control_expr_2774) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 246%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2774_ground inputs path old current result :
 (exists value ground, VM.find 2176 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2773 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2774 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2176 H2773 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2774 reference_control_expr_2774 reference_control_2_positions reference_control_2_safety reference_control_member_2774) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2774 reference_control_expr_2774 inputs path old current result Position Safe Nonreg (reference_control_ready_2774 old H2176 H2773) Step).
Qed.
Theorem reference_control_node_2774_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2176 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2773 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2176 left = VM.find 2176 right ->
 VM.find 2622 left = VM.find 2622 right ->
 VM.find 2773 left = VM.find 2773 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2774 next_left = VM.find 2774 next_right.
Proof.
 intros H2176 H2773 E2176 E2622 E2773 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2774 reference_control_expr_2774 reference_control_2_positions reference_control_2_safety reference_control_member_2774) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2774 reference_control_expr_2774 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2774 left H2176 H2773)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2774 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2176.
 rewrite E2622.
 rewrite E2773.
 reflexivity.
Qed.
Lemma reference_control_ready_2775 old :
 (exists value ground, VM.find 2175 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2774 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2775.
Proof.
 intros H2175 H2774.
 destruct H2175 as [v2175 [G2175 [V2175 T2175]]].
 destruct H2774 as [v2774 [G2774 [V2774 T2774]]].
 unfold reference_control_expr_2775.
apply rc_mux.
{ eapply rc_ref; [exact V2175|exists G2175; exact T2175].
}
{ eapply rc_ref; [exact V2774|exists G2774; exact T2774].
}
Qed.
Lemma reference_control_member_2775 : List.In (2775,reference_control_expr_2775) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 247%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2775_ground inputs path old current result :
 (exists value ground, VM.find 2175 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2774 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2775 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2175 H2774 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2775 reference_control_expr_2775 reference_control_2_positions reference_control_2_safety reference_control_member_2775) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2775 reference_control_expr_2775 inputs path old current result Position Safe Nonreg (reference_control_ready_2775 old H2175 H2774) Step).
Qed.
Theorem reference_control_node_2775_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2175 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2774 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2175 left = VM.find 2175 right ->
 VM.find 2622 left = VM.find 2622 right ->
 VM.find 2774 left = VM.find 2774 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2775 next_left = VM.find 2775 next_right.
Proof.
 intros H2175 H2774 E2175 E2622 E2774 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2775 reference_control_expr_2775 reference_control_2_positions reference_control_2_safety reference_control_member_2775) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2775 reference_control_expr_2775 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2775 left H2175 H2774)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2775 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2175.
 rewrite E2622.
 rewrite E2774.
 reflexivity.
Qed.
Lemma reference_control_ready_2776 old :
 (exists value ground, VM.find 2174 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2775 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2776.
Proof.
 intros H2174 H2775.
 destruct H2174 as [v2174 [G2174 [V2174 T2174]]].
 destruct H2775 as [v2775 [G2775 [V2775 T2775]]].
 unfold reference_control_expr_2776.
apply rc_mux.
{ eapply rc_ref; [exact V2174|exists G2174; exact T2174].
}
{ eapply rc_ref; [exact V2775|exists G2775; exact T2775].
}
Qed.
Lemma reference_control_member_2776 : List.In (2776,reference_control_expr_2776) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 248%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2776_ground inputs path old current result :
 (exists value ground, VM.find 2174 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2775 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2776 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2174 H2775 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2776 reference_control_expr_2776 reference_control_2_positions reference_control_2_safety reference_control_member_2776) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2776 reference_control_expr_2776 inputs path old current result Position Safe Nonreg (reference_control_ready_2776 old H2174 H2775) Step).
Qed.
Theorem reference_control_node_2776_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2174 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2775 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2174 left = VM.find 2174 right ->
 VM.find 2622 left = VM.find 2622 right ->
 VM.find 2775 left = VM.find 2775 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2776 next_left = VM.find 2776 next_right.
Proof.
 intros H2174 H2775 E2174 E2622 E2775 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2776 reference_control_expr_2776 reference_control_2_positions reference_control_2_safety reference_control_member_2776) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2776 reference_control_expr_2776 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2776 left H2174 H2775)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2776 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2174.
 rewrite E2622.
 rewrite E2775.
 reflexivity.
Qed.
Lemma reference_control_ready_2777 old :
 (exists value ground, VM.find 2173 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2776 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2777.
Proof.
 intros H2173 H2776.
 destruct H2173 as [v2173 [G2173 [V2173 T2173]]].
 destruct H2776 as [v2776 [G2776 [V2776 T2776]]].
 unfold reference_control_expr_2777.
apply rc_mux.
{ eapply rc_ref; [exact V2173|exists G2173; exact T2173].
}
{ eapply rc_ref; [exact V2776|exists G2776; exact T2776].
}
Qed.
Lemma reference_control_member_2777 : List.In (2777,reference_control_expr_2777) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 249%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2777_ground inputs path old current result :
 (exists value ground, VM.find 2173 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2776 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2777 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2173 H2776 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2777 reference_control_expr_2777 reference_control_2_positions reference_control_2_safety reference_control_member_2777) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2777 reference_control_expr_2777 inputs path old current result Position Safe Nonreg (reference_control_ready_2777 old H2173 H2776) Step).
Qed.
Theorem reference_control_node_2777_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2173 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2776 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2173 left = VM.find 2173 right ->
 VM.find 2622 left = VM.find 2622 right ->
 VM.find 2776 left = VM.find 2776 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2777 next_left = VM.find 2777 next_right.
Proof.
 intros H2173 H2776 E2173 E2622 E2776 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2777 reference_control_expr_2777 reference_control_2_positions reference_control_2_safety reference_control_member_2777) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2777 reference_control_expr_2777 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2777 left H2173 H2776)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2777 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2173.
 rewrite E2622.
 rewrite E2776.
 reflexivity.
Qed.
Lemma reference_control_ready_2778 old :
 (exists value ground, VM.find 2172 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2777 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2778.
Proof.
 intros H2172 H2777.
 destruct H2172 as [v2172 [G2172 [V2172 T2172]]].
 destruct H2777 as [v2777 [G2777 [V2777 T2777]]].
 unfold reference_control_expr_2778.
apply rc_mux.
{ eapply rc_ref; [exact V2172|exists G2172; exact T2172].
}
{ eapply rc_ref; [exact V2777|exists G2777; exact T2777].
}
Qed.
Lemma reference_control_member_2778 : List.In (2778,reference_control_expr_2778) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 250%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2778_ground inputs path old current result :
 (exists value ground, VM.find 2172 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2777 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2778 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2172 H2777 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2778 reference_control_expr_2778 reference_control_2_positions reference_control_2_safety reference_control_member_2778) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2778 reference_control_expr_2778 inputs path old current result Position Safe Nonreg (reference_control_ready_2778 old H2172 H2777) Step).
Qed.
Theorem reference_control_node_2778_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2172 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2777 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2172 left = VM.find 2172 right ->
 VM.find 2622 left = VM.find 2622 right ->
 VM.find 2777 left = VM.find 2777 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2778 next_left = VM.find 2778 next_right.
Proof.
 intros H2172 H2777 E2172 E2622 E2777 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2778 reference_control_expr_2778 reference_control_2_positions reference_control_2_safety reference_control_member_2778) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2778 reference_control_expr_2778 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2778 left H2172 H2777)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2778 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2172.
 rewrite E2622.
 rewrite E2777.
 reflexivity.
Qed.
Lemma reference_control_ready_2779 old :
 (exists value ground, VM.find 2171 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2778 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2779.
Proof.
 intros H2171 H2778.
 destruct H2171 as [v2171 [G2171 [V2171 T2171]]].
 destruct H2778 as [v2778 [G2778 [V2778 T2778]]].
 unfold reference_control_expr_2779.
apply rc_mux.
{ eapply rc_ref; [exact V2171|exists G2171; exact T2171].
}
{ eapply rc_ref; [exact V2778|exists G2778; exact T2778].
}
Qed.
Lemma reference_control_member_2779 : List.In (2779,reference_control_expr_2779) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 251%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2779_ground inputs path old current result :
 (exists value ground, VM.find 2171 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2778 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2779 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2171 H2778 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2779 reference_control_expr_2779 reference_control_2_positions reference_control_2_safety reference_control_member_2779) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2779 reference_control_expr_2779 inputs path old current result Position Safe Nonreg (reference_control_ready_2779 old H2171 H2778) Step).
Qed.
Theorem reference_control_node_2779_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2171 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2778 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2171 left = VM.find 2171 right ->
 VM.find 2622 left = VM.find 2622 right ->
 VM.find 2778 left = VM.find 2778 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2779 next_left = VM.find 2779 next_right.
Proof.
 intros H2171 H2778 E2171 E2622 E2778 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2779 reference_control_expr_2779 reference_control_2_positions reference_control_2_safety reference_control_member_2779) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2779 reference_control_expr_2779 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2779 left H2171 H2778)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2779 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2171.
 rewrite E2622.
 rewrite E2778.
 reflexivity.
Qed.
Lemma reference_control_ready_2780 old :
 (exists value ground, VM.find 2170 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2779 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2780.
Proof.
 intros H2170 H2779.
 destruct H2170 as [v2170 [G2170 [V2170 T2170]]].
 destruct H2779 as [v2779 [G2779 [V2779 T2779]]].
 unfold reference_control_expr_2780.
apply rc_mux.
{ eapply rc_ref; [exact V2170|exists G2170; exact T2170].
}
{ eapply rc_ref; [exact V2779|exists G2779; exact T2779].
}
Qed.
Lemma reference_control_member_2780 : List.In (2780,reference_control_expr_2780) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 252%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2780_ground inputs path old current result :
 (exists value ground, VM.find 2170 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2779 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2780 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2170 H2779 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2780 reference_control_expr_2780 reference_control_2_positions reference_control_2_safety reference_control_member_2780) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2780 reference_control_expr_2780 inputs path old current result Position Safe Nonreg (reference_control_ready_2780 old H2170 H2779) Step).
Qed.
Theorem reference_control_node_2780_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2170 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2779 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2170 left = VM.find 2170 right ->
 VM.find 2622 left = VM.find 2622 right ->
 VM.find 2779 left = VM.find 2779 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2780 next_left = VM.find 2780 next_right.
Proof.
 intros H2170 H2779 E2170 E2622 E2779 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2780 reference_control_expr_2780 reference_control_2_positions reference_control_2_safety reference_control_member_2780) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2780 reference_control_expr_2780 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2780 left H2170 H2779)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2780 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2170.
 rewrite E2622.
 rewrite E2779.
 reflexivity.
Qed.
Lemma reference_control_ready_2781 old :
 (exists value ground, VM.find 2169 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2780 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2781.
Proof.
 intros H2169 H2780.
 destruct H2169 as [v2169 [G2169 [V2169 T2169]]].
 destruct H2780 as [v2780 [G2780 [V2780 T2780]]].
 unfold reference_control_expr_2781.
apply rc_mux.
{ eapply rc_ref; [exact V2169|exists G2169; exact T2169].
}
{ eapply rc_ref; [exact V2780|exists G2780; exact T2780].
}
Qed.
Lemma reference_control_member_2781 : List.In (2781,reference_control_expr_2781) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 253%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2781_ground inputs path old current result :
 (exists value ground, VM.find 2169 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2780 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2781 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2169 H2780 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2781 reference_control_expr_2781 reference_control_2_positions reference_control_2_safety reference_control_member_2781) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2781 reference_control_expr_2781 inputs path old current result Position Safe Nonreg (reference_control_ready_2781 old H2169 H2780) Step).
Qed.
Theorem reference_control_node_2781_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2169 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2780 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2169 left = VM.find 2169 right ->
 VM.find 2622 left = VM.find 2622 right ->
 VM.find 2780 left = VM.find 2780 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2781 next_left = VM.find 2781 next_right.
Proof.
 intros H2169 H2780 E2169 E2622 E2780 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2781 reference_control_expr_2781 reference_control_2_positions reference_control_2_safety reference_control_member_2781) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2781 reference_control_expr_2781 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2781 left H2169 H2780)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2781 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2169.
 rewrite E2622.
 rewrite E2780.
 reflexivity.
Qed.
Lemma reference_control_ready_2782 old :
 (exists value ground, VM.find 2168 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2781 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2782.
Proof.
 intros H2168 H2781.
 destruct H2168 as [v2168 [G2168 [V2168 T2168]]].
 destruct H2781 as [v2781 [G2781 [V2781 T2781]]].
 unfold reference_control_expr_2782.
apply rc_mux.
{ eapply rc_ref; [exact V2168|exists G2168; exact T2168].
}
{ eapply rc_ref; [exact V2781|exists G2781; exact T2781].
}
Qed.
Lemma reference_control_member_2782 : List.In (2782,reference_control_expr_2782) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 254%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2782_ground inputs path old current result :
 (exists value ground, VM.find 2168 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2781 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2782 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2168 H2781 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2782 reference_control_expr_2782 reference_control_2_positions reference_control_2_safety reference_control_member_2782) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2782 reference_control_expr_2782 inputs path old current result Position Safe Nonreg (reference_control_ready_2782 old H2168 H2781) Step).
Qed.
Theorem reference_control_node_2782_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2168 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2781 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2168 left = VM.find 2168 right ->
 VM.find 2622 left = VM.find 2622 right ->
 VM.find 2781 left = VM.find 2781 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2782 next_left = VM.find 2782 next_right.
Proof.
 intros H2168 H2781 E2168 E2622 E2781 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2782 reference_control_expr_2782 reference_control_2_positions reference_control_2_safety reference_control_member_2782) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2782 reference_control_expr_2782 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2782 left H2168 H2781)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2782 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2168.
 rewrite E2622.
 rewrite E2781.
 reflexivity.
Qed.
Lemma reference_control_ready_2783 old :
 (exists value ground, VM.find 2167 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2782 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2783.
Proof.
 intros H2167 H2782.
 destruct H2167 as [v2167 [G2167 [V2167 T2167]]].
 destruct H2782 as [v2782 [G2782 [V2782 T2782]]].
 unfold reference_control_expr_2783.
apply rc_mux.
{ eapply rc_ref; [exact V2167|exists G2167; exact T2167].
}
{ eapply rc_ref; [exact V2782|exists G2782; exact T2782].
}
Qed.
Lemma reference_control_member_2783 : List.In (2783,reference_control_expr_2783) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 255%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2783_ground inputs path old current result :
 (exists value ground, VM.find 2167 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2782 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2783 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2167 H2782 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2783 reference_control_expr_2783 reference_control_2_positions reference_control_2_safety reference_control_member_2783) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2783 reference_control_expr_2783 inputs path old current result Position Safe Nonreg (reference_control_ready_2783 old H2167 H2782) Step).
Qed.
Theorem reference_control_node_2783_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2167 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2782 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2167 left = VM.find 2167 right ->
 VM.find 2622 left = VM.find 2622 right ->
 VM.find 2782 left = VM.find 2782 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2783 next_left = VM.find 2783 next_right.
Proof.
 intros H2167 H2782 E2167 E2622 E2782 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2783 reference_control_expr_2783 reference_control_2_positions reference_control_2_safety reference_control_member_2783) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2783 reference_control_expr_2783 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2783 left H2167 H2782)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2783 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2167.
 rewrite E2622.
 rewrite E2782.
 reflexivity.
Qed.
Lemma reference_control_ready_2784 old :
 (exists value ground, VM.find 2166 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2783 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2784.
Proof.
 intros H2166 H2783.
 destruct H2166 as [v2166 [G2166 [V2166 T2166]]].
 destruct H2783 as [v2783 [G2783 [V2783 T2783]]].
 unfold reference_control_expr_2784.
apply rc_mux.
{ eapply rc_ref; [exact V2166|exists G2166; exact T2166].
}
{ eapply rc_ref; [exact V2783|exists G2783; exact T2783].
}
Qed.
Lemma reference_control_member_2784 : List.In (2784,reference_control_expr_2784) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 256%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2784_ground inputs path old current result :
 (exists value ground, VM.find 2166 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2783 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2784 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2166 H2783 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2784 reference_control_expr_2784 reference_control_2_positions reference_control_2_safety reference_control_member_2784) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2784 reference_control_expr_2784 inputs path old current result Position Safe Nonreg (reference_control_ready_2784 old H2166 H2783) Step).
Qed.
Theorem reference_control_node_2784_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2166 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2783 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2166 left = VM.find 2166 right ->
 VM.find 2622 left = VM.find 2622 right ->
 VM.find 2783 left = VM.find 2783 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2784 next_left = VM.find 2784 next_right.
Proof.
 intros H2166 H2783 E2166 E2622 E2783 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2784 reference_control_expr_2784 reference_control_2_positions reference_control_2_safety reference_control_member_2784) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2784 reference_control_expr_2784 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2784 left H2166 H2783)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2784 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2166.
 rewrite E2622.
 rewrite E2783.
 reflexivity.
Qed.
Lemma reference_control_ready_2785 old :
 (exists value ground, VM.find 2165 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2784 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2785.
Proof.
 intros H2165 H2784.
 destruct H2165 as [v2165 [G2165 [V2165 T2165]]].
 destruct H2784 as [v2784 [G2784 [V2784 T2784]]].
 unfold reference_control_expr_2785.
apply rc_mux.
{ eapply rc_ref; [exact V2165|exists G2165; exact T2165].
}
{ eapply rc_ref; [exact V2784|exists G2784; exact T2784].
}
Qed.
Lemma reference_control_member_2785 : List.In (2785,reference_control_expr_2785) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 257%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2785_ground inputs path old current result :
 (exists value ground, VM.find 2165 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2784 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2785 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2165 H2784 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2785 reference_control_expr_2785 reference_control_2_positions reference_control_2_safety reference_control_member_2785) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2785 reference_control_expr_2785 inputs path old current result Position Safe Nonreg (reference_control_ready_2785 old H2165 H2784) Step).
Qed.
Theorem reference_control_node_2785_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2165 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2784 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2165 left = VM.find 2165 right ->
 VM.find 2622 left = VM.find 2622 right ->
 VM.find 2784 left = VM.find 2784 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2785 next_left = VM.find 2785 next_right.
Proof.
 intros H2165 H2784 E2165 E2622 E2784 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2785 reference_control_expr_2785 reference_control_2_positions reference_control_2_safety reference_control_member_2785) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2785 reference_control_expr_2785 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2785 left H2165 H2784)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2785 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2165.
 rewrite E2622.
 rewrite E2784.
 reflexivity.
Qed.
Lemma reference_control_ready_2786 old :
 (exists value ground, VM.find 2164 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2785 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2786.
Proof.
 intros H2164 H2785.
 destruct H2164 as [v2164 [G2164 [V2164 T2164]]].
 destruct H2785 as [v2785 [G2785 [V2785 T2785]]].
 unfold reference_control_expr_2786.
apply rc_mux.
{ eapply rc_ref; [exact V2164|exists G2164; exact T2164].
}
{ eapply rc_ref; [exact V2785|exists G2785; exact T2785].
}
Qed.
Lemma reference_control_member_2786 : List.In (2786,reference_control_expr_2786) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 258%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2786_ground inputs path old current result :
 (exists value ground, VM.find 2164 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2785 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2786 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2164 H2785 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2786 reference_control_expr_2786 reference_control_2_positions reference_control_2_safety reference_control_member_2786) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2786 reference_control_expr_2786 inputs path old current result Position Safe Nonreg (reference_control_ready_2786 old H2164 H2785) Step).
Qed.
Theorem reference_control_node_2786_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2164 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2785 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2164 left = VM.find 2164 right ->
 VM.find 2622 left = VM.find 2622 right ->
 VM.find 2785 left = VM.find 2785 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2786 next_left = VM.find 2786 next_right.
Proof.
 intros H2164 H2785 E2164 E2622 E2785 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2786 reference_control_expr_2786 reference_control_2_positions reference_control_2_safety reference_control_member_2786) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2786 reference_control_expr_2786 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2786 left H2164 H2785)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2786 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2164.
 rewrite E2622.
 rewrite E2785.
 reflexivity.
Qed.
Lemma reference_control_ready_2787 old :
 (exists value ground, VM.find 2163 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2786 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2787.
Proof.
 intros H2163 H2786.
 destruct H2163 as [v2163 [G2163 [V2163 T2163]]].
 destruct H2786 as [v2786 [G2786 [V2786 T2786]]].
 unfold reference_control_expr_2787.
apply rc_mux.
{ eapply rc_ref; [exact V2163|exists G2163; exact T2163].
}
{ eapply rc_ref; [exact V2786|exists G2786; exact T2786].
}
Qed.
Lemma reference_control_member_2787 : List.In (2787,reference_control_expr_2787) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 259%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2787_ground inputs path old current result :
 (exists value ground, VM.find 2163 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2786 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2787 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2163 H2786 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2787 reference_control_expr_2787 reference_control_2_positions reference_control_2_safety reference_control_member_2787) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2787 reference_control_expr_2787 inputs path old current result Position Safe Nonreg (reference_control_ready_2787 old H2163 H2786) Step).
Qed.
Theorem reference_control_node_2787_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2163 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2786 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2163 left = VM.find 2163 right ->
 VM.find 2622 left = VM.find 2622 right ->
 VM.find 2786 left = VM.find 2786 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2787 next_left = VM.find 2787 next_right.
Proof.
 intros H2163 H2786 E2163 E2622 E2786 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2787 reference_control_expr_2787 reference_control_2_positions reference_control_2_safety reference_control_member_2787) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2787 reference_control_expr_2787 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2787 left H2163 H2786)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2787 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2163.
 rewrite E2622.
 rewrite E2786.
 reflexivity.
Qed.
Lemma reference_control_ready_2788 old :
 (exists value ground, VM.find 2162 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2787 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2788.
Proof.
 intros H2162 H2787.
 destruct H2162 as [v2162 [G2162 [V2162 T2162]]].
 destruct H2787 as [v2787 [G2787 [V2787 T2787]]].
 unfold reference_control_expr_2788.
apply rc_mux.
{ eapply rc_ref; [exact V2162|exists G2162; exact T2162].
}
{ eapply rc_ref; [exact V2787|exists G2787; exact T2787].
}
Qed.
Lemma reference_control_member_2788 : List.In (2788,reference_control_expr_2788) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 260%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2788_ground inputs path old current result :
 (exists value ground, VM.find 2162 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2787 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2788 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2162 H2787 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2788 reference_control_expr_2788 reference_control_2_positions reference_control_2_safety reference_control_member_2788) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2788 reference_control_expr_2788 inputs path old current result Position Safe Nonreg (reference_control_ready_2788 old H2162 H2787) Step).
Qed.
Theorem reference_control_node_2788_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2162 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2787 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2162 left = VM.find 2162 right ->
 VM.find 2622 left = VM.find 2622 right ->
 VM.find 2787 left = VM.find 2787 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2788 next_left = VM.find 2788 next_right.
Proof.
 intros H2162 H2787 E2162 E2622 E2787 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2788 reference_control_expr_2788 reference_control_2_positions reference_control_2_safety reference_control_member_2788) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2788 reference_control_expr_2788 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2788 left H2162 H2787)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2788 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2162.
 rewrite E2622.
 rewrite E2787.
 reflexivity.
Qed.
Lemma reference_control_ready_2789 old :
 (exists value ground, VM.find 2161 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2788 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2789.
Proof.
 intros H2161 H2788.
 destruct H2161 as [v2161 [G2161 [V2161 T2161]]].
 destruct H2788 as [v2788 [G2788 [V2788 T2788]]].
 unfold reference_control_expr_2789.
apply rc_mux.
{ eapply rc_ref; [exact V2161|exists G2161; exact T2161].
}
{ eapply rc_ref; [exact V2788|exists G2788; exact T2788].
}
Qed.
Lemma reference_control_member_2789 : List.In (2789,reference_control_expr_2789) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 261%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2789_ground inputs path old current result :
 (exists value ground, VM.find 2161 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2788 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2789 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2161 H2788 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2789 reference_control_expr_2789 reference_control_2_positions reference_control_2_safety reference_control_member_2789) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2789 reference_control_expr_2789 inputs path old current result Position Safe Nonreg (reference_control_ready_2789 old H2161 H2788) Step).
Qed.
Theorem reference_control_node_2789_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2161 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2788 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2161 left = VM.find 2161 right ->
 VM.find 2622 left = VM.find 2622 right ->
 VM.find 2788 left = VM.find 2788 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2789 next_left = VM.find 2789 next_right.
Proof.
 intros H2161 H2788 E2161 E2622 E2788 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2789 reference_control_expr_2789 reference_control_2_positions reference_control_2_safety reference_control_member_2789) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2789 reference_control_expr_2789 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2789 left H2161 H2788)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2789 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2161.
 rewrite E2622.
 rewrite E2788.
 reflexivity.
Qed.
Lemma reference_control_ready_2790 old :
 (exists value ground, VM.find 2160 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2789 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2790.
Proof.
 intros H2160 H2789.
 destruct H2160 as [v2160 [G2160 [V2160 T2160]]].
 destruct H2789 as [v2789 [G2789 [V2789 T2789]]].
 unfold reference_control_expr_2790.
apply rc_mux.
{ eapply rc_ref; [exact V2160|exists G2160; exact T2160].
}
{ eapply rc_ref; [exact V2789|exists G2789; exact T2789].
}
Qed.
Lemma reference_control_member_2790 : List.In (2790,reference_control_expr_2790) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 262%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2790_ground inputs path old current result :
 (exists value ground, VM.find 2160 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2789 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2790 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2160 H2789 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2790 reference_control_expr_2790 reference_control_2_positions reference_control_2_safety reference_control_member_2790) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2790 reference_control_expr_2790 inputs path old current result Position Safe Nonreg (reference_control_ready_2790 old H2160 H2789) Step).
Qed.
Theorem reference_control_node_2790_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2160 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2789 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2160 left = VM.find 2160 right ->
 VM.find 2622 left = VM.find 2622 right ->
 VM.find 2789 left = VM.find 2789 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2790 next_left = VM.find 2790 next_right.
Proof.
 intros H2160 H2789 E2160 E2622 E2789 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2790 reference_control_expr_2790 reference_control_2_positions reference_control_2_safety reference_control_member_2790) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2790 reference_control_expr_2790 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2790 left H2160 H2789)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2790 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2160.
 rewrite E2622.
 rewrite E2789.
 reflexivity.
Qed.
Lemma reference_control_ready_2791 old :
 (exists value ground, VM.find 2159 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2790 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2791.
Proof.
 intros H2159 H2790.
 destruct H2159 as [v2159 [G2159 [V2159 T2159]]].
 destruct H2790 as [v2790 [G2790 [V2790 T2790]]].
 unfold reference_control_expr_2791.
apply rc_mux.
{ eapply rc_ref; [exact V2159|exists G2159; exact T2159].
}
{ eapply rc_ref; [exact V2790|exists G2790; exact T2790].
}
Qed.
Lemma reference_control_member_2791 : List.In (2791,reference_control_expr_2791) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 263%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2791_ground inputs path old current result :
 (exists value ground, VM.find 2159 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2790 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2791 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2159 H2790 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2791 reference_control_expr_2791 reference_control_2_positions reference_control_2_safety reference_control_member_2791) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2791 reference_control_expr_2791 inputs path old current result Position Safe Nonreg (reference_control_ready_2791 old H2159 H2790) Step).
Qed.
Theorem reference_control_node_2791_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2159 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2790 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2159 left = VM.find 2159 right ->
 VM.find 2622 left = VM.find 2622 right ->
 VM.find 2790 left = VM.find 2790 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2791 next_left = VM.find 2791 next_right.
Proof.
 intros H2159 H2790 E2159 E2622 E2790 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2791 reference_control_expr_2791 reference_control_2_positions reference_control_2_safety reference_control_member_2791) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2791 reference_control_expr_2791 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2791 left H2159 H2790)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2791 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2159.
 rewrite E2622.
 rewrite E2790.
 reflexivity.
Qed.
Lemma reference_control_ready_2792 old :
 (exists value ground, VM.find 2158 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2791 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2792.
Proof.
 intros H2158 H2791.
 destruct H2158 as [v2158 [G2158 [V2158 T2158]]].
 destruct H2791 as [v2791 [G2791 [V2791 T2791]]].
 unfold reference_control_expr_2792.
apply rc_mux.
{ eapply rc_ref; [exact V2158|exists G2158; exact T2158].
}
{ eapply rc_ref; [exact V2791|exists G2791; exact T2791].
}
Qed.
Lemma reference_control_member_2792 : List.In (2792,reference_control_expr_2792) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 264%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2792_ground inputs path old current result :
 (exists value ground, VM.find 2158 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2791 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2792 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2158 H2791 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2792 reference_control_expr_2792 reference_control_2_positions reference_control_2_safety reference_control_member_2792) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2792 reference_control_expr_2792 inputs path old current result Position Safe Nonreg (reference_control_ready_2792 old H2158 H2791) Step).
Qed.
Theorem reference_control_node_2792_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2158 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2791 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2158 left = VM.find 2158 right ->
 VM.find 2622 left = VM.find 2622 right ->
 VM.find 2791 left = VM.find 2791 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2792 next_left = VM.find 2792 next_right.
Proof.
 intros H2158 H2791 E2158 E2622 E2791 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2792 reference_control_expr_2792 reference_control_2_positions reference_control_2_safety reference_control_member_2792) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2792 reference_control_expr_2792 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2792 left H2158 H2791)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2792 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2158.
 rewrite E2622.
 rewrite E2791.
 reflexivity.
Qed.
Lemma reference_control_ready_2793 old :
 (exists value ground, VM.find 2157 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2792 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2793.
Proof.
 intros H2157 H2792.
 destruct H2157 as [v2157 [G2157 [V2157 T2157]]].
 destruct H2792 as [v2792 [G2792 [V2792 T2792]]].
 unfold reference_control_expr_2793.
apply rc_mux.
{ eapply rc_ref; [exact V2157|exists G2157; exact T2157].
}
{ eapply rc_ref; [exact V2792|exists G2792; exact T2792].
}
Qed.
Lemma reference_control_member_2793 : List.In (2793,reference_control_expr_2793) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 265%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2793_ground inputs path old current result :
 (exists value ground, VM.find 2157 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2792 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2793 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2157 H2792 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2793 reference_control_expr_2793 reference_control_2_positions reference_control_2_safety reference_control_member_2793) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2793 reference_control_expr_2793 inputs path old current result Position Safe Nonreg (reference_control_ready_2793 old H2157 H2792) Step).
Qed.
Theorem reference_control_node_2793_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2157 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2792 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2157 left = VM.find 2157 right ->
 VM.find 2622 left = VM.find 2622 right ->
 VM.find 2792 left = VM.find 2792 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2793 next_left = VM.find 2793 next_right.
Proof.
 intros H2157 H2792 E2157 E2622 E2792 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2793 reference_control_expr_2793 reference_control_2_positions reference_control_2_safety reference_control_member_2793) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2793 reference_control_expr_2793 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2793 left H2157 H2792)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2793 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2157.
 rewrite E2622.
 rewrite E2792.
 reflexivity.
Qed.
Lemma reference_control_ready_2794 old :
 (exists value ground, VM.find 2156 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2793 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2794.
Proof.
 intros H2156 H2793.
 destruct H2156 as [v2156 [G2156 [V2156 T2156]]].
 destruct H2793 as [v2793 [G2793 [V2793 T2793]]].
 unfold reference_control_expr_2794.
apply rc_mux.
{ eapply rc_ref; [exact V2156|exists G2156; exact T2156].
}
{ eapply rc_ref; [exact V2793|exists G2793; exact T2793].
}
Qed.
Lemma reference_control_member_2794 : List.In (2794,reference_control_expr_2794) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 266%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2794_ground inputs path old current result :
 (exists value ground, VM.find 2156 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2793 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2794 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2156 H2793 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2794 reference_control_expr_2794 reference_control_2_positions reference_control_2_safety reference_control_member_2794) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2794 reference_control_expr_2794 inputs path old current result Position Safe Nonreg (reference_control_ready_2794 old H2156 H2793) Step).
Qed.
Theorem reference_control_node_2794_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2156 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2793 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2156 left = VM.find 2156 right ->
 VM.find 2622 left = VM.find 2622 right ->
 VM.find 2793 left = VM.find 2793 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2794 next_left = VM.find 2794 next_right.
Proof.
 intros H2156 H2793 E2156 E2622 E2793 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2794 reference_control_expr_2794 reference_control_2_positions reference_control_2_safety reference_control_member_2794) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2794 reference_control_expr_2794 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2794 left H2156 H2793)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2794 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2156.
 rewrite E2622.
 rewrite E2793.
 reflexivity.
Qed.
Lemma reference_control_ready_2795 old :
 (exists value ground, VM.find 2155 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2794 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2795.
Proof.
 intros H2155 H2794.
 destruct H2155 as [v2155 [G2155 [V2155 T2155]]].
 destruct H2794 as [v2794 [G2794 [V2794 T2794]]].
 unfold reference_control_expr_2795.
apply rc_mux.
{ eapply rc_ref; [exact V2155|exists G2155; exact T2155].
}
{ eapply rc_ref; [exact V2794|exists G2794; exact T2794].
}
Qed.
Lemma reference_control_member_2795 : List.In (2795,reference_control_expr_2795) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 267%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2795_ground inputs path old current result :
 (exists value ground, VM.find 2155 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2794 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2795 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2155 H2794 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2795 reference_control_expr_2795 reference_control_2_positions reference_control_2_safety reference_control_member_2795) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2795 reference_control_expr_2795 inputs path old current result Position Safe Nonreg (reference_control_ready_2795 old H2155 H2794) Step).
Qed.
Theorem reference_control_node_2795_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2155 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2794 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2155 left = VM.find 2155 right ->
 VM.find 2622 left = VM.find 2622 right ->
 VM.find 2794 left = VM.find 2794 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2795 next_left = VM.find 2795 next_right.
Proof.
 intros H2155 H2794 E2155 E2622 E2794 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2795 reference_control_expr_2795 reference_control_2_positions reference_control_2_safety reference_control_member_2795) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2795 reference_control_expr_2795 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2795 left H2155 H2794)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2795 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2155.
 rewrite E2622.
 rewrite E2794.
 reflexivity.
Qed.
Lemma reference_control_ready_2796 old :
 (exists value ground, VM.find 2154 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2795 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2796.
Proof.
 intros H2154 H2795.
 destruct H2154 as [v2154 [G2154 [V2154 T2154]]].
 destruct H2795 as [v2795 [G2795 [V2795 T2795]]].
 unfold reference_control_expr_2796.
apply rc_mux.
{ eapply rc_ref; [exact V2154|exists G2154; exact T2154].
}
{ eapply rc_ref; [exact V2795|exists G2795; exact T2795].
}
Qed.
Lemma reference_control_member_2796 : List.In (2796,reference_control_expr_2796) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 268%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2796_ground inputs path old current result :
 (exists value ground, VM.find 2154 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2795 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2796 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2154 H2795 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2796 reference_control_expr_2796 reference_control_2_positions reference_control_2_safety reference_control_member_2796) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2796 reference_control_expr_2796 inputs path old current result Position Safe Nonreg (reference_control_ready_2796 old H2154 H2795) Step).
Qed.
Theorem reference_control_node_2796_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2154 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2795 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2154 left = VM.find 2154 right ->
 VM.find 2622 left = VM.find 2622 right ->
 VM.find 2795 left = VM.find 2795 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2796 next_left = VM.find 2796 next_right.
Proof.
 intros H2154 H2795 E2154 E2622 E2795 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2796 reference_control_expr_2796 reference_control_2_positions reference_control_2_safety reference_control_member_2796) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2796 reference_control_expr_2796 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2796 left H2154 H2795)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2796 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2154.
 rewrite E2622.
 rewrite E2795.
 reflexivity.
Qed.
Lemma reference_control_ready_2797 old :
 (exists value ground, VM.find 2153 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2796 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2797.
Proof.
 intros H2153 H2796.
 destruct H2153 as [v2153 [G2153 [V2153 T2153]]].
 destruct H2796 as [v2796 [G2796 [V2796 T2796]]].
 unfold reference_control_expr_2797.
apply rc_mux.
{ eapply rc_ref; [exact V2153|exists G2153; exact T2153].
}
{ eapply rc_ref; [exact V2796|exists G2796; exact T2796].
}
Qed.
Lemma reference_control_member_2797 : List.In (2797,reference_control_expr_2797) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 269%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2797_ground inputs path old current result :
 (exists value ground, VM.find 2153 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2796 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2797 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2153 H2796 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2797 reference_control_expr_2797 reference_control_2_positions reference_control_2_safety reference_control_member_2797) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2797 reference_control_expr_2797 inputs path old current result Position Safe Nonreg (reference_control_ready_2797 old H2153 H2796) Step).
Qed.
Theorem reference_control_node_2797_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2153 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2796 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2153 left = VM.find 2153 right ->
 VM.find 2622 left = VM.find 2622 right ->
 VM.find 2796 left = VM.find 2796 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2797 next_left = VM.find 2797 next_right.
Proof.
 intros H2153 H2796 E2153 E2622 E2796 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2797 reference_control_expr_2797 reference_control_2_positions reference_control_2_safety reference_control_member_2797) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2797 reference_control_expr_2797 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2797 left H2153 H2796)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2797 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2153.
 rewrite E2622.
 rewrite E2796.
 reflexivity.
Qed.
Lemma reference_control_ready_2798 old :
 (exists value ground, VM.find 2152 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2797 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2798.
Proof.
 intros H2152 H2797.
 destruct H2152 as [v2152 [G2152 [V2152 T2152]]].
 destruct H2797 as [v2797 [G2797 [V2797 T2797]]].
 unfold reference_control_expr_2798.
apply rc_mux.
{ eapply rc_ref; [exact V2152|exists G2152; exact T2152].
}
{ eapply rc_ref; [exact V2797|exists G2797; exact T2797].
}
Qed.
Lemma reference_control_member_2798 : List.In (2798,reference_control_expr_2798) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 270%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2798_ground inputs path old current result :
 (exists value ground, VM.find 2152 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2797 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2798 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2152 H2797 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2798 reference_control_expr_2798 reference_control_2_positions reference_control_2_safety reference_control_member_2798) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2798 reference_control_expr_2798 inputs path old current result Position Safe Nonreg (reference_control_ready_2798 old H2152 H2797) Step).
Qed.
Theorem reference_control_node_2798_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2152 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2797 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2152 left = VM.find 2152 right ->
 VM.find 2622 left = VM.find 2622 right ->
 VM.find 2797 left = VM.find 2797 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2798 next_left = VM.find 2798 next_right.
Proof.
 intros H2152 H2797 E2152 E2622 E2797 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2798 reference_control_expr_2798 reference_control_2_positions reference_control_2_safety reference_control_member_2798) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2798 reference_control_expr_2798 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2798 left H2152 H2797)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2798 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2152.
 rewrite E2622.
 rewrite E2797.
 reflexivity.
Qed.
Lemma reference_control_ready_2799 old :
 (exists value ground, VM.find 2151 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2798 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2799.
Proof.
 intros H2151 H2798.
 destruct H2151 as [v2151 [G2151 [V2151 T2151]]].
 destruct H2798 as [v2798 [G2798 [V2798 T2798]]].
 unfold reference_control_expr_2799.
apply rc_mux.
{ eapply rc_ref; [exact V2151|exists G2151; exact T2151].
}
{ eapply rc_ref; [exact V2798|exists G2798; exact T2798].
}
Qed.
Lemma reference_control_member_2799 : List.In (2799,reference_control_expr_2799) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 271%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2799_ground inputs path old current result :
 (exists value ground, VM.find 2151 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2798 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2799 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2151 H2798 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2799 reference_control_expr_2799 reference_control_2_positions reference_control_2_safety reference_control_member_2799) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2799 reference_control_expr_2799 inputs path old current result Position Safe Nonreg (reference_control_ready_2799 old H2151 H2798) Step).
Qed.
Theorem reference_control_node_2799_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2151 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2798 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2151 left = VM.find 2151 right ->
 VM.find 2622 left = VM.find 2622 right ->
 VM.find 2798 left = VM.find 2798 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2799 next_left = VM.find 2799 next_right.
Proof.
 intros H2151 H2798 E2151 E2622 E2798 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2799 reference_control_expr_2799 reference_control_2_positions reference_control_2_safety reference_control_member_2799) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2799 reference_control_expr_2799 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2799 left H2151 H2798)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2799 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2151.
 rewrite E2622.
 rewrite E2798.
 reflexivity.
Qed.
Lemma reference_control_ready_2800 old :
 (exists value ground, VM.find 2150 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2799 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2800.
Proof.
 intros H2150 H2799.
 destruct H2150 as [v2150 [G2150 [V2150 T2150]]].
 destruct H2799 as [v2799 [G2799 [V2799 T2799]]].
 unfold reference_control_expr_2800.
apply rc_mux.
{ eapply rc_ref; [exact V2150|exists G2150; exact T2150].
}
{ eapply rc_ref; [exact V2799|exists G2799; exact T2799].
}
Qed.
Lemma reference_control_member_2800 : List.In (2800,reference_control_expr_2800) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 272%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2800_ground inputs path old current result :
 (exists value ground, VM.find 2150 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2799 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2800 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2150 H2799 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2800 reference_control_expr_2800 reference_control_2_positions reference_control_2_safety reference_control_member_2800) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2800 reference_control_expr_2800 inputs path old current result Position Safe Nonreg (reference_control_ready_2800 old H2150 H2799) Step).
Qed.
Theorem reference_control_node_2800_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2150 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2799 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2150 left = VM.find 2150 right ->
 VM.find 2622 left = VM.find 2622 right ->
 VM.find 2799 left = VM.find 2799 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2800 next_left = VM.find 2800 next_right.
Proof.
 intros H2150 H2799 E2150 E2622 E2799 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2800 reference_control_expr_2800 reference_control_2_positions reference_control_2_safety reference_control_member_2800) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2800 reference_control_expr_2800 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2800 left H2150 H2799)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2800 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2150.
 rewrite E2622.
 rewrite E2799.
 reflexivity.
Qed.
Lemma reference_control_ready_2801 old :
 (exists value ground, VM.find 2149 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2800 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2801.
Proof.
 intros H2149 H2800.
 destruct H2149 as [v2149 [G2149 [V2149 T2149]]].
 destruct H2800 as [v2800 [G2800 [V2800 T2800]]].
 unfold reference_control_expr_2801.
apply rc_mux.
{ eapply rc_ref; [exact V2149|exists G2149; exact T2149].
}
{ eapply rc_ref; [exact V2800|exists G2800; exact T2800].
}
Qed.
Lemma reference_control_member_2801 : List.In (2801,reference_control_expr_2801) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 273%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2801_ground inputs path old current result :
 (exists value ground, VM.find 2149 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2800 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2801 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2149 H2800 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2801 reference_control_expr_2801 reference_control_2_positions reference_control_2_safety reference_control_member_2801) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2801 reference_control_expr_2801 inputs path old current result Position Safe Nonreg (reference_control_ready_2801 old H2149 H2800) Step).
Qed.
Theorem reference_control_node_2801_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2149 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2800 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2149 left = VM.find 2149 right ->
 VM.find 2622 left = VM.find 2622 right ->
 VM.find 2800 left = VM.find 2800 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2801 next_left = VM.find 2801 next_right.
Proof.
 intros H2149 H2800 E2149 E2622 E2800 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2801 reference_control_expr_2801 reference_control_2_positions reference_control_2_safety reference_control_member_2801) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2801 reference_control_expr_2801 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2801 left H2149 H2800)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2801 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2149.
 rewrite E2622.
 rewrite E2800.
 reflexivity.
Qed.
Lemma reference_control_ready_2802 old :
 (exists value ground, VM.find 2148 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2801 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2802.
Proof.
 intros H2148 H2801.
 destruct H2148 as [v2148 [G2148 [V2148 T2148]]].
 destruct H2801 as [v2801 [G2801 [V2801 T2801]]].
 unfold reference_control_expr_2802.
apply rc_mux.
{ eapply rc_ref; [exact V2148|exists G2148; exact T2148].
}
{ eapply rc_ref; [exact V2801|exists G2801; exact T2801].
}
Qed.
Lemma reference_control_member_2802 : List.In (2802,reference_control_expr_2802) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 274%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2802_ground inputs path old current result :
 (exists value ground, VM.find 2148 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2801 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2802 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2148 H2801 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2802 reference_control_expr_2802 reference_control_2_positions reference_control_2_safety reference_control_member_2802) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2802 reference_control_expr_2802 inputs path old current result Position Safe Nonreg (reference_control_ready_2802 old H2148 H2801) Step).
Qed.
Theorem reference_control_node_2802_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2148 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2801 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2148 left = VM.find 2148 right ->
 VM.find 2622 left = VM.find 2622 right ->
 VM.find 2801 left = VM.find 2801 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2802 next_left = VM.find 2802 next_right.
Proof.
 intros H2148 H2801 E2148 E2622 E2801 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2802 reference_control_expr_2802 reference_control_2_positions reference_control_2_safety reference_control_member_2802) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2802 reference_control_expr_2802 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2802 left H2148 H2801)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2802 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2148.
 rewrite E2622.
 rewrite E2801.
 reflexivity.
Qed.
Lemma reference_control_ready_2803 old :
 (exists value ground, VM.find 2147 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2802 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2803.
Proof.
 intros H2147 H2802.
 destruct H2147 as [v2147 [G2147 [V2147 T2147]]].
 destruct H2802 as [v2802 [G2802 [V2802 T2802]]].
 unfold reference_control_expr_2803.
apply rc_mux.
{ eapply rc_ref; [exact V2147|exists G2147; exact T2147].
}
{ eapply rc_ref; [exact V2802|exists G2802; exact T2802].
}
Qed.
Lemma reference_control_member_2803 : List.In (2803,reference_control_expr_2803) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 275%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2803_ground inputs path old current result :
 (exists value ground, VM.find 2147 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2802 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2803 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2147 H2802 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2803 reference_control_expr_2803 reference_control_2_positions reference_control_2_safety reference_control_member_2803) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2803 reference_control_expr_2803 inputs path old current result Position Safe Nonreg (reference_control_ready_2803 old H2147 H2802) Step).
Qed.
Theorem reference_control_node_2803_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2147 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2802 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2147 left = VM.find 2147 right ->
 VM.find 2622 left = VM.find 2622 right ->
 VM.find 2802 left = VM.find 2802 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2803 next_left = VM.find 2803 next_right.
Proof.
 intros H2147 H2802 E2147 E2622 E2802 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2803 reference_control_expr_2803 reference_control_2_positions reference_control_2_safety reference_control_member_2803) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2803 reference_control_expr_2803 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2803 left H2147 H2802)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2803 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2147.
 rewrite E2622.
 rewrite E2802.
 reflexivity.
Qed.
Lemma reference_control_ready_2804 old :
 (exists value ground, VM.find 2146 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2803 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2804.
Proof.
 intros H2146 H2803.
 destruct H2146 as [v2146 [G2146 [V2146 T2146]]].
 destruct H2803 as [v2803 [G2803 [V2803 T2803]]].
 unfold reference_control_expr_2804.
apply rc_mux.
{ eapply rc_ref; [exact V2146|exists G2146; exact T2146].
}
{ eapply rc_ref; [exact V2803|exists G2803; exact T2803].
}
Qed.
Lemma reference_control_member_2804 : List.In (2804,reference_control_expr_2804) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 276%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2804_ground inputs path old current result :
 (exists value ground, VM.find 2146 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2803 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2804 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2146 H2803 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2804 reference_control_expr_2804 reference_control_2_positions reference_control_2_safety reference_control_member_2804) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2804 reference_control_expr_2804 inputs path old current result Position Safe Nonreg (reference_control_ready_2804 old H2146 H2803) Step).
Qed.
Theorem reference_control_node_2804_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2146 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2803 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2146 left = VM.find 2146 right ->
 VM.find 2622 left = VM.find 2622 right ->
 VM.find 2803 left = VM.find 2803 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2804 next_left = VM.find 2804 next_right.
Proof.
 intros H2146 H2803 E2146 E2622 E2803 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2804 reference_control_expr_2804 reference_control_2_positions reference_control_2_safety reference_control_member_2804) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2804 reference_control_expr_2804 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2804 left H2146 H2803)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2804 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2146.
 rewrite E2622.
 rewrite E2803.
 reflexivity.
Qed.
Lemma reference_control_ready_2805 old :
 (exists value ground, VM.find 2804 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2805.
Proof.
 intros H2804.
 destruct H2804 as [v2804 [G2804 [V2804 T2804]]].
 unfold reference_control_expr_2805.
eapply rc_ref; [exact V2804|exists G2804; exact T2804].
Qed.
Lemma reference_control_member_2805 : List.In (2805,reference_control_expr_2805) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 277%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2805_ground inputs path old current result :
 (exists value ground, VM.find 2804 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2805 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2804 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2805 reference_control_expr_2805 reference_control_2_positions reference_control_2_safety reference_control_member_2805) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2805 reference_control_expr_2805 inputs path old current result Position Safe Nonreg (reference_control_ready_2805 old H2804) Step).
Qed.
Theorem reference_control_node_2805_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2804 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2804 left = VM.find 2804 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2805 next_left = VM.find 2805 next_right.
Proof.
 intros H2804 E2804 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2805 reference_control_expr_2805 reference_control_2_positions reference_control_2_safety reference_control_member_2805) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2805 reference_control_expr_2805 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2805 left H2804)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2805 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2804.
 reflexivity.
Qed.
Lemma reference_control_ready_2806 old :
 reference_control_ready old reference_control_expr_2806.
Proof.
 unfold reference_control_expr_2806.
apply rc_binary.
Qed.
Lemma reference_control_member_2806 : List.In (2806,reference_control_expr_2806) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 278%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2806_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2806 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2806 reference_control_expr_2806 reference_control_2_positions reference_control_2_safety reference_control_member_2806) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2806 reference_control_expr_2806 inputs path old current result Position Safe Nonreg (reference_control_ready_2806 old ) Step).
Qed.
Theorem reference_control_node_2806_congruent inputs path left right next_left next_right :
 VM.find 2772 left = VM.find 2772 right ->
 VM.find 2805 left = VM.find 2805 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2806 next_left = VM.find 2806 next_right.
Proof.
 intros  E2772 E2805 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2806 reference_control_expr_2806 reference_control_2_positions reference_control_2_safety reference_control_member_2806) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2806 reference_control_expr_2806 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2806 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2806 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2772.
 rewrite E2805.
 reflexivity.
Qed.
Lemma reference_control_ready_2807 old :
 (exists value ground, VM.find 1750 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2807.
Proof.
 intros H1750.
 destruct H1750 as [v1750 [G1750 [V1750 T1750]]].
 unfold reference_control_expr_2807.
eapply rc_ref; [exact V1750|exists G1750; exact T1750].
Qed.
Lemma reference_control_member_2807 : List.In (2807,reference_control_expr_2807) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 279%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2807_ground inputs path old current result :
 (exists value ground, VM.find 1750 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2807 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H1750 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2807 reference_control_expr_2807 reference_control_2_positions reference_control_2_safety reference_control_member_2807) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2807 reference_control_expr_2807 inputs path old current result Position Safe Nonreg (reference_control_ready_2807 old H1750) Step).
Qed.
Theorem reference_control_node_2807_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 1750 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1750 left = VM.find 1750 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2807 next_left = VM.find 2807 next_right.
Proof.
 intros H1750 E1750 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2807 reference_control_expr_2807 reference_control_2_positions reference_control_2_safety reference_control_member_2807) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2807 reference_control_expr_2807 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2807 left H1750)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2807 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1750.
 reflexivity.
Qed.
Lemma reference_control_ready_2808 old :
 reference_control_ready old reference_control_expr_2808.
Proof.
 unfold reference_control_expr_2808.
apply rc_unary.
Qed.
Lemma reference_control_member_2808 : List.In (2808,reference_control_expr_2808) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 280%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2808_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2808 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2808 reference_control_expr_2808 reference_control_2_positions reference_control_2_safety reference_control_member_2808) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2808 reference_control_expr_2808 inputs path old current result Position Safe Nonreg (reference_control_ready_2808 old ) Step).
Qed.
Theorem reference_control_node_2808_congruent inputs path left right next_left next_right :
 VM.find 2807 left = VM.find 2807 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2808 next_left = VM.find 2808 next_right.
Proof.
 intros  E2807 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2808 reference_control_expr_2808 reference_control_2_positions reference_control_2_safety reference_control_member_2808) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2808 reference_control_expr_2808 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2808 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2808 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2807.
 reflexivity.
Qed.
Lemma reference_control_ready_2809 old :
 reference_control_ready old reference_control_expr_2809.
Proof.
 unfold reference_control_expr_2809.
apply rc_binary.
Qed.
Lemma reference_control_member_2809 : List.In (2809,reference_control_expr_2809) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 281%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2809_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2809 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2809 reference_control_expr_2809 reference_control_2_positions reference_control_2_safety reference_control_member_2809) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2809 reference_control_expr_2809 inputs path old current result Position Safe Nonreg (reference_control_ready_2809 old ) Step).
Qed.
Theorem reference_control_node_2809_congruent inputs path left right next_left next_right :
 VM.find 2808 left = VM.find 2808 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2809 next_left = VM.find 2809 next_right.
Proof.
 intros  E2808 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2809 reference_control_expr_2809 reference_control_2_positions reference_control_2_safety reference_control_member_2809) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2809 reference_control_expr_2809 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2809 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2809 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2808.
 reflexivity.
Qed.
Lemma reference_control_ready_2810 old :
 reference_control_ready old reference_control_expr_2810.
Proof.
 unfold reference_control_expr_2810.
apply rc_mux.
{ apply rc_const.
}
{ apply rc_const.
}
Qed.
Lemma reference_control_member_2810 : List.In (2810,reference_control_expr_2810) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 282%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2810_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2810 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2810 reference_control_expr_2810 reference_control_2_positions reference_control_2_safety reference_control_member_2810) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2810 reference_control_expr_2810 inputs path old current result Position Safe Nonreg (reference_control_ready_2810 old ) Step).
Qed.
Theorem reference_control_node_2810_congruent inputs path left right next_left next_right :
 VM.find 2809 left = VM.find 2809 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2810 next_left = VM.find 2810 next_right.
Proof.
 intros  E2809 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2810 reference_control_expr_2810 reference_control_2_positions reference_control_2_safety reference_control_member_2810) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2810 reference_control_expr_2810 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2810 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2810 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2809.
 reflexivity.
Qed.
Lemma reference_control_ready_2811 old :
 reference_control_ready old reference_control_expr_2811.
Proof.
 unfold reference_control_expr_2811.
apply rc_binary.
Qed.
Lemma reference_control_member_2811 : List.In (2811,reference_control_expr_2811) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 283%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2811_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2811 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2811 reference_control_expr_2811 reference_control_2_positions reference_control_2_safety reference_control_member_2811) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2811 reference_control_expr_2811 inputs path old current result Position Safe Nonreg (reference_control_ready_2811 old ) Step).
Qed.
Theorem reference_control_node_2811_congruent inputs path left right next_left next_right :
 VM.find 2810 left = VM.find 2810 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2811 next_left = VM.find 2811 next_right.
Proof.
 intros  E2810 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2811 reference_control_expr_2811 reference_control_2_positions reference_control_2_safety reference_control_member_2811) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2811 reference_control_expr_2811 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2811 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2811 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2810.
 reflexivity.
Qed.
Lemma reference_control_ready_2812 old :
 (exists value ground, VM.find 1749 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2812.
Proof.
 intros H1749.
 destruct H1749 as [v1749 [G1749 [V1749 T1749]]].
 unfold reference_control_expr_2812.
eapply rc_ref; [exact V1749|exists G1749; exact T1749].
Qed.
Lemma reference_control_member_2812 : List.In (2812,reference_control_expr_2812) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 284%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2812_ground inputs path old current result :
 (exists value ground, VM.find 1749 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2812 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H1749 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2812 reference_control_expr_2812 reference_control_2_positions reference_control_2_safety reference_control_member_2812) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2812 reference_control_expr_2812 inputs path old current result Position Safe Nonreg (reference_control_ready_2812 old H1749) Step).
Qed.
Theorem reference_control_node_2812_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 1749 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1749 left = VM.find 1749 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2812 next_left = VM.find 2812 next_right.
Proof.
 intros H1749 E1749 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2812 reference_control_expr_2812 reference_control_2_positions reference_control_2_safety reference_control_member_2812) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2812 reference_control_expr_2812 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2812 left H1749)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2812 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1749.
 reflexivity.
Qed.
Lemma reference_control_ready_2813 old :
 reference_control_ready old reference_control_expr_2813.
Proof.
 unfold reference_control_expr_2813.
apply rc_binary.
Qed.
Lemma reference_control_member_2813 : List.In (2813,reference_control_expr_2813) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 285%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2813_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2813 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2813 reference_control_expr_2813 reference_control_2_positions reference_control_2_safety reference_control_member_2813) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2813 reference_control_expr_2813 inputs path old current result Position Safe Nonreg (reference_control_ready_2813 old ) Step).
Qed.
Theorem reference_control_node_2813_congruent inputs path left right next_left next_right :
 VM.find 2552 left = VM.find 2552 right ->
 VM.find 2812 left = VM.find 2812 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2813 next_left = VM.find 2813 next_right.
Proof.
 intros  E2552 E2812 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2813 reference_control_expr_2813 reference_control_2_positions reference_control_2_safety reference_control_member_2813) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2813 reference_control_expr_2813 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2813 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2813 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2552.
 rewrite E2812.
 reflexivity.
Qed.
Lemma reference_control_ready_2814 old :
 reference_control_ready old reference_control_expr_2814.
Proof.
 unfold reference_control_expr_2814.
apply rc_unary.
Qed.
Lemma reference_control_member_2814 : List.In (2814,reference_control_expr_2814) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 286%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2814_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2814 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2814 reference_control_expr_2814 reference_control_2_positions reference_control_2_safety reference_control_member_2814) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2814 reference_control_expr_2814 inputs path old current result Position Safe Nonreg (reference_control_ready_2814 old ) Step).
Qed.
Theorem reference_control_node_2814_congruent inputs path left right next_left next_right :
 VM.find 2813 left = VM.find 2813 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2814 next_left = VM.find 2814 next_right.
Proof.
 intros  E2813 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2814 reference_control_expr_2814 reference_control_2_positions reference_control_2_safety reference_control_member_2814) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2814 reference_control_expr_2814 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2814 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2814 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2813.
 reflexivity.
Qed.
Lemma reference_control_ready_2815 old :
 reference_control_ready old reference_control_expr_2815.
Proof.
 unfold reference_control_expr_2815.
apply rc_unary.
Qed.
Lemma reference_control_member_2815 : List.In (2815,reference_control_expr_2815) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 287%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2815_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2815 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2815 reference_control_expr_2815 reference_control_2_positions reference_control_2_safety reference_control_member_2815) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2815 reference_control_expr_2815 inputs path old current result Position Safe Nonreg (reference_control_ready_2815 old ) Step).
Qed.
Theorem reference_control_node_2815_congruent inputs path left right next_left next_right :
 VM.find 2814 left = VM.find 2814 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2815 next_left = VM.find 2815 next_right.
Proof.
 intros  E2814 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2815 reference_control_expr_2815 reference_control_2_positions reference_control_2_safety reference_control_member_2815) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2815 reference_control_expr_2815 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2815 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2815 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2814.
 reflexivity.
Qed.
Lemma reference_control_ready_2816 old :
 reference_control_ready old reference_control_expr_2816.
Proof.
 unfold reference_control_expr_2816.
apply rc_binary.
Qed.
Lemma reference_control_member_2816 : List.In (2816,reference_control_expr_2816) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 288%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2816_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2816 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2816 reference_control_expr_2816 reference_control_2_positions reference_control_2_safety reference_control_member_2816) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2816 reference_control_expr_2816 inputs path old current result Position Safe Nonreg (reference_control_ready_2816 old ) Step).
Qed.
Theorem reference_control_node_2816_congruent inputs path left right next_left next_right :
 VM.find 2815 left = VM.find 2815 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2816 next_left = VM.find 2816 next_right.
Proof.
 intros  E2815 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2816 reference_control_expr_2816 reference_control_2_positions reference_control_2_safety reference_control_member_2816) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2816 reference_control_expr_2816 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2816 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2816 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2815.
 reflexivity.
Qed.
Lemma reference_control_ready_2817 old :
 reference_control_ready old reference_control_expr_2817.
Proof.
 unfold reference_control_expr_2817.
apply rc_binary.
Qed.
Lemma reference_control_member_2817 : List.In (2817,reference_control_expr_2817) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 289%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2817_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2817 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2817 reference_control_expr_2817 reference_control_2_positions reference_control_2_safety reference_control_member_2817) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2817 reference_control_expr_2817 inputs path old current result Position Safe Nonreg (reference_control_ready_2817 old ) Step).
Qed.
Theorem reference_control_node_2817_congruent inputs path left right next_left next_right :
 VM.find 2810 left = VM.find 2810 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2817 next_left = VM.find 2817 next_right.
Proof.
 intros  E2810 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2817 reference_control_expr_2817 reference_control_2_positions reference_control_2_safety reference_control_member_2817) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2817 reference_control_expr_2817 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2817 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2817 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2810.
 reflexivity.
Qed.
Lemma reference_control_ready_2818 old :
 reference_control_ready old reference_control_expr_2818.
Proof.
 unfold reference_control_expr_2818.
apply rc_unary.
Qed.
Lemma reference_control_member_2818 : List.In (2818,reference_control_expr_2818) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 290%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2818_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2818 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2818 reference_control_expr_2818 reference_control_2_positions reference_control_2_safety reference_control_member_2818) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2818 reference_control_expr_2818 inputs path old current result Position Safe Nonreg (reference_control_ready_2818 old ) Step).
Qed.
Theorem reference_control_node_2818_congruent inputs path left right next_left next_right :
 VM.find 2814 left = VM.find 2814 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2818 next_left = VM.find 2818 next_right.
Proof.
 intros  E2814 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2818 reference_control_expr_2818 reference_control_2_positions reference_control_2_safety reference_control_member_2818) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2818 reference_control_expr_2818 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2818 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2818 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2814.
 reflexivity.
Qed.
Lemma reference_control_ready_2819 old :
 reference_control_ready old reference_control_expr_2819.
Proof.
 unfold reference_control_expr_2819.
apply rc_binary.
Qed.
Lemma reference_control_member_2819 : List.In (2819,reference_control_expr_2819) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 291%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2819_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2819 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2819 reference_control_expr_2819 reference_control_2_positions reference_control_2_safety reference_control_member_2819) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2819 reference_control_expr_2819 inputs path old current result Position Safe Nonreg (reference_control_ready_2819 old ) Step).
Qed.
Theorem reference_control_node_2819_congruent inputs path left right next_left next_right :
 VM.find 2818 left = VM.find 2818 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2819 next_left = VM.find 2819 next_right.
Proof.
 intros  E2818 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2819 reference_control_expr_2819 reference_control_2_positions reference_control_2_safety reference_control_member_2819) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2819 reference_control_expr_2819 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2819 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2819 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2818.
 reflexivity.
Qed.
Lemma reference_control_ready_2820 old :
 reference_control_ready old reference_control_expr_2820.
Proof.
 unfold reference_control_expr_2820.
apply rc_binary.
Qed.
Lemma reference_control_member_2820 : List.In (2820,reference_control_expr_2820) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 292%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2820_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2820 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2820 reference_control_expr_2820 reference_control_2_positions reference_control_2_safety reference_control_member_2820) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2820 reference_control_expr_2820 inputs path old current result Position Safe Nonreg (reference_control_ready_2820 old ) Step).
Qed.
Theorem reference_control_node_2820_congruent inputs path left right next_left next_right :
 VM.find 2810 left = VM.find 2810 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2820 next_left = VM.find 2820 next_right.
Proof.
 intros  E2810 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2820 reference_control_expr_2820 reference_control_2_positions reference_control_2_safety reference_control_member_2820) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2820 reference_control_expr_2820 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2820 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2820 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2810.
 reflexivity.
Qed.
Lemma reference_control_ready_2821 old :
 reference_control_ready old reference_control_expr_2821.
Proof.
 unfold reference_control_expr_2821.
apply rc_unary.
Qed.
Lemma reference_control_member_2821 : List.In (2821,reference_control_expr_2821) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 293%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2821_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2821 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2821 reference_control_expr_2821 reference_control_2_positions reference_control_2_safety reference_control_member_2821) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2821 reference_control_expr_2821 inputs path old current result Position Safe Nonreg (reference_control_ready_2821 old ) Step).
Qed.
Theorem reference_control_node_2821_congruent inputs path left right next_left next_right :
 VM.find 2814 left = VM.find 2814 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2821 next_left = VM.find 2821 next_right.
Proof.
 intros  E2814 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2821 reference_control_expr_2821 reference_control_2_positions reference_control_2_safety reference_control_member_2821) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2821 reference_control_expr_2821 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2821 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2821 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2814.
 reflexivity.
Qed.
Lemma reference_control_ready_2822 old :
 reference_control_ready old reference_control_expr_2822.
Proof.
 unfold reference_control_expr_2822.
apply rc_binary.
Qed.
Lemma reference_control_member_2822 : List.In (2822,reference_control_expr_2822) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 294%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2822_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2822 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2822 reference_control_expr_2822 reference_control_2_positions reference_control_2_safety reference_control_member_2822) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2822 reference_control_expr_2822 inputs path old current result Position Safe Nonreg (reference_control_ready_2822 old ) Step).
Qed.
Theorem reference_control_node_2822_congruent inputs path left right next_left next_right :
 VM.find 2821 left = VM.find 2821 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2822 next_left = VM.find 2822 next_right.
Proof.
 intros  E2821 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2822 reference_control_expr_2822 reference_control_2_positions reference_control_2_safety reference_control_member_2822) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2822 reference_control_expr_2822 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2822 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2822 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2821.
 reflexivity.
Qed.
Lemma reference_control_ready_2823 old :
 (exists value ground, VM.find 2822 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2823.
Proof.
 intros H2822.
 destruct H2822 as [v2822 [G2822 [V2822 T2822]]].
 unfold reference_control_expr_2823.
apply rc_mux.
{ eapply rc_ref; [exact V2822|exists G2822; exact T2822].
}
{ apply rc_const.
}
Qed.
Lemma reference_control_member_2823 : List.In (2823,reference_control_expr_2823) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 295%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2823_ground inputs path old current result :
 (exists value ground, VM.find 2822 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2823 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2822 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2823 reference_control_expr_2823 reference_control_2_positions reference_control_2_safety reference_control_member_2823) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2823 reference_control_expr_2823 inputs path old current result Position Safe Nonreg (reference_control_ready_2823 old H2822) Step).
Qed.
Theorem reference_control_node_2823_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2822 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2820 left = VM.find 2820 right ->
 VM.find 2822 left = VM.find 2822 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2823 next_left = VM.find 2823 next_right.
Proof.
 intros H2822 E2820 E2822 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2823 reference_control_expr_2823 reference_control_2_positions reference_control_2_safety reference_control_member_2823) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2823 reference_control_expr_2823 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2823 left H2822)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2823 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2820.
 rewrite E2822.
 reflexivity.
Qed.
Lemma reference_control_ready_2824 old :
 (exists value ground, VM.find 2819 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2823 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2824.
Proof.
 intros H2819 H2823.
 destruct H2819 as [v2819 [G2819 [V2819 T2819]]].
 destruct H2823 as [v2823 [G2823 [V2823 T2823]]].
 unfold reference_control_expr_2824.
apply rc_mux.
{ eapply rc_ref; [exact V2819|exists G2819; exact T2819].
}
{ eapply rc_ref; [exact V2823|exists G2823; exact T2823].
}
Qed.
Lemma reference_control_member_2824 : List.In (2824,reference_control_expr_2824) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 296%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2824_ground inputs path old current result :
 (exists value ground, VM.find 2819 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2823 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2824 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2819 H2823 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2824 reference_control_expr_2824 reference_control_2_positions reference_control_2_safety reference_control_member_2824) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2824 reference_control_expr_2824 inputs path old current result Position Safe Nonreg (reference_control_ready_2824 old H2819 H2823) Step).
Qed.
Theorem reference_control_node_2824_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2819 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2823 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2817 left = VM.find 2817 right ->
 VM.find 2819 left = VM.find 2819 right ->
 VM.find 2823 left = VM.find 2823 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2824 next_left = VM.find 2824 next_right.
Proof.
 intros H2819 H2823 E2817 E2819 E2823 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2824 reference_control_expr_2824 reference_control_2_positions reference_control_2_safety reference_control_member_2824) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2824 reference_control_expr_2824 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2824 left H2819 H2823)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2824 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2817.
 rewrite E2819.
 rewrite E2823.
 reflexivity.
Qed.
Lemma reference_control_ready_2825 old :
 (exists value ground, VM.find 2816 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2824 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2825.
Proof.
 intros H2816 H2824.
 destruct H2816 as [v2816 [G2816 [V2816 T2816]]].
 destruct H2824 as [v2824 [G2824 [V2824 T2824]]].
 unfold reference_control_expr_2825.
apply rc_mux.
{ eapply rc_ref; [exact V2816|exists G2816; exact T2816].
}
{ eapply rc_ref; [exact V2824|exists G2824; exact T2824].
}
Qed.
Lemma reference_control_member_2825 : List.In (2825,reference_control_expr_2825) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 297%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2825_ground inputs path old current result :
 (exists value ground, VM.find 2816 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2824 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2825 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2816 H2824 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2825 reference_control_expr_2825 reference_control_2_positions reference_control_2_safety reference_control_member_2825) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2825 reference_control_expr_2825 inputs path old current result Position Safe Nonreg (reference_control_ready_2825 old H2816 H2824) Step).
Qed.
Theorem reference_control_node_2825_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2816 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2824 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2811 left = VM.find 2811 right ->
 VM.find 2816 left = VM.find 2816 right ->
 VM.find 2824 left = VM.find 2824 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2825 next_left = VM.find 2825 next_right.
Proof.
 intros H2816 H2824 E2811 E2816 E2824 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2825 reference_control_expr_2825 reference_control_2_positions reference_control_2_safety reference_control_member_2825) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2825 reference_control_expr_2825 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2825 left H2816 H2824)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2825 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2811.
 rewrite E2816.
 rewrite E2824.
 reflexivity.
Qed.
Lemma reference_control_ready_2826 old :
 (exists value ground, VM.find 2209 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2826.
Proof.
 intros H2209.
 destruct H2209 as [v2209 [G2209 [V2209 T2209]]].
 unfold reference_control_expr_2826.
eapply rc_ref; [exact V2209|exists G2209; exact T2209].
Qed.
Lemma reference_control_member_2826 : List.In (2826,reference_control_expr_2826) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 298%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2826_ground inputs path old current result :
 (exists value ground, VM.find 2209 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2826 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2209 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2826 reference_control_expr_2826 reference_control_2_positions reference_control_2_safety reference_control_member_2826) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2826 reference_control_expr_2826 inputs path old current result Position Safe Nonreg (reference_control_ready_2826 old H2209) Step).
Qed.
Theorem reference_control_node_2826_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2209 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2209 left = VM.find 2209 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2826 next_left = VM.find 2826 next_right.
Proof.
 intros H2209 E2209 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2826 reference_control_expr_2826 reference_control_2_positions reference_control_2_safety reference_control_member_2826) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2826 reference_control_expr_2826 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2826 left H2209)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2826 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2209.
 reflexivity.
Qed.
Lemma reference_control_ready_2827 old :
 reference_control_ready old reference_control_expr_2827.
Proof.
 unfold reference_control_expr_2827.
apply rc_cast.
Qed.
Lemma reference_control_member_2827 : List.In (2827,reference_control_expr_2827) reference_control_2_nodes.
Proof. apply (List.nth_error_In reference_control_2_nodes 299%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2827_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2827 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2827 reference_control_expr_2827 reference_control_2_positions reference_control_2_safety reference_control_member_2827) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2827 reference_control_expr_2827 inputs path old current result Position Safe Nonreg (reference_control_ready_2827 old ) Step).
Qed.
Theorem reference_control_node_2827_congruent inputs path left right next_left next_right :
 VM.find 2826 left = VM.find 2826 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2827 next_left = VM.find 2827 next_right.
Proof.
 intros  E2826 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_2_offsets flat_statements
 reference_control_2_nodes 2827 reference_control_expr_2827 reference_control_2_positions reference_control_2_safety reference_control_member_2827) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2827 reference_control_expr_2827 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2827 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2827 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2826.
 reflexivity.
Qed.
Print Assumptions reference_control_node_2827_congruent.
