Require Import CoreSocModel ComparisonNodes ReferenceControlExpressions ReferenceControlGroundOperations ReferenceControlGroundExpressions ReferenceControlNodeGeneric SelectedNodeSafety.
From Coq Require Import ZArith List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Require Import ReferenceControlNodeCertificates3.
Lemma reference_control_ready_2828 old :
 (exists value ground, VM.find 2804 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2828.
Proof.
 intros H2804.
 destruct H2804 as [v2804 [G2804 [V2804 T2804]]].
 unfold reference_control_expr_2828.
eapply rc_ref; [exact V2804|exists G2804; exact T2804].
Qed.
Lemma reference_control_member_2828 : List.In (2828,reference_control_expr_2828) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 0%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2828_ground inputs path old current result :
 (exists value ground, VM.find 2804 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2828 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2804 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2828 reference_control_expr_2828 reference_control_3_positions reference_control_3_safety reference_control_member_2828) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2828 reference_control_expr_2828 inputs path old current result Position Safe Nonreg (reference_control_ready_2828 old H2804) Step).
Qed.
Theorem reference_control_node_2828_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2804 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2804 left = VM.find 2804 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2828 next_left = VM.find 2828 next_right.
Proof.
 intros H2804 E2804 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2828 reference_control_expr_2828 reference_control_3_positions reference_control_3_safety reference_control_member_2828) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2828 reference_control_expr_2828 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2828 left H2804)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2828 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2804.
 reflexivity.
Qed.
Lemma reference_control_ready_2829 old :
 reference_control_ready old reference_control_expr_2829.
Proof.
 unfold reference_control_expr_2829.
apply rc_cast.
Qed.
Lemma reference_control_member_2829 : List.In (2829,reference_control_expr_2829) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 1%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2829_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2829 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2829 reference_control_expr_2829 reference_control_3_positions reference_control_3_safety reference_control_member_2829) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2829 reference_control_expr_2829 inputs path old current result Position Safe Nonreg (reference_control_ready_2829 old ) Step).
Qed.
Theorem reference_control_node_2829_congruent inputs path left right next_left next_right :
 VM.find 2828 left = VM.find 2828 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2829 next_left = VM.find 2829 next_right.
Proof.
 intros  E2828 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2829 reference_control_expr_2829 reference_control_3_positions reference_control_3_safety reference_control_member_2829) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2829 reference_control_expr_2829 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2829 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2829 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2828.
 reflexivity.
Qed.
Lemma reference_control_ready_2830 old :
 reference_control_ready old reference_control_expr_2830.
Proof.
 unfold reference_control_expr_2830.
apply rc_binary.
Qed.
Lemma reference_control_member_2830 : List.In (2830,reference_control_expr_2830) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 2%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2830_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2830 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2830 reference_control_expr_2830 reference_control_3_positions reference_control_3_safety reference_control_member_2830) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2830 reference_control_expr_2830 inputs path old current result Position Safe Nonreg (reference_control_ready_2830 old ) Step).
Qed.
Theorem reference_control_node_2830_congruent inputs path left right next_left next_right :
 VM.find 2827 left = VM.find 2827 right ->
 VM.find 2829 left = VM.find 2829 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2830 next_left = VM.find 2830 next_right.
Proof.
 intros  E2827 E2829 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2830 reference_control_expr_2830 reference_control_3_positions reference_control_3_safety reference_control_member_2830) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2830 reference_control_expr_2830 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2830 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2830 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2827.
 rewrite E2829.
 reflexivity.
Qed.
Lemma reference_control_ready_2831 old :
 reference_control_ready old reference_control_expr_2831.
Proof.
 unfold reference_control_expr_2831.
apply rc_unary.
Qed.
Lemma reference_control_member_2831 : List.In (2831,reference_control_expr_2831) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 3%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2831_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2831 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2831 reference_control_expr_2831 reference_control_3_positions reference_control_3_safety reference_control_member_2831) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2831 reference_control_expr_2831 inputs path old current result Position Safe Nonreg (reference_control_ready_2831 old ) Step).
Qed.
Theorem reference_control_node_2831_congruent inputs path left right next_left next_right :
 VM.find 2807 left = VM.find 2807 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2831 next_left = VM.find 2831 next_right.
Proof.
 intros  E2807 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2831 reference_control_expr_2831 reference_control_3_positions reference_control_3_safety reference_control_member_2831) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2831 reference_control_expr_2831 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2831 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2831 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2807.
 reflexivity.
Qed.
Lemma reference_control_ready_2832 old :
 reference_control_ready old reference_control_expr_2832.
Proof.
 unfold reference_control_expr_2832.
apply rc_binary.
Qed.
Lemma reference_control_member_2832 : List.In (2832,reference_control_expr_2832) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 4%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2832_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2832 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2832 reference_control_expr_2832 reference_control_3_positions reference_control_3_safety reference_control_member_2832) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2832 reference_control_expr_2832 inputs path old current result Position Safe Nonreg (reference_control_ready_2832 old ) Step).
Qed.
Theorem reference_control_node_2832_congruent inputs path left right next_left next_right :
 VM.find 2831 left = VM.find 2831 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2832 next_left = VM.find 2832 next_right.
Proof.
 intros  E2831 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2832 reference_control_expr_2832 reference_control_3_positions reference_control_3_safety reference_control_member_2832) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2832 reference_control_expr_2832 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2832 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2832 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2831.
 reflexivity.
Qed.
Lemma reference_control_ready_2833 old :
 reference_control_ready old reference_control_expr_2833.
Proof.
 unfold reference_control_expr_2833.
apply rc_mux.
{ apply rc_const.
}
{ apply rc_const.
}
Qed.
Lemma reference_control_member_2833 : List.In (2833,reference_control_expr_2833) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 5%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2833_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2833 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2833 reference_control_expr_2833 reference_control_3_positions reference_control_3_safety reference_control_member_2833) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2833 reference_control_expr_2833 inputs path old current result Position Safe Nonreg (reference_control_ready_2833 old ) Step).
Qed.
Theorem reference_control_node_2833_congruent inputs path left right next_left next_right :
 VM.find 2832 left = VM.find 2832 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2833 next_left = VM.find 2833 next_right.
Proof.
 intros  E2832 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2833 reference_control_expr_2833 reference_control_3_positions reference_control_3_safety reference_control_member_2833) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2833 reference_control_expr_2833 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2833 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2833 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2832.
 reflexivity.
Qed.
Lemma reference_control_ready_2834 old :
 reference_control_ready old reference_control_expr_2834.
Proof.
 unfold reference_control_expr_2834.
apply rc_binary.
Qed.
Lemma reference_control_member_2834 : List.In (2834,reference_control_expr_2834) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 6%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2834_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2834 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2834 reference_control_expr_2834 reference_control_3_positions reference_control_3_safety reference_control_member_2834) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2834 reference_control_expr_2834 inputs path old current result Position Safe Nonreg (reference_control_ready_2834 old ) Step).
Qed.
Theorem reference_control_node_2834_congruent inputs path left right next_left next_right :
 VM.find 2833 left = VM.find 2833 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2834 next_left = VM.find 2834 next_right.
Proof.
 intros  E2833 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2834 reference_control_expr_2834 reference_control_3_positions reference_control_3_safety reference_control_member_2834) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2834 reference_control_expr_2834 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2834 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2834 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2833.
 reflexivity.
Qed.
Lemma reference_control_ready_2835 old :
 reference_control_ready old reference_control_expr_2835.
Proof.
 unfold reference_control_expr_2835.
apply rc_binary.
Qed.
Lemma reference_control_member_2835 : List.In (2835,reference_control_expr_2835) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 7%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2835_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2835 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2835 reference_control_expr_2835 reference_control_3_positions reference_control_3_safety reference_control_member_2835) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2835 reference_control_expr_2835 inputs path old current result Position Safe Nonreg (reference_control_ready_2835 old ) Step).
Qed.
Theorem reference_control_node_2835_congruent inputs path left right next_left next_right :
 VM.find 2552 left = VM.find 2552 right ->
 VM.find 2812 left = VM.find 2812 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2835 next_left = VM.find 2835 next_right.
Proof.
 intros  E2552 E2812 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2835 reference_control_expr_2835 reference_control_3_positions reference_control_3_safety reference_control_member_2835) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2835 reference_control_expr_2835 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2835 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2835 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2552.
 rewrite E2812.
 reflexivity.
Qed.
Lemma reference_control_ready_2836 old :
 reference_control_ready old reference_control_expr_2836.
Proof.
 unfold reference_control_expr_2836.
apply rc_unary.
Qed.
Lemma reference_control_member_2836 : List.In (2836,reference_control_expr_2836) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 8%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2836_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2836 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2836 reference_control_expr_2836 reference_control_3_positions reference_control_3_safety reference_control_member_2836) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2836 reference_control_expr_2836 inputs path old current result Position Safe Nonreg (reference_control_ready_2836 old ) Step).
Qed.
Theorem reference_control_node_2836_congruent inputs path left right next_left next_right :
 VM.find 2835 left = VM.find 2835 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2836 next_left = VM.find 2836 next_right.
Proof.
 intros  E2835 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2836 reference_control_expr_2836 reference_control_3_positions reference_control_3_safety reference_control_member_2836) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2836 reference_control_expr_2836 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2836 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2836 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2835.
 reflexivity.
Qed.
Lemma reference_control_ready_2837 old :
 reference_control_ready old reference_control_expr_2837.
Proof.
 unfold reference_control_expr_2837.
apply rc_unary.
Qed.
Lemma reference_control_member_2837 : List.In (2837,reference_control_expr_2837) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 9%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2837_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2837 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2837 reference_control_expr_2837 reference_control_3_positions reference_control_3_safety reference_control_member_2837) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2837 reference_control_expr_2837 inputs path old current result Position Safe Nonreg (reference_control_ready_2837 old ) Step).
Qed.
Theorem reference_control_node_2837_congruent inputs path left right next_left next_right :
 VM.find 2836 left = VM.find 2836 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2837 next_left = VM.find 2837 next_right.
Proof.
 intros  E2836 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2837 reference_control_expr_2837 reference_control_3_positions reference_control_3_safety reference_control_member_2837) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2837 reference_control_expr_2837 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2837 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2837 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2836.
 reflexivity.
Qed.
Lemma reference_control_ready_2838 old :
 reference_control_ready old reference_control_expr_2838.
Proof.
 unfold reference_control_expr_2838.
apply rc_binary.
Qed.
Lemma reference_control_member_2838 : List.In (2838,reference_control_expr_2838) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 10%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2838_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2838 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2838 reference_control_expr_2838 reference_control_3_positions reference_control_3_safety reference_control_member_2838) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2838 reference_control_expr_2838 inputs path old current result Position Safe Nonreg (reference_control_ready_2838 old ) Step).
Qed.
Theorem reference_control_node_2838_congruent inputs path left right next_left next_right :
 VM.find 2837 left = VM.find 2837 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2838 next_left = VM.find 2838 next_right.
Proof.
 intros  E2837 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2838 reference_control_expr_2838 reference_control_3_positions reference_control_3_safety reference_control_member_2838) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2838 reference_control_expr_2838 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2838 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2838 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2837.
 reflexivity.
Qed.
Lemma reference_control_ready_2839 old :
 reference_control_ready old reference_control_expr_2839.
Proof.
 unfold reference_control_expr_2839.
apply rc_binary.
Qed.
Lemma reference_control_member_2839 : List.In (2839,reference_control_expr_2839) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 11%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2839_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2839 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2839 reference_control_expr_2839 reference_control_3_positions reference_control_3_safety reference_control_member_2839) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2839 reference_control_expr_2839 inputs path old current result Position Safe Nonreg (reference_control_ready_2839 old ) Step).
Qed.
Theorem reference_control_node_2839_congruent inputs path left right next_left next_right :
 VM.find 2833 left = VM.find 2833 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2839 next_left = VM.find 2839 next_right.
Proof.
 intros  E2833 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2839 reference_control_expr_2839 reference_control_3_positions reference_control_3_safety reference_control_member_2839) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2839 reference_control_expr_2839 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2839 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2839 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2833.
 reflexivity.
Qed.
Lemma reference_control_ready_2840 old :
 reference_control_ready old reference_control_expr_2840.
Proof.
 unfold reference_control_expr_2840.
apply rc_unary.
Qed.
Lemma reference_control_member_2840 : List.In (2840,reference_control_expr_2840) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 12%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2840_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2840 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2840 reference_control_expr_2840 reference_control_3_positions reference_control_3_safety reference_control_member_2840) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2840 reference_control_expr_2840 inputs path old current result Position Safe Nonreg (reference_control_ready_2840 old ) Step).
Qed.
Theorem reference_control_node_2840_congruent inputs path left right next_left next_right :
 VM.find 2836 left = VM.find 2836 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2840 next_left = VM.find 2840 next_right.
Proof.
 intros  E2836 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2840 reference_control_expr_2840 reference_control_3_positions reference_control_3_safety reference_control_member_2840) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2840 reference_control_expr_2840 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2840 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2840 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2836.
 reflexivity.
Qed.
Lemma reference_control_ready_2841 old :
 reference_control_ready old reference_control_expr_2841.
Proof.
 unfold reference_control_expr_2841.
apply rc_binary.
Qed.
Lemma reference_control_member_2841 : List.In (2841,reference_control_expr_2841) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 13%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2841_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2841 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2841 reference_control_expr_2841 reference_control_3_positions reference_control_3_safety reference_control_member_2841) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2841 reference_control_expr_2841 inputs path old current result Position Safe Nonreg (reference_control_ready_2841 old ) Step).
Qed.
Theorem reference_control_node_2841_congruent inputs path left right next_left next_right :
 VM.find 2840 left = VM.find 2840 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2841 next_left = VM.find 2841 next_right.
Proof.
 intros  E2840 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2841 reference_control_expr_2841 reference_control_3_positions reference_control_3_safety reference_control_member_2841) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2841 reference_control_expr_2841 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2841 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2841 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2840.
 reflexivity.
Qed.
Lemma reference_control_ready_2842 old :
 reference_control_ready old reference_control_expr_2842.
Proof.
 unfold reference_control_expr_2842.
apply rc_binary.
Qed.
Lemma reference_control_member_2842 : List.In (2842,reference_control_expr_2842) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 14%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2842_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2842 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2842 reference_control_expr_2842 reference_control_3_positions reference_control_3_safety reference_control_member_2842) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2842 reference_control_expr_2842 inputs path old current result Position Safe Nonreg (reference_control_ready_2842 old ) Step).
Qed.
Theorem reference_control_node_2842_congruent inputs path left right next_left next_right :
 VM.find 2833 left = VM.find 2833 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2842 next_left = VM.find 2842 next_right.
Proof.
 intros  E2833 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2842 reference_control_expr_2842 reference_control_3_positions reference_control_3_safety reference_control_member_2842) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2842 reference_control_expr_2842 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2842 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2842 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2833.
 reflexivity.
Qed.
Lemma reference_control_ready_2843 old :
 reference_control_ready old reference_control_expr_2843.
Proof.
 unfold reference_control_expr_2843.
apply rc_unary.
Qed.
Lemma reference_control_member_2843 : List.In (2843,reference_control_expr_2843) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 15%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2843_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2843 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2843 reference_control_expr_2843 reference_control_3_positions reference_control_3_safety reference_control_member_2843) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2843 reference_control_expr_2843 inputs path old current result Position Safe Nonreg (reference_control_ready_2843 old ) Step).
Qed.
Theorem reference_control_node_2843_congruent inputs path left right next_left next_right :
 VM.find 2836 left = VM.find 2836 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2843 next_left = VM.find 2843 next_right.
Proof.
 intros  E2836 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2843 reference_control_expr_2843 reference_control_3_positions reference_control_3_safety reference_control_member_2843) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2843 reference_control_expr_2843 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2843 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2843 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2836.
 reflexivity.
Qed.
Lemma reference_control_ready_2844 old :
 reference_control_ready old reference_control_expr_2844.
Proof.
 unfold reference_control_expr_2844.
apply rc_binary.
Qed.
Lemma reference_control_member_2844 : List.In (2844,reference_control_expr_2844) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 16%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2844_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2844 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2844 reference_control_expr_2844 reference_control_3_positions reference_control_3_safety reference_control_member_2844) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2844 reference_control_expr_2844 inputs path old current result Position Safe Nonreg (reference_control_ready_2844 old ) Step).
Qed.
Theorem reference_control_node_2844_congruent inputs path left right next_left next_right :
 VM.find 2843 left = VM.find 2843 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2844 next_left = VM.find 2844 next_right.
Proof.
 intros  E2843 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2844 reference_control_expr_2844 reference_control_3_positions reference_control_3_safety reference_control_member_2844) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2844 reference_control_expr_2844 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2844 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2844 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2843.
 reflexivity.
Qed.
Lemma reference_control_ready_2845 old :
 (exists value ground, VM.find 2844 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2845.
Proof.
 intros H2844.
 destruct H2844 as [v2844 [G2844 [V2844 T2844]]].
 unfold reference_control_expr_2845.
apply rc_mux.
{ eapply rc_ref; [exact V2844|exists G2844; exact T2844].
}
{ apply rc_const.
}
Qed.
Lemma reference_control_member_2845 : List.In (2845,reference_control_expr_2845) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 17%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2845_ground inputs path old current result :
 (exists value ground, VM.find 2844 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2845 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2844 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2845 reference_control_expr_2845 reference_control_3_positions reference_control_3_safety reference_control_member_2845) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2845 reference_control_expr_2845 inputs path old current result Position Safe Nonreg (reference_control_ready_2845 old H2844) Step).
Qed.
Theorem reference_control_node_2845_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2844 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2842 left = VM.find 2842 right ->
 VM.find 2844 left = VM.find 2844 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2845 next_left = VM.find 2845 next_right.
Proof.
 intros H2844 E2842 E2844 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2845 reference_control_expr_2845 reference_control_3_positions reference_control_3_safety reference_control_member_2845) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2845 reference_control_expr_2845 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2845 left H2844)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2845 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2842.
 rewrite E2844.
 reflexivity.
Qed.
Lemma reference_control_ready_2846 old :
 (exists value ground, VM.find 2841 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2845 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2846.
Proof.
 intros H2841 H2845.
 destruct H2841 as [v2841 [G2841 [V2841 T2841]]].
 destruct H2845 as [v2845 [G2845 [V2845 T2845]]].
 unfold reference_control_expr_2846.
apply rc_mux.
{ eapply rc_ref; [exact V2841|exists G2841; exact T2841].
}
{ eapply rc_ref; [exact V2845|exists G2845; exact T2845].
}
Qed.
Lemma reference_control_member_2846 : List.In (2846,reference_control_expr_2846) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 18%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2846_ground inputs path old current result :
 (exists value ground, VM.find 2841 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2845 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2846 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2841 H2845 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2846 reference_control_expr_2846 reference_control_3_positions reference_control_3_safety reference_control_member_2846) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2846 reference_control_expr_2846 inputs path old current result Position Safe Nonreg (reference_control_ready_2846 old H2841 H2845) Step).
Qed.
Theorem reference_control_node_2846_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2841 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2845 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2839 left = VM.find 2839 right ->
 VM.find 2841 left = VM.find 2841 right ->
 VM.find 2845 left = VM.find 2845 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2846 next_left = VM.find 2846 next_right.
Proof.
 intros H2841 H2845 E2839 E2841 E2845 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2846 reference_control_expr_2846 reference_control_3_positions reference_control_3_safety reference_control_member_2846) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2846 reference_control_expr_2846 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2846 left H2841 H2845)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2846 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2839.
 rewrite E2841.
 rewrite E2845.
 reflexivity.
Qed.
Lemma reference_control_ready_2847 old :
 (exists value ground, VM.find 2838 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2846 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2847.
Proof.
 intros H2838 H2846.
 destruct H2838 as [v2838 [G2838 [V2838 T2838]]].
 destruct H2846 as [v2846 [G2846 [V2846 T2846]]].
 unfold reference_control_expr_2847.
apply rc_mux.
{ eapply rc_ref; [exact V2838|exists G2838; exact T2838].
}
{ eapply rc_ref; [exact V2846|exists G2846; exact T2846].
}
Qed.
Lemma reference_control_member_2847 : List.In (2847,reference_control_expr_2847) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 19%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2847_ground inputs path old current result :
 (exists value ground, VM.find 2838 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2846 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2847 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2838 H2846 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2847 reference_control_expr_2847 reference_control_3_positions reference_control_3_safety reference_control_member_2847) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2847 reference_control_expr_2847 inputs path old current result Position Safe Nonreg (reference_control_ready_2847 old H2838 H2846) Step).
Qed.
Theorem reference_control_node_2847_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2838 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2846 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2834 left = VM.find 2834 right ->
 VM.find 2838 left = VM.find 2838 right ->
 VM.find 2846 left = VM.find 2846 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2847 next_left = VM.find 2847 next_right.
Proof.
 intros H2838 H2846 E2834 E2838 E2846 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2847 reference_control_expr_2847 reference_control_3_positions reference_control_3_safety reference_control_member_2847) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2847 reference_control_expr_2847 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2847 left H2838 H2846)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2847 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2834.
 rewrite E2838.
 rewrite E2846.
 reflexivity.
Qed.
Lemma reference_control_ready_2848 old :
 (exists value ground, VM.find 2209 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2848.
Proof.
 intros H2209.
 destruct H2209 as [v2209 [G2209 [V2209 T2209]]].
 unfold reference_control_expr_2848.
eapply rc_ref; [exact V2209|exists G2209; exact T2209].
Qed.
Lemma reference_control_member_2848 : List.In (2848,reference_control_expr_2848) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 20%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2848_ground inputs path old current result :
 (exists value ground, VM.find 2209 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2848 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2209 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2848 reference_control_expr_2848 reference_control_3_positions reference_control_3_safety reference_control_member_2848) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2848 reference_control_expr_2848 inputs path old current result Position Safe Nonreg (reference_control_ready_2848 old H2209) Step).
Qed.
Theorem reference_control_node_2848_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2209 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2209 left = VM.find 2209 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2848 next_left = VM.find 2848 next_right.
Proof.
 intros H2209 E2209 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2848 reference_control_expr_2848 reference_control_3_positions reference_control_3_safety reference_control_member_2848) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2848 reference_control_expr_2848 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2848 left H2209)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2848 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2209.
 reflexivity.
Qed.
Lemma reference_control_ready_2849 old :
 (exists value ground, VM.find 2804 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2849.
Proof.
 intros H2804.
 destruct H2804 as [v2804 [G2804 [V2804 T2804]]].
 unfold reference_control_expr_2849.
eapply rc_ref; [exact V2804|exists G2804; exact T2804].
Qed.
Lemma reference_control_member_2849 : List.In (2849,reference_control_expr_2849) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 21%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2849_ground inputs path old current result :
 (exists value ground, VM.find 2804 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2849 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2804 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2849 reference_control_expr_2849 reference_control_3_positions reference_control_3_safety reference_control_member_2849) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2849 reference_control_expr_2849 inputs path old current result Position Safe Nonreg (reference_control_ready_2849 old H2804) Step).
Qed.
Theorem reference_control_node_2849_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2804 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2804 left = VM.find 2804 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2849 next_left = VM.find 2849 next_right.
Proof.
 intros H2804 E2804 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2849 reference_control_expr_2849 reference_control_3_positions reference_control_3_safety reference_control_member_2849) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2849 reference_control_expr_2849 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2849 left H2804)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2849 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2804.
 reflexivity.
Qed.
Lemma reference_control_ready_2850 old :
 reference_control_ready old reference_control_expr_2850.
Proof.
 unfold reference_control_expr_2850.
apply rc_binary.
Qed.
Lemma reference_control_member_2850 : List.In (2850,reference_control_expr_2850) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 22%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2850_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2850 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2850 reference_control_expr_2850 reference_control_3_positions reference_control_3_safety reference_control_member_2850) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2850 reference_control_expr_2850 inputs path old current result Position Safe Nonreg (reference_control_ready_2850 old ) Step).
Qed.
Theorem reference_control_node_2850_congruent inputs path left right next_left next_right :
 VM.find 2848 left = VM.find 2848 right ->
 VM.find 2849 left = VM.find 2849 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2850 next_left = VM.find 2850 next_right.
Proof.
 intros  E2848 E2849 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2850 reference_control_expr_2850 reference_control_3_positions reference_control_3_safety reference_control_member_2850) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2850 reference_control_expr_2850 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2850 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2850 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2848.
 rewrite E2849.
 reflexivity.
Qed.
Lemma reference_control_ready_2851 old :
 reference_control_ready old reference_control_expr_2851.
Proof.
 unfold reference_control_expr_2851.
apply rc_unary.
Qed.
Lemma reference_control_member_2851 : List.In (2851,reference_control_expr_2851) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 23%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2851_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2851 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2851 reference_control_expr_2851 reference_control_3_positions reference_control_3_safety reference_control_member_2851) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2851 reference_control_expr_2851 inputs path old current result Position Safe Nonreg (reference_control_ready_2851 old ) Step).
Qed.
Theorem reference_control_node_2851_congruent inputs path left right next_left next_right :
 VM.find 2807 left = VM.find 2807 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2851 next_left = VM.find 2851 next_right.
Proof.
 intros  E2807 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2851 reference_control_expr_2851 reference_control_3_positions reference_control_3_safety reference_control_member_2851) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2851 reference_control_expr_2851 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2851 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2851 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2807.
 reflexivity.
Qed.
Lemma reference_control_ready_2852 old :
 reference_control_ready old reference_control_expr_2852.
Proof.
 unfold reference_control_expr_2852.
apply rc_binary.
Qed.
Lemma reference_control_member_2852 : List.In (2852,reference_control_expr_2852) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 24%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2852_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2852 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2852 reference_control_expr_2852 reference_control_3_positions reference_control_3_safety reference_control_member_2852) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2852 reference_control_expr_2852 inputs path old current result Position Safe Nonreg (reference_control_ready_2852 old ) Step).
Qed.
Theorem reference_control_node_2852_congruent inputs path left right next_left next_right :
 VM.find 2851 left = VM.find 2851 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2852 next_left = VM.find 2852 next_right.
Proof.
 intros  E2851 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2852 reference_control_expr_2852 reference_control_3_positions reference_control_3_safety reference_control_member_2852) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2852 reference_control_expr_2852 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2852 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2852 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2851.
 reflexivity.
Qed.
Lemma reference_control_ready_2853 old :
 reference_control_ready old reference_control_expr_2853.
Proof.
 unfold reference_control_expr_2853.
apply rc_mux.
{ apply rc_const.
}
{ apply rc_const.
}
Qed.
Lemma reference_control_member_2853 : List.In (2853,reference_control_expr_2853) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 25%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2853_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2853 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2853 reference_control_expr_2853 reference_control_3_positions reference_control_3_safety reference_control_member_2853) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2853 reference_control_expr_2853 inputs path old current result Position Safe Nonreg (reference_control_ready_2853 old ) Step).
Qed.
Theorem reference_control_node_2853_congruent inputs path left right next_left next_right :
 VM.find 2852 left = VM.find 2852 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2853 next_left = VM.find 2853 next_right.
Proof.
 intros  E2852 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2853 reference_control_expr_2853 reference_control_3_positions reference_control_3_safety reference_control_member_2853) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2853 reference_control_expr_2853 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2853 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2853 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2852.
 reflexivity.
Qed.
Lemma reference_control_ready_2854 old :
 reference_control_ready old reference_control_expr_2854.
Proof.
 unfold reference_control_expr_2854.
apply rc_binary.
Qed.
Lemma reference_control_member_2854 : List.In (2854,reference_control_expr_2854) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 26%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2854_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2854 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2854 reference_control_expr_2854 reference_control_3_positions reference_control_3_safety reference_control_member_2854) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2854 reference_control_expr_2854 inputs path old current result Position Safe Nonreg (reference_control_ready_2854 old ) Step).
Qed.
Theorem reference_control_node_2854_congruent inputs path left right next_left next_right :
 VM.find 2853 left = VM.find 2853 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2854 next_left = VM.find 2854 next_right.
Proof.
 intros  E2853 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2854 reference_control_expr_2854 reference_control_3_positions reference_control_3_safety reference_control_member_2854) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2854 reference_control_expr_2854 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2854 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2854 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2853.
 reflexivity.
Qed.
Lemma reference_control_ready_2855 old :
 reference_control_ready old reference_control_expr_2855.
Proof.
 unfold reference_control_expr_2855.
apply rc_binary.
Qed.
Lemma reference_control_member_2855 : List.In (2855,reference_control_expr_2855) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 27%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2855_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2855 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2855 reference_control_expr_2855 reference_control_3_positions reference_control_3_safety reference_control_member_2855) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2855 reference_control_expr_2855 inputs path old current result Position Safe Nonreg (reference_control_ready_2855 old ) Step).
Qed.
Theorem reference_control_node_2855_congruent inputs path left right next_left next_right :
 VM.find 2552 left = VM.find 2552 right ->
 VM.find 2812 left = VM.find 2812 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2855 next_left = VM.find 2855 next_right.
Proof.
 intros  E2552 E2812 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2855 reference_control_expr_2855 reference_control_3_positions reference_control_3_safety reference_control_member_2855) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2855 reference_control_expr_2855 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2855 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2855 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2552.
 rewrite E2812.
 reflexivity.
Qed.
Lemma reference_control_ready_2856 old :
 reference_control_ready old reference_control_expr_2856.
Proof.
 unfold reference_control_expr_2856.
apply rc_unary.
Qed.
Lemma reference_control_member_2856 : List.In (2856,reference_control_expr_2856) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 28%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2856_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2856 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2856 reference_control_expr_2856 reference_control_3_positions reference_control_3_safety reference_control_member_2856) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2856 reference_control_expr_2856 inputs path old current result Position Safe Nonreg (reference_control_ready_2856 old ) Step).
Qed.
Theorem reference_control_node_2856_congruent inputs path left right next_left next_right :
 VM.find 2855 left = VM.find 2855 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2856 next_left = VM.find 2856 next_right.
Proof.
 intros  E2855 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2856 reference_control_expr_2856 reference_control_3_positions reference_control_3_safety reference_control_member_2856) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2856 reference_control_expr_2856 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2856 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2856 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2855.
 reflexivity.
Qed.
Lemma reference_control_ready_2857 old :
 reference_control_ready old reference_control_expr_2857.
Proof.
 unfold reference_control_expr_2857.
apply rc_unary.
Qed.
Lemma reference_control_member_2857 : List.In (2857,reference_control_expr_2857) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 29%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2857_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2857 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2857 reference_control_expr_2857 reference_control_3_positions reference_control_3_safety reference_control_member_2857) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2857 reference_control_expr_2857 inputs path old current result Position Safe Nonreg (reference_control_ready_2857 old ) Step).
Qed.
Theorem reference_control_node_2857_congruent inputs path left right next_left next_right :
 VM.find 2856 left = VM.find 2856 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2857 next_left = VM.find 2857 next_right.
Proof.
 intros  E2856 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2857 reference_control_expr_2857 reference_control_3_positions reference_control_3_safety reference_control_member_2857) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2857 reference_control_expr_2857 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2857 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2857 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2856.
 reflexivity.
Qed.
Lemma reference_control_ready_2858 old :
 reference_control_ready old reference_control_expr_2858.
Proof.
 unfold reference_control_expr_2858.
apply rc_binary.
Qed.
Lemma reference_control_member_2858 : List.In (2858,reference_control_expr_2858) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 30%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2858_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2858 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2858 reference_control_expr_2858 reference_control_3_positions reference_control_3_safety reference_control_member_2858) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2858 reference_control_expr_2858 inputs path old current result Position Safe Nonreg (reference_control_ready_2858 old ) Step).
Qed.
Theorem reference_control_node_2858_congruent inputs path left right next_left next_right :
 VM.find 2857 left = VM.find 2857 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2858 next_left = VM.find 2858 next_right.
Proof.
 intros  E2857 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2858 reference_control_expr_2858 reference_control_3_positions reference_control_3_safety reference_control_member_2858) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2858 reference_control_expr_2858 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2858 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2858 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2857.
 reflexivity.
Qed.
Lemma reference_control_ready_2859 old :
 reference_control_ready old reference_control_expr_2859.
Proof.
 unfold reference_control_expr_2859.
apply rc_binary.
Qed.
Lemma reference_control_member_2859 : List.In (2859,reference_control_expr_2859) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 31%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2859_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2859 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2859 reference_control_expr_2859 reference_control_3_positions reference_control_3_safety reference_control_member_2859) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2859 reference_control_expr_2859 inputs path old current result Position Safe Nonreg (reference_control_ready_2859 old ) Step).
Qed.
Theorem reference_control_node_2859_congruent inputs path left right next_left next_right :
 VM.find 2853 left = VM.find 2853 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2859 next_left = VM.find 2859 next_right.
Proof.
 intros  E2853 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2859 reference_control_expr_2859 reference_control_3_positions reference_control_3_safety reference_control_member_2859) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2859 reference_control_expr_2859 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2859 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2859 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2853.
 reflexivity.
Qed.
Lemma reference_control_ready_2860 old :
 reference_control_ready old reference_control_expr_2860.
Proof.
 unfold reference_control_expr_2860.
apply rc_unary.
Qed.
Lemma reference_control_member_2860 : List.In (2860,reference_control_expr_2860) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 32%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2860_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2860 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2860 reference_control_expr_2860 reference_control_3_positions reference_control_3_safety reference_control_member_2860) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2860 reference_control_expr_2860 inputs path old current result Position Safe Nonreg (reference_control_ready_2860 old ) Step).
Qed.
Theorem reference_control_node_2860_congruent inputs path left right next_left next_right :
 VM.find 2856 left = VM.find 2856 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2860 next_left = VM.find 2860 next_right.
Proof.
 intros  E2856 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2860 reference_control_expr_2860 reference_control_3_positions reference_control_3_safety reference_control_member_2860) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2860 reference_control_expr_2860 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2860 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2860 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2856.
 reflexivity.
Qed.
Lemma reference_control_ready_2861 old :
 reference_control_ready old reference_control_expr_2861.
Proof.
 unfold reference_control_expr_2861.
apply rc_binary.
Qed.
Lemma reference_control_member_2861 : List.In (2861,reference_control_expr_2861) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 33%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2861_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2861 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2861 reference_control_expr_2861 reference_control_3_positions reference_control_3_safety reference_control_member_2861) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2861 reference_control_expr_2861 inputs path old current result Position Safe Nonreg (reference_control_ready_2861 old ) Step).
Qed.
Theorem reference_control_node_2861_congruent inputs path left right next_left next_right :
 VM.find 2860 left = VM.find 2860 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2861 next_left = VM.find 2861 next_right.
Proof.
 intros  E2860 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2861 reference_control_expr_2861 reference_control_3_positions reference_control_3_safety reference_control_member_2861) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2861 reference_control_expr_2861 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2861 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2861 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2860.
 reflexivity.
Qed.
Lemma reference_control_ready_2862 old :
 reference_control_ready old reference_control_expr_2862.
Proof.
 unfold reference_control_expr_2862.
apply rc_binary.
Qed.
Lemma reference_control_member_2862 : List.In (2862,reference_control_expr_2862) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 34%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2862_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2862 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2862 reference_control_expr_2862 reference_control_3_positions reference_control_3_safety reference_control_member_2862) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2862 reference_control_expr_2862 inputs path old current result Position Safe Nonreg (reference_control_ready_2862 old ) Step).
Qed.
Theorem reference_control_node_2862_congruent inputs path left right next_left next_right :
 VM.find 2853 left = VM.find 2853 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2862 next_left = VM.find 2862 next_right.
Proof.
 intros  E2853 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2862 reference_control_expr_2862 reference_control_3_positions reference_control_3_safety reference_control_member_2862) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2862 reference_control_expr_2862 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2862 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2862 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2853.
 reflexivity.
Qed.
Lemma reference_control_ready_2863 old :
 reference_control_ready old reference_control_expr_2863.
Proof.
 unfold reference_control_expr_2863.
apply rc_unary.
Qed.
Lemma reference_control_member_2863 : List.In (2863,reference_control_expr_2863) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 35%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2863_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2863 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2863 reference_control_expr_2863 reference_control_3_positions reference_control_3_safety reference_control_member_2863) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2863 reference_control_expr_2863 inputs path old current result Position Safe Nonreg (reference_control_ready_2863 old ) Step).
Qed.
Theorem reference_control_node_2863_congruent inputs path left right next_left next_right :
 VM.find 2856 left = VM.find 2856 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2863 next_left = VM.find 2863 next_right.
Proof.
 intros  E2856 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2863 reference_control_expr_2863 reference_control_3_positions reference_control_3_safety reference_control_member_2863) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2863 reference_control_expr_2863 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2863 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2863 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2856.
 reflexivity.
Qed.
Lemma reference_control_ready_2864 old :
 reference_control_ready old reference_control_expr_2864.
Proof.
 unfold reference_control_expr_2864.
apply rc_binary.
Qed.
Lemma reference_control_member_2864 : List.In (2864,reference_control_expr_2864) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 36%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2864_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2864 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2864 reference_control_expr_2864 reference_control_3_positions reference_control_3_safety reference_control_member_2864) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2864 reference_control_expr_2864 inputs path old current result Position Safe Nonreg (reference_control_ready_2864 old ) Step).
Qed.
Theorem reference_control_node_2864_congruent inputs path left right next_left next_right :
 VM.find 2863 left = VM.find 2863 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2864 next_left = VM.find 2864 next_right.
Proof.
 intros  E2863 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2864 reference_control_expr_2864 reference_control_3_positions reference_control_3_safety reference_control_member_2864) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2864 reference_control_expr_2864 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2864 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2864 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2863.
 reflexivity.
Qed.
Lemma reference_control_ready_2865 old :
 (exists value ground, VM.find 2864 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2865.
Proof.
 intros H2864.
 destruct H2864 as [v2864 [G2864 [V2864 T2864]]].
 unfold reference_control_expr_2865.
apply rc_mux.
{ eapply rc_ref; [exact V2864|exists G2864; exact T2864].
}
{ apply rc_const.
}
Qed.
Lemma reference_control_member_2865 : List.In (2865,reference_control_expr_2865) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 37%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2865_ground inputs path old current result :
 (exists value ground, VM.find 2864 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2865 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2864 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2865 reference_control_expr_2865 reference_control_3_positions reference_control_3_safety reference_control_member_2865) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2865 reference_control_expr_2865 inputs path old current result Position Safe Nonreg (reference_control_ready_2865 old H2864) Step).
Qed.
Theorem reference_control_node_2865_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2864 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2862 left = VM.find 2862 right ->
 VM.find 2864 left = VM.find 2864 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2865 next_left = VM.find 2865 next_right.
Proof.
 intros H2864 E2862 E2864 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2865 reference_control_expr_2865 reference_control_3_positions reference_control_3_safety reference_control_member_2865) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2865 reference_control_expr_2865 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2865 left H2864)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2865 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2862.
 rewrite E2864.
 reflexivity.
Qed.
Lemma reference_control_ready_2866 old :
 (exists value ground, VM.find 2861 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2865 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2866.
Proof.
 intros H2861 H2865.
 destruct H2861 as [v2861 [G2861 [V2861 T2861]]].
 destruct H2865 as [v2865 [G2865 [V2865 T2865]]].
 unfold reference_control_expr_2866.
apply rc_mux.
{ eapply rc_ref; [exact V2861|exists G2861; exact T2861].
}
{ eapply rc_ref; [exact V2865|exists G2865; exact T2865].
}
Qed.
Lemma reference_control_member_2866 : List.In (2866,reference_control_expr_2866) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 38%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2866_ground inputs path old current result :
 (exists value ground, VM.find 2861 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2865 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2866 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2861 H2865 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2866 reference_control_expr_2866 reference_control_3_positions reference_control_3_safety reference_control_member_2866) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2866 reference_control_expr_2866 inputs path old current result Position Safe Nonreg (reference_control_ready_2866 old H2861 H2865) Step).
Qed.
Theorem reference_control_node_2866_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2861 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2865 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2859 left = VM.find 2859 right ->
 VM.find 2861 left = VM.find 2861 right ->
 VM.find 2865 left = VM.find 2865 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2866 next_left = VM.find 2866 next_right.
Proof.
 intros H2861 H2865 E2859 E2861 E2865 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2866 reference_control_expr_2866 reference_control_3_positions reference_control_3_safety reference_control_member_2866) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2866 reference_control_expr_2866 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2866 left H2861 H2865)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2866 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2859.
 rewrite E2861.
 rewrite E2865.
 reflexivity.
Qed.
Lemma reference_control_ready_2867 old :
 (exists value ground, VM.find 2858 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2866 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2867.
Proof.
 intros H2858 H2866.
 destruct H2858 as [v2858 [G2858 [V2858 T2858]]].
 destruct H2866 as [v2866 [G2866 [V2866 T2866]]].
 unfold reference_control_expr_2867.
apply rc_mux.
{ eapply rc_ref; [exact V2858|exists G2858; exact T2858].
}
{ eapply rc_ref; [exact V2866|exists G2866; exact T2866].
}
Qed.
Lemma reference_control_member_2867 : List.In (2867,reference_control_expr_2867) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 39%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2867_ground inputs path old current result :
 (exists value ground, VM.find 2858 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2866 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2867 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2858 H2866 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2867 reference_control_expr_2867 reference_control_3_positions reference_control_3_safety reference_control_member_2867) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2867 reference_control_expr_2867 inputs path old current result Position Safe Nonreg (reference_control_ready_2867 old H2858 H2866) Step).
Qed.
Theorem reference_control_node_2867_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2858 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2866 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2854 left = VM.find 2854 right ->
 VM.find 2858 left = VM.find 2858 right ->
 VM.find 2866 left = VM.find 2866 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2867 next_left = VM.find 2867 next_right.
Proof.
 intros H2858 H2866 E2854 E2858 E2866 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2867 reference_control_expr_2867 reference_control_3_positions reference_control_3_safety reference_control_member_2867) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2867 reference_control_expr_2867 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2867 left H2858 H2866)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2867 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2854.
 rewrite E2858.
 rewrite E2866.
 reflexivity.
Qed.
Lemma reference_control_ready_2868 old :
 (exists value ground, VM.find 2209 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2868.
Proof.
 intros H2209.
 destruct H2209 as [v2209 [G2209 [V2209 T2209]]].
 unfold reference_control_expr_2868.
eapply rc_ref; [exact V2209|exists G2209; exact T2209].
Qed.
Lemma reference_control_member_2868 : List.In (2868,reference_control_expr_2868) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 40%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2868_ground inputs path old current result :
 (exists value ground, VM.find 2209 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2868 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2209 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2868 reference_control_expr_2868 reference_control_3_positions reference_control_3_safety reference_control_member_2868) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2868 reference_control_expr_2868 inputs path old current result Position Safe Nonreg (reference_control_ready_2868 old H2209) Step).
Qed.
Theorem reference_control_node_2868_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2209 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2209 left = VM.find 2209 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2868 next_left = VM.find 2868 next_right.
Proof.
 intros H2209 E2209 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2868 reference_control_expr_2868 reference_control_3_positions reference_control_3_safety reference_control_member_2868) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2868 reference_control_expr_2868 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2868 left H2209)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2868 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2209.
 reflexivity.
Qed.
Lemma reference_control_ready_2869 old :
 reference_control_ready old reference_control_expr_2869.
Proof.
 unfold reference_control_expr_2869.
apply rc_cast.
Qed.
Lemma reference_control_member_2869 : List.In (2869,reference_control_expr_2869) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 41%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2869_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2869 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2869 reference_control_expr_2869 reference_control_3_positions reference_control_3_safety reference_control_member_2869) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2869 reference_control_expr_2869 inputs path old current result Position Safe Nonreg (reference_control_ready_2869 old ) Step).
Qed.
Theorem reference_control_node_2869_congruent inputs path left right next_left next_right :
 VM.find 2868 left = VM.find 2868 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2869 next_left = VM.find 2869 next_right.
Proof.
 intros  E2868 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2869 reference_control_expr_2869 reference_control_3_positions reference_control_3_safety reference_control_member_2869) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2869 reference_control_expr_2869 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2869 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2869 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2868.
 reflexivity.
Qed.
Lemma reference_control_ready_2870 old :
 (exists value ground, VM.find 2804 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2870.
Proof.
 intros H2804.
 destruct H2804 as [v2804 [G2804 [V2804 T2804]]].
 unfold reference_control_expr_2870.
eapply rc_ref; [exact V2804|exists G2804; exact T2804].
Qed.
Lemma reference_control_member_2870 : List.In (2870,reference_control_expr_2870) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 42%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2870_ground inputs path old current result :
 (exists value ground, VM.find 2804 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2870 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2804 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2870 reference_control_expr_2870 reference_control_3_positions reference_control_3_safety reference_control_member_2870) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2870 reference_control_expr_2870 inputs path old current result Position Safe Nonreg (reference_control_ready_2870 old H2804) Step).
Qed.
Theorem reference_control_node_2870_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2804 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2804 left = VM.find 2804 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2870 next_left = VM.find 2870 next_right.
Proof.
 intros H2804 E2804 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2870 reference_control_expr_2870 reference_control_3_positions reference_control_3_safety reference_control_member_2870) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2870 reference_control_expr_2870 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2870 left H2804)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2870 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2804.
 reflexivity.
Qed.
Lemma reference_control_ready_2871 old :
 reference_control_ready old reference_control_expr_2871.
Proof.
 unfold reference_control_expr_2871.
apply rc_cast.
Qed.
Lemma reference_control_member_2871 : List.In (2871,reference_control_expr_2871) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 43%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2871_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2871 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2871 reference_control_expr_2871 reference_control_3_positions reference_control_3_safety reference_control_member_2871) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2871 reference_control_expr_2871 inputs path old current result Position Safe Nonreg (reference_control_ready_2871 old ) Step).
Qed.
Theorem reference_control_node_2871_congruent inputs path left right next_left next_right :
 VM.find 2870 left = VM.find 2870 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2871 next_left = VM.find 2871 next_right.
Proof.
 intros  E2870 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2871 reference_control_expr_2871 reference_control_3_positions reference_control_3_safety reference_control_member_2871) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2871 reference_control_expr_2871 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2871 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2871 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2870.
 reflexivity.
Qed.
Lemma reference_control_ready_2872 old :
 reference_control_ready old reference_control_expr_2872.
Proof.
 unfold reference_control_expr_2872.
apply rc_binary.
Qed.
Lemma reference_control_member_2872 : List.In (2872,reference_control_expr_2872) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 44%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2872_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2872 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2872 reference_control_expr_2872 reference_control_3_positions reference_control_3_safety reference_control_member_2872) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2872 reference_control_expr_2872 inputs path old current result Position Safe Nonreg (reference_control_ready_2872 old ) Step).
Qed.
Theorem reference_control_node_2872_congruent inputs path left right next_left next_right :
 VM.find 2869 left = VM.find 2869 right ->
 VM.find 2871 left = VM.find 2871 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2872 next_left = VM.find 2872 next_right.
Proof.
 intros  E2869 E2871 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2872 reference_control_expr_2872 reference_control_3_positions reference_control_3_safety reference_control_member_2872) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2872 reference_control_expr_2872 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2872 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2872 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2869.
 rewrite E2871.
 reflexivity.
Qed.
Lemma reference_control_ready_2873 old :
 reference_control_ready old reference_control_expr_2873.
Proof.
 unfold reference_control_expr_2873.
apply rc_unary.
Qed.
Lemma reference_control_member_2873 : List.In (2873,reference_control_expr_2873) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 45%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2873_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2873 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2873 reference_control_expr_2873 reference_control_3_positions reference_control_3_safety reference_control_member_2873) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2873 reference_control_expr_2873 inputs path old current result Position Safe Nonreg (reference_control_ready_2873 old ) Step).
Qed.
Theorem reference_control_node_2873_congruent inputs path left right next_left next_right :
 VM.find 2807 left = VM.find 2807 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2873 next_left = VM.find 2873 next_right.
Proof.
 intros  E2807 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2873 reference_control_expr_2873 reference_control_3_positions reference_control_3_safety reference_control_member_2873) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2873 reference_control_expr_2873 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2873 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2873 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2807.
 reflexivity.
Qed.
Lemma reference_control_ready_2874 old :
 reference_control_ready old reference_control_expr_2874.
Proof.
 unfold reference_control_expr_2874.
apply rc_binary.
Qed.
Lemma reference_control_member_2874 : List.In (2874,reference_control_expr_2874) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 46%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2874_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2874 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2874 reference_control_expr_2874 reference_control_3_positions reference_control_3_safety reference_control_member_2874) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2874 reference_control_expr_2874 inputs path old current result Position Safe Nonreg (reference_control_ready_2874 old ) Step).
Qed.
Theorem reference_control_node_2874_congruent inputs path left right next_left next_right :
 VM.find 2873 left = VM.find 2873 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2874 next_left = VM.find 2874 next_right.
Proof.
 intros  E2873 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2874 reference_control_expr_2874 reference_control_3_positions reference_control_3_safety reference_control_member_2874) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2874 reference_control_expr_2874 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2874 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2874 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2873.
 reflexivity.
Qed.
Lemma reference_control_ready_2875 old :
 reference_control_ready old reference_control_expr_2875.
Proof.
 unfold reference_control_expr_2875.
apply rc_mux.
{ apply rc_const.
}
{ apply rc_const.
}
Qed.
Lemma reference_control_member_2875 : List.In (2875,reference_control_expr_2875) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 47%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2875_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2875 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2875 reference_control_expr_2875 reference_control_3_positions reference_control_3_safety reference_control_member_2875) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2875 reference_control_expr_2875 inputs path old current result Position Safe Nonreg (reference_control_ready_2875 old ) Step).
Qed.
Theorem reference_control_node_2875_congruent inputs path left right next_left next_right :
 VM.find 2874 left = VM.find 2874 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2875 next_left = VM.find 2875 next_right.
Proof.
 intros  E2874 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2875 reference_control_expr_2875 reference_control_3_positions reference_control_3_safety reference_control_member_2875) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2875 reference_control_expr_2875 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2875 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2875 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2874.
 reflexivity.
Qed.
Lemma reference_control_ready_2876 old :
 reference_control_ready old reference_control_expr_2876.
Proof.
 unfold reference_control_expr_2876.
apply rc_binary.
Qed.
Lemma reference_control_member_2876 : List.In (2876,reference_control_expr_2876) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 48%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2876_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2876 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2876 reference_control_expr_2876 reference_control_3_positions reference_control_3_safety reference_control_member_2876) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2876 reference_control_expr_2876 inputs path old current result Position Safe Nonreg (reference_control_ready_2876 old ) Step).
Qed.
Theorem reference_control_node_2876_congruent inputs path left right next_left next_right :
 VM.find 2875 left = VM.find 2875 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2876 next_left = VM.find 2876 next_right.
Proof.
 intros  E2875 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2876 reference_control_expr_2876 reference_control_3_positions reference_control_3_safety reference_control_member_2876) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2876 reference_control_expr_2876 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2876 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2876 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2875.
 reflexivity.
Qed.
Lemma reference_control_ready_2877 old :
 reference_control_ready old reference_control_expr_2877.
Proof.
 unfold reference_control_expr_2877.
apply rc_binary.
Qed.
Lemma reference_control_member_2877 : List.In (2877,reference_control_expr_2877) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 49%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2877_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2877 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2877 reference_control_expr_2877 reference_control_3_positions reference_control_3_safety reference_control_member_2877) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2877 reference_control_expr_2877 inputs path old current result Position Safe Nonreg (reference_control_ready_2877 old ) Step).
Qed.
Theorem reference_control_node_2877_congruent inputs path left right next_left next_right :
 VM.find 2552 left = VM.find 2552 right ->
 VM.find 2812 left = VM.find 2812 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2877 next_left = VM.find 2877 next_right.
Proof.
 intros  E2552 E2812 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2877 reference_control_expr_2877 reference_control_3_positions reference_control_3_safety reference_control_member_2877) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2877 reference_control_expr_2877 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2877 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2877 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2552.
 rewrite E2812.
 reflexivity.
Qed.
Lemma reference_control_ready_2878 old :
 reference_control_ready old reference_control_expr_2878.
Proof.
 unfold reference_control_expr_2878.
apply rc_unary.
Qed.
Lemma reference_control_member_2878 : List.In (2878,reference_control_expr_2878) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 50%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2878_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2878 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2878 reference_control_expr_2878 reference_control_3_positions reference_control_3_safety reference_control_member_2878) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2878 reference_control_expr_2878 inputs path old current result Position Safe Nonreg (reference_control_ready_2878 old ) Step).
Qed.
Theorem reference_control_node_2878_congruent inputs path left right next_left next_right :
 VM.find 2877 left = VM.find 2877 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2878 next_left = VM.find 2878 next_right.
Proof.
 intros  E2877 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2878 reference_control_expr_2878 reference_control_3_positions reference_control_3_safety reference_control_member_2878) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2878 reference_control_expr_2878 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2878 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2878 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2877.
 reflexivity.
Qed.
Lemma reference_control_ready_2879 old :
 reference_control_ready old reference_control_expr_2879.
Proof.
 unfold reference_control_expr_2879.
apply rc_unary.
Qed.
Lemma reference_control_member_2879 : List.In (2879,reference_control_expr_2879) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 51%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2879_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2879 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2879 reference_control_expr_2879 reference_control_3_positions reference_control_3_safety reference_control_member_2879) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2879 reference_control_expr_2879 inputs path old current result Position Safe Nonreg (reference_control_ready_2879 old ) Step).
Qed.
Theorem reference_control_node_2879_congruent inputs path left right next_left next_right :
 VM.find 2878 left = VM.find 2878 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2879 next_left = VM.find 2879 next_right.
Proof.
 intros  E2878 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2879 reference_control_expr_2879 reference_control_3_positions reference_control_3_safety reference_control_member_2879) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2879 reference_control_expr_2879 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2879 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2879 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2878.
 reflexivity.
Qed.
Lemma reference_control_ready_2880 old :
 reference_control_ready old reference_control_expr_2880.
Proof.
 unfold reference_control_expr_2880.
apply rc_binary.
Qed.
Lemma reference_control_member_2880 : List.In (2880,reference_control_expr_2880) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 52%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2880_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2880 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2880 reference_control_expr_2880 reference_control_3_positions reference_control_3_safety reference_control_member_2880) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2880 reference_control_expr_2880 inputs path old current result Position Safe Nonreg (reference_control_ready_2880 old ) Step).
Qed.
Theorem reference_control_node_2880_congruent inputs path left right next_left next_right :
 VM.find 2879 left = VM.find 2879 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2880 next_left = VM.find 2880 next_right.
Proof.
 intros  E2879 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2880 reference_control_expr_2880 reference_control_3_positions reference_control_3_safety reference_control_member_2880) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2880 reference_control_expr_2880 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2880 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2880 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2879.
 reflexivity.
Qed.
Lemma reference_control_ready_2881 old :
 reference_control_ready old reference_control_expr_2881.
Proof.
 unfold reference_control_expr_2881.
apply rc_binary.
Qed.
Lemma reference_control_member_2881 : List.In (2881,reference_control_expr_2881) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 53%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2881_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2881 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2881 reference_control_expr_2881 reference_control_3_positions reference_control_3_safety reference_control_member_2881) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2881 reference_control_expr_2881 inputs path old current result Position Safe Nonreg (reference_control_ready_2881 old ) Step).
Qed.
Theorem reference_control_node_2881_congruent inputs path left right next_left next_right :
 VM.find 2875 left = VM.find 2875 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2881 next_left = VM.find 2881 next_right.
Proof.
 intros  E2875 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2881 reference_control_expr_2881 reference_control_3_positions reference_control_3_safety reference_control_member_2881) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2881 reference_control_expr_2881 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2881 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2881 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2875.
 reflexivity.
Qed.
Lemma reference_control_ready_2882 old :
 reference_control_ready old reference_control_expr_2882.
Proof.
 unfold reference_control_expr_2882.
apply rc_unary.
Qed.
Lemma reference_control_member_2882 : List.In (2882,reference_control_expr_2882) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 54%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2882_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2882 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2882 reference_control_expr_2882 reference_control_3_positions reference_control_3_safety reference_control_member_2882) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2882 reference_control_expr_2882 inputs path old current result Position Safe Nonreg (reference_control_ready_2882 old ) Step).
Qed.
Theorem reference_control_node_2882_congruent inputs path left right next_left next_right :
 VM.find 2878 left = VM.find 2878 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2882 next_left = VM.find 2882 next_right.
Proof.
 intros  E2878 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2882 reference_control_expr_2882 reference_control_3_positions reference_control_3_safety reference_control_member_2882) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2882 reference_control_expr_2882 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2882 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2882 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2878.
 reflexivity.
Qed.
Lemma reference_control_ready_2883 old :
 reference_control_ready old reference_control_expr_2883.
Proof.
 unfold reference_control_expr_2883.
apply rc_binary.
Qed.
Lemma reference_control_member_2883 : List.In (2883,reference_control_expr_2883) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 55%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2883_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2883 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2883 reference_control_expr_2883 reference_control_3_positions reference_control_3_safety reference_control_member_2883) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2883 reference_control_expr_2883 inputs path old current result Position Safe Nonreg (reference_control_ready_2883 old ) Step).
Qed.
Theorem reference_control_node_2883_congruent inputs path left right next_left next_right :
 VM.find 2882 left = VM.find 2882 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2883 next_left = VM.find 2883 next_right.
Proof.
 intros  E2882 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2883 reference_control_expr_2883 reference_control_3_positions reference_control_3_safety reference_control_member_2883) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2883 reference_control_expr_2883 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2883 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2883 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2882.
 reflexivity.
Qed.
Lemma reference_control_ready_2884 old :
 reference_control_ready old reference_control_expr_2884.
Proof.
 unfold reference_control_expr_2884.
apply rc_binary.
Qed.
Lemma reference_control_member_2884 : List.In (2884,reference_control_expr_2884) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 56%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2884_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2884 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2884 reference_control_expr_2884 reference_control_3_positions reference_control_3_safety reference_control_member_2884) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2884 reference_control_expr_2884 inputs path old current result Position Safe Nonreg (reference_control_ready_2884 old ) Step).
Qed.
Theorem reference_control_node_2884_congruent inputs path left right next_left next_right :
 VM.find 2875 left = VM.find 2875 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2884 next_left = VM.find 2884 next_right.
Proof.
 intros  E2875 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2884 reference_control_expr_2884 reference_control_3_positions reference_control_3_safety reference_control_member_2884) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2884 reference_control_expr_2884 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2884 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2884 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2875.
 reflexivity.
Qed.
Lemma reference_control_ready_2885 old :
 reference_control_ready old reference_control_expr_2885.
Proof.
 unfold reference_control_expr_2885.
apply rc_unary.
Qed.
Lemma reference_control_member_2885 : List.In (2885,reference_control_expr_2885) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 57%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2885_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2885 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2885 reference_control_expr_2885 reference_control_3_positions reference_control_3_safety reference_control_member_2885) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2885 reference_control_expr_2885 inputs path old current result Position Safe Nonreg (reference_control_ready_2885 old ) Step).
Qed.
Theorem reference_control_node_2885_congruent inputs path left right next_left next_right :
 VM.find 2878 left = VM.find 2878 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2885 next_left = VM.find 2885 next_right.
Proof.
 intros  E2878 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2885 reference_control_expr_2885 reference_control_3_positions reference_control_3_safety reference_control_member_2885) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2885 reference_control_expr_2885 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2885 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2885 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2878.
 reflexivity.
Qed.
Lemma reference_control_ready_2886 old :
 reference_control_ready old reference_control_expr_2886.
Proof.
 unfold reference_control_expr_2886.
apply rc_binary.
Qed.
Lemma reference_control_member_2886 : List.In (2886,reference_control_expr_2886) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 58%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2886_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2886 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2886 reference_control_expr_2886 reference_control_3_positions reference_control_3_safety reference_control_member_2886) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2886 reference_control_expr_2886 inputs path old current result Position Safe Nonreg (reference_control_ready_2886 old ) Step).
Qed.
Theorem reference_control_node_2886_congruent inputs path left right next_left next_right :
 VM.find 2885 left = VM.find 2885 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2886 next_left = VM.find 2886 next_right.
Proof.
 intros  E2885 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2886 reference_control_expr_2886 reference_control_3_positions reference_control_3_safety reference_control_member_2886) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2886 reference_control_expr_2886 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2886 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2886 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2885.
 reflexivity.
Qed.
Lemma reference_control_ready_2887 old :
 (exists value ground, VM.find 2886 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2887.
Proof.
 intros H2886.
 destruct H2886 as [v2886 [G2886 [V2886 T2886]]].
 unfold reference_control_expr_2887.
apply rc_mux.
{ eapply rc_ref; [exact V2886|exists G2886; exact T2886].
}
{ apply rc_const.
}
Qed.
Lemma reference_control_member_2887 : List.In (2887,reference_control_expr_2887) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 59%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2887_ground inputs path old current result :
 (exists value ground, VM.find 2886 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2887 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2886 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2887 reference_control_expr_2887 reference_control_3_positions reference_control_3_safety reference_control_member_2887) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2887 reference_control_expr_2887 inputs path old current result Position Safe Nonreg (reference_control_ready_2887 old H2886) Step).
Qed.
Theorem reference_control_node_2887_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2886 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2884 left = VM.find 2884 right ->
 VM.find 2886 left = VM.find 2886 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2887 next_left = VM.find 2887 next_right.
Proof.
 intros H2886 E2884 E2886 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2887 reference_control_expr_2887 reference_control_3_positions reference_control_3_safety reference_control_member_2887) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2887 reference_control_expr_2887 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2887 left H2886)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2887 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2884.
 rewrite E2886.
 reflexivity.
Qed.
Lemma reference_control_ready_2888 old :
 (exists value ground, VM.find 2883 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2887 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2888.
Proof.
 intros H2883 H2887.
 destruct H2883 as [v2883 [G2883 [V2883 T2883]]].
 destruct H2887 as [v2887 [G2887 [V2887 T2887]]].
 unfold reference_control_expr_2888.
apply rc_mux.
{ eapply rc_ref; [exact V2883|exists G2883; exact T2883].
}
{ eapply rc_ref; [exact V2887|exists G2887; exact T2887].
}
Qed.
Lemma reference_control_member_2888 : List.In (2888,reference_control_expr_2888) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 60%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2888_ground inputs path old current result :
 (exists value ground, VM.find 2883 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2887 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2888 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2883 H2887 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2888 reference_control_expr_2888 reference_control_3_positions reference_control_3_safety reference_control_member_2888) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2888 reference_control_expr_2888 inputs path old current result Position Safe Nonreg (reference_control_ready_2888 old H2883 H2887) Step).
Qed.
Theorem reference_control_node_2888_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2883 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2887 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2881 left = VM.find 2881 right ->
 VM.find 2883 left = VM.find 2883 right ->
 VM.find 2887 left = VM.find 2887 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2888 next_left = VM.find 2888 next_right.
Proof.
 intros H2883 H2887 E2881 E2883 E2887 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2888 reference_control_expr_2888 reference_control_3_positions reference_control_3_safety reference_control_member_2888) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2888 reference_control_expr_2888 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2888 left H2883 H2887)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2888 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2881.
 rewrite E2883.
 rewrite E2887.
 reflexivity.
Qed.
Lemma reference_control_ready_2889 old :
 (exists value ground, VM.find 2880 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2888 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2889.
Proof.
 intros H2880 H2888.
 destruct H2880 as [v2880 [G2880 [V2880 T2880]]].
 destruct H2888 as [v2888 [G2888 [V2888 T2888]]].
 unfold reference_control_expr_2889.
apply rc_mux.
{ eapply rc_ref; [exact V2880|exists G2880; exact T2880].
}
{ eapply rc_ref; [exact V2888|exists G2888; exact T2888].
}
Qed.
Lemma reference_control_member_2889 : List.In (2889,reference_control_expr_2889) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 61%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2889_ground inputs path old current result :
 (exists value ground, VM.find 2880 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2888 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2889 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2880 H2888 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2889 reference_control_expr_2889 reference_control_3_positions reference_control_3_safety reference_control_member_2889) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2889 reference_control_expr_2889 inputs path old current result Position Safe Nonreg (reference_control_ready_2889 old H2880 H2888) Step).
Qed.
Theorem reference_control_node_2889_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2880 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2888 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2876 left = VM.find 2876 right ->
 VM.find 2880 left = VM.find 2880 right ->
 VM.find 2888 left = VM.find 2888 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2889 next_left = VM.find 2889 next_right.
Proof.
 intros H2880 H2888 E2876 E2880 E2888 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2889 reference_control_expr_2889 reference_control_3_positions reference_control_3_safety reference_control_member_2889) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2889 reference_control_expr_2889 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2889 left H2880 H2888)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2889 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2876.
 rewrite E2880.
 rewrite E2888.
 reflexivity.
Qed.
Lemma reference_control_ready_2890 old :
 (exists value ground, VM.find 2209 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2890.
Proof.
 intros H2209.
 destruct H2209 as [v2209 [G2209 [V2209 T2209]]].
 unfold reference_control_expr_2890.
eapply rc_ref; [exact V2209|exists G2209; exact T2209].
Qed.
Lemma reference_control_member_2890 : List.In (2890,reference_control_expr_2890) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 62%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2890_ground inputs path old current result :
 (exists value ground, VM.find 2209 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2890 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2209 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2890 reference_control_expr_2890 reference_control_3_positions reference_control_3_safety reference_control_member_2890) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2890 reference_control_expr_2890 inputs path old current result Position Safe Nonreg (reference_control_ready_2890 old H2209) Step).
Qed.
Theorem reference_control_node_2890_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2209 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2209 left = VM.find 2209 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2890 next_left = VM.find 2890 next_right.
Proof.
 intros H2209 E2209 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2890 reference_control_expr_2890 reference_control_3_positions reference_control_3_safety reference_control_member_2890) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2890 reference_control_expr_2890 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2890 left H2209)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2890 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2209.
 reflexivity.
Qed.
Lemma reference_control_ready_2891 old :
 (exists value ground, VM.find 2804 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2891.
Proof.
 intros H2804.
 destruct H2804 as [v2804 [G2804 [V2804 T2804]]].
 unfold reference_control_expr_2891.
eapply rc_ref; [exact V2804|exists G2804; exact T2804].
Qed.
Lemma reference_control_member_2891 : List.In (2891,reference_control_expr_2891) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 63%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2891_ground inputs path old current result :
 (exists value ground, VM.find 2804 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2891 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2804 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2891 reference_control_expr_2891 reference_control_3_positions reference_control_3_safety reference_control_member_2891) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2891 reference_control_expr_2891 inputs path old current result Position Safe Nonreg (reference_control_ready_2891 old H2804) Step).
Qed.
Theorem reference_control_node_2891_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2804 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2804 left = VM.find 2804 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2891 next_left = VM.find 2891 next_right.
Proof.
 intros H2804 E2804 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2891 reference_control_expr_2891 reference_control_3_positions reference_control_3_safety reference_control_member_2891) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2891 reference_control_expr_2891 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2891 left H2804)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2891 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2804.
 reflexivity.
Qed.
Lemma reference_control_ready_2892 old :
 reference_control_ready old reference_control_expr_2892.
Proof.
 unfold reference_control_expr_2892.
apply rc_binary.
Qed.
Lemma reference_control_member_2892 : List.In (2892,reference_control_expr_2892) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 64%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2892_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2892 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2892 reference_control_expr_2892 reference_control_3_positions reference_control_3_safety reference_control_member_2892) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2892 reference_control_expr_2892 inputs path old current result Position Safe Nonreg (reference_control_ready_2892 old ) Step).
Qed.
Theorem reference_control_node_2892_congruent inputs path left right next_left next_right :
 VM.find 2890 left = VM.find 2890 right ->
 VM.find 2891 left = VM.find 2891 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2892 next_left = VM.find 2892 next_right.
Proof.
 intros  E2890 E2891 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2892 reference_control_expr_2892 reference_control_3_positions reference_control_3_safety reference_control_member_2892) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2892 reference_control_expr_2892 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2892 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2892 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2890.
 rewrite E2891.
 reflexivity.
Qed.
Lemma reference_control_ready_2893 old :
 reference_control_ready old reference_control_expr_2893.
Proof.
 unfold reference_control_expr_2893.
apply rc_unary.
Qed.
Lemma reference_control_member_2893 : List.In (2893,reference_control_expr_2893) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 65%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2893_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2893 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2893 reference_control_expr_2893 reference_control_3_positions reference_control_3_safety reference_control_member_2893) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2893 reference_control_expr_2893 inputs path old current result Position Safe Nonreg (reference_control_ready_2893 old ) Step).
Qed.
Theorem reference_control_node_2893_congruent inputs path left right next_left next_right :
 VM.find 2807 left = VM.find 2807 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2893 next_left = VM.find 2893 next_right.
Proof.
 intros  E2807 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2893 reference_control_expr_2893 reference_control_3_positions reference_control_3_safety reference_control_member_2893) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2893 reference_control_expr_2893 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2893 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2893 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2807.
 reflexivity.
Qed.
Lemma reference_control_ready_2894 old :
 reference_control_ready old reference_control_expr_2894.
Proof.
 unfold reference_control_expr_2894.
apply rc_binary.
Qed.
Lemma reference_control_member_2894 : List.In (2894,reference_control_expr_2894) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 66%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2894_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2894 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2894 reference_control_expr_2894 reference_control_3_positions reference_control_3_safety reference_control_member_2894) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2894 reference_control_expr_2894 inputs path old current result Position Safe Nonreg (reference_control_ready_2894 old ) Step).
Qed.
Theorem reference_control_node_2894_congruent inputs path left right next_left next_right :
 VM.find 2893 left = VM.find 2893 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2894 next_left = VM.find 2894 next_right.
Proof.
 intros  E2893 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2894 reference_control_expr_2894 reference_control_3_positions reference_control_3_safety reference_control_member_2894) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2894 reference_control_expr_2894 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2894 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2894 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2893.
 reflexivity.
Qed.
Lemma reference_control_ready_2895 old :
 reference_control_ready old reference_control_expr_2895.
Proof.
 unfold reference_control_expr_2895.
apply rc_mux.
{ apply rc_const.
}
{ apply rc_const.
}
Qed.
Lemma reference_control_member_2895 : List.In (2895,reference_control_expr_2895) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 67%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2895_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2895 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2895 reference_control_expr_2895 reference_control_3_positions reference_control_3_safety reference_control_member_2895) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2895 reference_control_expr_2895 inputs path old current result Position Safe Nonreg (reference_control_ready_2895 old ) Step).
Qed.
Theorem reference_control_node_2895_congruent inputs path left right next_left next_right :
 VM.find 2894 left = VM.find 2894 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2895 next_left = VM.find 2895 next_right.
Proof.
 intros  E2894 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2895 reference_control_expr_2895 reference_control_3_positions reference_control_3_safety reference_control_member_2895) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2895 reference_control_expr_2895 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2895 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2895 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2894.
 reflexivity.
Qed.
Lemma reference_control_ready_2896 old :
 reference_control_ready old reference_control_expr_2896.
Proof.
 unfold reference_control_expr_2896.
apply rc_binary.
Qed.
Lemma reference_control_member_2896 : List.In (2896,reference_control_expr_2896) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 68%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2896_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2896 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2896 reference_control_expr_2896 reference_control_3_positions reference_control_3_safety reference_control_member_2896) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2896 reference_control_expr_2896 inputs path old current result Position Safe Nonreg (reference_control_ready_2896 old ) Step).
Qed.
Theorem reference_control_node_2896_congruent inputs path left right next_left next_right :
 VM.find 2895 left = VM.find 2895 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2896 next_left = VM.find 2896 next_right.
Proof.
 intros  E2895 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2896 reference_control_expr_2896 reference_control_3_positions reference_control_3_safety reference_control_member_2896) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2896 reference_control_expr_2896 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2896 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2896 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2895.
 reflexivity.
Qed.
Lemma reference_control_ready_2897 old :
 reference_control_ready old reference_control_expr_2897.
Proof.
 unfold reference_control_expr_2897.
apply rc_binary.
Qed.
Lemma reference_control_member_2897 : List.In (2897,reference_control_expr_2897) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 69%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2897_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2897 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2897 reference_control_expr_2897 reference_control_3_positions reference_control_3_safety reference_control_member_2897) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2897 reference_control_expr_2897 inputs path old current result Position Safe Nonreg (reference_control_ready_2897 old ) Step).
Qed.
Theorem reference_control_node_2897_congruent inputs path left right next_left next_right :
 VM.find 2552 left = VM.find 2552 right ->
 VM.find 2812 left = VM.find 2812 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2897 next_left = VM.find 2897 next_right.
Proof.
 intros  E2552 E2812 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2897 reference_control_expr_2897 reference_control_3_positions reference_control_3_safety reference_control_member_2897) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2897 reference_control_expr_2897 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2897 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2897 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2552.
 rewrite E2812.
 reflexivity.
Qed.
Lemma reference_control_ready_2898 old :
 reference_control_ready old reference_control_expr_2898.
Proof.
 unfold reference_control_expr_2898.
apply rc_unary.
Qed.
Lemma reference_control_member_2898 : List.In (2898,reference_control_expr_2898) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 70%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2898_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2898 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2898 reference_control_expr_2898 reference_control_3_positions reference_control_3_safety reference_control_member_2898) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2898 reference_control_expr_2898 inputs path old current result Position Safe Nonreg (reference_control_ready_2898 old ) Step).
Qed.
Theorem reference_control_node_2898_congruent inputs path left right next_left next_right :
 VM.find 2897 left = VM.find 2897 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2898 next_left = VM.find 2898 next_right.
Proof.
 intros  E2897 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2898 reference_control_expr_2898 reference_control_3_positions reference_control_3_safety reference_control_member_2898) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2898 reference_control_expr_2898 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2898 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2898 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2897.
 reflexivity.
Qed.
Lemma reference_control_ready_2899 old :
 reference_control_ready old reference_control_expr_2899.
Proof.
 unfold reference_control_expr_2899.
apply rc_unary.
Qed.
Lemma reference_control_member_2899 : List.In (2899,reference_control_expr_2899) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 71%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2899_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2899 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2899 reference_control_expr_2899 reference_control_3_positions reference_control_3_safety reference_control_member_2899) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2899 reference_control_expr_2899 inputs path old current result Position Safe Nonreg (reference_control_ready_2899 old ) Step).
Qed.
Theorem reference_control_node_2899_congruent inputs path left right next_left next_right :
 VM.find 2898 left = VM.find 2898 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2899 next_left = VM.find 2899 next_right.
Proof.
 intros  E2898 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2899 reference_control_expr_2899 reference_control_3_positions reference_control_3_safety reference_control_member_2899) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2899 reference_control_expr_2899 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2899 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2899 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2898.
 reflexivity.
Qed.
Lemma reference_control_ready_2900 old :
 reference_control_ready old reference_control_expr_2900.
Proof.
 unfold reference_control_expr_2900.
apply rc_binary.
Qed.
Lemma reference_control_member_2900 : List.In (2900,reference_control_expr_2900) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 72%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2900_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2900 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2900 reference_control_expr_2900 reference_control_3_positions reference_control_3_safety reference_control_member_2900) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2900 reference_control_expr_2900 inputs path old current result Position Safe Nonreg (reference_control_ready_2900 old ) Step).
Qed.
Theorem reference_control_node_2900_congruent inputs path left right next_left next_right :
 VM.find 2899 left = VM.find 2899 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2900 next_left = VM.find 2900 next_right.
Proof.
 intros  E2899 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2900 reference_control_expr_2900 reference_control_3_positions reference_control_3_safety reference_control_member_2900) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2900 reference_control_expr_2900 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2900 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2900 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2899.
 reflexivity.
Qed.
Lemma reference_control_ready_2901 old :
 reference_control_ready old reference_control_expr_2901.
Proof.
 unfold reference_control_expr_2901.
apply rc_binary.
Qed.
Lemma reference_control_member_2901 : List.In (2901,reference_control_expr_2901) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 73%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2901_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2901 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2901 reference_control_expr_2901 reference_control_3_positions reference_control_3_safety reference_control_member_2901) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2901 reference_control_expr_2901 inputs path old current result Position Safe Nonreg (reference_control_ready_2901 old ) Step).
Qed.
Theorem reference_control_node_2901_congruent inputs path left right next_left next_right :
 VM.find 2895 left = VM.find 2895 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2901 next_left = VM.find 2901 next_right.
Proof.
 intros  E2895 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2901 reference_control_expr_2901 reference_control_3_positions reference_control_3_safety reference_control_member_2901) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2901 reference_control_expr_2901 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2901 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2901 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2895.
 reflexivity.
Qed.
Lemma reference_control_ready_2902 old :
 reference_control_ready old reference_control_expr_2902.
Proof.
 unfold reference_control_expr_2902.
apply rc_unary.
Qed.
Lemma reference_control_member_2902 : List.In (2902,reference_control_expr_2902) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 74%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2902_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2902 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2902 reference_control_expr_2902 reference_control_3_positions reference_control_3_safety reference_control_member_2902) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2902 reference_control_expr_2902 inputs path old current result Position Safe Nonreg (reference_control_ready_2902 old ) Step).
Qed.
Theorem reference_control_node_2902_congruent inputs path left right next_left next_right :
 VM.find 2898 left = VM.find 2898 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2902 next_left = VM.find 2902 next_right.
Proof.
 intros  E2898 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2902 reference_control_expr_2902 reference_control_3_positions reference_control_3_safety reference_control_member_2902) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2902 reference_control_expr_2902 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2902 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2902 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2898.
 reflexivity.
Qed.
Lemma reference_control_ready_2903 old :
 reference_control_ready old reference_control_expr_2903.
Proof.
 unfold reference_control_expr_2903.
apply rc_binary.
Qed.
Lemma reference_control_member_2903 : List.In (2903,reference_control_expr_2903) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 75%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2903_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2903 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2903 reference_control_expr_2903 reference_control_3_positions reference_control_3_safety reference_control_member_2903) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2903 reference_control_expr_2903 inputs path old current result Position Safe Nonreg (reference_control_ready_2903 old ) Step).
Qed.
Theorem reference_control_node_2903_congruent inputs path left right next_left next_right :
 VM.find 2902 left = VM.find 2902 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2903 next_left = VM.find 2903 next_right.
Proof.
 intros  E2902 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2903 reference_control_expr_2903 reference_control_3_positions reference_control_3_safety reference_control_member_2903) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2903 reference_control_expr_2903 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2903 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2903 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2902.
 reflexivity.
Qed.
Lemma reference_control_ready_2904 old :
 reference_control_ready old reference_control_expr_2904.
Proof.
 unfold reference_control_expr_2904.
apply rc_binary.
Qed.
Lemma reference_control_member_2904 : List.In (2904,reference_control_expr_2904) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 76%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2904_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2904 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2904 reference_control_expr_2904 reference_control_3_positions reference_control_3_safety reference_control_member_2904) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2904 reference_control_expr_2904 inputs path old current result Position Safe Nonreg (reference_control_ready_2904 old ) Step).
Qed.
Theorem reference_control_node_2904_congruent inputs path left right next_left next_right :
 VM.find 2895 left = VM.find 2895 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2904 next_left = VM.find 2904 next_right.
Proof.
 intros  E2895 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2904 reference_control_expr_2904 reference_control_3_positions reference_control_3_safety reference_control_member_2904) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2904 reference_control_expr_2904 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2904 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2904 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2895.
 reflexivity.
Qed.
Lemma reference_control_ready_2905 old :
 reference_control_ready old reference_control_expr_2905.
Proof.
 unfold reference_control_expr_2905.
apply rc_unary.
Qed.
Lemma reference_control_member_2905 : List.In (2905,reference_control_expr_2905) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 77%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2905_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2905 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2905 reference_control_expr_2905 reference_control_3_positions reference_control_3_safety reference_control_member_2905) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2905 reference_control_expr_2905 inputs path old current result Position Safe Nonreg (reference_control_ready_2905 old ) Step).
Qed.
Theorem reference_control_node_2905_congruent inputs path left right next_left next_right :
 VM.find 2898 left = VM.find 2898 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2905 next_left = VM.find 2905 next_right.
Proof.
 intros  E2898 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2905 reference_control_expr_2905 reference_control_3_positions reference_control_3_safety reference_control_member_2905) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2905 reference_control_expr_2905 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2905 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2905 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2898.
 reflexivity.
Qed.
Lemma reference_control_ready_2906 old :
 reference_control_ready old reference_control_expr_2906.
Proof.
 unfold reference_control_expr_2906.
apply rc_binary.
Qed.
Lemma reference_control_member_2906 : List.In (2906,reference_control_expr_2906) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 78%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2906_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2906 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2906 reference_control_expr_2906 reference_control_3_positions reference_control_3_safety reference_control_member_2906) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2906 reference_control_expr_2906 inputs path old current result Position Safe Nonreg (reference_control_ready_2906 old ) Step).
Qed.
Theorem reference_control_node_2906_congruent inputs path left right next_left next_right :
 VM.find 2905 left = VM.find 2905 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2906 next_left = VM.find 2906 next_right.
Proof.
 intros  E2905 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2906 reference_control_expr_2906 reference_control_3_positions reference_control_3_safety reference_control_member_2906) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2906 reference_control_expr_2906 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2906 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2906 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2905.
 reflexivity.
Qed.
Lemma reference_control_ready_2907 old :
 (exists value ground, VM.find 2906 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2907.
Proof.
 intros H2906.
 destruct H2906 as [v2906 [G2906 [V2906 T2906]]].
 unfold reference_control_expr_2907.
apply rc_mux.
{ eapply rc_ref; [exact V2906|exists G2906; exact T2906].
}
{ apply rc_const.
}
Qed.
Lemma reference_control_member_2907 : List.In (2907,reference_control_expr_2907) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 79%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2907_ground inputs path old current result :
 (exists value ground, VM.find 2906 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2907 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2906 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2907 reference_control_expr_2907 reference_control_3_positions reference_control_3_safety reference_control_member_2907) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2907 reference_control_expr_2907 inputs path old current result Position Safe Nonreg (reference_control_ready_2907 old H2906) Step).
Qed.
Theorem reference_control_node_2907_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2906 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2904 left = VM.find 2904 right ->
 VM.find 2906 left = VM.find 2906 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2907 next_left = VM.find 2907 next_right.
Proof.
 intros H2906 E2904 E2906 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2907 reference_control_expr_2907 reference_control_3_positions reference_control_3_safety reference_control_member_2907) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2907 reference_control_expr_2907 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2907 left H2906)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2907 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2904.
 rewrite E2906.
 reflexivity.
Qed.
Lemma reference_control_ready_2908 old :
 (exists value ground, VM.find 2903 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2907 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2908.
Proof.
 intros H2903 H2907.
 destruct H2903 as [v2903 [G2903 [V2903 T2903]]].
 destruct H2907 as [v2907 [G2907 [V2907 T2907]]].
 unfold reference_control_expr_2908.
apply rc_mux.
{ eapply rc_ref; [exact V2903|exists G2903; exact T2903].
}
{ eapply rc_ref; [exact V2907|exists G2907; exact T2907].
}
Qed.
Lemma reference_control_member_2908 : List.In (2908,reference_control_expr_2908) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 80%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2908_ground inputs path old current result :
 (exists value ground, VM.find 2903 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2907 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2908 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2903 H2907 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2908 reference_control_expr_2908 reference_control_3_positions reference_control_3_safety reference_control_member_2908) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2908 reference_control_expr_2908 inputs path old current result Position Safe Nonreg (reference_control_ready_2908 old H2903 H2907) Step).
Qed.
Theorem reference_control_node_2908_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2903 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2907 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2901 left = VM.find 2901 right ->
 VM.find 2903 left = VM.find 2903 right ->
 VM.find 2907 left = VM.find 2907 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2908 next_left = VM.find 2908 next_right.
Proof.
 intros H2903 H2907 E2901 E2903 E2907 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2908 reference_control_expr_2908 reference_control_3_positions reference_control_3_safety reference_control_member_2908) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2908 reference_control_expr_2908 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2908 left H2903 H2907)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2908 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2901.
 rewrite E2903.
 rewrite E2907.
 reflexivity.
Qed.
Lemma reference_control_ready_2909 old :
 (exists value ground, VM.find 2900 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2908 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2909.
Proof.
 intros H2900 H2908.
 destruct H2900 as [v2900 [G2900 [V2900 T2900]]].
 destruct H2908 as [v2908 [G2908 [V2908 T2908]]].
 unfold reference_control_expr_2909.
apply rc_mux.
{ eapply rc_ref; [exact V2900|exists G2900; exact T2900].
}
{ eapply rc_ref; [exact V2908|exists G2908; exact T2908].
}
Qed.
Lemma reference_control_member_2909 : List.In (2909,reference_control_expr_2909) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 81%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2909_ground inputs path old current result :
 (exists value ground, VM.find 2900 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2908 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2909 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2900 H2908 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2909 reference_control_expr_2909 reference_control_3_positions reference_control_3_safety reference_control_member_2909) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2909 reference_control_expr_2909 inputs path old current result Position Safe Nonreg (reference_control_ready_2909 old H2900 H2908) Step).
Qed.
Theorem reference_control_node_2909_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2900 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2908 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2896 left = VM.find 2896 right ->
 VM.find 2900 left = VM.find 2900 right ->
 VM.find 2908 left = VM.find 2908 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2909 next_left = VM.find 2909 next_right.
Proof.
 intros H2900 H2908 E2896 E2900 E2908 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2909 reference_control_expr_2909 reference_control_3_positions reference_control_3_safety reference_control_member_2909) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2909 reference_control_expr_2909 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2909 left H2900 H2908)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2909 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2896.
 rewrite E2900.
 rewrite E2908.
 reflexivity.
Qed.
Lemma reference_control_ready_2910 old :
 (exists value ground, VM.find 2209 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2910.
Proof.
 intros H2209.
 destruct H2209 as [v2209 [G2209 [V2209 T2209]]].
 unfold reference_control_expr_2910.
eapply rc_ref; [exact V2209|exists G2209; exact T2209].
Qed.
Lemma reference_control_member_2910 : List.In (2910,reference_control_expr_2910) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 82%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2910_ground inputs path old current result :
 (exists value ground, VM.find 2209 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2910 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2209 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2910 reference_control_expr_2910 reference_control_3_positions reference_control_3_safety reference_control_member_2910) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2910 reference_control_expr_2910 inputs path old current result Position Safe Nonreg (reference_control_ready_2910 old H2209) Step).
Qed.
Theorem reference_control_node_2910_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2209 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2209 left = VM.find 2209 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2910 next_left = VM.find 2910 next_right.
Proof.
 intros H2209 E2209 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2910 reference_control_expr_2910 reference_control_3_positions reference_control_3_safety reference_control_member_2910) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2910 reference_control_expr_2910 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2910 left H2209)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2910 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2209.
 reflexivity.
Qed.
Lemma reference_control_ready_2911 old :
 (exists value ground, VM.find 2804 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2911.
Proof.
 intros H2804.
 destruct H2804 as [v2804 [G2804 [V2804 T2804]]].
 unfold reference_control_expr_2911.
eapply rc_ref; [exact V2804|exists G2804; exact T2804].
Qed.
Lemma reference_control_member_2911 : List.In (2911,reference_control_expr_2911) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 83%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2911_ground inputs path old current result :
 (exists value ground, VM.find 2804 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2911 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2804 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2911 reference_control_expr_2911 reference_control_3_positions reference_control_3_safety reference_control_member_2911) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2911 reference_control_expr_2911 inputs path old current result Position Safe Nonreg (reference_control_ready_2911 old H2804) Step).
Qed.
Theorem reference_control_node_2911_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2804 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2804 left = VM.find 2804 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2911 next_left = VM.find 2911 next_right.
Proof.
 intros H2804 E2804 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2911 reference_control_expr_2911 reference_control_3_positions reference_control_3_safety reference_control_member_2911) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2911 reference_control_expr_2911 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2911 left H2804)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2911 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2804.
 reflexivity.
Qed.
Lemma reference_control_ready_2912 old :
 reference_control_ready old reference_control_expr_2912.
Proof.
 unfold reference_control_expr_2912.
apply rc_binary.
Qed.
Lemma reference_control_member_2912 : List.In (2912,reference_control_expr_2912) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 84%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2912_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2912 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2912 reference_control_expr_2912 reference_control_3_positions reference_control_3_safety reference_control_member_2912) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2912 reference_control_expr_2912 inputs path old current result Position Safe Nonreg (reference_control_ready_2912 old ) Step).
Qed.
Theorem reference_control_node_2912_congruent inputs path left right next_left next_right :
 VM.find 2910 left = VM.find 2910 right ->
 VM.find 2911 left = VM.find 2911 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2912 next_left = VM.find 2912 next_right.
Proof.
 intros  E2910 E2911 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2912 reference_control_expr_2912 reference_control_3_positions reference_control_3_safety reference_control_member_2912) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2912 reference_control_expr_2912 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2912 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2912 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2910.
 rewrite E2911.
 reflexivity.
Qed.
Lemma reference_control_ready_2913 old :
 reference_control_ready old reference_control_expr_2913.
Proof.
 unfold reference_control_expr_2913.
apply rc_unary.
Qed.
Lemma reference_control_member_2913 : List.In (2913,reference_control_expr_2913) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 85%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2913_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2913 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2913 reference_control_expr_2913 reference_control_3_positions reference_control_3_safety reference_control_member_2913) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2913 reference_control_expr_2913 inputs path old current result Position Safe Nonreg (reference_control_ready_2913 old ) Step).
Qed.
Theorem reference_control_node_2913_congruent inputs path left right next_left next_right :
 VM.find 2807 left = VM.find 2807 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2913 next_left = VM.find 2913 next_right.
Proof.
 intros  E2807 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2913 reference_control_expr_2913 reference_control_3_positions reference_control_3_safety reference_control_member_2913) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2913 reference_control_expr_2913 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2913 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2913 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2807.
 reflexivity.
Qed.
Lemma reference_control_ready_2914 old :
 reference_control_ready old reference_control_expr_2914.
Proof.
 unfold reference_control_expr_2914.
apply rc_binary.
Qed.
Lemma reference_control_member_2914 : List.In (2914,reference_control_expr_2914) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 86%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2914_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2914 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2914 reference_control_expr_2914 reference_control_3_positions reference_control_3_safety reference_control_member_2914) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2914 reference_control_expr_2914 inputs path old current result Position Safe Nonreg (reference_control_ready_2914 old ) Step).
Qed.
Theorem reference_control_node_2914_congruent inputs path left right next_left next_right :
 VM.find 2913 left = VM.find 2913 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2914 next_left = VM.find 2914 next_right.
Proof.
 intros  E2913 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2914 reference_control_expr_2914 reference_control_3_positions reference_control_3_safety reference_control_member_2914) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2914 reference_control_expr_2914 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2914 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2914 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2913.
 reflexivity.
Qed.
Lemma reference_control_ready_2915 old :
 reference_control_ready old reference_control_expr_2915.
Proof.
 unfold reference_control_expr_2915.
apply rc_mux.
{ apply rc_const.
}
{ apply rc_const.
}
Qed.
Lemma reference_control_member_2915 : List.In (2915,reference_control_expr_2915) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 87%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2915_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2915 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2915 reference_control_expr_2915 reference_control_3_positions reference_control_3_safety reference_control_member_2915) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2915 reference_control_expr_2915 inputs path old current result Position Safe Nonreg (reference_control_ready_2915 old ) Step).
Qed.
Theorem reference_control_node_2915_congruent inputs path left right next_left next_right :
 VM.find 2914 left = VM.find 2914 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2915 next_left = VM.find 2915 next_right.
Proof.
 intros  E2914 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2915 reference_control_expr_2915 reference_control_3_positions reference_control_3_safety reference_control_member_2915) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2915 reference_control_expr_2915 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2915 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2915 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2914.
 reflexivity.
Qed.
Lemma reference_control_ready_2916 old :
 reference_control_ready old reference_control_expr_2916.
Proof.
 unfold reference_control_expr_2916.
apply rc_binary.
Qed.
Lemma reference_control_member_2916 : List.In (2916,reference_control_expr_2916) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 88%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2916_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2916 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2916 reference_control_expr_2916 reference_control_3_positions reference_control_3_safety reference_control_member_2916) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2916 reference_control_expr_2916 inputs path old current result Position Safe Nonreg (reference_control_ready_2916 old ) Step).
Qed.
Theorem reference_control_node_2916_congruent inputs path left right next_left next_right :
 VM.find 2915 left = VM.find 2915 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2916 next_left = VM.find 2916 next_right.
Proof.
 intros  E2915 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2916 reference_control_expr_2916 reference_control_3_positions reference_control_3_safety reference_control_member_2916) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2916 reference_control_expr_2916 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2916 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2916 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2915.
 reflexivity.
Qed.
Lemma reference_control_ready_2917 old :
 reference_control_ready old reference_control_expr_2917.
Proof.
 unfold reference_control_expr_2917.
apply rc_binary.
Qed.
Lemma reference_control_member_2917 : List.In (2917,reference_control_expr_2917) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 89%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2917_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2917 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2917 reference_control_expr_2917 reference_control_3_positions reference_control_3_safety reference_control_member_2917) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2917 reference_control_expr_2917 inputs path old current result Position Safe Nonreg (reference_control_ready_2917 old ) Step).
Qed.
Theorem reference_control_node_2917_congruent inputs path left right next_left next_right :
 VM.find 2552 left = VM.find 2552 right ->
 VM.find 2812 left = VM.find 2812 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2917 next_left = VM.find 2917 next_right.
Proof.
 intros  E2552 E2812 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2917 reference_control_expr_2917 reference_control_3_positions reference_control_3_safety reference_control_member_2917) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2917 reference_control_expr_2917 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2917 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2917 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2552.
 rewrite E2812.
 reflexivity.
Qed.
Lemma reference_control_ready_2918 old :
 reference_control_ready old reference_control_expr_2918.
Proof.
 unfold reference_control_expr_2918.
apply rc_unary.
Qed.
Lemma reference_control_member_2918 : List.In (2918,reference_control_expr_2918) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 90%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2918_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2918 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2918 reference_control_expr_2918 reference_control_3_positions reference_control_3_safety reference_control_member_2918) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2918 reference_control_expr_2918 inputs path old current result Position Safe Nonreg (reference_control_ready_2918 old ) Step).
Qed.
Theorem reference_control_node_2918_congruent inputs path left right next_left next_right :
 VM.find 2917 left = VM.find 2917 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2918 next_left = VM.find 2918 next_right.
Proof.
 intros  E2917 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2918 reference_control_expr_2918 reference_control_3_positions reference_control_3_safety reference_control_member_2918) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2918 reference_control_expr_2918 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2918 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2918 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2917.
 reflexivity.
Qed.
Lemma reference_control_ready_2919 old :
 reference_control_ready old reference_control_expr_2919.
Proof.
 unfold reference_control_expr_2919.
apply rc_unary.
Qed.
Lemma reference_control_member_2919 : List.In (2919,reference_control_expr_2919) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 91%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2919_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2919 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2919 reference_control_expr_2919 reference_control_3_positions reference_control_3_safety reference_control_member_2919) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2919 reference_control_expr_2919 inputs path old current result Position Safe Nonreg (reference_control_ready_2919 old ) Step).
Qed.
Theorem reference_control_node_2919_congruent inputs path left right next_left next_right :
 VM.find 2918 left = VM.find 2918 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2919 next_left = VM.find 2919 next_right.
Proof.
 intros  E2918 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2919 reference_control_expr_2919 reference_control_3_positions reference_control_3_safety reference_control_member_2919) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2919 reference_control_expr_2919 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2919 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2919 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2918.
 reflexivity.
Qed.
Lemma reference_control_ready_2920 old :
 reference_control_ready old reference_control_expr_2920.
Proof.
 unfold reference_control_expr_2920.
apply rc_binary.
Qed.
Lemma reference_control_member_2920 : List.In (2920,reference_control_expr_2920) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 92%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2920_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2920 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2920 reference_control_expr_2920 reference_control_3_positions reference_control_3_safety reference_control_member_2920) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2920 reference_control_expr_2920 inputs path old current result Position Safe Nonreg (reference_control_ready_2920 old ) Step).
Qed.
Theorem reference_control_node_2920_congruent inputs path left right next_left next_right :
 VM.find 2919 left = VM.find 2919 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2920 next_left = VM.find 2920 next_right.
Proof.
 intros  E2919 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2920 reference_control_expr_2920 reference_control_3_positions reference_control_3_safety reference_control_member_2920) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2920 reference_control_expr_2920 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2920 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2920 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2919.
 reflexivity.
Qed.
Lemma reference_control_ready_2921 old :
 reference_control_ready old reference_control_expr_2921.
Proof.
 unfold reference_control_expr_2921.
apply rc_binary.
Qed.
Lemma reference_control_member_2921 : List.In (2921,reference_control_expr_2921) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 93%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2921_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2921 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2921 reference_control_expr_2921 reference_control_3_positions reference_control_3_safety reference_control_member_2921) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2921 reference_control_expr_2921 inputs path old current result Position Safe Nonreg (reference_control_ready_2921 old ) Step).
Qed.
Theorem reference_control_node_2921_congruent inputs path left right next_left next_right :
 VM.find 2915 left = VM.find 2915 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2921 next_left = VM.find 2921 next_right.
Proof.
 intros  E2915 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2921 reference_control_expr_2921 reference_control_3_positions reference_control_3_safety reference_control_member_2921) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2921 reference_control_expr_2921 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2921 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2921 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2915.
 reflexivity.
Qed.
Lemma reference_control_ready_2922 old :
 reference_control_ready old reference_control_expr_2922.
Proof.
 unfold reference_control_expr_2922.
apply rc_unary.
Qed.
Lemma reference_control_member_2922 : List.In (2922,reference_control_expr_2922) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 94%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2922_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2922 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2922 reference_control_expr_2922 reference_control_3_positions reference_control_3_safety reference_control_member_2922) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2922 reference_control_expr_2922 inputs path old current result Position Safe Nonreg (reference_control_ready_2922 old ) Step).
Qed.
Theorem reference_control_node_2922_congruent inputs path left right next_left next_right :
 VM.find 2918 left = VM.find 2918 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2922 next_left = VM.find 2922 next_right.
Proof.
 intros  E2918 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2922 reference_control_expr_2922 reference_control_3_positions reference_control_3_safety reference_control_member_2922) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2922 reference_control_expr_2922 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2922 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2922 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2918.
 reflexivity.
Qed.
Lemma reference_control_ready_2923 old :
 reference_control_ready old reference_control_expr_2923.
Proof.
 unfold reference_control_expr_2923.
apply rc_binary.
Qed.
Lemma reference_control_member_2923 : List.In (2923,reference_control_expr_2923) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 95%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2923_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2923 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2923 reference_control_expr_2923 reference_control_3_positions reference_control_3_safety reference_control_member_2923) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2923 reference_control_expr_2923 inputs path old current result Position Safe Nonreg (reference_control_ready_2923 old ) Step).
Qed.
Theorem reference_control_node_2923_congruent inputs path left right next_left next_right :
 VM.find 2922 left = VM.find 2922 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2923 next_left = VM.find 2923 next_right.
Proof.
 intros  E2922 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2923 reference_control_expr_2923 reference_control_3_positions reference_control_3_safety reference_control_member_2923) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2923 reference_control_expr_2923 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2923 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2923 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2922.
 reflexivity.
Qed.
Lemma reference_control_ready_2924 old :
 reference_control_ready old reference_control_expr_2924.
Proof.
 unfold reference_control_expr_2924.
apply rc_binary.
Qed.
Lemma reference_control_member_2924 : List.In (2924,reference_control_expr_2924) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 96%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2924_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2924 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2924 reference_control_expr_2924 reference_control_3_positions reference_control_3_safety reference_control_member_2924) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2924 reference_control_expr_2924 inputs path old current result Position Safe Nonreg (reference_control_ready_2924 old ) Step).
Qed.
Theorem reference_control_node_2924_congruent inputs path left right next_left next_right :
 VM.find 2915 left = VM.find 2915 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2924 next_left = VM.find 2924 next_right.
Proof.
 intros  E2915 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2924 reference_control_expr_2924 reference_control_3_positions reference_control_3_safety reference_control_member_2924) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2924 reference_control_expr_2924 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2924 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2924 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2915.
 reflexivity.
Qed.
Lemma reference_control_ready_2925 old :
 reference_control_ready old reference_control_expr_2925.
Proof.
 unfold reference_control_expr_2925.
apply rc_unary.
Qed.
Lemma reference_control_member_2925 : List.In (2925,reference_control_expr_2925) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 97%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2925_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2925 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2925 reference_control_expr_2925 reference_control_3_positions reference_control_3_safety reference_control_member_2925) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2925 reference_control_expr_2925 inputs path old current result Position Safe Nonreg (reference_control_ready_2925 old ) Step).
Qed.
Theorem reference_control_node_2925_congruent inputs path left right next_left next_right :
 VM.find 2918 left = VM.find 2918 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2925 next_left = VM.find 2925 next_right.
Proof.
 intros  E2918 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2925 reference_control_expr_2925 reference_control_3_positions reference_control_3_safety reference_control_member_2925) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2925 reference_control_expr_2925 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2925 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2925 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2918.
 reflexivity.
Qed.
Lemma reference_control_ready_2926 old :
 reference_control_ready old reference_control_expr_2926.
Proof.
 unfold reference_control_expr_2926.
apply rc_binary.
Qed.
Lemma reference_control_member_2926 : List.In (2926,reference_control_expr_2926) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 98%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2926_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2926 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2926 reference_control_expr_2926 reference_control_3_positions reference_control_3_safety reference_control_member_2926) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2926 reference_control_expr_2926 inputs path old current result Position Safe Nonreg (reference_control_ready_2926 old ) Step).
Qed.
Theorem reference_control_node_2926_congruent inputs path left right next_left next_right :
 VM.find 2925 left = VM.find 2925 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2926 next_left = VM.find 2926 next_right.
Proof.
 intros  E2925 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2926 reference_control_expr_2926 reference_control_3_positions reference_control_3_safety reference_control_member_2926) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2926 reference_control_expr_2926 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2926 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2926 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2925.
 reflexivity.
Qed.
Lemma reference_control_ready_2927 old :
 (exists value ground, VM.find 2926 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2927.
Proof.
 intros H2926.
 destruct H2926 as [v2926 [G2926 [V2926 T2926]]].
 unfold reference_control_expr_2927.
apply rc_mux.
{ eapply rc_ref; [exact V2926|exists G2926; exact T2926].
}
{ apply rc_const.
}
Qed.
Lemma reference_control_member_2927 : List.In (2927,reference_control_expr_2927) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 99%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2927_ground inputs path old current result :
 (exists value ground, VM.find 2926 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2927 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2926 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2927 reference_control_expr_2927 reference_control_3_positions reference_control_3_safety reference_control_member_2927) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2927 reference_control_expr_2927 inputs path old current result Position Safe Nonreg (reference_control_ready_2927 old H2926) Step).
Qed.
Theorem reference_control_node_2927_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2926 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2924 left = VM.find 2924 right ->
 VM.find 2926 left = VM.find 2926 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2927 next_left = VM.find 2927 next_right.
Proof.
 intros H2926 E2924 E2926 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2927 reference_control_expr_2927 reference_control_3_positions reference_control_3_safety reference_control_member_2927) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2927 reference_control_expr_2927 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2927 left H2926)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2927 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2924.
 rewrite E2926.
 reflexivity.
Qed.
Lemma reference_control_ready_2928 old :
 (exists value ground, VM.find 2923 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2927 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2928.
Proof.
 intros H2923 H2927.
 destruct H2923 as [v2923 [G2923 [V2923 T2923]]].
 destruct H2927 as [v2927 [G2927 [V2927 T2927]]].
 unfold reference_control_expr_2928.
apply rc_mux.
{ eapply rc_ref; [exact V2923|exists G2923; exact T2923].
}
{ eapply rc_ref; [exact V2927|exists G2927; exact T2927].
}
Qed.
Lemma reference_control_member_2928 : List.In (2928,reference_control_expr_2928) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 100%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2928_ground inputs path old current result :
 (exists value ground, VM.find 2923 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2927 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2928 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2923 H2927 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2928 reference_control_expr_2928 reference_control_3_positions reference_control_3_safety reference_control_member_2928) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2928 reference_control_expr_2928 inputs path old current result Position Safe Nonreg (reference_control_ready_2928 old H2923 H2927) Step).
Qed.
Theorem reference_control_node_2928_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2923 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2927 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2921 left = VM.find 2921 right ->
 VM.find 2923 left = VM.find 2923 right ->
 VM.find 2927 left = VM.find 2927 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2928 next_left = VM.find 2928 next_right.
Proof.
 intros H2923 H2927 E2921 E2923 E2927 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2928 reference_control_expr_2928 reference_control_3_positions reference_control_3_safety reference_control_member_2928) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2928 reference_control_expr_2928 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2928 left H2923 H2927)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2928 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2921.
 rewrite E2923.
 rewrite E2927.
 reflexivity.
Qed.
Lemma reference_control_ready_2929 old :
 (exists value ground, VM.find 2920 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2928 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2929.
Proof.
 intros H2920 H2928.
 destruct H2920 as [v2920 [G2920 [V2920 T2920]]].
 destruct H2928 as [v2928 [G2928 [V2928 T2928]]].
 unfold reference_control_expr_2929.
apply rc_mux.
{ eapply rc_ref; [exact V2920|exists G2920; exact T2920].
}
{ eapply rc_ref; [exact V2928|exists G2928; exact T2928].
}
Qed.
Lemma reference_control_member_2929 : List.In (2929,reference_control_expr_2929) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 101%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2929_ground inputs path old current result :
 (exists value ground, VM.find 2920 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2928 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2929 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2920 H2928 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2929 reference_control_expr_2929 reference_control_3_positions reference_control_3_safety reference_control_member_2929) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2929 reference_control_expr_2929 inputs path old current result Position Safe Nonreg (reference_control_ready_2929 old H2920 H2928) Step).
Qed.
Theorem reference_control_node_2929_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2920 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2928 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2916 left = VM.find 2916 right ->
 VM.find 2920 left = VM.find 2920 right ->
 VM.find 2928 left = VM.find 2928 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2929 next_left = VM.find 2929 next_right.
Proof.
 intros H2920 H2928 E2916 E2920 E2928 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2929 reference_control_expr_2929 reference_control_3_positions reference_control_3_safety reference_control_member_2929) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2929 reference_control_expr_2929 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2929 left H2920 H2928)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2929 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2916.
 rewrite E2920.
 rewrite E2928.
 reflexivity.
Qed.
Lemma reference_control_ready_2930 old :
 reference_control_ready old reference_control_expr_2930.
Proof.
 unfold reference_control_expr_2930.
apply rc_unary.
Qed.
Lemma reference_control_member_2930 : List.In (2930,reference_control_expr_2930) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 102%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2930_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2930 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2930 reference_control_expr_2930 reference_control_3_positions reference_control_3_safety reference_control_member_2930) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2930 reference_control_expr_2930 inputs path old current result Position Safe Nonreg (reference_control_ready_2930 old ) Step).
Qed.
Theorem reference_control_node_2930_congruent inputs path left right next_left next_right :
 VM.find 2807 left = VM.find 2807 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2930 next_left = VM.find 2930 next_right.
Proof.
 intros  E2807 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2930 reference_control_expr_2930 reference_control_3_positions reference_control_3_safety reference_control_member_2930) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2930 reference_control_expr_2930 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2930 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2930 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2807.
 reflexivity.
Qed.
Lemma reference_control_ready_2931 old :
 reference_control_ready old reference_control_expr_2931.
Proof.
 unfold reference_control_expr_2931.
apply rc_binary.
Qed.
Lemma reference_control_member_2931 : List.In (2931,reference_control_expr_2931) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 103%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2931_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2931 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2931 reference_control_expr_2931 reference_control_3_positions reference_control_3_safety reference_control_member_2931) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2931 reference_control_expr_2931 inputs path old current result Position Safe Nonreg (reference_control_ready_2931 old ) Step).
Qed.
Theorem reference_control_node_2931_congruent inputs path left right next_left next_right :
 VM.find 2930 left = VM.find 2930 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2931 next_left = VM.find 2931 next_right.
Proof.
 intros  E2930 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2931 reference_control_expr_2931 reference_control_3_positions reference_control_3_safety reference_control_member_2931) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2931 reference_control_expr_2931 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2931 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2931 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2930.
 reflexivity.
Qed.
Lemma reference_control_ready_2932 old :
 reference_control_ready old reference_control_expr_2932.
Proof.
 unfold reference_control_expr_2932.
apply rc_mux.
{ apply rc_const.
}
{ apply rc_const.
}
Qed.
Lemma reference_control_member_2932 : List.In (2932,reference_control_expr_2932) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 104%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2932_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2932 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2932 reference_control_expr_2932 reference_control_3_positions reference_control_3_safety reference_control_member_2932) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2932 reference_control_expr_2932 inputs path old current result Position Safe Nonreg (reference_control_ready_2932 old ) Step).
Qed.
Theorem reference_control_node_2932_congruent inputs path left right next_left next_right :
 VM.find 2931 left = VM.find 2931 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2932 next_left = VM.find 2932 next_right.
Proof.
 intros  E2931 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2932 reference_control_expr_2932 reference_control_3_positions reference_control_3_safety reference_control_member_2932) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2932 reference_control_expr_2932 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2932 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2932 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2931.
 reflexivity.
Qed.
Lemma reference_control_ready_2933 old :
 reference_control_ready old reference_control_expr_2933.
Proof.
 unfold reference_control_expr_2933.
apply rc_binary.
Qed.
Lemma reference_control_member_2933 : List.In (2933,reference_control_expr_2933) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 105%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2933_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2933 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2933 reference_control_expr_2933 reference_control_3_positions reference_control_3_safety reference_control_member_2933) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2933 reference_control_expr_2933 inputs path old current result Position Safe Nonreg (reference_control_ready_2933 old ) Step).
Qed.
Theorem reference_control_node_2933_congruent inputs path left right next_left next_right :
 VM.find 2932 left = VM.find 2932 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2933 next_left = VM.find 2933 next_right.
Proof.
 intros  E2932 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2933 reference_control_expr_2933 reference_control_3_positions reference_control_3_safety reference_control_member_2933) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2933 reference_control_expr_2933 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2933 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2933 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2932.
 reflexivity.
Qed.
Lemma reference_control_ready_2934 old :
 (exists value ground, VM.find 2209 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2934.
Proof.
 intros H2209.
 destruct H2209 as [v2209 [G2209 [V2209 T2209]]].
 unfold reference_control_expr_2934.
eapply rc_ref; [exact V2209|exists G2209; exact T2209].
Qed.
Lemma reference_control_member_2934 : List.In (2934,reference_control_expr_2934) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 106%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2934_ground inputs path old current result :
 (exists value ground, VM.find 2209 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2934 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2209 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2934 reference_control_expr_2934 reference_control_3_positions reference_control_3_safety reference_control_member_2934) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2934 reference_control_expr_2934 inputs path old current result Position Safe Nonreg (reference_control_ready_2934 old H2209) Step).
Qed.
Theorem reference_control_node_2934_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2209 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2209 left = VM.find 2209 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2934 next_left = VM.find 2934 next_right.
Proof.
 intros H2209 E2209 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2934 reference_control_expr_2934 reference_control_3_positions reference_control_3_safety reference_control_member_2934) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2934 reference_control_expr_2934 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2934 left H2209)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2934 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2209.
 reflexivity.
Qed.
Lemma reference_control_ready_2935 old :
 reference_control_ready old reference_control_expr_2935.
Proof.
 unfold reference_control_expr_2935.
apply rc_binary.
Qed.
Lemma reference_control_member_2935 : List.In (2935,reference_control_expr_2935) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 107%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2935_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2935 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2935 reference_control_expr_2935 reference_control_3_positions reference_control_3_safety reference_control_member_2935) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2935 reference_control_expr_2935 inputs path old current result Position Safe Nonreg (reference_control_ready_2935 old ) Step).
Qed.
Theorem reference_control_node_2935_congruent inputs path left right next_left next_right :
 VM.find 2552 left = VM.find 2552 right ->
 VM.find 2934 left = VM.find 2934 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2935 next_left = VM.find 2935 next_right.
Proof.
 intros  E2552 E2934 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2935 reference_control_expr_2935 reference_control_3_positions reference_control_3_safety reference_control_member_2935) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2935 reference_control_expr_2935 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2935 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2935 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2552.
 rewrite E2934.
 reflexivity.
Qed.
Lemma reference_control_ready_2936 old :
 reference_control_ready old reference_control_expr_2936.
Proof.
 unfold reference_control_expr_2936.
apply rc_unary.
Qed.
Lemma reference_control_member_2936 : List.In (2936,reference_control_expr_2936) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 108%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2936_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2936 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2936 reference_control_expr_2936 reference_control_3_positions reference_control_3_safety reference_control_member_2936) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2936 reference_control_expr_2936 inputs path old current result Position Safe Nonreg (reference_control_ready_2936 old ) Step).
Qed.
Theorem reference_control_node_2936_congruent inputs path left right next_left next_right :
 VM.find 2935 left = VM.find 2935 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2936 next_left = VM.find 2936 next_right.
Proof.
 intros  E2935 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2936 reference_control_expr_2936 reference_control_3_positions reference_control_3_safety reference_control_member_2936) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2936 reference_control_expr_2936 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2936 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2936 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2935.
 reflexivity.
Qed.
Lemma reference_control_ready_2937 old :
 reference_control_ready old reference_control_expr_2937.
Proof.
 unfold reference_control_expr_2937.
apply rc_unary.
Qed.
Lemma reference_control_member_2937 : List.In (2937,reference_control_expr_2937) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 109%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2937_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2937 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2937 reference_control_expr_2937 reference_control_3_positions reference_control_3_safety reference_control_member_2937) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2937 reference_control_expr_2937 inputs path old current result Position Safe Nonreg (reference_control_ready_2937 old ) Step).
Qed.
Theorem reference_control_node_2937_congruent inputs path left right next_left next_right :
 VM.find 2936 left = VM.find 2936 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2937 next_left = VM.find 2937 next_right.
Proof.
 intros  E2936 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2937 reference_control_expr_2937 reference_control_3_positions reference_control_3_safety reference_control_member_2937) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2937 reference_control_expr_2937 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2937 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2937 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2936.
 reflexivity.
Qed.
Lemma reference_control_ready_2938 old :
 reference_control_ready old reference_control_expr_2938.
Proof.
 unfold reference_control_expr_2938.
apply rc_binary.
Qed.
Lemma reference_control_member_2938 : List.In (2938,reference_control_expr_2938) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 110%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2938_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2938 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2938 reference_control_expr_2938 reference_control_3_positions reference_control_3_safety reference_control_member_2938) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2938 reference_control_expr_2938 inputs path old current result Position Safe Nonreg (reference_control_ready_2938 old ) Step).
Qed.
Theorem reference_control_node_2938_congruent inputs path left right next_left next_right :
 VM.find 2937 left = VM.find 2937 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2938 next_left = VM.find 2938 next_right.
Proof.
 intros  E2937 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2938 reference_control_expr_2938 reference_control_3_positions reference_control_3_safety reference_control_member_2938) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2938 reference_control_expr_2938 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2938 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2938 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2937.
 reflexivity.
Qed.
Lemma reference_control_ready_2939 old :
 reference_control_ready old reference_control_expr_2939.
Proof.
 unfold reference_control_expr_2939.
apply rc_unary.
Qed.
Lemma reference_control_member_2939 : List.In (2939,reference_control_expr_2939) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 111%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2939_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2939 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2939 reference_control_expr_2939 reference_control_3_positions reference_control_3_safety reference_control_member_2939) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2939 reference_control_expr_2939 inputs path old current result Position Safe Nonreg (reference_control_ready_2939 old ) Step).
Qed.
Theorem reference_control_node_2939_congruent inputs path left right next_left next_right :
 VM.find 2938 left = VM.find 2938 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2939 next_left = VM.find 2939 next_right.
Proof.
 intros  E2938 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2939 reference_control_expr_2939 reference_control_3_positions reference_control_3_safety reference_control_member_2939) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2939 reference_control_expr_2939 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2939 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2939 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2938.
 reflexivity.
Qed.
Lemma reference_control_ready_2940 old :
 reference_control_ready old reference_control_expr_2940.
Proof.
 unfold reference_control_expr_2940.
apply rc_binary.
Qed.
Lemma reference_control_member_2940 : List.In (2940,reference_control_expr_2940) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 112%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2940_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2940 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2940 reference_control_expr_2940 reference_control_3_positions reference_control_3_safety reference_control_member_2940) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2940 reference_control_expr_2940 inputs path old current result Position Safe Nonreg (reference_control_ready_2940 old ) Step).
Qed.
Theorem reference_control_node_2940_congruent inputs path left right next_left next_right :
 VM.find 2939 left = VM.find 2939 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2940 next_left = VM.find 2940 next_right.
Proof.
 intros  E2939 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2940 reference_control_expr_2940 reference_control_3_positions reference_control_3_safety reference_control_member_2940) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2940 reference_control_expr_2940 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2940 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2940 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2939.
 reflexivity.
Qed.
Lemma reference_control_ready_2941 old :
 reference_control_ready old reference_control_expr_2941.
Proof.
 unfold reference_control_expr_2941.
apply rc_binary.
Qed.
Lemma reference_control_member_2941 : List.In (2941,reference_control_expr_2941) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 113%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2941_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2941 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2941 reference_control_expr_2941 reference_control_3_positions reference_control_3_safety reference_control_member_2941) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2941 reference_control_expr_2941 inputs path old current result Position Safe Nonreg (reference_control_ready_2941 old ) Step).
Qed.
Theorem reference_control_node_2941_congruent inputs path left right next_left next_right :
 VM.find 2932 left = VM.find 2932 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2941 next_left = VM.find 2941 next_right.
Proof.
 intros  E2932 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2941 reference_control_expr_2941 reference_control_3_positions reference_control_3_safety reference_control_member_2941) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2941 reference_control_expr_2941 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2941 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2941 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2932.
 reflexivity.
Qed.
Lemma reference_control_ready_2942 old :
 reference_control_ready old reference_control_expr_2942.
Proof.
 unfold reference_control_expr_2942.
apply rc_unary.
Qed.
Lemma reference_control_member_2942 : List.In (2942,reference_control_expr_2942) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 114%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2942_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2942 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2942 reference_control_expr_2942 reference_control_3_positions reference_control_3_safety reference_control_member_2942) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2942 reference_control_expr_2942 inputs path old current result Position Safe Nonreg (reference_control_ready_2942 old ) Step).
Qed.
Theorem reference_control_node_2942_congruent inputs path left right next_left next_right :
 VM.find 2938 left = VM.find 2938 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2942 next_left = VM.find 2942 next_right.
Proof.
 intros  E2938 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2942 reference_control_expr_2942 reference_control_3_positions reference_control_3_safety reference_control_member_2942) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2942 reference_control_expr_2942 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2942 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2942 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2938.
 reflexivity.
Qed.
Lemma reference_control_ready_2943 old :
 reference_control_ready old reference_control_expr_2943.
Proof.
 unfold reference_control_expr_2943.
apply rc_binary.
Qed.
Lemma reference_control_member_2943 : List.In (2943,reference_control_expr_2943) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 115%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2943_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2943 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2943 reference_control_expr_2943 reference_control_3_positions reference_control_3_safety reference_control_member_2943) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2943 reference_control_expr_2943 inputs path old current result Position Safe Nonreg (reference_control_ready_2943 old ) Step).
Qed.
Theorem reference_control_node_2943_congruent inputs path left right next_left next_right :
 VM.find 2942 left = VM.find 2942 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2943 next_left = VM.find 2943 next_right.
Proof.
 intros  E2942 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2943 reference_control_expr_2943 reference_control_3_positions reference_control_3_safety reference_control_member_2943) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2943 reference_control_expr_2943 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2943 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2943 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2942.
 reflexivity.
Qed.
Lemma reference_control_ready_2944 old :
 reference_control_ready old reference_control_expr_2944.
Proof.
 unfold reference_control_expr_2944.
apply rc_binary.
Qed.
Lemma reference_control_member_2944 : List.In (2944,reference_control_expr_2944) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 116%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2944_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2944 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2944 reference_control_expr_2944 reference_control_3_positions reference_control_3_safety reference_control_member_2944) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2944 reference_control_expr_2944 inputs path old current result Position Safe Nonreg (reference_control_ready_2944 old ) Step).
Qed.
Theorem reference_control_node_2944_congruent inputs path left right next_left next_right :
 VM.find 2932 left = VM.find 2932 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2944 next_left = VM.find 2944 next_right.
Proof.
 intros  E2932 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2944 reference_control_expr_2944 reference_control_3_positions reference_control_3_safety reference_control_member_2944) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2944 reference_control_expr_2944 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2944 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2944 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2932.
 reflexivity.
Qed.
Lemma reference_control_ready_2945 old :
 reference_control_ready old reference_control_expr_2945.
Proof.
 unfold reference_control_expr_2945.
apply rc_unary.
Qed.
Lemma reference_control_member_2945 : List.In (2945,reference_control_expr_2945) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 117%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2945_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2945 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2945 reference_control_expr_2945 reference_control_3_positions reference_control_3_safety reference_control_member_2945) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2945 reference_control_expr_2945 inputs path old current result Position Safe Nonreg (reference_control_ready_2945 old ) Step).
Qed.
Theorem reference_control_node_2945_congruent inputs path left right next_left next_right :
 VM.find 2938 left = VM.find 2938 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2945 next_left = VM.find 2945 next_right.
Proof.
 intros  E2938 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2945 reference_control_expr_2945 reference_control_3_positions reference_control_3_safety reference_control_member_2945) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2945 reference_control_expr_2945 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2945 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2945 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2938.
 reflexivity.
Qed.
Lemma reference_control_ready_2946 old :
 reference_control_ready old reference_control_expr_2946.
Proof.
 unfold reference_control_expr_2946.
apply rc_binary.
Qed.
Lemma reference_control_member_2946 : List.In (2946,reference_control_expr_2946) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 118%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2946_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2946 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2946 reference_control_expr_2946 reference_control_3_positions reference_control_3_safety reference_control_member_2946) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2946 reference_control_expr_2946 inputs path old current result Position Safe Nonreg (reference_control_ready_2946 old ) Step).
Qed.
Theorem reference_control_node_2946_congruent inputs path left right next_left next_right :
 VM.find 2945 left = VM.find 2945 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2946 next_left = VM.find 2946 next_right.
Proof.
 intros  E2945 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2946 reference_control_expr_2946 reference_control_3_positions reference_control_3_safety reference_control_member_2946) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2946 reference_control_expr_2946 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2946 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2946 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2945.
 reflexivity.
Qed.
Lemma reference_control_ready_2947 old :
 (exists value ground, VM.find 2946 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2947.
Proof.
 intros H2946.
 destruct H2946 as [v2946 [G2946 [V2946 T2946]]].
 unfold reference_control_expr_2947.
apply rc_mux.
{ eapply rc_ref; [exact V2946|exists G2946; exact T2946].
}
{ apply rc_const.
}
Qed.
Lemma reference_control_member_2947 : List.In (2947,reference_control_expr_2947) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 119%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2947_ground inputs path old current result :
 (exists value ground, VM.find 2946 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2947 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2946 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2947 reference_control_expr_2947 reference_control_3_positions reference_control_3_safety reference_control_member_2947) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2947 reference_control_expr_2947 inputs path old current result Position Safe Nonreg (reference_control_ready_2947 old H2946) Step).
Qed.
Theorem reference_control_node_2947_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2946 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2944 left = VM.find 2944 right ->
 VM.find 2946 left = VM.find 2946 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2947 next_left = VM.find 2947 next_right.
Proof.
 intros H2946 E2944 E2946 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2947 reference_control_expr_2947 reference_control_3_positions reference_control_3_safety reference_control_member_2947) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2947 reference_control_expr_2947 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2947 left H2946)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2947 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2944.
 rewrite E2946.
 reflexivity.
Qed.
Lemma reference_control_ready_2948 old :
 (exists value ground, VM.find 2943 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2947 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2948.
Proof.
 intros H2943 H2947.
 destruct H2943 as [v2943 [G2943 [V2943 T2943]]].
 destruct H2947 as [v2947 [G2947 [V2947 T2947]]].
 unfold reference_control_expr_2948.
apply rc_mux.
{ eapply rc_ref; [exact V2943|exists G2943; exact T2943].
}
{ eapply rc_ref; [exact V2947|exists G2947; exact T2947].
}
Qed.
Lemma reference_control_member_2948 : List.In (2948,reference_control_expr_2948) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 120%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2948_ground inputs path old current result :
 (exists value ground, VM.find 2943 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2947 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2948 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2943 H2947 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2948 reference_control_expr_2948 reference_control_3_positions reference_control_3_safety reference_control_member_2948) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2948 reference_control_expr_2948 inputs path old current result Position Safe Nonreg (reference_control_ready_2948 old H2943 H2947) Step).
Qed.
Theorem reference_control_node_2948_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2943 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2947 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2941 left = VM.find 2941 right ->
 VM.find 2943 left = VM.find 2943 right ->
 VM.find 2947 left = VM.find 2947 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2948 next_left = VM.find 2948 next_right.
Proof.
 intros H2943 H2947 E2941 E2943 E2947 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2948 reference_control_expr_2948 reference_control_3_positions reference_control_3_safety reference_control_member_2948) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2948 reference_control_expr_2948 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2948 left H2943 H2947)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2948 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2941.
 rewrite E2943.
 rewrite E2947.
 reflexivity.
Qed.
Lemma reference_control_ready_2949 old :
 (exists value ground, VM.find 2940 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2948 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2949.
Proof.
 intros H2940 H2948.
 destruct H2940 as [v2940 [G2940 [V2940 T2940]]].
 destruct H2948 as [v2948 [G2948 [V2948 T2948]]].
 unfold reference_control_expr_2949.
apply rc_mux.
{ eapply rc_ref; [exact V2940|exists G2940; exact T2940].
}
{ eapply rc_ref; [exact V2948|exists G2948; exact T2948].
}
Qed.
Lemma reference_control_member_2949 : List.In (2949,reference_control_expr_2949) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 121%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2949_ground inputs path old current result :
 (exists value ground, VM.find 2940 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2948 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2949 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2940 H2948 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2949 reference_control_expr_2949 reference_control_3_positions reference_control_3_safety reference_control_member_2949) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2949 reference_control_expr_2949 inputs path old current result Position Safe Nonreg (reference_control_ready_2949 old H2940 H2948) Step).
Qed.
Theorem reference_control_node_2949_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2940 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2948 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2933 left = VM.find 2933 right ->
 VM.find 2940 left = VM.find 2940 right ->
 VM.find 2948 left = VM.find 2948 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2949 next_left = VM.find 2949 next_right.
Proof.
 intros H2940 H2948 E2933 E2940 E2948 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2949 reference_control_expr_2949 reference_control_3_positions reference_control_3_safety reference_control_member_2949) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2949 reference_control_expr_2949 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2949 left H2940 H2948)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2949 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2933.
 rewrite E2940.
 rewrite E2948.
 reflexivity.
Qed.
Lemma reference_control_ready_2950 old :
 reference_control_ready old reference_control_expr_2950.
Proof.
 unfold reference_control_expr_2950.
apply rc_unary.
Qed.
Lemma reference_control_member_2950 : List.In (2950,reference_control_expr_2950) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 122%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2950_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2950 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2950 reference_control_expr_2950 reference_control_3_positions reference_control_3_safety reference_control_member_2950) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2950 reference_control_expr_2950 inputs path old current result Position Safe Nonreg (reference_control_ready_2950 old ) Step).
Qed.
Theorem reference_control_node_2950_congruent inputs path left right next_left next_right :
 VM.find 2807 left = VM.find 2807 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2950 next_left = VM.find 2950 next_right.
Proof.
 intros  E2807 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2950 reference_control_expr_2950 reference_control_3_positions reference_control_3_safety reference_control_member_2950) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2950 reference_control_expr_2950 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2950 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2950 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2807.
 reflexivity.
Qed.
Lemma reference_control_ready_2951 old :
 reference_control_ready old reference_control_expr_2951.
Proof.
 unfold reference_control_expr_2951.
apply rc_binary.
Qed.
Lemma reference_control_member_2951 : List.In (2951,reference_control_expr_2951) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 123%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2951_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2951 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2951 reference_control_expr_2951 reference_control_3_positions reference_control_3_safety reference_control_member_2951) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2951 reference_control_expr_2951 inputs path old current result Position Safe Nonreg (reference_control_ready_2951 old ) Step).
Qed.
Theorem reference_control_node_2951_congruent inputs path left right next_left next_right :
 VM.find 2950 left = VM.find 2950 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2951 next_left = VM.find 2951 next_right.
Proof.
 intros  E2950 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2951 reference_control_expr_2951 reference_control_3_positions reference_control_3_safety reference_control_member_2951) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2951 reference_control_expr_2951 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2951 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2951 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2950.
 reflexivity.
Qed.
Lemma reference_control_ready_2952 old :
 reference_control_ready old reference_control_expr_2952.
Proof.
 unfold reference_control_expr_2952.
apply rc_mux.
{ apply rc_const.
}
{ apply rc_const.
}
Qed.
Lemma reference_control_member_2952 : List.In (2952,reference_control_expr_2952) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 124%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2952_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2952 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2952 reference_control_expr_2952 reference_control_3_positions reference_control_3_safety reference_control_member_2952) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2952 reference_control_expr_2952 inputs path old current result Position Safe Nonreg (reference_control_ready_2952 old ) Step).
Qed.
Theorem reference_control_node_2952_congruent inputs path left right next_left next_right :
 VM.find 2951 left = VM.find 2951 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2952 next_left = VM.find 2952 next_right.
Proof.
 intros  E2951 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2952 reference_control_expr_2952 reference_control_3_positions reference_control_3_safety reference_control_member_2952) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2952 reference_control_expr_2952 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2952 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2952 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2951.
 reflexivity.
Qed.
Lemma reference_control_ready_2953 old :
 reference_control_ready old reference_control_expr_2953.
Proof.
 unfold reference_control_expr_2953.
apply rc_binary.
Qed.
Lemma reference_control_member_2953 : List.In (2953,reference_control_expr_2953) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 125%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2953_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2953 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2953 reference_control_expr_2953 reference_control_3_positions reference_control_3_safety reference_control_member_2953) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2953 reference_control_expr_2953 inputs path old current result Position Safe Nonreg (reference_control_ready_2953 old ) Step).
Qed.
Theorem reference_control_node_2953_congruent inputs path left right next_left next_right :
 VM.find 2952 left = VM.find 2952 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2953 next_left = VM.find 2953 next_right.
Proof.
 intros  E2952 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2953 reference_control_expr_2953 reference_control_3_positions reference_control_3_safety reference_control_member_2953) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2953 reference_control_expr_2953 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2953 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2953 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2952.
 reflexivity.
Qed.
Lemma reference_control_ready_2954 old :
 reference_control_ready old reference_control_expr_2954.
Proof.
 unfold reference_control_expr_2954.
apply rc_binary.
Qed.
Lemma reference_control_member_2954 : List.In (2954,reference_control_expr_2954) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 126%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2954_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2954 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2954 reference_control_expr_2954 reference_control_3_positions reference_control_3_safety reference_control_member_2954) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2954 reference_control_expr_2954 inputs path old current result Position Safe Nonreg (reference_control_ready_2954 old ) Step).
Qed.
Theorem reference_control_node_2954_congruent inputs path left right next_left next_right :
 VM.find 2552 left = VM.find 2552 right ->
 VM.find 2812 left = VM.find 2812 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2954 next_left = VM.find 2954 next_right.
Proof.
 intros  E2552 E2812 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2954 reference_control_expr_2954 reference_control_3_positions reference_control_3_safety reference_control_member_2954) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2954 reference_control_expr_2954 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2954 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2954 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2552.
 rewrite E2812.
 reflexivity.
Qed.
Lemma reference_control_ready_2955 old :
 reference_control_ready old reference_control_expr_2955.
Proof.
 unfold reference_control_expr_2955.
apply rc_unary.
Qed.
Lemma reference_control_member_2955 : List.In (2955,reference_control_expr_2955) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 127%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2955_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2955 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2955 reference_control_expr_2955 reference_control_3_positions reference_control_3_safety reference_control_member_2955) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2955 reference_control_expr_2955 inputs path old current result Position Safe Nonreg (reference_control_ready_2955 old ) Step).
Qed.
Theorem reference_control_node_2955_congruent inputs path left right next_left next_right :
 VM.find 2954 left = VM.find 2954 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2955 next_left = VM.find 2955 next_right.
Proof.
 intros  E2954 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2955 reference_control_expr_2955 reference_control_3_positions reference_control_3_safety reference_control_member_2955) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2955 reference_control_expr_2955 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2955 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2955 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2954.
 reflexivity.
Qed.
Lemma reference_control_ready_2956 old :
 reference_control_ready old reference_control_expr_2956.
Proof.
 unfold reference_control_expr_2956.
apply rc_unary.
Qed.
Lemma reference_control_member_2956 : List.In (2956,reference_control_expr_2956) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 128%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2956_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2956 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2956 reference_control_expr_2956 reference_control_3_positions reference_control_3_safety reference_control_member_2956) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2956 reference_control_expr_2956 inputs path old current result Position Safe Nonreg (reference_control_ready_2956 old ) Step).
Qed.
Theorem reference_control_node_2956_congruent inputs path left right next_left next_right :
 VM.find 2955 left = VM.find 2955 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2956 next_left = VM.find 2956 next_right.
Proof.
 intros  E2955 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2956 reference_control_expr_2956 reference_control_3_positions reference_control_3_safety reference_control_member_2956) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2956 reference_control_expr_2956 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2956 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2956 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2955.
 reflexivity.
Qed.
Lemma reference_control_ready_2957 old :
 reference_control_ready old reference_control_expr_2957.
Proof.
 unfold reference_control_expr_2957.
apply rc_binary.
Qed.
Lemma reference_control_member_2957 : List.In (2957,reference_control_expr_2957) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 129%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2957_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2957 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2957 reference_control_expr_2957 reference_control_3_positions reference_control_3_safety reference_control_member_2957) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2957 reference_control_expr_2957 inputs path old current result Position Safe Nonreg (reference_control_ready_2957 old ) Step).
Qed.
Theorem reference_control_node_2957_congruent inputs path left right next_left next_right :
 VM.find 2956 left = VM.find 2956 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2957 next_left = VM.find 2957 next_right.
Proof.
 intros  E2956 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2957 reference_control_expr_2957 reference_control_3_positions reference_control_3_safety reference_control_member_2957) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2957 reference_control_expr_2957 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2957 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2957 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2956.
 reflexivity.
Qed.
Lemma reference_control_ready_2958 old :
 reference_control_ready old reference_control_expr_2958.
Proof.
 unfold reference_control_expr_2958.
apply rc_binary.
Qed.
Lemma reference_control_member_2958 : List.In (2958,reference_control_expr_2958) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 130%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2958_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2958 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2958 reference_control_expr_2958 reference_control_3_positions reference_control_3_safety reference_control_member_2958) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2958 reference_control_expr_2958 inputs path old current result Position Safe Nonreg (reference_control_ready_2958 old ) Step).
Qed.
Theorem reference_control_node_2958_congruent inputs path left right next_left next_right :
 VM.find 2952 left = VM.find 2952 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2958 next_left = VM.find 2958 next_right.
Proof.
 intros  E2952 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2958 reference_control_expr_2958 reference_control_3_positions reference_control_3_safety reference_control_member_2958) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2958 reference_control_expr_2958 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2958 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2958 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2952.
 reflexivity.
Qed.
Lemma reference_control_ready_2959 old :
 reference_control_ready old reference_control_expr_2959.
Proof.
 unfold reference_control_expr_2959.
apply rc_unary.
Qed.
Lemma reference_control_member_2959 : List.In (2959,reference_control_expr_2959) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 131%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2959_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2959 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2959 reference_control_expr_2959 reference_control_3_positions reference_control_3_safety reference_control_member_2959) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2959 reference_control_expr_2959 inputs path old current result Position Safe Nonreg (reference_control_ready_2959 old ) Step).
Qed.
Theorem reference_control_node_2959_congruent inputs path left right next_left next_right :
 VM.find 2955 left = VM.find 2955 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2959 next_left = VM.find 2959 next_right.
Proof.
 intros  E2955 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2959 reference_control_expr_2959 reference_control_3_positions reference_control_3_safety reference_control_member_2959) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2959 reference_control_expr_2959 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2959 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2959 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2955.
 reflexivity.
Qed.
Lemma reference_control_ready_2960 old :
 reference_control_ready old reference_control_expr_2960.
Proof.
 unfold reference_control_expr_2960.
apply rc_binary.
Qed.
Lemma reference_control_member_2960 : List.In (2960,reference_control_expr_2960) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 132%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2960_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2960 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2960 reference_control_expr_2960 reference_control_3_positions reference_control_3_safety reference_control_member_2960) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2960 reference_control_expr_2960 inputs path old current result Position Safe Nonreg (reference_control_ready_2960 old ) Step).
Qed.
Theorem reference_control_node_2960_congruent inputs path left right next_left next_right :
 VM.find 2959 left = VM.find 2959 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2960 next_left = VM.find 2960 next_right.
Proof.
 intros  E2959 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2960 reference_control_expr_2960 reference_control_3_positions reference_control_3_safety reference_control_member_2960) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2960 reference_control_expr_2960 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2960 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2960 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2959.
 reflexivity.
Qed.
Lemma reference_control_ready_2961 old :
 reference_control_ready old reference_control_expr_2961.
Proof.
 unfold reference_control_expr_2961.
apply rc_binary.
Qed.
Lemma reference_control_member_2961 : List.In (2961,reference_control_expr_2961) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 133%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2961_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2961 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2961 reference_control_expr_2961 reference_control_3_positions reference_control_3_safety reference_control_member_2961) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2961 reference_control_expr_2961 inputs path old current result Position Safe Nonreg (reference_control_ready_2961 old ) Step).
Qed.
Theorem reference_control_node_2961_congruent inputs path left right next_left next_right :
 VM.find 2952 left = VM.find 2952 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2961 next_left = VM.find 2961 next_right.
Proof.
 intros  E2952 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2961 reference_control_expr_2961 reference_control_3_positions reference_control_3_safety reference_control_member_2961) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2961 reference_control_expr_2961 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2961 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2961 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2952.
 reflexivity.
Qed.
Lemma reference_control_ready_2962 old :
 reference_control_ready old reference_control_expr_2962.
Proof.
 unfold reference_control_expr_2962.
apply rc_unary.
Qed.
Lemma reference_control_member_2962 : List.In (2962,reference_control_expr_2962) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 134%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2962_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2962 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2962 reference_control_expr_2962 reference_control_3_positions reference_control_3_safety reference_control_member_2962) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2962 reference_control_expr_2962 inputs path old current result Position Safe Nonreg (reference_control_ready_2962 old ) Step).
Qed.
Theorem reference_control_node_2962_congruent inputs path left right next_left next_right :
 VM.find 2955 left = VM.find 2955 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2962 next_left = VM.find 2962 next_right.
Proof.
 intros  E2955 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2962 reference_control_expr_2962 reference_control_3_positions reference_control_3_safety reference_control_member_2962) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2962 reference_control_expr_2962 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2962 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2962 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2955.
 reflexivity.
Qed.
Lemma reference_control_ready_2963 old :
 reference_control_ready old reference_control_expr_2963.
Proof.
 unfold reference_control_expr_2963.
apply rc_binary.
Qed.
Lemma reference_control_member_2963 : List.In (2963,reference_control_expr_2963) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 135%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2963_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2963 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2963 reference_control_expr_2963 reference_control_3_positions reference_control_3_safety reference_control_member_2963) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2963 reference_control_expr_2963 inputs path old current result Position Safe Nonreg (reference_control_ready_2963 old ) Step).
Qed.
Theorem reference_control_node_2963_congruent inputs path left right next_left next_right :
 VM.find 2962 left = VM.find 2962 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2963 next_left = VM.find 2963 next_right.
Proof.
 intros  E2962 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2963 reference_control_expr_2963 reference_control_3_positions reference_control_3_safety reference_control_member_2963) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2963 reference_control_expr_2963 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2963 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2963 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2962.
 reflexivity.
Qed.
Lemma reference_control_ready_2964 old :
 (exists value ground, VM.find 2963 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2964.
Proof.
 intros H2963.
 destruct H2963 as [v2963 [G2963 [V2963 T2963]]].
 unfold reference_control_expr_2964.
apply rc_mux.
{ eapply rc_ref; [exact V2963|exists G2963; exact T2963].
}
{ apply rc_const.
}
Qed.
Lemma reference_control_member_2964 : List.In (2964,reference_control_expr_2964) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 136%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2964_ground inputs path old current result :
 (exists value ground, VM.find 2963 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2964 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2963 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2964 reference_control_expr_2964 reference_control_3_positions reference_control_3_safety reference_control_member_2964) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2964 reference_control_expr_2964 inputs path old current result Position Safe Nonreg (reference_control_ready_2964 old H2963) Step).
Qed.
Theorem reference_control_node_2964_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2963 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2961 left = VM.find 2961 right ->
 VM.find 2963 left = VM.find 2963 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2964 next_left = VM.find 2964 next_right.
Proof.
 intros H2963 E2961 E2963 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2964 reference_control_expr_2964 reference_control_3_positions reference_control_3_safety reference_control_member_2964) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2964 reference_control_expr_2964 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2964 left H2963)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2964 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2961.
 rewrite E2963.
 reflexivity.
Qed.
Lemma reference_control_ready_2965 old :
 (exists value ground, VM.find 2960 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2964 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2965.
Proof.
 intros H2960 H2964.
 destruct H2960 as [v2960 [G2960 [V2960 T2960]]].
 destruct H2964 as [v2964 [G2964 [V2964 T2964]]].
 unfold reference_control_expr_2965.
apply rc_mux.
{ eapply rc_ref; [exact V2960|exists G2960; exact T2960].
}
{ eapply rc_ref; [exact V2964|exists G2964; exact T2964].
}
Qed.
Lemma reference_control_member_2965 : List.In (2965,reference_control_expr_2965) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 137%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2965_ground inputs path old current result :
 (exists value ground, VM.find 2960 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2964 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2965 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2960 H2964 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2965 reference_control_expr_2965 reference_control_3_positions reference_control_3_safety reference_control_member_2965) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2965 reference_control_expr_2965 inputs path old current result Position Safe Nonreg (reference_control_ready_2965 old H2960 H2964) Step).
Qed.
Theorem reference_control_node_2965_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2960 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2964 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2958 left = VM.find 2958 right ->
 VM.find 2960 left = VM.find 2960 right ->
 VM.find 2964 left = VM.find 2964 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2965 next_left = VM.find 2965 next_right.
Proof.
 intros H2960 H2964 E2958 E2960 E2964 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2965 reference_control_expr_2965 reference_control_3_positions reference_control_3_safety reference_control_member_2965) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2965 reference_control_expr_2965 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2965 left H2960 H2964)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2965 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2958.
 rewrite E2960.
 rewrite E2964.
 reflexivity.
Qed.
Lemma reference_control_ready_2966 old :
 (exists value ground, VM.find 2957 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2965 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2966.
Proof.
 intros H2957 H2965.
 destruct H2957 as [v2957 [G2957 [V2957 T2957]]].
 destruct H2965 as [v2965 [G2965 [V2965 T2965]]].
 unfold reference_control_expr_2966.
apply rc_mux.
{ eapply rc_ref; [exact V2957|exists G2957; exact T2957].
}
{ eapply rc_ref; [exact V2965|exists G2965; exact T2965].
}
Qed.
Lemma reference_control_member_2966 : List.In (2966,reference_control_expr_2966) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 138%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2966_ground inputs path old current result :
 (exists value ground, VM.find 2957 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2965 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2966 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2957 H2965 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2966 reference_control_expr_2966 reference_control_3_positions reference_control_3_safety reference_control_member_2966) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2966 reference_control_expr_2966 inputs path old current result Position Safe Nonreg (reference_control_ready_2966 old H2957 H2965) Step).
Qed.
Theorem reference_control_node_2966_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2957 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2965 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2953 left = VM.find 2953 right ->
 VM.find 2957 left = VM.find 2957 right ->
 VM.find 2965 left = VM.find 2965 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2966 next_left = VM.find 2966 next_right.
Proof.
 intros H2957 H2965 E2953 E2957 E2965 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2966 reference_control_expr_2966 reference_control_3_positions reference_control_3_safety reference_control_member_2966) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2966 reference_control_expr_2966 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2966 left H2957 H2965)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2966 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2953.
 rewrite E2957.
 rewrite E2965.
 reflexivity.
Qed.
Lemma reference_control_ready_2993 old :
 reference_control_ready old reference_control_expr_2993.
Proof.
 unfold reference_control_expr_2993.
apply rc_mux.
{ apply rc_const.
}
{ apply rc_const.
}
Qed.
Lemma reference_control_member_2993 : List.In (2993,reference_control_expr_2993) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 139%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2993_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2993 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2993 reference_control_expr_2993 reference_control_3_positions reference_control_3_safety reference_control_member_2993) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2993 reference_control_expr_2993 inputs path old current result Position Safe Nonreg (reference_control_ready_2993 old ) Step).
Qed.
Theorem reference_control_node_2993_congruent inputs path left right next_left next_right :
 VM.find 2096 left = VM.find 2096 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2993 next_left = VM.find 2993 next_right.
Proof.
 intros  E2096 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2993 reference_control_expr_2993 reference_control_3_positions reference_control_3_safety reference_control_member_2993) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2993 reference_control_expr_2993 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2993 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2993 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2096.
 reflexivity.
Qed.
Lemma reference_control_ready_2994 old :
 (exists value ground, VM.find 2993 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2994.
Proof.
 intros H2993.
 destruct H2993 as [v2993 [G2993 [V2993 T2993]]].
 unfold reference_control_expr_2994.
apply rc_mux.
{ apply rc_const.
}
{ eapply rc_ref; [exact V2993|exists G2993; exact T2993].
}
Qed.
Lemma reference_control_member_2994 : List.In (2994,reference_control_expr_2994) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 140%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2994_ground inputs path old current result :
 (exists value ground, VM.find 2993 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2994 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2993 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2994 reference_control_expr_2994 reference_control_3_positions reference_control_3_safety reference_control_member_2994) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2994 reference_control_expr_2994 inputs path old current result Position Safe Nonreg (reference_control_ready_2994 old H2993) Step).
Qed.
Theorem reference_control_node_2994_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2993 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2092 left = VM.find 2092 right ->
 VM.find 2993 left = VM.find 2993 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2994 next_left = VM.find 2994 next_right.
Proof.
 intros H2993 E2092 E2993 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2994 reference_control_expr_2994 reference_control_3_positions reference_control_3_safety reference_control_member_2994) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2994 reference_control_expr_2994 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2994 left H2993)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2994 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2092.
 rewrite E2993.
 reflexivity.
Qed.
Lemma reference_control_ready_2995 old :
 (exists value ground, VM.find 2994 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2995.
Proof.
 intros H2994.
 destruct H2994 as [v2994 [G2994 [V2994 T2994]]].
 unfold reference_control_expr_2995.
apply rc_mux.
{ apply rc_const.
}
{ eapply rc_ref; [exact V2994|exists G2994; exact T2994].
}
Qed.
Lemma reference_control_member_2995 : List.In (2995,reference_control_expr_2995) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 141%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2995_ground inputs path old current result :
 (exists value ground, VM.find 2994 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2995 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2994 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2995 reference_control_expr_2995 reference_control_3_positions reference_control_3_safety reference_control_member_2995) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2995 reference_control_expr_2995 inputs path old current result Position Safe Nonreg (reference_control_ready_2995 old H2994) Step).
Qed.
Theorem reference_control_node_2995_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2994 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2088 left = VM.find 2088 right ->
 VM.find 2994 left = VM.find 2994 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2995 next_left = VM.find 2995 next_right.
Proof.
 intros H2994 E2088 E2994 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2995 reference_control_expr_2995 reference_control_3_positions reference_control_3_safety reference_control_member_2995) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2995 reference_control_expr_2995 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2995 left H2994)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2995 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2088.
 rewrite E2994.
 reflexivity.
Qed.
Lemma reference_control_ready_2996 old :
 (exists value ground, VM.find 2995 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2996.
Proof.
 intros H2995.
 destruct H2995 as [v2995 [G2995 [V2995 T2995]]].
 unfold reference_control_expr_2996.
apply rc_mux.
{ apply rc_const.
}
{ eapply rc_ref; [exact V2995|exists G2995; exact T2995].
}
Qed.
Lemma reference_control_member_2996 : List.In (2996,reference_control_expr_2996) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 142%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2996_ground inputs path old current result :
 (exists value ground, VM.find 2995 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2996 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2995 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2996 reference_control_expr_2996 reference_control_3_positions reference_control_3_safety reference_control_member_2996) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2996 reference_control_expr_2996 inputs path old current result Position Safe Nonreg (reference_control_ready_2996 old H2995) Step).
Qed.
Theorem reference_control_node_2996_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2995 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2084 left = VM.find 2084 right ->
 VM.find 2995 left = VM.find 2995 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2996 next_left = VM.find 2996 next_right.
Proof.
 intros H2995 E2084 E2995 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2996 reference_control_expr_2996 reference_control_3_positions reference_control_3_safety reference_control_member_2996) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2996 reference_control_expr_2996 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2996 left H2995)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2996 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2084.
 rewrite E2995.
 reflexivity.
Qed.
Lemma reference_control_ready_2997 old :
 (exists value ground, VM.find 2996 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2997.
Proof.
 intros H2996.
 destruct H2996 as [v2996 [G2996 [V2996 T2996]]].
 unfold reference_control_expr_2997.
apply rc_mux.
{ apply rc_const.
}
{ eapply rc_ref; [exact V2996|exists G2996; exact T2996].
}
Qed.
Lemma reference_control_member_2997 : List.In (2997,reference_control_expr_2997) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 143%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2997_ground inputs path old current result :
 (exists value ground, VM.find 2996 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2997 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2996 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2997 reference_control_expr_2997 reference_control_3_positions reference_control_3_safety reference_control_member_2997) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2997 reference_control_expr_2997 inputs path old current result Position Safe Nonreg (reference_control_ready_2997 old H2996) Step).
Qed.
Theorem reference_control_node_2997_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2996 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2080 left = VM.find 2080 right ->
 VM.find 2996 left = VM.find 2996 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2997 next_left = VM.find 2997 next_right.
Proof.
 intros H2996 E2080 E2996 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2997 reference_control_expr_2997 reference_control_3_positions reference_control_3_safety reference_control_member_2997) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2997 reference_control_expr_2997 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2997 left H2996)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2997 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2080.
 rewrite E2996.
 reflexivity.
Qed.
Lemma reference_control_ready_2998 old :
 (exists value ground, VM.find 2997 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2998.
Proof.
 intros H2997.
 destruct H2997 as [v2997 [G2997 [V2997 T2997]]].
 unfold reference_control_expr_2998.
apply rc_mux.
{ apply rc_const.
}
{ eapply rc_ref; [exact V2997|exists G2997; exact T2997].
}
Qed.
Lemma reference_control_member_2998 : List.In (2998,reference_control_expr_2998) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 144%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2998_ground inputs path old current result :
 (exists value ground, VM.find 2997 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2998 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2997 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2998 reference_control_expr_2998 reference_control_3_positions reference_control_3_safety reference_control_member_2998) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2998 reference_control_expr_2998 inputs path old current result Position Safe Nonreg (reference_control_ready_2998 old H2997) Step).
Qed.
Theorem reference_control_node_2998_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2997 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2076 left = VM.find 2076 right ->
 VM.find 2997 left = VM.find 2997 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2998 next_left = VM.find 2998 next_right.
Proof.
 intros H2997 E2076 E2997 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2998 reference_control_expr_2998 reference_control_3_positions reference_control_3_safety reference_control_member_2998) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2998 reference_control_expr_2998 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2998 left H2997)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2998 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2076.
 rewrite E2997.
 reflexivity.
Qed.
Lemma reference_control_ready_2999 old :
 (exists value ground, VM.find 2998 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2999.
Proof.
 intros H2998.
 destruct H2998 as [v2998 [G2998 [V2998 T2998]]].
 unfold reference_control_expr_2999.
apply rc_mux.
{ apply rc_const.
}
{ eapply rc_ref; [exact V2998|exists G2998; exact T2998].
}
Qed.
Lemma reference_control_member_2999 : List.In (2999,reference_control_expr_2999) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 145%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2999_ground inputs path old current result :
 (exists value ground, VM.find 2998 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2999 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2998 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2999 reference_control_expr_2999 reference_control_3_positions reference_control_3_safety reference_control_member_2999) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2999 reference_control_expr_2999 inputs path old current result Position Safe Nonreg (reference_control_ready_2999 old H2998) Step).
Qed.
Theorem reference_control_node_2999_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2998 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2072 left = VM.find 2072 right ->
 VM.find 2998 left = VM.find 2998 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2999 next_left = VM.find 2999 next_right.
Proof.
 intros H2998 E2072 E2998 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 2999 reference_control_expr_2999 reference_control_3_positions reference_control_3_safety reference_control_member_2999) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2999 reference_control_expr_2999 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2999 left H2998)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2999 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2072.
 rewrite E2998.
 reflexivity.
Qed.
Lemma reference_control_ready_3000 old :
 (exists value ground, VM.find 2999 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_3000.
Proof.
 intros H2999.
 destruct H2999 as [v2999 [G2999 [V2999 T2999]]].
 unfold reference_control_expr_3000.
apply rc_mux.
{ apply rc_const.
}
{ eapply rc_ref; [exact V2999|exists G2999; exact T2999].
}
Qed.
Lemma reference_control_member_3000 : List.In (3000,reference_control_expr_3000) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 146%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_3000_ground inputs path old current result :
 (exists value ground, VM.find 2999 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 3000 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2999 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 3000 reference_control_expr_3000 reference_control_3_positions reference_control_3_safety reference_control_member_3000) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 3000 reference_control_expr_3000 inputs path old current result Position Safe Nonreg (reference_control_ready_3000 old H2999) Step).
Qed.
Theorem reference_control_node_3000_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2999 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2068 left = VM.find 2068 right ->
 VM.find 2999 left = VM.find 2999 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 3000 next_left = VM.find 3000 next_right.
Proof.
 intros H2999 E2068 E2999 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 3000 reference_control_expr_3000 reference_control_3_positions reference_control_3_safety reference_control_member_3000) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 3000 reference_control_expr_3000 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_3000 left H2999)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_3000 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2068.
 rewrite E2999.
 reflexivity.
Qed.
Lemma reference_control_ready_3001 old :
 (exists value ground, VM.find 3000 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_3001.
Proof.
 intros H3000.
 destruct H3000 as [v3000 [G3000 [V3000 T3000]]].
 unfold reference_control_expr_3001.
apply rc_mux.
{ apply rc_const.
}
{ eapply rc_ref; [exact V3000|exists G3000; exact T3000].
}
Qed.
Lemma reference_control_member_3001 : List.In (3001,reference_control_expr_3001) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 147%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_3001_ground inputs path old current result :
 (exists value ground, VM.find 3000 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 3001 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H3000 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 3001 reference_control_expr_3001 reference_control_3_positions reference_control_3_safety reference_control_member_3001) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 3001 reference_control_expr_3001 inputs path old current result Position Safe Nonreg (reference_control_ready_3001 old H3000) Step).
Qed.
Theorem reference_control_node_3001_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 3000 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2064 left = VM.find 2064 right ->
 VM.find 3000 left = VM.find 3000 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 3001 next_left = VM.find 3001 next_right.
Proof.
 intros H3000 E2064 E3000 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 3001 reference_control_expr_3001 reference_control_3_positions reference_control_3_safety reference_control_member_3001) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 3001 reference_control_expr_3001 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_3001 left H3000)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_3001 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2064.
 rewrite E3000.
 reflexivity.
Qed.
Lemma reference_control_ready_3002 old :
 (exists value ground, VM.find 3001 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_3002.
Proof.
 intros H3001.
 destruct H3001 as [v3001 [G3001 [V3001 T3001]]].
 unfold reference_control_expr_3002.
apply rc_mux.
{ apply rc_const.
}
{ eapply rc_ref; [exact V3001|exists G3001; exact T3001].
}
Qed.
Lemma reference_control_member_3002 : List.In (3002,reference_control_expr_3002) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 148%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_3002_ground inputs path old current result :
 (exists value ground, VM.find 3001 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 3002 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H3001 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 3002 reference_control_expr_3002 reference_control_3_positions reference_control_3_safety reference_control_member_3002) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 3002 reference_control_expr_3002 inputs path old current result Position Safe Nonreg (reference_control_ready_3002 old H3001) Step).
Qed.
Theorem reference_control_node_3002_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 3001 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2475 left = VM.find 2475 right ->
 VM.find 3001 left = VM.find 3001 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 3002 next_left = VM.find 3002 next_right.
Proof.
 intros H3001 E2475 E3001 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 3002 reference_control_expr_3002 reference_control_3_positions reference_control_3_safety reference_control_member_3002) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 3002 reference_control_expr_3002 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_3002 left H3001)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_3002 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2475.
 rewrite E3001.
 reflexivity.
Qed.
Lemma reference_control_ready_3003 old :
 (exists value ground, VM.find 3002 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_3003.
Proof.
 intros H3002.
 destruct H3002 as [v3002 [G3002 [V3002 T3002]]].
 unfold reference_control_expr_3003.
apply rc_mux.
{ apply rc_const.
}
{ eapply rc_ref; [exact V3002|exists G3002; exact T3002].
}
Qed.
Lemma reference_control_member_3003 : List.In (3003,reference_control_expr_3003) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 149%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_3003_ground inputs path old current result :
 (exists value ground, VM.find 3002 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 3003 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H3002 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 3003 reference_control_expr_3003 reference_control_3_positions reference_control_3_safety reference_control_member_3003) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 3003 reference_control_expr_3003 inputs path old current result Position Safe Nonreg (reference_control_ready_3003 old H3002) Step).
Qed.
Theorem reference_control_node_3003_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 3002 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2472 left = VM.find 2472 right ->
 VM.find 3002 left = VM.find 3002 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 3003 next_left = VM.find 3003 next_right.
Proof.
 intros H3002 E2472 E3002 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 3003 reference_control_expr_3003 reference_control_3_positions reference_control_3_safety reference_control_member_3003) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 3003 reference_control_expr_3003 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_3003 left H3002)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_3003 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2472.
 rewrite E3002.
 reflexivity.
Qed.
Lemma reference_control_ready_3004 old :
 (exists value ground, VM.find 3003 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_3004.
Proof.
 intros H3003.
 destruct H3003 as [v3003 [G3003 [V3003 T3003]]].
 unfold reference_control_expr_3004.
apply rc_mux.
{ apply rc_const.
}
{ eapply rc_ref; [exact V3003|exists G3003; exact T3003].
}
Qed.
Lemma reference_control_member_3004 : List.In (3004,reference_control_expr_3004) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 150%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_3004_ground inputs path old current result :
 (exists value ground, VM.find 3003 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 3004 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H3003 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 3004 reference_control_expr_3004 reference_control_3_positions reference_control_3_safety reference_control_member_3004) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 3004 reference_control_expr_3004 inputs path old current result Position Safe Nonreg (reference_control_ready_3004 old H3003) Step).
Qed.
Theorem reference_control_node_3004_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 3003 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2059 left = VM.find 2059 right ->
 VM.find 3003 left = VM.find 3003 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 3004 next_left = VM.find 3004 next_right.
Proof.
 intros H3003 E2059 E3003 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 3004 reference_control_expr_3004 reference_control_3_positions reference_control_3_safety reference_control_member_3004) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 3004 reference_control_expr_3004 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_3004 left H3003)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_3004 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2059.
 rewrite E3003.
 reflexivity.
Qed.
Lemma reference_control_ready_3005 old :
 (exists value ground, VM.find 3004 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_3005.
Proof.
 intros H3004.
 destruct H3004 as [v3004 [G3004 [V3004 T3004]]].
 unfold reference_control_expr_3005.
apply rc_mux.
{ apply rc_const.
}
{ eapply rc_ref; [exact V3004|exists G3004; exact T3004].
}
Qed.
Lemma reference_control_member_3005 : List.In (3005,reference_control_expr_3005) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 151%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_3005_ground inputs path old current result :
 (exists value ground, VM.find 3004 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 3005 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H3004 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 3005 reference_control_expr_3005 reference_control_3_positions reference_control_3_safety reference_control_member_3005) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 3005 reference_control_expr_3005 inputs path old current result Position Safe Nonreg (reference_control_ready_3005 old H3004) Step).
Qed.
Theorem reference_control_node_3005_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 3004 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2054 left = VM.find 2054 right ->
 VM.find 3004 left = VM.find 3004 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 3005 next_left = VM.find 3005 next_right.
Proof.
 intros H3004 E2054 E3004 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 3005 reference_control_expr_3005 reference_control_3_positions reference_control_3_safety reference_control_member_3005) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 3005 reference_control_expr_3005 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_3005 left H3004)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_3005 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2054.
 rewrite E3004.
 reflexivity.
Qed.
Lemma reference_control_ready_3006 old :
 (exists value ground, VM.find 3005 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_3006.
Proof.
 intros H3005.
 destruct H3005 as [v3005 [G3005 [V3005 T3005]]].
 unfold reference_control_expr_3006.
apply rc_mux.
{ apply rc_const.
}
{ eapply rc_ref; [exact V3005|exists G3005; exact T3005].
}
Qed.
Lemma reference_control_member_3006 : List.In (3006,reference_control_expr_3006) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 152%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_3006_ground inputs path old current result :
 (exists value ground, VM.find 3005 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 3006 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H3005 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 3006 reference_control_expr_3006 reference_control_3_positions reference_control_3_safety reference_control_member_3006) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 3006 reference_control_expr_3006 inputs path old current result Position Safe Nonreg (reference_control_ready_3006 old H3005) Step).
Qed.
Theorem reference_control_node_3006_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 3005 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2049 left = VM.find 2049 right ->
 VM.find 3005 left = VM.find 3005 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 3006 next_left = VM.find 3006 next_right.
Proof.
 intros H3005 E2049 E3005 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 3006 reference_control_expr_3006 reference_control_3_positions reference_control_3_safety reference_control_member_3006) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 3006 reference_control_expr_3006 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_3006 left H3005)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_3006 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2049.
 rewrite E3005.
 reflexivity.
Qed.
Lemma reference_control_ready_3007 old :
 (exists value ground, VM.find 3006 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_3007.
Proof.
 intros H3006.
 destruct H3006 as [v3006 [G3006 [V3006 T3006]]].
 unfold reference_control_expr_3007.
apply rc_mux.
{ apply rc_const.
}
{ eapply rc_ref; [exact V3006|exists G3006; exact T3006].
}
Qed.
Lemma reference_control_member_3007 : List.In (3007,reference_control_expr_3007) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 153%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_3007_ground inputs path old current result :
 (exists value ground, VM.find 3006 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 3007 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H3006 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 3007 reference_control_expr_3007 reference_control_3_positions reference_control_3_safety reference_control_member_3007) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 3007 reference_control_expr_3007 inputs path old current result Position Safe Nonreg (reference_control_ready_3007 old H3006) Step).
Qed.
Theorem reference_control_node_3007_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 3006 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2044 left = VM.find 2044 right ->
 VM.find 3006 left = VM.find 3006 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 3007 next_left = VM.find 3007 next_right.
Proof.
 intros H3006 E2044 E3006 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 3007 reference_control_expr_3007 reference_control_3_positions reference_control_3_safety reference_control_member_3007) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 3007 reference_control_expr_3007 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_3007 left H3006)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_3007 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2044.
 rewrite E3006.
 reflexivity.
Qed.
Lemma reference_control_ready_3008 old :
 (exists value ground, VM.find 3007 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_3008.
Proof.
 intros H3007.
 destruct H3007 as [v3007 [G3007 [V3007 T3007]]].
 unfold reference_control_expr_3008.
apply rc_mux.
{ apply rc_const.
}
{ eapply rc_ref; [exact V3007|exists G3007; exact T3007].
}
Qed.
Lemma reference_control_member_3008 : List.In (3008,reference_control_expr_3008) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 154%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_3008_ground inputs path old current result :
 (exists value ground, VM.find 3007 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 3008 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H3007 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 3008 reference_control_expr_3008 reference_control_3_positions reference_control_3_safety reference_control_member_3008) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 3008 reference_control_expr_3008 inputs path old current result Position Safe Nonreg (reference_control_ready_3008 old H3007) Step).
Qed.
Theorem reference_control_node_3008_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 3007 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2039 left = VM.find 2039 right ->
 VM.find 3007 left = VM.find 3007 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 3008 next_left = VM.find 3008 next_right.
Proof.
 intros H3007 E2039 E3007 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 3008 reference_control_expr_3008 reference_control_3_positions reference_control_3_safety reference_control_member_3008) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 3008 reference_control_expr_3008 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_3008 left H3007)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_3008 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2039.
 rewrite E3007.
 reflexivity.
Qed.
Lemma reference_control_ready_3009 old :
 (exists value ground, VM.find 3008 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_3009.
Proof.
 intros H3008.
 destruct H3008 as [v3008 [G3008 [V3008 T3008]]].
 unfold reference_control_expr_3009.
apply rc_mux.
{ apply rc_const.
}
{ eapply rc_ref; [exact V3008|exists G3008; exact T3008].
}
Qed.
Lemma reference_control_member_3009 : List.In (3009,reference_control_expr_3009) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 155%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_3009_ground inputs path old current result :
 (exists value ground, VM.find 3008 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 3009 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H3008 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 3009 reference_control_expr_3009 reference_control_3_positions reference_control_3_safety reference_control_member_3009) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 3009 reference_control_expr_3009 inputs path old current result Position Safe Nonreg (reference_control_ready_3009 old H3008) Step).
Qed.
Theorem reference_control_node_3009_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 3008 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2034 left = VM.find 2034 right ->
 VM.find 3008 left = VM.find 3008 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 3009 next_left = VM.find 3009 next_right.
Proof.
 intros H3008 E2034 E3008 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 3009 reference_control_expr_3009 reference_control_3_positions reference_control_3_safety reference_control_member_3009) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 3009 reference_control_expr_3009 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_3009 left H3008)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_3009 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2034.
 rewrite E3008.
 reflexivity.
Qed.
Lemma reference_control_ready_3010 old :
 (exists value ground, VM.find 3009 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_3010.
Proof.
 intros H3009.
 destruct H3009 as [v3009 [G3009 [V3009 T3009]]].
 unfold reference_control_expr_3010.
apply rc_mux.
{ apply rc_const.
}
{ eapply rc_ref; [exact V3009|exists G3009; exact T3009].
}
Qed.
Lemma reference_control_member_3010 : List.In (3010,reference_control_expr_3010) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 156%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_3010_ground inputs path old current result :
 (exists value ground, VM.find 3009 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 3010 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H3009 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 3010 reference_control_expr_3010 reference_control_3_positions reference_control_3_safety reference_control_member_3010) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 3010 reference_control_expr_3010 inputs path old current result Position Safe Nonreg (reference_control_ready_3010 old H3009) Step).
Qed.
Theorem reference_control_node_3010_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 3009 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2029 left = VM.find 2029 right ->
 VM.find 3009 left = VM.find 3009 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 3010 next_left = VM.find 3010 next_right.
Proof.
 intros H3009 E2029 E3009 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 3010 reference_control_expr_3010 reference_control_3_positions reference_control_3_safety reference_control_member_3010) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 3010 reference_control_expr_3010 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_3010 left H3009)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_3010 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2029.
 rewrite E3009.
 reflexivity.
Qed.
Lemma reference_control_ready_3011 old :
 (exists value ground, VM.find 3010 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_3011.
Proof.
 intros H3010.
 destruct H3010 as [v3010 [G3010 [V3010 T3010]]].
 unfold reference_control_expr_3011.
apply rc_mux.
{ apply rc_const.
}
{ eapply rc_ref; [exact V3010|exists G3010; exact T3010].
}
Qed.
Lemma reference_control_member_3011 : List.In (3011,reference_control_expr_3011) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 157%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_3011_ground inputs path old current result :
 (exists value ground, VM.find 3010 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 3011 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H3010 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 3011 reference_control_expr_3011 reference_control_3_positions reference_control_3_safety reference_control_member_3011) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 3011 reference_control_expr_3011 inputs path old current result Position Safe Nonreg (reference_control_ready_3011 old H3010) Step).
Qed.
Theorem reference_control_node_3011_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 3010 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2024 left = VM.find 2024 right ->
 VM.find 3010 left = VM.find 3010 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 3011 next_left = VM.find 3011 next_right.
Proof.
 intros H3010 E2024 E3010 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 3011 reference_control_expr_3011 reference_control_3_positions reference_control_3_safety reference_control_member_3011) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 3011 reference_control_expr_3011 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_3011 left H3010)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_3011 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2024.
 rewrite E3010.
 reflexivity.
Qed.
Lemma reference_control_ready_3012 old :
 (exists value ground, VM.find 3011 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_3012.
Proof.
 intros H3011.
 destruct H3011 as [v3011 [G3011 [V3011 T3011]]].
 unfold reference_control_expr_3012.
apply rc_mux.
{ apply rc_const.
}
{ eapply rc_ref; [exact V3011|exists G3011; exact T3011].
}
Qed.
Lemma reference_control_member_3012 : List.In (3012,reference_control_expr_3012) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 158%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_3012_ground inputs path old current result :
 (exists value ground, VM.find 3011 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 3012 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H3011 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 3012 reference_control_expr_3012 reference_control_3_positions reference_control_3_safety reference_control_member_3012) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 3012 reference_control_expr_3012 inputs path old current result Position Safe Nonreg (reference_control_ready_3012 old H3011) Step).
Qed.
Theorem reference_control_node_3012_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 3011 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2019 left = VM.find 2019 right ->
 VM.find 3011 left = VM.find 3011 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 3012 next_left = VM.find 3012 next_right.
Proof.
 intros H3011 E2019 E3011 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 3012 reference_control_expr_3012 reference_control_3_positions reference_control_3_safety reference_control_member_3012) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 3012 reference_control_expr_3012 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_3012 left H3011)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_3012 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2019.
 rewrite E3011.
 reflexivity.
Qed.
Lemma reference_control_ready_3013 old :
 (exists value ground, VM.find 3012 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_3013.
Proof.
 intros H3012.
 destruct H3012 as [v3012 [G3012 [V3012 T3012]]].
 unfold reference_control_expr_3013.
apply rc_mux.
{ apply rc_const.
}
{ eapply rc_ref; [exact V3012|exists G3012; exact T3012].
}
Qed.
Lemma reference_control_member_3013 : List.In (3013,reference_control_expr_3013) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 159%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_3013_ground inputs path old current result :
 (exists value ground, VM.find 3012 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 3013 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H3012 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 3013 reference_control_expr_3013 reference_control_3_positions reference_control_3_safety reference_control_member_3013) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 3013 reference_control_expr_3013 inputs path old current result Position Safe Nonreg (reference_control_ready_3013 old H3012) Step).
Qed.
Theorem reference_control_node_3013_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 3012 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2014 left = VM.find 2014 right ->
 VM.find 3012 left = VM.find 3012 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 3013 next_left = VM.find 3013 next_right.
Proof.
 intros H3012 E2014 E3012 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 3013 reference_control_expr_3013 reference_control_3_positions reference_control_3_safety reference_control_member_3013) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 3013 reference_control_expr_3013 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_3013 left H3012)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_3013 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2014.
 rewrite E3012.
 reflexivity.
Qed.
Lemma reference_control_ready_3014 old :
 (exists value ground, VM.find 3013 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_3014.
Proof.
 intros H3013.
 destruct H3013 as [v3013 [G3013 [V3013 T3013]]].
 unfold reference_control_expr_3014.
apply rc_mux.
{ apply rc_const.
}
{ eapply rc_ref; [exact V3013|exists G3013; exact T3013].
}
Qed.
Lemma reference_control_member_3014 : List.In (3014,reference_control_expr_3014) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 160%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_3014_ground inputs path old current result :
 (exists value ground, VM.find 3013 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 3014 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H3013 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 3014 reference_control_expr_3014 reference_control_3_positions reference_control_3_safety reference_control_member_3014) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 3014 reference_control_expr_3014 inputs path old current result Position Safe Nonreg (reference_control_ready_3014 old H3013) Step).
Qed.
Theorem reference_control_node_3014_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 3013 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2357 left = VM.find 2357 right ->
 VM.find 3013 left = VM.find 3013 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 3014 next_left = VM.find 3014 next_right.
Proof.
 intros H3013 E2357 E3013 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 3014 reference_control_expr_3014 reference_control_3_positions reference_control_3_safety reference_control_member_3014) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 3014 reference_control_expr_3014 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_3014 left H3013)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_3014 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2357.
 rewrite E3013.
 reflexivity.
Qed.
Lemma reference_control_ready_3015 old :
 (exists value ground, VM.find 3014 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_3015.
Proof.
 intros H3014.
 destruct H3014 as [v3014 [G3014 [V3014 T3014]]].
 unfold reference_control_expr_3015.
apply rc_mux.
{ apply rc_const.
}
{ eapply rc_ref; [exact V3014|exists G3014; exact T3014].
}
Qed.
Lemma reference_control_member_3015 : List.In (3015,reference_control_expr_3015) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 161%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_3015_ground inputs path old current result :
 (exists value ground, VM.find 3014 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 3015 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H3014 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 3015 reference_control_expr_3015 reference_control_3_positions reference_control_3_safety reference_control_member_3015) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 3015 reference_control_expr_3015 inputs path old current result Position Safe Nonreg (reference_control_ready_3015 old H3014) Step).
Qed.
Theorem reference_control_node_3015_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 3014 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2010 left = VM.find 2010 right ->
 VM.find 3014 left = VM.find 3014 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 3015 next_left = VM.find 3015 next_right.
Proof.
 intros H3014 E2010 E3014 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 3015 reference_control_expr_3015 reference_control_3_positions reference_control_3_safety reference_control_member_3015) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 3015 reference_control_expr_3015 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_3015 left H3014)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_3015 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2010.
 rewrite E3014.
 reflexivity.
Qed.
Lemma reference_control_ready_3016 old :
 (exists value ground, VM.find 3015 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_3016.
Proof.
 intros H3015.
 destruct H3015 as [v3015 [G3015 [V3015 T3015]]].
 unfold reference_control_expr_3016.
apply rc_mux.
{ apply rc_const.
}
{ eapply rc_ref; [exact V3015|exists G3015; exact T3015].
}
Qed.
Lemma reference_control_member_3016 : List.In (3016,reference_control_expr_3016) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 162%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_3016_ground inputs path old current result :
 (exists value ground, VM.find 3015 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 3016 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H3015 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 3016 reference_control_expr_3016 reference_control_3_positions reference_control_3_safety reference_control_member_3016) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 3016 reference_control_expr_3016 inputs path old current result Position Safe Nonreg (reference_control_ready_3016 old H3015) Step).
Qed.
Theorem reference_control_node_3016_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 3015 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2004 left = VM.find 2004 right ->
 VM.find 3015 left = VM.find 3015 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 3016 next_left = VM.find 3016 next_right.
Proof.
 intros H3015 E2004 E3015 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 3016 reference_control_expr_3016 reference_control_3_positions reference_control_3_safety reference_control_member_3016) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 3016 reference_control_expr_3016 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_3016 left H3015)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_3016 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2004.
 rewrite E3015.
 reflexivity.
Qed.
Lemma reference_control_ready_3017 old :
 (exists value ground, VM.find 3016 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_3017.
Proof.
 intros H3016.
 destruct H3016 as [v3016 [G3016 [V3016 T3016]]].
 unfold reference_control_expr_3017.
apply rc_mux.
{ apply rc_const.
}
{ eapply rc_ref; [exact V3016|exists G3016; exact T3016].
}
Qed.
Lemma reference_control_member_3017 : List.In (3017,reference_control_expr_3017) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 163%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_3017_ground inputs path old current result :
 (exists value ground, VM.find 3016 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 3017 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H3016 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 3017 reference_control_expr_3017 reference_control_3_positions reference_control_3_safety reference_control_member_3017) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 3017 reference_control_expr_3017 inputs path old current result Position Safe Nonreg (reference_control_ready_3017 old H3016) Step).
Qed.
Theorem reference_control_node_3017_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 3016 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1998 left = VM.find 1998 right ->
 VM.find 3016 left = VM.find 3016 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 3017 next_left = VM.find 3017 next_right.
Proof.
 intros H3016 E1998 E3016 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 3017 reference_control_expr_3017 reference_control_3_positions reference_control_3_safety reference_control_member_3017) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 3017 reference_control_expr_3017 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_3017 left H3016)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_3017 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1998.
 rewrite E3016.
 reflexivity.
Qed.
Lemma reference_control_ready_3018 old :
 (exists value ground, VM.find 3017 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_3018.
Proof.
 intros H3017.
 destruct H3017 as [v3017 [G3017 [V3017 T3017]]].
 unfold reference_control_expr_3018.
apply rc_mux.
{ apply rc_const.
}
{ eapply rc_ref; [exact V3017|exists G3017; exact T3017].
}
Qed.
Lemma reference_control_member_3018 : List.In (3018,reference_control_expr_3018) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 164%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_3018_ground inputs path old current result :
 (exists value ground, VM.find 3017 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 3018 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H3017 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 3018 reference_control_expr_3018 reference_control_3_positions reference_control_3_safety reference_control_member_3018) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 3018 reference_control_expr_3018 inputs path old current result Position Safe Nonreg (reference_control_ready_3018 old H3017) Step).
Qed.
Theorem reference_control_node_3018_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 3017 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1992 left = VM.find 1992 right ->
 VM.find 3017 left = VM.find 3017 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 3018 next_left = VM.find 3018 next_right.
Proof.
 intros H3017 E1992 E3017 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 3018 reference_control_expr_3018 reference_control_3_positions reference_control_3_safety reference_control_member_3018) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 3018 reference_control_expr_3018 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_3018 left H3017)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_3018 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1992.
 rewrite E3017.
 reflexivity.
Qed.
Lemma reference_control_ready_3019 old :
 (exists value ground, VM.find 3018 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_3019.
Proof.
 intros H3018.
 destruct H3018 as [v3018 [G3018 [V3018 T3018]]].
 unfold reference_control_expr_3019.
apply rc_mux.
{ apply rc_const.
}
{ eapply rc_ref; [exact V3018|exists G3018; exact T3018].
}
Qed.
Lemma reference_control_member_3019 : List.In (3019,reference_control_expr_3019) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 165%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_3019_ground inputs path old current result :
 (exists value ground, VM.find 3018 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 3019 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H3018 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 3019 reference_control_expr_3019 reference_control_3_positions reference_control_3_safety reference_control_member_3019) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 3019 reference_control_expr_3019 inputs path old current result Position Safe Nonreg (reference_control_ready_3019 old H3018) Step).
Qed.
Theorem reference_control_node_3019_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 3018 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1986 left = VM.find 1986 right ->
 VM.find 3018 left = VM.find 3018 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 3019 next_left = VM.find 3019 next_right.
Proof.
 intros H3018 E1986 E3018 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 3019 reference_control_expr_3019 reference_control_3_positions reference_control_3_safety reference_control_member_3019) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 3019 reference_control_expr_3019 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_3019 left H3018)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_3019 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1986.
 rewrite E3018.
 reflexivity.
Qed.
Lemma reference_control_ready_3020 old :
 (exists value ground, VM.find 3019 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_3020.
Proof.
 intros H3019.
 destruct H3019 as [v3019 [G3019 [V3019 T3019]]].
 unfold reference_control_expr_3020.
apply rc_mux.
{ apply rc_const.
}
{ eapply rc_ref; [exact V3019|exists G3019; exact T3019].
}
Qed.
Lemma reference_control_member_3020 : List.In (3020,reference_control_expr_3020) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 166%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_3020_ground inputs path old current result :
 (exists value ground, VM.find 3019 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 3020 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H3019 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 3020 reference_control_expr_3020 reference_control_3_positions reference_control_3_safety reference_control_member_3020) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 3020 reference_control_expr_3020 inputs path old current result Position Safe Nonreg (reference_control_ready_3020 old H3019) Step).
Qed.
Theorem reference_control_node_3020_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 3019 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1980 left = VM.find 1980 right ->
 VM.find 3019 left = VM.find 3019 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 3020 next_left = VM.find 3020 next_right.
Proof.
 intros H3019 E1980 E3019 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 3020 reference_control_expr_3020 reference_control_3_positions reference_control_3_safety reference_control_member_3020) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 3020 reference_control_expr_3020 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_3020 left H3019)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_3020 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1980.
 rewrite E3019.
 reflexivity.
Qed.
Lemma reference_control_ready_3021 old :
 (exists value ground, VM.find 3020 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_3021.
Proof.
 intros H3020.
 destruct H3020 as [v3020 [G3020 [V3020 T3020]]].
 unfold reference_control_expr_3021.
apply rc_mux.
{ apply rc_const.
}
{ eapply rc_ref; [exact V3020|exists G3020; exact T3020].
}
Qed.
Lemma reference_control_member_3021 : List.In (3021,reference_control_expr_3021) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 167%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_3021_ground inputs path old current result :
 (exists value ground, VM.find 3020 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 3021 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H3020 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 3021 reference_control_expr_3021 reference_control_3_positions reference_control_3_safety reference_control_member_3021) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 3021 reference_control_expr_3021 inputs path old current result Position Safe Nonreg (reference_control_ready_3021 old H3020) Step).
Qed.
Theorem reference_control_node_3021_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 3020 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1974 left = VM.find 1974 right ->
 VM.find 3020 left = VM.find 3020 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 3021 next_left = VM.find 3021 next_right.
Proof.
 intros H3020 E1974 E3020 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 3021 reference_control_expr_3021 reference_control_3_positions reference_control_3_safety reference_control_member_3021) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 3021 reference_control_expr_3021 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_3021 left H3020)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_3021 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1974.
 rewrite E3020.
 reflexivity.
Qed.
Lemma reference_control_ready_3022 old :
 (exists value ground, VM.find 3021 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_3022.
Proof.
 intros H3021.
 destruct H3021 as [v3021 [G3021 [V3021 T3021]]].
 unfold reference_control_expr_3022.
apply rc_mux.
{ apply rc_const.
}
{ eapply rc_ref; [exact V3021|exists G3021; exact T3021].
}
Qed.
Lemma reference_control_member_3022 : List.In (3022,reference_control_expr_3022) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 168%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_3022_ground inputs path old current result :
 (exists value ground, VM.find 3021 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 3022 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H3021 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 3022 reference_control_expr_3022 reference_control_3_positions reference_control_3_safety reference_control_member_3022) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 3022 reference_control_expr_3022 inputs path old current result Position Safe Nonreg (reference_control_ready_3022 old H3021) Step).
Qed.
Theorem reference_control_node_3022_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 3021 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1970 left = VM.find 1970 right ->
 VM.find 3021 left = VM.find 3021 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 3022 next_left = VM.find 3022 next_right.
Proof.
 intros H3021 E1970 E3021 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 3022 reference_control_expr_3022 reference_control_3_positions reference_control_3_safety reference_control_member_3022) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 3022 reference_control_expr_3022 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_3022 left H3021)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_3022 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1970.
 rewrite E3021.
 reflexivity.
Qed.
Lemma reference_control_ready_3023 old :
 (exists value ground, VM.find 3022 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_3023.
Proof.
 intros H3022.
 destruct H3022 as [v3022 [G3022 [V3022 T3022]]].
 unfold reference_control_expr_3023.
apply rc_mux.
{ apply rc_const.
}
{ eapply rc_ref; [exact V3022|exists G3022; exact T3022].
}
Qed.
Lemma reference_control_member_3023 : List.In (3023,reference_control_expr_3023) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 169%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_3023_ground inputs path old current result :
 (exists value ground, VM.find 3022 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 3023 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H3022 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 3023 reference_control_expr_3023 reference_control_3_positions reference_control_3_safety reference_control_member_3023) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 3023 reference_control_expr_3023 inputs path old current result Position Safe Nonreg (reference_control_ready_3023 old H3022) Step).
Qed.
Theorem reference_control_node_3023_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 3022 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1966 left = VM.find 1966 right ->
 VM.find 3022 left = VM.find 3022 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 3023 next_left = VM.find 3023 next_right.
Proof.
 intros H3022 E1966 E3022 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 3023 reference_control_expr_3023 reference_control_3_positions reference_control_3_safety reference_control_member_3023) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 3023 reference_control_expr_3023 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_3023 left H3022)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_3023 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1966.
 rewrite E3022.
 reflexivity.
Qed.
Lemma reference_control_ready_3024 old :
 (exists value ground, VM.find 3023 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_3024.
Proof.
 intros H3023.
 destruct H3023 as [v3023 [G3023 [V3023 T3023]]].
 unfold reference_control_expr_3024.
apply rc_mux.
{ apply rc_const.
}
{ eapply rc_ref; [exact V3023|exists G3023; exact T3023].
}
Qed.
Lemma reference_control_member_3024 : List.In (3024,reference_control_expr_3024) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 170%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_3024_ground inputs path old current result :
 (exists value ground, VM.find 3023 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 3024 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H3023 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 3024 reference_control_expr_3024 reference_control_3_positions reference_control_3_safety reference_control_member_3024) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 3024 reference_control_expr_3024 inputs path old current result Position Safe Nonreg (reference_control_ready_3024 old H3023) Step).
Qed.
Theorem reference_control_node_3024_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 3023 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1962 left = VM.find 1962 right ->
 VM.find 3023 left = VM.find 3023 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 3024 next_left = VM.find 3024 next_right.
Proof.
 intros H3023 E1962 E3023 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 3024 reference_control_expr_3024 reference_control_3_positions reference_control_3_safety reference_control_member_3024) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 3024 reference_control_expr_3024 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_3024 left H3023)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_3024 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1962.
 rewrite E3023.
 reflexivity.
Qed.
Lemma reference_control_ready_3025 old :
 (exists value ground, VM.find 3024 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_3025.
Proof.
 intros H3024.
 destruct H3024 as [v3024 [G3024 [V3024 T3024]]].
 unfold reference_control_expr_3025.
apply rc_mux.
{ apply rc_const.
}
{ eapply rc_ref; [exact V3024|exists G3024; exact T3024].
}
Qed.
Lemma reference_control_member_3025 : List.In (3025,reference_control_expr_3025) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 171%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_3025_ground inputs path old current result :
 (exists value ground, VM.find 3024 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 3025 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H3024 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 3025 reference_control_expr_3025 reference_control_3_positions reference_control_3_safety reference_control_member_3025) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 3025 reference_control_expr_3025 inputs path old current result Position Safe Nonreg (reference_control_ready_3025 old H3024) Step).
Qed.
Theorem reference_control_node_3025_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 3024 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1958 left = VM.find 1958 right ->
 VM.find 3024 left = VM.find 3024 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 3025 next_left = VM.find 3025 next_right.
Proof.
 intros H3024 E1958 E3024 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 3025 reference_control_expr_3025 reference_control_3_positions reference_control_3_safety reference_control_member_3025) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 3025 reference_control_expr_3025 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_3025 left H3024)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_3025 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1958.
 rewrite E3024.
 reflexivity.
Qed.
Lemma reference_control_ready_3026 old :
 (exists value ground, VM.find 3025 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_3026.
Proof.
 intros H3025.
 destruct H3025 as [v3025 [G3025 [V3025 T3025]]].
 unfold reference_control_expr_3026.
apply rc_mux.
{ apply rc_const.
}
{ eapply rc_ref; [exact V3025|exists G3025; exact T3025].
}
Qed.
Lemma reference_control_member_3026 : List.In (3026,reference_control_expr_3026) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 172%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_3026_ground inputs path old current result :
 (exists value ground, VM.find 3025 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 3026 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H3025 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 3026 reference_control_expr_3026 reference_control_3_positions reference_control_3_safety reference_control_member_3026) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 3026 reference_control_expr_3026 inputs path old current result Position Safe Nonreg (reference_control_ready_3026 old H3025) Step).
Qed.
Theorem reference_control_node_3026_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 3025 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1886 left = VM.find 1886 right ->
 VM.find 3025 left = VM.find 3025 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 3026 next_left = VM.find 3026 next_right.
Proof.
 intros H3025 E1886 E3025 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 3026 reference_control_expr_3026 reference_control_3_positions reference_control_3_safety reference_control_member_3026) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 3026 reference_control_expr_3026 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_3026 left H3025)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_3026 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1886.
 rewrite E3025.
 reflexivity.
Qed.
Lemma reference_control_ready_3027 old :
 (exists value ground, VM.find 3026 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_3027.
Proof.
 intros H3026.
 destruct H3026 as [v3026 [G3026 [V3026 T3026]]].
 unfold reference_control_expr_3027.
apply rc_mux.
{ apply rc_const.
}
{ eapply rc_ref; [exact V3026|exists G3026; exact T3026].
}
Qed.
Lemma reference_control_member_3027 : List.In (3027,reference_control_expr_3027) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 173%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_3027_ground inputs path old current result :
 (exists value ground, VM.find 3026 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 3027 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H3026 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 3027 reference_control_expr_3027 reference_control_3_positions reference_control_3_safety reference_control_member_3027) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 3027 reference_control_expr_3027 inputs path old current result Position Safe Nonreg (reference_control_ready_3027 old H3026) Step).
Qed.
Theorem reference_control_node_3027_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 3026 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1951 left = VM.find 1951 right ->
 VM.find 3026 left = VM.find 3026 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 3027 next_left = VM.find 3027 next_right.
Proof.
 intros H3026 E1951 E3026 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 3027 reference_control_expr_3027 reference_control_3_positions reference_control_3_safety reference_control_member_3027) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 3027 reference_control_expr_3027 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_3027 left H3026)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_3027 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1951.
 rewrite E3026.
 reflexivity.
Qed.
Lemma reference_control_ready_3028 old :
 (exists value ground, VM.find 3027 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_3028.
Proof.
 intros H3027.
 destruct H3027 as [v3027 [G3027 [V3027 T3027]]].
 unfold reference_control_expr_3028.
apply rc_mux.
{ apply rc_const.
}
{ eapply rc_ref; [exact V3027|exists G3027; exact T3027].
}
Qed.
Lemma reference_control_member_3028 : List.In (3028,reference_control_expr_3028) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 174%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_3028_ground inputs path old current result :
 (exists value ground, VM.find 3027 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 3028 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H3027 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 3028 reference_control_expr_3028 reference_control_3_positions reference_control_3_safety reference_control_member_3028) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 3028 reference_control_expr_3028 inputs path old current result Position Safe Nonreg (reference_control_ready_3028 old H3027) Step).
Qed.
Theorem reference_control_node_3028_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 3027 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1946 left = VM.find 1946 right ->
 VM.find 3027 left = VM.find 3027 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 3028 next_left = VM.find 3028 next_right.
Proof.
 intros H3027 E1946 E3027 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 3028 reference_control_expr_3028 reference_control_3_positions reference_control_3_safety reference_control_member_3028) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 3028 reference_control_expr_3028 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_3028 left H3027)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_3028 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1946.
 rewrite E3027.
 reflexivity.
Qed.
Lemma reference_control_ready_3029 old :
 (exists value ground, VM.find 3028 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_3029.
Proof.
 intros H3028.
 destruct H3028 as [v3028 [G3028 [V3028 T3028]]].
 unfold reference_control_expr_3029.
apply rc_mux.
{ apply rc_const.
}
{ eapply rc_ref; [exact V3028|exists G3028; exact T3028].
}
Qed.
Lemma reference_control_member_3029 : List.In (3029,reference_control_expr_3029) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 175%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_3029_ground inputs path old current result :
 (exists value ground, VM.find 3028 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 3029 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H3028 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 3029 reference_control_expr_3029 reference_control_3_positions reference_control_3_safety reference_control_member_3029) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 3029 reference_control_expr_3029 inputs path old current result Position Safe Nonreg (reference_control_ready_3029 old H3028) Step).
Qed.
Theorem reference_control_node_3029_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 3028 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1941 left = VM.find 1941 right ->
 VM.find 3028 left = VM.find 3028 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 3029 next_left = VM.find 3029 next_right.
Proof.
 intros H3028 E1941 E3028 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 3029 reference_control_expr_3029 reference_control_3_positions reference_control_3_safety reference_control_member_3029) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 3029 reference_control_expr_3029 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_3029 left H3028)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_3029 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1941.
 rewrite E3028.
 reflexivity.
Qed.
Lemma reference_control_ready_3030 old :
 (exists value ground, VM.find 3029 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_3030.
Proof.
 intros H3029.
 destruct H3029 as [v3029 [G3029 [V3029 T3029]]].
 unfold reference_control_expr_3030.
apply rc_mux.
{ apply rc_const.
}
{ eapply rc_ref; [exact V3029|exists G3029; exact T3029].
}
Qed.
Lemma reference_control_member_3030 : List.In (3030,reference_control_expr_3030) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 176%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_3030_ground inputs path old current result :
 (exists value ground, VM.find 3029 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 3030 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H3029 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 3030 reference_control_expr_3030 reference_control_3_positions reference_control_3_safety reference_control_member_3030) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 3030 reference_control_expr_3030 inputs path old current result Position Safe Nonreg (reference_control_ready_3030 old H3029) Step).
Qed.
Theorem reference_control_node_3030_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 3029 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1937 left = VM.find 1937 right ->
 VM.find 3029 left = VM.find 3029 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 3030 next_left = VM.find 3030 next_right.
Proof.
 intros H3029 E1937 E3029 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 3030 reference_control_expr_3030 reference_control_3_positions reference_control_3_safety reference_control_member_3030) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 3030 reference_control_expr_3030 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_3030 left H3029)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_3030 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1937.
 rewrite E3029.
 reflexivity.
Qed.
Lemma reference_control_ready_3031 old :
 (exists value ground, VM.find 3030 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_3031.
Proof.
 intros H3030.
 destruct H3030 as [v3030 [G3030 [V3030 T3030]]].
 unfold reference_control_expr_3031.
apply rc_mux.
{ apply rc_const.
}
{ eapply rc_ref; [exact V3030|exists G3030; exact T3030].
}
Qed.
Lemma reference_control_member_3031 : List.In (3031,reference_control_expr_3031) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 177%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_3031_ground inputs path old current result :
 (exists value ground, VM.find 3030 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 3031 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H3030 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 3031 reference_control_expr_3031 reference_control_3_positions reference_control_3_safety reference_control_member_3031) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 3031 reference_control_expr_3031 inputs path old current result Position Safe Nonreg (reference_control_ready_3031 old H3030) Step).
Qed.
Theorem reference_control_node_3031_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 3030 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1933 left = VM.find 1933 right ->
 VM.find 3030 left = VM.find 3030 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 3031 next_left = VM.find 3031 next_right.
Proof.
 intros H3030 E1933 E3030 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 3031 reference_control_expr_3031 reference_control_3_positions reference_control_3_safety reference_control_member_3031) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 3031 reference_control_expr_3031 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_3031 left H3030)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_3031 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1933.
 rewrite E3030.
 reflexivity.
Qed.
Lemma reference_control_ready_3032 old :
 (exists value ground, VM.find 3031 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_3032.
Proof.
 intros H3031.
 destruct H3031 as [v3031 [G3031 [V3031 T3031]]].
 unfold reference_control_expr_3032.
apply rc_mux.
{ apply rc_const.
}
{ eapply rc_ref; [exact V3031|exists G3031; exact T3031].
}
Qed.
Lemma reference_control_member_3032 : List.In (3032,reference_control_expr_3032) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 178%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_3032_ground inputs path old current result :
 (exists value ground, VM.find 3031 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 3032 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H3031 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 3032 reference_control_expr_3032 reference_control_3_positions reference_control_3_safety reference_control_member_3032) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 3032 reference_control_expr_3032 inputs path old current result Position Safe Nonreg (reference_control_ready_3032 old H3031) Step).
Qed.
Theorem reference_control_node_3032_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 3031 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1929 left = VM.find 1929 right ->
 VM.find 3031 left = VM.find 3031 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 3032 next_left = VM.find 3032 next_right.
Proof.
 intros H3031 E1929 E3031 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 3032 reference_control_expr_3032 reference_control_3_positions reference_control_3_safety reference_control_member_3032) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 3032 reference_control_expr_3032 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_3032 left H3031)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_3032 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1929.
 rewrite E3031.
 reflexivity.
Qed.
Lemma reference_control_ready_3033 old :
 (exists value ground, VM.find 3032 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_3033.
Proof.
 intros H3032.
 destruct H3032 as [v3032 [G3032 [V3032 T3032]]].
 unfold reference_control_expr_3033.
apply rc_mux.
{ apply rc_const.
}
{ eapply rc_ref; [exact V3032|exists G3032; exact T3032].
}
Qed.
Lemma reference_control_member_3033 : List.In (3033,reference_control_expr_3033) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 179%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_3033_ground inputs path old current result :
 (exists value ground, VM.find 3032 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 3033 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H3032 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 3033 reference_control_expr_3033 reference_control_3_positions reference_control_3_safety reference_control_member_3033) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 3033 reference_control_expr_3033 inputs path old current result Position Safe Nonreg (reference_control_ready_3033 old H3032) Step).
Qed.
Theorem reference_control_node_3033_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 3032 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1924 left = VM.find 1924 right ->
 VM.find 3032 left = VM.find 3032 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 3033 next_left = VM.find 3033 next_right.
Proof.
 intros H3032 E1924 E3032 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 3033 reference_control_expr_3033 reference_control_3_positions reference_control_3_safety reference_control_member_3033) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 3033 reference_control_expr_3033 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_3033 left H3032)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_3033 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1924.
 rewrite E3032.
 reflexivity.
Qed.
Lemma reference_control_ready_3034 old :
 (exists value ground, VM.find 3033 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_3034.
Proof.
 intros H3033.
 destruct H3033 as [v3033 [G3033 [V3033 T3033]]].
 unfold reference_control_expr_3034.
apply rc_mux.
{ apply rc_const.
}
{ eapply rc_ref; [exact V3033|exists G3033; exact T3033].
}
Qed.
Lemma reference_control_member_3034 : List.In (3034,reference_control_expr_3034) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 180%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_3034_ground inputs path old current result :
 (exists value ground, VM.find 3033 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 3034 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H3033 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 3034 reference_control_expr_3034 reference_control_3_positions reference_control_3_safety reference_control_member_3034) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 3034 reference_control_expr_3034 inputs path old current result Position Safe Nonreg (reference_control_ready_3034 old H3033) Step).
Qed.
Theorem reference_control_node_3034_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 3033 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1919 left = VM.find 1919 right ->
 VM.find 3033 left = VM.find 3033 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 3034 next_left = VM.find 3034 next_right.
Proof.
 intros H3033 E1919 E3033 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 3034 reference_control_expr_3034 reference_control_3_positions reference_control_3_safety reference_control_member_3034) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 3034 reference_control_expr_3034 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_3034 left H3033)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_3034 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1919.
 rewrite E3033.
 reflexivity.
Qed.
Lemma reference_control_ready_3035 old :
 (exists value ground, VM.find 3034 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_3035.
Proof.
 intros H3034.
 destruct H3034 as [v3034 [G3034 [V3034 T3034]]].
 unfold reference_control_expr_3035.
apply rc_mux.
{ apply rc_const.
}
{ eapply rc_ref; [exact V3034|exists G3034; exact T3034].
}
Qed.
Lemma reference_control_member_3035 : List.In (3035,reference_control_expr_3035) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 181%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_3035_ground inputs path old current result :
 (exists value ground, VM.find 3034 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 3035 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H3034 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 3035 reference_control_expr_3035 reference_control_3_positions reference_control_3_safety reference_control_member_3035) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 3035 reference_control_expr_3035 inputs path old current result Position Safe Nonreg (reference_control_ready_3035 old H3034) Step).
Qed.
Theorem reference_control_node_3035_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 3034 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1914 left = VM.find 1914 right ->
 VM.find 3034 left = VM.find 3034 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 3035 next_left = VM.find 3035 next_right.
Proof.
 intros H3034 E1914 E3034 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 3035 reference_control_expr_3035 reference_control_3_positions reference_control_3_safety reference_control_member_3035) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 3035 reference_control_expr_3035 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_3035 left H3034)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_3035 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1914.
 rewrite E3034.
 reflexivity.
Qed.
Lemma reference_control_ready_3036 old :
 (exists value ground, VM.find 3035 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_3036.
Proof.
 intros H3035.
 destruct H3035 as [v3035 [G3035 [V3035 T3035]]].
 unfold reference_control_expr_3036.
apply rc_mux.
{ apply rc_const.
}
{ eapply rc_ref; [exact V3035|exists G3035; exact T3035].
}
Qed.
Lemma reference_control_member_3036 : List.In (3036,reference_control_expr_3036) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 182%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_3036_ground inputs path old current result :
 (exists value ground, VM.find 3035 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 3036 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H3035 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 3036 reference_control_expr_3036 reference_control_3_positions reference_control_3_safety reference_control_member_3036) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 3036 reference_control_expr_3036 inputs path old current result Position Safe Nonreg (reference_control_ready_3036 old H3035) Step).
Qed.
Theorem reference_control_node_3036_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 3035 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1909 left = VM.find 1909 right ->
 VM.find 3035 left = VM.find 3035 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 3036 next_left = VM.find 3036 next_right.
Proof.
 intros H3035 E1909 E3035 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 3036 reference_control_expr_3036 reference_control_3_positions reference_control_3_safety reference_control_member_3036) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 3036 reference_control_expr_3036 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_3036 left H3035)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_3036 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1909.
 rewrite E3035.
 reflexivity.
Qed.
Lemma reference_control_ready_3037 old :
 (exists value ground, VM.find 3036 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_3037.
Proof.
 intros H3036.
 destruct H3036 as [v3036 [G3036 [V3036 T3036]]].
 unfold reference_control_expr_3037.
apply rc_mux.
{ apply rc_const.
}
{ eapply rc_ref; [exact V3036|exists G3036; exact T3036].
}
Qed.
Lemma reference_control_member_3037 : List.In (3037,reference_control_expr_3037) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 183%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_3037_ground inputs path old current result :
 (exists value ground, VM.find 3036 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 3037 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H3036 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 3037 reference_control_expr_3037 reference_control_3_positions reference_control_3_safety reference_control_member_3037) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 3037 reference_control_expr_3037 inputs path old current result Position Safe Nonreg (reference_control_ready_3037 old H3036) Step).
Qed.
Theorem reference_control_node_3037_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 3036 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1904 left = VM.find 1904 right ->
 VM.find 3036 left = VM.find 3036 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 3037 next_left = VM.find 3037 next_right.
Proof.
 intros H3036 E1904 E3036 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 3037 reference_control_expr_3037 reference_control_3_positions reference_control_3_safety reference_control_member_3037) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 3037 reference_control_expr_3037 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_3037 left H3036)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_3037 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1904.
 rewrite E3036.
 reflexivity.
Qed.
Lemma reference_control_ready_3038 old :
 (exists value ground, VM.find 3037 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_3038.
Proof.
 intros H3037.
 destruct H3037 as [v3037 [G3037 [V3037 T3037]]].
 unfold reference_control_expr_3038.
apply rc_mux.
{ apply rc_const.
}
{ eapply rc_ref; [exact V3037|exists G3037; exact T3037].
}
Qed.
Lemma reference_control_member_3038 : List.In (3038,reference_control_expr_3038) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 184%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_3038_ground inputs path old current result :
 (exists value ground, VM.find 3037 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 3038 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H3037 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 3038 reference_control_expr_3038 reference_control_3_positions reference_control_3_safety reference_control_member_3038) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 3038 reference_control_expr_3038 inputs path old current result Position Safe Nonreg (reference_control_ready_3038 old H3037) Step).
Qed.
Theorem reference_control_node_3038_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 3037 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1899 left = VM.find 1899 right ->
 VM.find 3037 left = VM.find 3037 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 3038 next_left = VM.find 3038 next_right.
Proof.
 intros H3037 E1899 E3037 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 3038 reference_control_expr_3038 reference_control_3_positions reference_control_3_safety reference_control_member_3038) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 3038 reference_control_expr_3038 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_3038 left H3037)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_3038 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1899.
 rewrite E3037.
 reflexivity.
Qed.
Lemma reference_control_ready_3039 old :
 (exists value ground, VM.find 3038 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_3039.
Proof.
 intros H3038.
 destruct H3038 as [v3038 [G3038 [V3038 T3038]]].
 unfold reference_control_expr_3039.
apply rc_mux.
{ apply rc_const.
}
{ eapply rc_ref; [exact V3038|exists G3038; exact T3038].
}
Qed.
Lemma reference_control_member_3039 : List.In (3039,reference_control_expr_3039) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 185%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_3039_ground inputs path old current result :
 (exists value ground, VM.find 3038 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 3039 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H3038 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 3039 reference_control_expr_3039 reference_control_3_positions reference_control_3_safety reference_control_member_3039) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 3039 reference_control_expr_3039 inputs path old current result Position Safe Nonreg (reference_control_ready_3039 old H3038) Step).
Qed.
Theorem reference_control_node_3039_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 3038 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1894 left = VM.find 1894 right ->
 VM.find 3038 left = VM.find 3038 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 3039 next_left = VM.find 3039 next_right.
Proof.
 intros H3038 E1894 E3038 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 3039 reference_control_expr_3039 reference_control_3_positions reference_control_3_safety reference_control_member_3039) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 3039 reference_control_expr_3039 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_3039 left H3038)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_3039 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1894.
 rewrite E3038.
 reflexivity.
Qed.
Lemma reference_control_ready_3040 old :
 (exists value ground, VM.find 3039 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_3040.
Proof.
 intros H3039.
 destruct H3039 as [v3039 [G3039 [V3039 T3039]]].
 unfold reference_control_expr_3040.
apply rc_mux.
{ apply rc_const.
}
{ eapply rc_ref; [exact V3039|exists G3039; exact T3039].
}
Qed.
Lemma reference_control_member_3040 : List.In (3040,reference_control_expr_3040) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 186%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_3040_ground inputs path old current result :
 (exists value ground, VM.find 3039 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 3040 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H3039 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 3040 reference_control_expr_3040 reference_control_3_positions reference_control_3_safety reference_control_member_3040) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 3040 reference_control_expr_3040 inputs path old current result Position Safe Nonreg (reference_control_ready_3040 old H3039) Step).
Qed.
Theorem reference_control_node_3040_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 3039 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1889 left = VM.find 1889 right ->
 VM.find 3039 left = VM.find 3039 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 3040 next_left = VM.find 3040 next_right.
Proof.
 intros H3039 E1889 E3039 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 3040 reference_control_expr_3040 reference_control_3_positions reference_control_3_safety reference_control_member_3040) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 3040 reference_control_expr_3040 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_3040 left H3039)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_3040 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1889.
 rewrite E3039.
 reflexivity.
Qed.
Lemma reference_control_ready_3041 old :
 (exists value ground, VM.find 3040 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_3041.
Proof.
 intros H3040.
 destruct H3040 as [v3040 [G3040 [V3040 T3040]]].
 unfold reference_control_expr_3041.
apply rc_mux.
{ eapply rc_ref; [exact V3040|exists G3040; exact T3040].
}
{ apply rc_const.
}
Qed.
Lemma reference_control_member_3041 : List.In (3041,reference_control_expr_3041) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 187%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_3041_ground inputs path old current result :
 (exists value ground, VM.find 3040 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 3041 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H3040 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 3041 reference_control_expr_3041 reference_control_3_positions reference_control_3_safety reference_control_member_3041) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 3041 reference_control_expr_3041 inputs path old current result Position Safe Nonreg (reference_control_ready_3041 old H3040) Step).
Qed.
Theorem reference_control_node_3041_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 3040 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1707 left = VM.find 1707 right ->
 VM.find 3040 left = VM.find 3040 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 3041 next_left = VM.find 3041 next_right.
Proof.
 intros H3040 E1707 E3040 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 3041 reference_control_expr_3041 reference_control_3_positions reference_control_3_safety reference_control_member_3041) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 3041 reference_control_expr_3041 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_3041 left H3040)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_3041 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1707.
 rewrite E3040.
 reflexivity.
Qed.
Lemma reference_control_ready_3042 old :
 (exists value ground, VM.find 3041 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_3042.
Proof.
 intros H3041.
 destruct H3041 as [v3041 [G3041 [V3041 T3041]]].
 unfold reference_control_expr_3042.
eapply rc_ref; [exact V3041|exists G3041; exact T3041].
Qed.
Lemma reference_control_member_3042 : List.In (3042,reference_control_expr_3042) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 188%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_3042_ground inputs path old current result :
 (exists value ground, VM.find 3041 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 3042 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H3041 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 3042 reference_control_expr_3042 reference_control_3_positions reference_control_3_safety reference_control_member_3042) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 3042 reference_control_expr_3042 inputs path old current result Position Safe Nonreg (reference_control_ready_3042 old H3041) Step).
Qed.
Theorem reference_control_node_3042_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 3041 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 3041 left = VM.find 3041 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 3042 next_left = VM.find 3042 next_right.
Proof.
 intros H3041 E3041 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 3042 reference_control_expr_3042 reference_control_3_positions reference_control_3_safety reference_control_member_3042) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 3042 reference_control_expr_3042 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_3042 left H3041)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_3042 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E3041.
 reflexivity.
Qed.
Lemma reference_control_ready_6314 old :
 reference_control_ready old reference_control_expr_6314.
Proof.
 unfold reference_control_expr_6314.
apply rc_mux.
{ apply rc_const.
}
{ apply rc_const.
}
Qed.
Lemma reference_control_member_6314 : List.In (6314,reference_control_expr_6314) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 189%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_6314_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 6314 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 6314 reference_control_expr_6314 reference_control_3_positions reference_control_3_safety reference_control_member_6314) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 6314 reference_control_expr_6314 inputs path old current result Position Safe Nonreg (reference_control_ready_6314 old ) Step).
Qed.
Theorem reference_control_node_6314_congruent inputs path left right next_left next_right :
 VM.find 2966 left = VM.find 2966 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 6314 next_left = VM.find 6314 next_right.
Proof.
 intros  E2966 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 6314 reference_control_expr_6314 reference_control_3_positions reference_control_3_safety reference_control_member_6314) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 6314 reference_control_expr_6314 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_6314 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_6314 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2966.
 reflexivity.
Qed.
Lemma reference_control_ready_6323 old :
 reference_control_ready old reference_control_expr_6323.
Proof.
 unfold reference_control_expr_6323.
apply rc_mux.
{ apply rc_const.
}
{ apply rc_const.
}
Qed.
Lemma reference_control_member_6323 : List.In (6323,reference_control_expr_6323) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 190%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_6323_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 6323 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 6323 reference_control_expr_6323 reference_control_3_positions reference_control_3_safety reference_control_member_6323) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 6323 reference_control_expr_6323 inputs path old current result Position Safe Nonreg (reference_control_ready_6323 old ) Step).
Qed.
Theorem reference_control_node_6323_congruent inputs path left right next_left next_right :
 VM.find 2966 left = VM.find 2966 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 6323 next_left = VM.find 6323 next_right.
Proof.
 intros  E2966 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 6323 reference_control_expr_6323 reference_control_3_positions reference_control_3_safety reference_control_member_6323) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 6323 reference_control_expr_6323 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_6323 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_6323 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2966.
 reflexivity.
Qed.
Lemma reference_control_ready_6325 old :
 (exists value ground, VM.find 6314 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_6325.
Proof.
 intros H6314.
 destruct H6314 as [v6314 [G6314 [V6314 T6314]]].
 unfold reference_control_expr_6325.
apply rc_mux.
{ eapply rc_ref; [exact V6314|exists G6314; exact T6314].
}
{ apply rc_const.
}
Qed.
Lemma reference_control_member_6325 : List.In (6325,reference_control_expr_6325) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 191%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_6325_ground inputs path old current result :
 (exists value ground, VM.find 6314 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 6325 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H6314 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 6325 reference_control_expr_6325 reference_control_3_positions reference_control_3_safety reference_control_member_6325) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 6325 reference_control_expr_6325 inputs path old current result Position Safe Nonreg (reference_control_ready_6325 old H6314) Step).
Qed.
Theorem reference_control_node_6325_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 6314 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2357 left = VM.find 2357 right ->
 VM.find 6314 left = VM.find 6314 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 6325 next_left = VM.find 6325 next_right.
Proof.
 intros H6314 E2357 E6314 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 6325 reference_control_expr_6325 reference_control_3_positions reference_control_3_safety reference_control_member_6325) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 6325 reference_control_expr_6325 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_6325 left H6314)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_6325 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2357.
 rewrite E6314.
 reflexivity.
Qed.
Lemma reference_control_ready_6332 old :
 (exists value ground, VM.find 6323 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_6332.
Proof.
 intros H6323.
 destruct H6323 as [v6323 [G6323 [V6323 T6323]]].
 unfold reference_control_expr_6332.
apply rc_mux.
{ eapply rc_ref; [exact V6323|exists G6323; exact T6323].
}
{ apply rc_const.
}
Qed.
Lemma reference_control_member_6332 : List.In (6332,reference_control_expr_6332) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 192%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_6332_ground inputs path old current result :
 (exists value ground, VM.find 6323 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 6332 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H6323 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 6332 reference_control_expr_6332 reference_control_3_positions reference_control_3_safety reference_control_member_6332) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 6332 reference_control_expr_6332 inputs path old current result Position Safe Nonreg (reference_control_ready_6332 old H6323) Step).
Qed.
Theorem reference_control_node_6332_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 6323 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2357 left = VM.find 2357 right ->
 VM.find 6323 left = VM.find 6323 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 6332 next_left = VM.find 6332 next_right.
Proof.
 intros H6323 E2357 E6323 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 6332 reference_control_expr_6332 reference_control_3_positions reference_control_3_safety reference_control_member_6332) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 6332 reference_control_expr_6332 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_6332 left H6323)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_6332 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2357.
 rewrite E6323.
 reflexivity.
Qed.
Lemma reference_control_ready_6346 old :
 (exists value ground, VM.find 6325 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_6346.
Proof.
 intros H6325.
 destruct H6325 as [v6325 [G6325 [V6325 T6325]]].
 unfold reference_control_expr_6346.
apply rc_mux.
{ apply rc_const.
}
{ eapply rc_ref; [exact V6325|exists G6325; exact T6325].
}
Qed.
Lemma reference_control_member_6346 : List.In (6346,reference_control_expr_6346) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 193%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_6346_ground inputs path old current result :
 (exists value ground, VM.find 6325 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 6346 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H6325 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 6346 reference_control_expr_6346 reference_control_3_positions reference_control_3_safety reference_control_member_6346) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 6346 reference_control_expr_6346 inputs path old current result Position Safe Nonreg (reference_control_ready_6346 old H6325) Step).
Qed.
Theorem reference_control_node_6346_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 6325 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2949 left = VM.find 2949 right ->
 VM.find 6325 left = VM.find 6325 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 6346 next_left = VM.find 6346 next_right.
Proof.
 intros H6325 E2949 E6325 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 6346 reference_control_expr_6346 reference_control_3_positions reference_control_3_safety reference_control_member_6346) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 6346 reference_control_expr_6346 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_6346 left H6325)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_6346 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2949.
 rewrite E6325.
 reflexivity.
Qed.
Lemma reference_control_ready_6354 old :
 (exists value ground, VM.find 6332 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_6354.
Proof.
 intros H6332.
 destruct H6332 as [v6332 [G6332 [V6332 T6332]]].
 unfold reference_control_expr_6354.
apply rc_mux.
{ eapply rc_ref; [exact V6332|exists G6332; exact T6332].
}
{ apply rc_const.
}
Qed.
Lemma reference_control_member_6354 : List.In (6354,reference_control_expr_6354) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 194%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_6354_ground inputs path old current result :
 (exists value ground, VM.find 6332 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 6354 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H6332 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 6354 reference_control_expr_6354 reference_control_3_positions reference_control_3_safety reference_control_member_6354) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 6354 reference_control_expr_6354 inputs path old current result Position Safe Nonreg (reference_control_ready_6354 old H6332) Step).
Qed.
Theorem reference_control_node_6354_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 6332 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2949 left = VM.find 2949 right ->
 VM.find 6332 left = VM.find 6332 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 6354 next_left = VM.find 6354 next_right.
Proof.
 intros H6332 E2949 E6332 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 6354 reference_control_expr_6354 reference_control_3_positions reference_control_3_safety reference_control_member_6354) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 6354 reference_control_expr_6354 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_6354 left H6332)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_6354 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2949.
 rewrite E6332.
 reflexivity.
Qed.
Lemma reference_control_ready_6359 old :
 (exists value ground, VM.find 6325 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 6346 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_6359.
Proof.
 intros H6325 H6346.
 destruct H6325 as [v6325 [G6325 [V6325 T6325]]].
 destruct H6346 as [v6346 [G6346 [V6346 T6346]]].
 unfold reference_control_expr_6359.
apply rc_mux.
{ eapply rc_ref; [exact V6346|exists G6346; exact T6346].
}
{ eapply rc_ref; [exact V6325|exists G6325; exact T6325].
}
Qed.
Lemma reference_control_member_6359 : List.In (6359,reference_control_expr_6359) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 195%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_6359_ground inputs path old current result :
 (exists value ground, VM.find 6325 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 6346 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 6359 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H6325 H6346 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 6359 reference_control_expr_6359 reference_control_3_positions reference_control_3_safety reference_control_member_6359) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 6359 reference_control_expr_6359 inputs path old current result Position Safe Nonreg (reference_control_ready_6359 old H6325 H6346) Step).
Qed.
Theorem reference_control_node_6359_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 6325 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 6346 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2010 left = VM.find 2010 right ->
 VM.find 6325 left = VM.find 6325 right ->
 VM.find 6346 left = VM.find 6346 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 6359 next_left = VM.find 6359 next_right.
Proof.
 intros H6325 H6346 E2010 E6325 E6346 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 6359 reference_control_expr_6359 reference_control_3_positions reference_control_3_safety reference_control_member_6359) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 6359 reference_control_expr_6359 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_6359 left H6325 H6346)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_6359 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2010.
 rewrite E6325.
 rewrite E6346.
 reflexivity.
Qed.
Lemma reference_control_ready_6366 old :
 (exists value ground, VM.find 6332 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 6354 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_6366.
Proof.
 intros H6332 H6354.
 destruct H6332 as [v6332 [G6332 [V6332 T6332]]].
 destruct H6354 as [v6354 [G6354 [V6354 T6354]]].
 unfold reference_control_expr_6366.
apply rc_mux.
{ eapply rc_ref; [exact V6354|exists G6354; exact T6354].
}
{ eapply rc_ref; [exact V6332|exists G6332; exact T6332].
}
Qed.
Lemma reference_control_member_6366 : List.In (6366,reference_control_expr_6366) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 196%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_6366_ground inputs path old current result :
 (exists value ground, VM.find 6332 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 6354 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 6366 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H6332 H6354 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 6366 reference_control_expr_6366 reference_control_3_positions reference_control_3_safety reference_control_member_6366) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 6366 reference_control_expr_6366 inputs path old current result Position Safe Nonreg (reference_control_ready_6366 old H6332 H6354) Step).
Qed.
Theorem reference_control_node_6366_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 6332 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 6354 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2010 left = VM.find 2010 right ->
 VM.find 6332 left = VM.find 6332 right ->
 VM.find 6354 left = VM.find 6354 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 6366 next_left = VM.find 6366 next_right.
Proof.
 intros H6332 H6354 E2010 E6332 E6354 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 6366 reference_control_expr_6366 reference_control_3_positions reference_control_3_safety reference_control_member_6366) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 6366 reference_control_expr_6366 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_6366 left H6332 H6354)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_6366 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2010.
 rewrite E6332.
 rewrite E6354.
 reflexivity.
Qed.
Lemma reference_control_ready_6373 old :
 (exists value ground, VM.find 6359 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_6373.
Proof.
 intros H6359.
 destruct H6359 as [v6359 [G6359 [V6359 T6359]]].
 unfold reference_control_expr_6373.
apply rc_mux.
{ apply rc_const.
}
{ eapply rc_ref; [exact V6359|exists G6359; exact T6359].
}
Qed.
Lemma reference_control_member_6373 : List.In (6373,reference_control_expr_6373) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 197%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_6373_ground inputs path old current result :
 (exists value ground, VM.find 6359 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 6373 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H6359 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 6373 reference_control_expr_6373 reference_control_3_positions reference_control_3_safety reference_control_member_6373) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 6373 reference_control_expr_6373 inputs path old current result Position Safe Nonreg (reference_control_ready_6373 old H6359) Step).
Qed.
Theorem reference_control_node_6373_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 6359 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2929 left = VM.find 2929 right ->
 VM.find 6359 left = VM.find 6359 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 6373 next_left = VM.find 6373 next_right.
Proof.
 intros H6359 E2929 E6359 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 6373 reference_control_expr_6373 reference_control_3_positions reference_control_3_safety reference_control_member_6373) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 6373 reference_control_expr_6373 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_6373 left H6359)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_6373 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2929.
 rewrite E6359.
 reflexivity.
Qed.
Lemma reference_control_ready_6376 old :
 (exists value ground, VM.find 6366 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_6376.
Proof.
 intros H6366.
 destruct H6366 as [v6366 [G6366 [V6366 T6366]]].
 unfold reference_control_expr_6376.
apply rc_mux.
{ eapply rc_ref; [exact V6366|exists G6366; exact T6366].
}
{ apply rc_const.
}
Qed.
Lemma reference_control_member_6376 : List.In (6376,reference_control_expr_6376) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 198%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_6376_ground inputs path old current result :
 (exists value ground, VM.find 6366 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 6376 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H6366 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 6376 reference_control_expr_6376 reference_control_3_positions reference_control_3_safety reference_control_member_6376) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 6376 reference_control_expr_6376 inputs path old current result Position Safe Nonreg (reference_control_ready_6376 old H6366) Step).
Qed.
Theorem reference_control_node_6376_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 6366 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2929 left = VM.find 2929 right ->
 VM.find 6366 left = VM.find 6366 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 6376 next_left = VM.find 6376 next_right.
Proof.
 intros H6366 E2929 E6366 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 6376 reference_control_expr_6376 reference_control_3_positions reference_control_3_safety reference_control_member_6376) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 6376 reference_control_expr_6376 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_6376 left H6366)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_6376 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2929.
 rewrite E6366.
 reflexivity.
Qed.
Lemma reference_control_ready_6377 old :
 (exists value ground, VM.find 6359 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 6373 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_6377.
Proof.
 intros H6359 H6373.
 destruct H6359 as [v6359 [G6359 [V6359 T6359]]].
 destruct H6373 as [v6373 [G6373 [V6373 T6373]]].
 unfold reference_control_expr_6377.
apply rc_mux.
{ eapply rc_ref; [exact V6373|exists G6373; exact T6373].
}
{ eapply rc_ref; [exact V6359|exists G6359; exact T6359].
}
Qed.
Lemma reference_control_member_6377 : List.In (6377,reference_control_expr_6377) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 199%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_6377_ground inputs path old current result :
 (exists value ground, VM.find 6359 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 6373 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 6377 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H6359 H6373 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 6377 reference_control_expr_6377 reference_control_3_positions reference_control_3_safety reference_control_member_6377) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 6377 reference_control_expr_6377 inputs path old current result Position Safe Nonreg (reference_control_ready_6377 old H6359 H6373) Step).
Qed.
Theorem reference_control_node_6377_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 6359 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 6373 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2912 left = VM.find 2912 right ->
 VM.find 6359 left = VM.find 6359 right ->
 VM.find 6373 left = VM.find 6373 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 6377 next_left = VM.find 6377 next_right.
Proof.
 intros H6359 H6373 E2912 E6359 E6373 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 6377 reference_control_expr_6377 reference_control_3_positions reference_control_3_safety reference_control_member_6377) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 6377 reference_control_expr_6377 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_6377 left H6359 H6373)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_6377 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2912.
 rewrite E6359.
 rewrite E6373.
 reflexivity.
Qed.
Lemma reference_control_ready_6380 old :
 (exists value ground, VM.find 6366 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 6376 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_6380.
Proof.
 intros H6366 H6376.
 destruct H6366 as [v6366 [G6366 [V6366 T6366]]].
 destruct H6376 as [v6376 [G6376 [V6376 T6376]]].
 unfold reference_control_expr_6380.
apply rc_mux.
{ eapply rc_ref; [exact V6376|exists G6376; exact T6376].
}
{ eapply rc_ref; [exact V6366|exists G6366; exact T6366].
}
Qed.
Lemma reference_control_member_6380 : List.In (6380,reference_control_expr_6380) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 200%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_6380_ground inputs path old current result :
 (exists value ground, VM.find 6366 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 6376 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 6380 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H6366 H6376 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 6380 reference_control_expr_6380 reference_control_3_positions reference_control_3_safety reference_control_member_6380) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 6380 reference_control_expr_6380 inputs path old current result Position Safe Nonreg (reference_control_ready_6380 old H6366 H6376) Step).
Qed.
Theorem reference_control_node_6380_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 6366 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 6376 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2912 left = VM.find 2912 right ->
 VM.find 6366 left = VM.find 6366 right ->
 VM.find 6376 left = VM.find 6376 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 6380 next_left = VM.find 6380 next_right.
Proof.
 intros H6366 H6376 E2912 E6366 E6376 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 6380 reference_control_expr_6380 reference_control_3_positions reference_control_3_safety reference_control_member_6380) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 6380 reference_control_expr_6380 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_6380 left H6366 H6376)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_6380 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2912.
 rewrite E6366.
 rewrite E6376.
 reflexivity.
Qed.
Lemma reference_control_ready_6387 old :
 (exists value ground, VM.find 6359 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 6377 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_6387.
Proof.
 intros H6359 H6377.
 destruct H6359 as [v6359 [G6359 [V6359 T6359]]].
 destruct H6377 as [v6377 [G6377 [V6377 T6377]]].
 unfold reference_control_expr_6387.
apply rc_mux.
{ eapply rc_ref; [exact V6377|exists G6377; exact T6377].
}
{ eapply rc_ref; [exact V6359|exists G6359; exact T6359].
}
Qed.
Lemma reference_control_member_6387 : List.In (6387,reference_control_expr_6387) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 201%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_6387_ground inputs path old current result :
 (exists value ground, VM.find 6359 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 6377 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 6387 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H6359 H6377 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 6387 reference_control_expr_6387 reference_control_3_positions reference_control_3_safety reference_control_member_6387) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 6387 reference_control_expr_6387 inputs path old current result Position Safe Nonreg (reference_control_ready_6387 old H6359 H6377) Step).
Qed.
Theorem reference_control_node_6387_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 6359 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 6377 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2004 left = VM.find 2004 right ->
 VM.find 6359 left = VM.find 6359 right ->
 VM.find 6377 left = VM.find 6377 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 6387 next_left = VM.find 6387 next_right.
Proof.
 intros H6359 H6377 E2004 E6359 E6377 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 6387 reference_control_expr_6387 reference_control_3_positions reference_control_3_safety reference_control_member_6387) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 6387 reference_control_expr_6387 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_6387 left H6359 H6377)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_6387 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2004.
 rewrite E6359.
 rewrite E6377.
 reflexivity.
Qed.
Lemma reference_control_ready_6390 old :
 (exists value ground, VM.find 6366 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 6380 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_6390.
Proof.
 intros H6366 H6380.
 destruct H6366 as [v6366 [G6366 [V6366 T6366]]].
 destruct H6380 as [v6380 [G6380 [V6380 T6380]]].
 unfold reference_control_expr_6390.
apply rc_mux.
{ eapply rc_ref; [exact V6380|exists G6380; exact T6380].
}
{ eapply rc_ref; [exact V6366|exists G6366; exact T6366].
}
Qed.
Lemma reference_control_member_6390 : List.In (6390,reference_control_expr_6390) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 202%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_6390_ground inputs path old current result :
 (exists value ground, VM.find 6366 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 6380 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 6390 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H6366 H6380 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 6390 reference_control_expr_6390 reference_control_3_positions reference_control_3_safety reference_control_member_6390) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 6390 reference_control_expr_6390 inputs path old current result Position Safe Nonreg (reference_control_ready_6390 old H6366 H6380) Step).
Qed.
Theorem reference_control_node_6390_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 6366 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 6380 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2004 left = VM.find 2004 right ->
 VM.find 6366 left = VM.find 6366 right ->
 VM.find 6380 left = VM.find 6380 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 6390 next_left = VM.find 6390 next_right.
Proof.
 intros H6366 H6380 E2004 E6366 E6380 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 6390 reference_control_expr_6390 reference_control_3_positions reference_control_3_safety reference_control_member_6390) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 6390 reference_control_expr_6390 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_6390 left H6366 H6380)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_6390 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2004.
 rewrite E6366.
 rewrite E6380.
 reflexivity.
Qed.
Lemma reference_control_ready_6397 old :
 (exists value ground, VM.find 6387 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_6397.
Proof.
 intros H6387.
 destruct H6387 as [v6387 [G6387 [V6387 T6387]]].
 unfold reference_control_expr_6397.
apply rc_mux.
{ apply rc_const.
}
{ eapply rc_ref; [exact V6387|exists G6387; exact T6387].
}
Qed.
Lemma reference_control_member_6397 : List.In (6397,reference_control_expr_6397) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 203%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_6397_ground inputs path old current result :
 (exists value ground, VM.find 6387 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 6397 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H6387 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 6397 reference_control_expr_6397 reference_control_3_positions reference_control_3_safety reference_control_member_6397) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 6397 reference_control_expr_6397 inputs path old current result Position Safe Nonreg (reference_control_ready_6397 old H6387) Step).
Qed.
Theorem reference_control_node_6397_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 6387 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2909 left = VM.find 2909 right ->
 VM.find 6387 left = VM.find 6387 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 6397 next_left = VM.find 6397 next_right.
Proof.
 intros H6387 E2909 E6387 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 6397 reference_control_expr_6397 reference_control_3_positions reference_control_3_safety reference_control_member_6397) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 6397 reference_control_expr_6397 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_6397 left H6387)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_6397 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2909.
 rewrite E6387.
 reflexivity.
Qed.
Lemma reference_control_ready_6400 old :
 (exists value ground, VM.find 6390 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_6400.
Proof.
 intros H6390.
 destruct H6390 as [v6390 [G6390 [V6390 T6390]]].
 unfold reference_control_expr_6400.
apply rc_mux.
{ eapply rc_ref; [exact V6390|exists G6390; exact T6390].
}
{ apply rc_const.
}
Qed.
Lemma reference_control_member_6400 : List.In (6400,reference_control_expr_6400) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 204%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_6400_ground inputs path old current result :
 (exists value ground, VM.find 6390 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 6400 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H6390 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 6400 reference_control_expr_6400 reference_control_3_positions reference_control_3_safety reference_control_member_6400) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 6400 reference_control_expr_6400 inputs path old current result Position Safe Nonreg (reference_control_ready_6400 old H6390) Step).
Qed.
Theorem reference_control_node_6400_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 6390 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2909 left = VM.find 2909 right ->
 VM.find 6390 left = VM.find 6390 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 6400 next_left = VM.find 6400 next_right.
Proof.
 intros H6390 E2909 E6390 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 6400 reference_control_expr_6400 reference_control_3_positions reference_control_3_safety reference_control_member_6400) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 6400 reference_control_expr_6400 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_6400 left H6390)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_6400 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2909.
 rewrite E6390.
 reflexivity.
Qed.
Lemma reference_control_ready_6401 old :
 (exists value ground, VM.find 6387 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 6397 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_6401.
Proof.
 intros H6387 H6397.
 destruct H6387 as [v6387 [G6387 [V6387 T6387]]].
 destruct H6397 as [v6397 [G6397 [V6397 T6397]]].
 unfold reference_control_expr_6401.
apply rc_mux.
{ eapply rc_ref; [exact V6397|exists G6397; exact T6397].
}
{ eapply rc_ref; [exact V6387|exists G6387; exact T6387].
}
Qed.
Lemma reference_control_member_6401 : List.In (6401,reference_control_expr_6401) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 205%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_6401_ground inputs path old current result :
 (exists value ground, VM.find 6387 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 6397 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 6401 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H6387 H6397 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 6401 reference_control_expr_6401 reference_control_3_positions reference_control_3_safety reference_control_member_6401) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 6401 reference_control_expr_6401 inputs path old current result Position Safe Nonreg (reference_control_ready_6401 old H6387 H6397) Step).
Qed.
Theorem reference_control_node_6401_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 6387 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 6397 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2892 left = VM.find 2892 right ->
 VM.find 6387 left = VM.find 6387 right ->
 VM.find 6397 left = VM.find 6397 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 6401 next_left = VM.find 6401 next_right.
Proof.
 intros H6387 H6397 E2892 E6387 E6397 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 6401 reference_control_expr_6401 reference_control_3_positions reference_control_3_safety reference_control_member_6401) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 6401 reference_control_expr_6401 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_6401 left H6387 H6397)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_6401 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2892.
 rewrite E6387.
 rewrite E6397.
 reflexivity.
Qed.
Lemma reference_control_ready_6404 old :
 (exists value ground, VM.find 6390 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 6400 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_6404.
Proof.
 intros H6390 H6400.
 destruct H6390 as [v6390 [G6390 [V6390 T6390]]].
 destruct H6400 as [v6400 [G6400 [V6400 T6400]]].
 unfold reference_control_expr_6404.
apply rc_mux.
{ eapply rc_ref; [exact V6400|exists G6400; exact T6400].
}
{ eapply rc_ref; [exact V6390|exists G6390; exact T6390].
}
Qed.
Lemma reference_control_member_6404 : List.In (6404,reference_control_expr_6404) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 206%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_6404_ground inputs path old current result :
 (exists value ground, VM.find 6390 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 6400 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 6404 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H6390 H6400 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 6404 reference_control_expr_6404 reference_control_3_positions reference_control_3_safety reference_control_member_6404) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 6404 reference_control_expr_6404 inputs path old current result Position Safe Nonreg (reference_control_ready_6404 old H6390 H6400) Step).
Qed.
Theorem reference_control_node_6404_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 6390 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 6400 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2892 left = VM.find 2892 right ->
 VM.find 6390 left = VM.find 6390 right ->
 VM.find 6400 left = VM.find 6400 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 6404 next_left = VM.find 6404 next_right.
Proof.
 intros H6390 H6400 E2892 E6390 E6400 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 6404 reference_control_expr_6404 reference_control_3_positions reference_control_3_safety reference_control_member_6404) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 6404 reference_control_expr_6404 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_6404 left H6390 H6400)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_6404 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2892.
 rewrite E6390.
 rewrite E6400.
 reflexivity.
Qed.
Lemma reference_control_ready_6411 old :
 (exists value ground, VM.find 6387 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 6401 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_6411.
Proof.
 intros H6387 H6401.
 destruct H6387 as [v6387 [G6387 [V6387 T6387]]].
 destruct H6401 as [v6401 [G6401 [V6401 T6401]]].
 unfold reference_control_expr_6411.
apply rc_mux.
{ eapply rc_ref; [exact V6401|exists G6401; exact T6401].
}
{ eapply rc_ref; [exact V6387|exists G6387; exact T6387].
}
Qed.
Lemma reference_control_member_6411 : List.In (6411,reference_control_expr_6411) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 207%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_6411_ground inputs path old current result :
 (exists value ground, VM.find 6387 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 6401 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 6411 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H6387 H6401 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 6411 reference_control_expr_6411 reference_control_3_positions reference_control_3_safety reference_control_member_6411) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 6411 reference_control_expr_6411 inputs path old current result Position Safe Nonreg (reference_control_ready_6411 old H6387 H6401) Step).
Qed.
Theorem reference_control_node_6411_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 6387 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 6401 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1998 left = VM.find 1998 right ->
 VM.find 6387 left = VM.find 6387 right ->
 VM.find 6401 left = VM.find 6401 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 6411 next_left = VM.find 6411 next_right.
Proof.
 intros H6387 H6401 E1998 E6387 E6401 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 6411 reference_control_expr_6411 reference_control_3_positions reference_control_3_safety reference_control_member_6411) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 6411 reference_control_expr_6411 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_6411 left H6387 H6401)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_6411 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1998.
 rewrite E6387.
 rewrite E6401.
 reflexivity.
Qed.
Lemma reference_control_ready_6414 old :
 (exists value ground, VM.find 6390 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 6404 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_6414.
Proof.
 intros H6390 H6404.
 destruct H6390 as [v6390 [G6390 [V6390 T6390]]].
 destruct H6404 as [v6404 [G6404 [V6404 T6404]]].
 unfold reference_control_expr_6414.
apply rc_mux.
{ eapply rc_ref; [exact V6404|exists G6404; exact T6404].
}
{ eapply rc_ref; [exact V6390|exists G6390; exact T6390].
}
Qed.
Lemma reference_control_member_6414 : List.In (6414,reference_control_expr_6414) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 208%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_6414_ground inputs path old current result :
 (exists value ground, VM.find 6390 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 6404 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 6414 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H6390 H6404 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 6414 reference_control_expr_6414 reference_control_3_positions reference_control_3_safety reference_control_member_6414) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 6414 reference_control_expr_6414 inputs path old current result Position Safe Nonreg (reference_control_ready_6414 old H6390 H6404) Step).
Qed.
Theorem reference_control_node_6414_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 6390 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 6404 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1998 left = VM.find 1998 right ->
 VM.find 6390 left = VM.find 6390 right ->
 VM.find 6404 left = VM.find 6404 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 6414 next_left = VM.find 6414 next_right.
Proof.
 intros H6390 H6404 E1998 E6390 E6404 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 6414 reference_control_expr_6414 reference_control_3_positions reference_control_3_safety reference_control_member_6414) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 6414 reference_control_expr_6414 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_6414 left H6390 H6404)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_6414 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1998.
 rewrite E6390.
 rewrite E6404.
 reflexivity.
Qed.
Lemma reference_control_ready_6421 old :
 (exists value ground, VM.find 6411 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_6421.
Proof.
 intros H6411.
 destruct H6411 as [v6411 [G6411 [V6411 T6411]]].
 unfold reference_control_expr_6421.
apply rc_mux.
{ apply rc_const.
}
{ eapply rc_ref; [exact V6411|exists G6411; exact T6411].
}
Qed.
Lemma reference_control_member_6421 : List.In (6421,reference_control_expr_6421) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 209%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_6421_ground inputs path old current result :
 (exists value ground, VM.find 6411 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 6421 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H6411 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 6421 reference_control_expr_6421 reference_control_3_positions reference_control_3_safety reference_control_member_6421) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 6421 reference_control_expr_6421 inputs path old current result Position Safe Nonreg (reference_control_ready_6421 old H6411) Step).
Qed.
Theorem reference_control_node_6421_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 6411 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2889 left = VM.find 2889 right ->
 VM.find 6411 left = VM.find 6411 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 6421 next_left = VM.find 6421 next_right.
Proof.
 intros H6411 E2889 E6411 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 6421 reference_control_expr_6421 reference_control_3_positions reference_control_3_safety reference_control_member_6421) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 6421 reference_control_expr_6421 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_6421 left H6411)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_6421 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2889.
 rewrite E6411.
 reflexivity.
Qed.
Lemma reference_control_ready_6424 old :
 (exists value ground, VM.find 6414 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_6424.
Proof.
 intros H6414.
 destruct H6414 as [v6414 [G6414 [V6414 T6414]]].
 unfold reference_control_expr_6424.
apply rc_mux.
{ eapply rc_ref; [exact V6414|exists G6414; exact T6414].
}
{ apply rc_const.
}
Qed.
Lemma reference_control_member_6424 : List.In (6424,reference_control_expr_6424) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 210%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_6424_ground inputs path old current result :
 (exists value ground, VM.find 6414 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 6424 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H6414 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 6424 reference_control_expr_6424 reference_control_3_positions reference_control_3_safety reference_control_member_6424) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 6424 reference_control_expr_6424 inputs path old current result Position Safe Nonreg (reference_control_ready_6424 old H6414) Step).
Qed.
Theorem reference_control_node_6424_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 6414 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2889 left = VM.find 2889 right ->
 VM.find 6414 left = VM.find 6414 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 6424 next_left = VM.find 6424 next_right.
Proof.
 intros H6414 E2889 E6414 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 6424 reference_control_expr_6424 reference_control_3_positions reference_control_3_safety reference_control_member_6424) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 6424 reference_control_expr_6424 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_6424 left H6414)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_6424 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2889.
 rewrite E6414.
 reflexivity.
Qed.
Lemma reference_control_ready_6425 old :
 (exists value ground, VM.find 6411 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 6421 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_6425.
Proof.
 intros H6411 H6421.
 destruct H6411 as [v6411 [G6411 [V6411 T6411]]].
 destruct H6421 as [v6421 [G6421 [V6421 T6421]]].
 unfold reference_control_expr_6425.
apply rc_mux.
{ eapply rc_ref; [exact V6421|exists G6421; exact T6421].
}
{ eapply rc_ref; [exact V6411|exists G6411; exact T6411].
}
Qed.
Lemma reference_control_member_6425 : List.In (6425,reference_control_expr_6425) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 211%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_6425_ground inputs path old current result :
 (exists value ground, VM.find 6411 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 6421 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 6425 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H6411 H6421 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 6425 reference_control_expr_6425 reference_control_3_positions reference_control_3_safety reference_control_member_6425) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 6425 reference_control_expr_6425 inputs path old current result Position Safe Nonreg (reference_control_ready_6425 old H6411 H6421) Step).
Qed.
Theorem reference_control_node_6425_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 6411 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 6421 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2872 left = VM.find 2872 right ->
 VM.find 6411 left = VM.find 6411 right ->
 VM.find 6421 left = VM.find 6421 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 6425 next_left = VM.find 6425 next_right.
Proof.
 intros H6411 H6421 E2872 E6411 E6421 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 6425 reference_control_expr_6425 reference_control_3_positions reference_control_3_safety reference_control_member_6425) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 6425 reference_control_expr_6425 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_6425 left H6411 H6421)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_6425 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2872.
 rewrite E6411.
 rewrite E6421.
 reflexivity.
Qed.
Lemma reference_control_ready_6428 old :
 (exists value ground, VM.find 6414 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 6424 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_6428.
Proof.
 intros H6414 H6424.
 destruct H6414 as [v6414 [G6414 [V6414 T6414]]].
 destruct H6424 as [v6424 [G6424 [V6424 T6424]]].
 unfold reference_control_expr_6428.
apply rc_mux.
{ eapply rc_ref; [exact V6424|exists G6424; exact T6424].
}
{ eapply rc_ref; [exact V6414|exists G6414; exact T6414].
}
Qed.
Lemma reference_control_member_6428 : List.In (6428,reference_control_expr_6428) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 212%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_6428_ground inputs path old current result :
 (exists value ground, VM.find 6414 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 6424 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 6428 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H6414 H6424 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 6428 reference_control_expr_6428 reference_control_3_positions reference_control_3_safety reference_control_member_6428) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 6428 reference_control_expr_6428 inputs path old current result Position Safe Nonreg (reference_control_ready_6428 old H6414 H6424) Step).
Qed.
Theorem reference_control_node_6428_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 6414 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 6424 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2872 left = VM.find 2872 right ->
 VM.find 6414 left = VM.find 6414 right ->
 VM.find 6424 left = VM.find 6424 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 6428 next_left = VM.find 6428 next_right.
Proof.
 intros H6414 H6424 E2872 E6414 E6424 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 6428 reference_control_expr_6428 reference_control_3_positions reference_control_3_safety reference_control_member_6428) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 6428 reference_control_expr_6428 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_6428 left H6414 H6424)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_6428 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2872.
 rewrite E6414.
 rewrite E6424.
 reflexivity.
Qed.
Lemma reference_control_ready_6435 old :
 (exists value ground, VM.find 6411 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 6425 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_6435.
Proof.
 intros H6411 H6425.
 destruct H6411 as [v6411 [G6411 [V6411 T6411]]].
 destruct H6425 as [v6425 [G6425 [V6425 T6425]]].
 unfold reference_control_expr_6435.
apply rc_mux.
{ eapply rc_ref; [exact V6425|exists G6425; exact T6425].
}
{ eapply rc_ref; [exact V6411|exists G6411; exact T6411].
}
Qed.
Lemma reference_control_member_6435 : List.In (6435,reference_control_expr_6435) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 213%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_6435_ground inputs path old current result :
 (exists value ground, VM.find 6411 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 6425 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 6435 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H6411 H6425 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 6435 reference_control_expr_6435 reference_control_3_positions reference_control_3_safety reference_control_member_6435) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 6435 reference_control_expr_6435 inputs path old current result Position Safe Nonreg (reference_control_ready_6435 old H6411 H6425) Step).
Qed.
Theorem reference_control_node_6435_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 6411 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 6425 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1992 left = VM.find 1992 right ->
 VM.find 6411 left = VM.find 6411 right ->
 VM.find 6425 left = VM.find 6425 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 6435 next_left = VM.find 6435 next_right.
Proof.
 intros H6411 H6425 E1992 E6411 E6425 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 6435 reference_control_expr_6435 reference_control_3_positions reference_control_3_safety reference_control_member_6435) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 6435 reference_control_expr_6435 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_6435 left H6411 H6425)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_6435 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1992.
 rewrite E6411.
 rewrite E6425.
 reflexivity.
Qed.
Lemma reference_control_ready_6438 old :
 (exists value ground, VM.find 6414 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 6428 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_6438.
Proof.
 intros H6414 H6428.
 destruct H6414 as [v6414 [G6414 [V6414 T6414]]].
 destruct H6428 as [v6428 [G6428 [V6428 T6428]]].
 unfold reference_control_expr_6438.
apply rc_mux.
{ eapply rc_ref; [exact V6428|exists G6428; exact T6428].
}
{ eapply rc_ref; [exact V6414|exists G6414; exact T6414].
}
Qed.
Lemma reference_control_member_6438 : List.In (6438,reference_control_expr_6438) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 214%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_6438_ground inputs path old current result :
 (exists value ground, VM.find 6414 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 6428 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 6438 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H6414 H6428 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 6438 reference_control_expr_6438 reference_control_3_positions reference_control_3_safety reference_control_member_6438) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 6438 reference_control_expr_6438 inputs path old current result Position Safe Nonreg (reference_control_ready_6438 old H6414 H6428) Step).
Qed.
Theorem reference_control_node_6438_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 6414 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 6428 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1992 left = VM.find 1992 right ->
 VM.find 6414 left = VM.find 6414 right ->
 VM.find 6428 left = VM.find 6428 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 6438 next_left = VM.find 6438 next_right.
Proof.
 intros H6414 H6428 E1992 E6414 E6428 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 6438 reference_control_expr_6438 reference_control_3_positions reference_control_3_safety reference_control_member_6438) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 6438 reference_control_expr_6438 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_6438 left H6414 H6428)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_6438 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1992.
 rewrite E6414.
 rewrite E6428.
 reflexivity.
Qed.
Lemma reference_control_ready_6445 old :
 (exists value ground, VM.find 6435 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_6445.
Proof.
 intros H6435.
 destruct H6435 as [v6435 [G6435 [V6435 T6435]]].
 unfold reference_control_expr_6445.
apply rc_mux.
{ apply rc_const.
}
{ eapply rc_ref; [exact V6435|exists G6435; exact T6435].
}
Qed.
Lemma reference_control_member_6445 : List.In (6445,reference_control_expr_6445) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 215%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_6445_ground inputs path old current result :
 (exists value ground, VM.find 6435 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 6445 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H6435 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 6445 reference_control_expr_6445 reference_control_3_positions reference_control_3_safety reference_control_member_6445) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 6445 reference_control_expr_6445 inputs path old current result Position Safe Nonreg (reference_control_ready_6445 old H6435) Step).
Qed.
Theorem reference_control_node_6445_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 6435 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2867 left = VM.find 2867 right ->
 VM.find 6435 left = VM.find 6435 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 6445 next_left = VM.find 6445 next_right.
Proof.
 intros H6435 E2867 E6435 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 6445 reference_control_expr_6445 reference_control_3_positions reference_control_3_safety reference_control_member_6445) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 6445 reference_control_expr_6445 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_6445 left H6435)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_6445 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2867.
 rewrite E6435.
 reflexivity.
Qed.
Lemma reference_control_ready_6448 old :
 (exists value ground, VM.find 6438 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_6448.
Proof.
 intros H6438.
 destruct H6438 as [v6438 [G6438 [V6438 T6438]]].
 unfold reference_control_expr_6448.
apply rc_mux.
{ eapply rc_ref; [exact V6438|exists G6438; exact T6438].
}
{ apply rc_const.
}
Qed.
Lemma reference_control_member_6448 : List.In (6448,reference_control_expr_6448) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 216%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_6448_ground inputs path old current result :
 (exists value ground, VM.find 6438 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 6448 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H6438 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 6448 reference_control_expr_6448 reference_control_3_positions reference_control_3_safety reference_control_member_6448) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 6448 reference_control_expr_6448 inputs path old current result Position Safe Nonreg (reference_control_ready_6448 old H6438) Step).
Qed.
Theorem reference_control_node_6448_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 6438 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2867 left = VM.find 2867 right ->
 VM.find 6438 left = VM.find 6438 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 6448 next_left = VM.find 6448 next_right.
Proof.
 intros H6438 E2867 E6438 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 6448 reference_control_expr_6448 reference_control_3_positions reference_control_3_safety reference_control_member_6448) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 6448 reference_control_expr_6448 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_6448 left H6438)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_6448 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2867.
 rewrite E6438.
 reflexivity.
Qed.
Lemma reference_control_ready_6449 old :
 (exists value ground, VM.find 6435 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 6445 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_6449.
Proof.
 intros H6435 H6445.
 destruct H6435 as [v6435 [G6435 [V6435 T6435]]].
 destruct H6445 as [v6445 [G6445 [V6445 T6445]]].
 unfold reference_control_expr_6449.
apply rc_mux.
{ eapply rc_ref; [exact V6445|exists G6445; exact T6445].
}
{ eapply rc_ref; [exact V6435|exists G6435; exact T6435].
}
Qed.
Lemma reference_control_member_6449 : List.In (6449,reference_control_expr_6449) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 217%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_6449_ground inputs path old current result :
 (exists value ground, VM.find 6435 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 6445 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 6449 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H6435 H6445 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 6449 reference_control_expr_6449 reference_control_3_positions reference_control_3_safety reference_control_member_6449) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 6449 reference_control_expr_6449 inputs path old current result Position Safe Nonreg (reference_control_ready_6449 old H6435 H6445) Step).
Qed.
Theorem reference_control_node_6449_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 6435 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 6445 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2850 left = VM.find 2850 right ->
 VM.find 6435 left = VM.find 6435 right ->
 VM.find 6445 left = VM.find 6445 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 6449 next_left = VM.find 6449 next_right.
Proof.
 intros H6435 H6445 E2850 E6435 E6445 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 6449 reference_control_expr_6449 reference_control_3_positions reference_control_3_safety reference_control_member_6449) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 6449 reference_control_expr_6449 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_6449 left H6435 H6445)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_6449 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2850.
 rewrite E6435.
 rewrite E6445.
 reflexivity.
Qed.
Lemma reference_control_ready_6452 old :
 (exists value ground, VM.find 6438 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 6448 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_6452.
Proof.
 intros H6438 H6448.
 destruct H6438 as [v6438 [G6438 [V6438 T6438]]].
 destruct H6448 as [v6448 [G6448 [V6448 T6448]]].
 unfold reference_control_expr_6452.
apply rc_mux.
{ eapply rc_ref; [exact V6448|exists G6448; exact T6448].
}
{ eapply rc_ref; [exact V6438|exists G6438; exact T6438].
}
Qed.
Lemma reference_control_member_6452 : List.In (6452,reference_control_expr_6452) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 218%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_6452_ground inputs path old current result :
 (exists value ground, VM.find 6438 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 6448 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 6452 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H6438 H6448 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 6452 reference_control_expr_6452 reference_control_3_positions reference_control_3_safety reference_control_member_6452) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 6452 reference_control_expr_6452 inputs path old current result Position Safe Nonreg (reference_control_ready_6452 old H6438 H6448) Step).
Qed.
Theorem reference_control_node_6452_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 6438 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 6448 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2850 left = VM.find 2850 right ->
 VM.find 6438 left = VM.find 6438 right ->
 VM.find 6448 left = VM.find 6448 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 6452 next_left = VM.find 6452 next_right.
Proof.
 intros H6438 H6448 E2850 E6438 E6448 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 6452 reference_control_expr_6452 reference_control_3_positions reference_control_3_safety reference_control_member_6452) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 6452 reference_control_expr_6452 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_6452 left H6438 H6448)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_6452 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2850.
 rewrite E6438.
 rewrite E6448.
 reflexivity.
Qed.
Lemma reference_control_ready_6459 old :
 (exists value ground, VM.find 6435 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 6449 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_6459.
Proof.
 intros H6435 H6449.
 destruct H6435 as [v6435 [G6435 [V6435 T6435]]].
 destruct H6449 as [v6449 [G6449 [V6449 T6449]]].
 unfold reference_control_expr_6459.
apply rc_mux.
{ eapply rc_ref; [exact V6449|exists G6449; exact T6449].
}
{ eapply rc_ref; [exact V6435|exists G6435; exact T6435].
}
Qed.
Lemma reference_control_member_6459 : List.In (6459,reference_control_expr_6459) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 219%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_6459_ground inputs path old current result :
 (exists value ground, VM.find 6435 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 6449 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 6459 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H6435 H6449 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 6459 reference_control_expr_6459 reference_control_3_positions reference_control_3_safety reference_control_member_6459) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 6459 reference_control_expr_6459 inputs path old current result Position Safe Nonreg (reference_control_ready_6459 old H6435 H6449) Step).
Qed.
Theorem reference_control_node_6459_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 6435 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 6449 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1986 left = VM.find 1986 right ->
 VM.find 6435 left = VM.find 6435 right ->
 VM.find 6449 left = VM.find 6449 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 6459 next_left = VM.find 6459 next_right.
Proof.
 intros H6435 H6449 E1986 E6435 E6449 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 6459 reference_control_expr_6459 reference_control_3_positions reference_control_3_safety reference_control_member_6459) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 6459 reference_control_expr_6459 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_6459 left H6435 H6449)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_6459 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1986.
 rewrite E6435.
 rewrite E6449.
 reflexivity.
Qed.
Lemma reference_control_ready_6462 old :
 (exists value ground, VM.find 6438 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 6452 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_6462.
Proof.
 intros H6438 H6452.
 destruct H6438 as [v6438 [G6438 [V6438 T6438]]].
 destruct H6452 as [v6452 [G6452 [V6452 T6452]]].
 unfold reference_control_expr_6462.
apply rc_mux.
{ eapply rc_ref; [exact V6452|exists G6452; exact T6452].
}
{ eapply rc_ref; [exact V6438|exists G6438; exact T6438].
}
Qed.
Lemma reference_control_member_6462 : List.In (6462,reference_control_expr_6462) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 220%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_6462_ground inputs path old current result :
 (exists value ground, VM.find 6438 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 6452 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 6462 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H6438 H6452 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 6462 reference_control_expr_6462 reference_control_3_positions reference_control_3_safety reference_control_member_6462) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 6462 reference_control_expr_6462 inputs path old current result Position Safe Nonreg (reference_control_ready_6462 old H6438 H6452) Step).
Qed.
Theorem reference_control_node_6462_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 6438 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 6452 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1986 left = VM.find 1986 right ->
 VM.find 6438 left = VM.find 6438 right ->
 VM.find 6452 left = VM.find 6452 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 6462 next_left = VM.find 6462 next_right.
Proof.
 intros H6438 H6452 E1986 E6438 E6452 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 6462 reference_control_expr_6462 reference_control_3_positions reference_control_3_safety reference_control_member_6462) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 6462 reference_control_expr_6462 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_6462 left H6438 H6452)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_6462 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1986.
 rewrite E6438.
 rewrite E6452.
 reflexivity.
Qed.
Lemma reference_control_ready_6469 old :
 (exists value ground, VM.find 6459 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_6469.
Proof.
 intros H6459.
 destruct H6459 as [v6459 [G6459 [V6459 T6459]]].
 unfold reference_control_expr_6469.
apply rc_mux.
{ apply rc_const.
}
{ eapply rc_ref; [exact V6459|exists G6459; exact T6459].
}
Qed.
Lemma reference_control_member_6469 : List.In (6469,reference_control_expr_6469) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 221%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_6469_ground inputs path old current result :
 (exists value ground, VM.find 6459 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 6469 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H6459 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 6469 reference_control_expr_6469 reference_control_3_positions reference_control_3_safety reference_control_member_6469) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 6469 reference_control_expr_6469 inputs path old current result Position Safe Nonreg (reference_control_ready_6469 old H6459) Step).
Qed.
Theorem reference_control_node_6469_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 6459 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2847 left = VM.find 2847 right ->
 VM.find 6459 left = VM.find 6459 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 6469 next_left = VM.find 6469 next_right.
Proof.
 intros H6459 E2847 E6459 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 6469 reference_control_expr_6469 reference_control_3_positions reference_control_3_safety reference_control_member_6469) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 6469 reference_control_expr_6469 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_6469 left H6459)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_6469 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2847.
 rewrite E6459.
 reflexivity.
Qed.
Lemma reference_control_ready_6472 old :
 (exists value ground, VM.find 6462 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_6472.
Proof.
 intros H6462.
 destruct H6462 as [v6462 [G6462 [V6462 T6462]]].
 unfold reference_control_expr_6472.
apply rc_mux.
{ eapply rc_ref; [exact V6462|exists G6462; exact T6462].
}
{ apply rc_const.
}
Qed.
Lemma reference_control_member_6472 : List.In (6472,reference_control_expr_6472) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 222%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_6472_ground inputs path old current result :
 (exists value ground, VM.find 6462 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 6472 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H6462 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 6472 reference_control_expr_6472 reference_control_3_positions reference_control_3_safety reference_control_member_6472) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 6472 reference_control_expr_6472 inputs path old current result Position Safe Nonreg (reference_control_ready_6472 old H6462) Step).
Qed.
Theorem reference_control_node_6472_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 6462 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2847 left = VM.find 2847 right ->
 VM.find 6462 left = VM.find 6462 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 6472 next_left = VM.find 6472 next_right.
Proof.
 intros H6462 E2847 E6462 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 6472 reference_control_expr_6472 reference_control_3_positions reference_control_3_safety reference_control_member_6472) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 6472 reference_control_expr_6472 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_6472 left H6462)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_6472 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2847.
 rewrite E6462.
 reflexivity.
Qed.
Lemma reference_control_ready_6473 old :
 (exists value ground, VM.find 6459 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 6469 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_6473.
Proof.
 intros H6459 H6469.
 destruct H6459 as [v6459 [G6459 [V6459 T6459]]].
 destruct H6469 as [v6469 [G6469 [V6469 T6469]]].
 unfold reference_control_expr_6473.
apply rc_mux.
{ eapply rc_ref; [exact V6469|exists G6469; exact T6469].
}
{ eapply rc_ref; [exact V6459|exists G6459; exact T6459].
}
Qed.
Lemma reference_control_member_6473 : List.In (6473,reference_control_expr_6473) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 223%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_6473_ground inputs path old current result :
 (exists value ground, VM.find 6459 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 6469 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 6473 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H6459 H6469 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 6473 reference_control_expr_6473 reference_control_3_positions reference_control_3_safety reference_control_member_6473) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 6473 reference_control_expr_6473 inputs path old current result Position Safe Nonreg (reference_control_ready_6473 old H6459 H6469) Step).
Qed.
Theorem reference_control_node_6473_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 6459 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 6469 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2830 left = VM.find 2830 right ->
 VM.find 6459 left = VM.find 6459 right ->
 VM.find 6469 left = VM.find 6469 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 6473 next_left = VM.find 6473 next_right.
Proof.
 intros H6459 H6469 E2830 E6459 E6469 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 6473 reference_control_expr_6473 reference_control_3_positions reference_control_3_safety reference_control_member_6473) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 6473 reference_control_expr_6473 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_6473 left H6459 H6469)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_6473 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2830.
 rewrite E6459.
 rewrite E6469.
 reflexivity.
Qed.
Lemma reference_control_ready_6476 old :
 (exists value ground, VM.find 6462 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 6472 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_6476.
Proof.
 intros H6462 H6472.
 destruct H6462 as [v6462 [G6462 [V6462 T6462]]].
 destruct H6472 as [v6472 [G6472 [V6472 T6472]]].
 unfold reference_control_expr_6476.
apply rc_mux.
{ eapply rc_ref; [exact V6472|exists G6472; exact T6472].
}
{ eapply rc_ref; [exact V6462|exists G6462; exact T6462].
}
Qed.
Lemma reference_control_member_6476 : List.In (6476,reference_control_expr_6476) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 224%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_6476_ground inputs path old current result :
 (exists value ground, VM.find 6462 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 6472 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 6476 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H6462 H6472 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 6476 reference_control_expr_6476 reference_control_3_positions reference_control_3_safety reference_control_member_6476) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 6476 reference_control_expr_6476 inputs path old current result Position Safe Nonreg (reference_control_ready_6476 old H6462 H6472) Step).
Qed.
Theorem reference_control_node_6476_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 6462 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 6472 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2830 left = VM.find 2830 right ->
 VM.find 6462 left = VM.find 6462 right ->
 VM.find 6472 left = VM.find 6472 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 6476 next_left = VM.find 6476 next_right.
Proof.
 intros H6462 H6472 E2830 E6462 E6472 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 6476 reference_control_expr_6476 reference_control_3_positions reference_control_3_safety reference_control_member_6476) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 6476 reference_control_expr_6476 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_6476 left H6462 H6472)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_6476 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2830.
 rewrite E6462.
 rewrite E6472.
 reflexivity.
Qed.
Lemma reference_control_ready_6483 old :
 (exists value ground, VM.find 6459 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 6473 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_6483.
Proof.
 intros H6459 H6473.
 destruct H6459 as [v6459 [G6459 [V6459 T6459]]].
 destruct H6473 as [v6473 [G6473 [V6473 T6473]]].
 unfold reference_control_expr_6483.
apply rc_mux.
{ eapply rc_ref; [exact V6473|exists G6473; exact T6473].
}
{ eapply rc_ref; [exact V6459|exists G6459; exact T6459].
}
Qed.
Lemma reference_control_member_6483 : List.In (6483,reference_control_expr_6483) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 225%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_6483_ground inputs path old current result :
 (exists value ground, VM.find 6459 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 6473 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 6483 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H6459 H6473 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 6483 reference_control_expr_6483 reference_control_3_positions reference_control_3_safety reference_control_member_6483) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 6483 reference_control_expr_6483 inputs path old current result Position Safe Nonreg (reference_control_ready_6483 old H6459 H6473) Step).
Qed.
Theorem reference_control_node_6483_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 6459 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 6473 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1980 left = VM.find 1980 right ->
 VM.find 6459 left = VM.find 6459 right ->
 VM.find 6473 left = VM.find 6473 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 6483 next_left = VM.find 6483 next_right.
Proof.
 intros H6459 H6473 E1980 E6459 E6473 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 6483 reference_control_expr_6483 reference_control_3_positions reference_control_3_safety reference_control_member_6483) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 6483 reference_control_expr_6483 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_6483 left H6459 H6473)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_6483 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1980.
 rewrite E6459.
 rewrite E6473.
 reflexivity.
Qed.
Lemma reference_control_ready_6486 old :
 (exists value ground, VM.find 6462 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 6476 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_6486.
Proof.
 intros H6462 H6476.
 destruct H6462 as [v6462 [G6462 [V6462 T6462]]].
 destruct H6476 as [v6476 [G6476 [V6476 T6476]]].
 unfold reference_control_expr_6486.
apply rc_mux.
{ eapply rc_ref; [exact V6476|exists G6476; exact T6476].
}
{ eapply rc_ref; [exact V6462|exists G6462; exact T6462].
}
Qed.
Lemma reference_control_member_6486 : List.In (6486,reference_control_expr_6486) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 226%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_6486_ground inputs path old current result :
 (exists value ground, VM.find 6462 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 6476 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 6486 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H6462 H6476 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 6486 reference_control_expr_6486 reference_control_3_positions reference_control_3_safety reference_control_member_6486) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 6486 reference_control_expr_6486 inputs path old current result Position Safe Nonreg (reference_control_ready_6486 old H6462 H6476) Step).
Qed.
Theorem reference_control_node_6486_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 6462 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 6476 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1980 left = VM.find 1980 right ->
 VM.find 6462 left = VM.find 6462 right ->
 VM.find 6476 left = VM.find 6476 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 6486 next_left = VM.find 6486 next_right.
Proof.
 intros H6462 H6476 E1980 E6462 E6476 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 6486 reference_control_expr_6486 reference_control_3_positions reference_control_3_safety reference_control_member_6486) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 6486 reference_control_expr_6486 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_6486 left H6462 H6476)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_6486 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1980.
 rewrite E6462.
 rewrite E6476.
 reflexivity.
Qed.
Lemma reference_control_ready_6493 old :
 (exists value ground, VM.find 6483 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_6493.
Proof.
 intros H6483.
 destruct H6483 as [v6483 [G6483 [V6483 T6483]]].
 unfold reference_control_expr_6493.
apply rc_mux.
{ apply rc_const.
}
{ eapply rc_ref; [exact V6483|exists G6483; exact T6483].
}
Qed.
Lemma reference_control_member_6493 : List.In (6493,reference_control_expr_6493) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 227%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_6493_ground inputs path old current result :
 (exists value ground, VM.find 6483 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 6493 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H6483 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 6493 reference_control_expr_6493 reference_control_3_positions reference_control_3_safety reference_control_member_6493) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 6493 reference_control_expr_6493 inputs path old current result Position Safe Nonreg (reference_control_ready_6493 old H6483) Step).
Qed.
Theorem reference_control_node_6493_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 6483 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2825 left = VM.find 2825 right ->
 VM.find 6483 left = VM.find 6483 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 6493 next_left = VM.find 6493 next_right.
Proof.
 intros H6483 E2825 E6483 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 6493 reference_control_expr_6493 reference_control_3_positions reference_control_3_safety reference_control_member_6493) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 6493 reference_control_expr_6493 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_6493 left H6483)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_6493 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2825.
 rewrite E6483.
 reflexivity.
Qed.
Lemma reference_control_ready_6496 old :
 (exists value ground, VM.find 6486 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_6496.
Proof.
 intros H6486.
 destruct H6486 as [v6486 [G6486 [V6486 T6486]]].
 unfold reference_control_expr_6496.
apply rc_mux.
{ eapply rc_ref; [exact V6486|exists G6486; exact T6486].
}
{ apply rc_const.
}
Qed.
Lemma reference_control_member_6496 : List.In (6496,reference_control_expr_6496) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 228%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_6496_ground inputs path old current result :
 (exists value ground, VM.find 6486 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 6496 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H6486 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 6496 reference_control_expr_6496 reference_control_3_positions reference_control_3_safety reference_control_member_6496) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 6496 reference_control_expr_6496 inputs path old current result Position Safe Nonreg (reference_control_ready_6496 old H6486) Step).
Qed.
Theorem reference_control_node_6496_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 6486 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2825 left = VM.find 2825 right ->
 VM.find 6486 left = VM.find 6486 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 6496 next_left = VM.find 6496 next_right.
Proof.
 intros H6486 E2825 E6486 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 6496 reference_control_expr_6496 reference_control_3_positions reference_control_3_safety reference_control_member_6496) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 6496 reference_control_expr_6496 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_6496 left H6486)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_6496 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2825.
 rewrite E6486.
 reflexivity.
Qed.
Lemma reference_control_ready_6497 old :
 (exists value ground, VM.find 6483 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 6493 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_6497.
Proof.
 intros H6483 H6493.
 destruct H6483 as [v6483 [G6483 [V6483 T6483]]].
 destruct H6493 as [v6493 [G6493 [V6493 T6493]]].
 unfold reference_control_expr_6497.
apply rc_mux.
{ eapply rc_ref; [exact V6493|exists G6493; exact T6493].
}
{ eapply rc_ref; [exact V6483|exists G6483; exact T6483].
}
Qed.
Lemma reference_control_member_6497 : List.In (6497,reference_control_expr_6497) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 229%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_6497_ground inputs path old current result :
 (exists value ground, VM.find 6483 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 6493 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 6497 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H6483 H6493 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 6497 reference_control_expr_6497 reference_control_3_positions reference_control_3_safety reference_control_member_6497) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 6497 reference_control_expr_6497 inputs path old current result Position Safe Nonreg (reference_control_ready_6497 old H6483 H6493) Step).
Qed.
Theorem reference_control_node_6497_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 6483 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 6493 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2806 left = VM.find 2806 right ->
 VM.find 6483 left = VM.find 6483 right ->
 VM.find 6493 left = VM.find 6493 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 6497 next_left = VM.find 6497 next_right.
Proof.
 intros H6483 H6493 E2806 E6483 E6493 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 6497 reference_control_expr_6497 reference_control_3_positions reference_control_3_safety reference_control_member_6497) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 6497 reference_control_expr_6497 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_6497 left H6483 H6493)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_6497 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2806.
 rewrite E6483.
 rewrite E6493.
 reflexivity.
Qed.
Lemma reference_control_ready_6500 old :
 (exists value ground, VM.find 6486 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 6496 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_6500.
Proof.
 intros H6486 H6496.
 destruct H6486 as [v6486 [G6486 [V6486 T6486]]].
 destruct H6496 as [v6496 [G6496 [V6496 T6496]]].
 unfold reference_control_expr_6500.
apply rc_mux.
{ eapply rc_ref; [exact V6496|exists G6496; exact T6496].
}
{ eapply rc_ref; [exact V6486|exists G6486; exact T6486].
}
Qed.
Lemma reference_control_member_6500 : List.In (6500,reference_control_expr_6500) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 230%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_6500_ground inputs path old current result :
 (exists value ground, VM.find 6486 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 6496 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 6500 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H6486 H6496 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 6500 reference_control_expr_6500 reference_control_3_positions reference_control_3_safety reference_control_member_6500) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 6500 reference_control_expr_6500 inputs path old current result Position Safe Nonreg (reference_control_ready_6500 old H6486 H6496) Step).
Qed.
Theorem reference_control_node_6500_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 6486 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 6496 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2806 left = VM.find 2806 right ->
 VM.find 6486 left = VM.find 6486 right ->
 VM.find 6496 left = VM.find 6496 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 6500 next_left = VM.find 6500 next_right.
Proof.
 intros H6486 H6496 E2806 E6486 E6496 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 6500 reference_control_expr_6500 reference_control_3_positions reference_control_3_safety reference_control_member_6500) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 6500 reference_control_expr_6500 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_6500 left H6486 H6496)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_6500 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2806.
 rewrite E6486.
 rewrite E6496.
 reflexivity.
Qed.
Lemma reference_control_ready_6507 old :
 (exists value ground, VM.find 6483 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 6497 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_6507.
Proof.
 intros H6483 H6497.
 destruct H6483 as [v6483 [G6483 [V6483 T6483]]].
 destruct H6497 as [v6497 [G6497 [V6497 T6497]]].
 unfold reference_control_expr_6507.
apply rc_mux.
{ eapply rc_ref; [exact V6497|exists G6497; exact T6497].
}
{ eapply rc_ref; [exact V6483|exists G6483; exact T6483].
}
Qed.
Lemma reference_control_member_6507 : List.In (6507,reference_control_expr_6507) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 231%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_6507_ground inputs path old current result :
 (exists value ground, VM.find 6483 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 6497 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 6507 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H6483 H6497 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 6507 reference_control_expr_6507 reference_control_3_positions reference_control_3_safety reference_control_member_6507) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 6507 reference_control_expr_6507 inputs path old current result Position Safe Nonreg (reference_control_ready_6507 old H6483 H6497) Step).
Qed.
Theorem reference_control_node_6507_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 6483 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 6497 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1974 left = VM.find 1974 right ->
 VM.find 6483 left = VM.find 6483 right ->
 VM.find 6497 left = VM.find 6497 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 6507 next_left = VM.find 6507 next_right.
Proof.
 intros H6483 H6497 E1974 E6483 E6497 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 6507 reference_control_expr_6507 reference_control_3_positions reference_control_3_safety reference_control_member_6507) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 6507 reference_control_expr_6507 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_6507 left H6483 H6497)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_6507 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1974.
 rewrite E6483.
 rewrite E6497.
 reflexivity.
Qed.
Lemma reference_control_ready_6510 old :
 (exists value ground, VM.find 6486 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 6500 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_6510.
Proof.
 intros H6486 H6500.
 destruct H6486 as [v6486 [G6486 [V6486 T6486]]].
 destruct H6500 as [v6500 [G6500 [V6500 T6500]]].
 unfold reference_control_expr_6510.
apply rc_mux.
{ eapply rc_ref; [exact V6500|exists G6500; exact T6500].
}
{ eapply rc_ref; [exact V6486|exists G6486; exact T6486].
}
Qed.
Lemma reference_control_member_6510 : List.In (6510,reference_control_expr_6510) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 232%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_6510_ground inputs path old current result :
 (exists value ground, VM.find 6486 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 6500 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 6510 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H6486 H6500 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 6510 reference_control_expr_6510 reference_control_3_positions reference_control_3_safety reference_control_member_6510) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 6510 reference_control_expr_6510 inputs path old current result Position Safe Nonreg (reference_control_ready_6510 old H6486 H6500) Step).
Qed.
Theorem reference_control_node_6510_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 6486 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 6500 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1974 left = VM.find 1974 right ->
 VM.find 6486 left = VM.find 6486 right ->
 VM.find 6500 left = VM.find 6500 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 6510 next_left = VM.find 6510 next_right.
Proof.
 intros H6486 H6500 E1974 E6486 E6500 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 6510 reference_control_expr_6510 reference_control_3_positions reference_control_3_safety reference_control_member_6510) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 6510 reference_control_expr_6510 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_6510 left H6486 H6500)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_6510 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1974.
 rewrite E6486.
 rewrite E6500.
 reflexivity.
Qed.
Lemma reference_control_ready_6523 old :
 (exists value ground, VM.find 6510 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_6523.
Proof.
 intros H6510.
 destruct H6510 as [v6510 [G6510 [V6510 T6510]]].
 unfold reference_control_expr_6523.
apply rc_mux.
{ eapply rc_ref; [exact V6510|exists G6510; exact T6510].
}
{ apply rc_const.
}
Qed.
Lemma reference_control_member_6523 : List.In (6523,reference_control_expr_6523) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 233%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_6523_ground inputs path old current result :
 (exists value ground, VM.find 6510 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 6523 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H6510 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 6523 reference_control_expr_6523 reference_control_3_positions reference_control_3_safety reference_control_member_6523) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 6523 reference_control_expr_6523 inputs path old current result Position Safe Nonreg (reference_control_ready_6523 old H6510) Step).
Qed.
Theorem reference_control_node_6523_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 6510 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2679 left = VM.find 2679 right ->
 VM.find 6510 left = VM.find 6510 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 6523 next_left = VM.find 6523 next_right.
Proof.
 intros H6510 E2679 E6510 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 6523 reference_control_expr_6523 reference_control_3_positions reference_control_3_safety reference_control_member_6523) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 6523 reference_control_expr_6523 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_6523 left H6510)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_6523 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2679.
 rewrite E6510.
 reflexivity.
Qed.
Lemma reference_control_ready_6533 old :
 (exists value ground, VM.find 6510 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 6523 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_6533.
Proof.
 intros H6510 H6523.
 destruct H6510 as [v6510 [G6510 [V6510 T6510]]].
 destruct H6523 as [v6523 [G6523 [V6523 T6523]]].
 unfold reference_control_expr_6533.
apply rc_mux.
{ eapply rc_ref; [exact V6523|exists G6523; exact T6523].
}
{ eapply rc_ref; [exact V6510|exists G6510; exact T6510].
}
Qed.
Lemma reference_control_member_6533 : List.In (6533,reference_control_expr_6533) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 234%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_6533_ground inputs path old current result :
 (exists value ground, VM.find 6510 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 6523 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 6533 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H6510 H6523 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 6533 reference_control_expr_6533 reference_control_3_positions reference_control_3_safety reference_control_member_6533) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 6533 reference_control_expr_6533 inputs path old current result Position Safe Nonreg (reference_control_ready_6533 old H6510 H6523) Step).
Qed.
Theorem reference_control_node_6533_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 6510 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 6523 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1970 left = VM.find 1970 right ->
 VM.find 6510 left = VM.find 6510 right ->
 VM.find 6523 left = VM.find 6523 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 6533 next_left = VM.find 6533 next_right.
Proof.
 intros H6510 H6523 E1970 E6510 E6523 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 6533 reference_control_expr_6533 reference_control_3_positions reference_control_3_safety reference_control_member_6533) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 6533 reference_control_expr_6533 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_6533 left H6510 H6523)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_6533 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1970.
 rewrite E6510.
 rewrite E6523.
 reflexivity.
Qed.
Lemma reference_control_ready_6548 old :
 (exists value ground, VM.find 6533 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_6548.
Proof.
 intros H6533.
 destruct H6533 as [v6533 [G6533 [V6533 T6533]]].
 unfold reference_control_expr_6548.
apply rc_mux.
{ eapply rc_ref; [exact V6533|exists G6533; exact T6533].
}
{ apply rc_const.
}
Qed.
Lemma reference_control_member_6548 : List.In (6548,reference_control_expr_6548) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 235%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_6548_ground inputs path old current result :
 (exists value ground, VM.find 6533 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 6548 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H6533 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 6548 reference_control_expr_6548 reference_control_3_positions reference_control_3_safety reference_control_member_6548) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 6548 reference_control_expr_6548 inputs path old current result Position Safe Nonreg (reference_control_ready_6548 old H6533) Step).
Qed.
Theorem reference_control_node_6548_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 6533 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2664 left = VM.find 2664 right ->
 VM.find 6533 left = VM.find 6533 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 6548 next_left = VM.find 6548 next_right.
Proof.
 intros H6533 E2664 E6533 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 6548 reference_control_expr_6548 reference_control_3_positions reference_control_3_safety reference_control_member_6548) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 6548 reference_control_expr_6548 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_6548 left H6533)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_6548 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2664.
 rewrite E6533.
 reflexivity.
Qed.
Lemma reference_control_ready_6557 old :
 (exists value ground, VM.find 6533 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 6548 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_6557.
Proof.
 intros H6533 H6548.
 destruct H6533 as [v6533 [G6533 [V6533 T6533]]].
 destruct H6548 as [v6548 [G6548 [V6548 T6548]]].
 unfold reference_control_expr_6557.
apply rc_mux.
{ eapply rc_ref; [exact V6548|exists G6548; exact T6548].
}
{ eapply rc_ref; [exact V6533|exists G6533; exact T6533].
}
Qed.
Lemma reference_control_member_6557 : List.In (6557,reference_control_expr_6557) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 236%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_6557_ground inputs path old current result :
 (exists value ground, VM.find 6533 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 6548 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 6557 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H6533 H6548 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 6557 reference_control_expr_6557 reference_control_3_positions reference_control_3_safety reference_control_member_6557) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 6557 reference_control_expr_6557 inputs path old current result Position Safe Nonreg (reference_control_ready_6557 old H6533 H6548) Step).
Qed.
Theorem reference_control_node_6557_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 6533 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 6548 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1966 left = VM.find 1966 right ->
 VM.find 6533 left = VM.find 6533 right ->
 VM.find 6548 left = VM.find 6548 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 6557 next_left = VM.find 6557 next_right.
Proof.
 intros H6533 H6548 E1966 E6533 E6548 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 6557 reference_control_expr_6557 reference_control_3_positions reference_control_3_safety reference_control_member_6557) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 6557 reference_control_expr_6557 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_6557 left H6533 H6548)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_6557 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1966.
 rewrite E6533.
 rewrite E6548.
 reflexivity.
Qed.
Lemma reference_control_ready_6573 old :
 (exists value ground, VM.find 6557 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_6573.
Proof.
 intros H6557.
 destruct H6557 as [v6557 [G6557 [V6557 T6557]]].
 unfold reference_control_expr_6573.
apply rc_mux.
{ eapply rc_ref; [exact V6557|exists G6557; exact T6557].
}
{ apply rc_const.
}
Qed.
Lemma reference_control_member_6573 : List.In (6573,reference_control_expr_6573) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 237%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_6573_ground inputs path old current result :
 (exists value ground, VM.find 6557 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 6573 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H6557 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 6573 reference_control_expr_6573 reference_control_3_positions reference_control_3_safety reference_control_member_6573) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 6573 reference_control_expr_6573 inputs path old current result Position Safe Nonreg (reference_control_ready_6573 old H6557) Step).
Qed.
Theorem reference_control_node_6573_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 6557 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2649 left = VM.find 2649 right ->
 VM.find 6557 left = VM.find 6557 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 6573 next_left = VM.find 6573 next_right.
Proof.
 intros H6557 E2649 E6557 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 6573 reference_control_expr_6573 reference_control_3_positions reference_control_3_safety reference_control_member_6573) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 6573 reference_control_expr_6573 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_6573 left H6557)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_6573 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2649.
 rewrite E6557.
 reflexivity.
Qed.
Lemma reference_control_ready_6582 old :
 (exists value ground, VM.find 6557 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 6573 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_6582.
Proof.
 intros H6557 H6573.
 destruct H6557 as [v6557 [G6557 [V6557 T6557]]].
 destruct H6573 as [v6573 [G6573 [V6573 T6573]]].
 unfold reference_control_expr_6582.
apply rc_mux.
{ eapply rc_ref; [exact V6573|exists G6573; exact T6573].
}
{ eapply rc_ref; [exact V6557|exists G6557; exact T6557].
}
Qed.
Lemma reference_control_member_6582 : List.In (6582,reference_control_expr_6582) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 238%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_6582_ground inputs path old current result :
 (exists value ground, VM.find 6557 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 6573 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 6582 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H6557 H6573 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 6582 reference_control_expr_6582 reference_control_3_positions reference_control_3_safety reference_control_member_6582) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 6582 reference_control_expr_6582 inputs path old current result Position Safe Nonreg (reference_control_ready_6582 old H6557 H6573) Step).
Qed.
Theorem reference_control_node_6582_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 6557 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 6573 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1962 left = VM.find 1962 right ->
 VM.find 6557 left = VM.find 6557 right ->
 VM.find 6573 left = VM.find 6573 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 6582 next_left = VM.find 6582 next_right.
Proof.
 intros H6557 H6573 E1962 E6557 E6573 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 6582 reference_control_expr_6582 reference_control_3_positions reference_control_3_safety reference_control_member_6582) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 6582 reference_control_expr_6582 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_6582 left H6557 H6573)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_6582 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1962.
 rewrite E6557.
 rewrite E6573.
 reflexivity.
Qed.
Lemma reference_control_ready_6589 old :
 (exists value ground, VM.find 6582 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_6589.
Proof.
 intros H6582.
 destruct H6582 as [v6582 [G6582 [V6582 T6582]]].
 unfold reference_control_expr_6589.
apply rc_mux.
{ apply rc_const.
}
{ eapply rc_ref; [exact V6582|exists G6582; exact T6582].
}
Qed.
Lemma reference_control_member_6589 : List.In (6589,reference_control_expr_6589) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 239%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_6589_ground inputs path old current result :
 (exists value ground, VM.find 6582 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 6589 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H6582 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 6589 reference_control_expr_6589 reference_control_3_positions reference_control_3_safety reference_control_member_6589) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 6589 reference_control_expr_6589 inputs path old current result Position Safe Nonreg (reference_control_ready_6589 old H6582) Step).
Qed.
Theorem reference_control_node_6589_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 6582 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2634 left = VM.find 2634 right ->
 VM.find 6582 left = VM.find 6582 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 6589 next_left = VM.find 6589 next_right.
Proof.
 intros H6582 E2634 E6582 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 6589 reference_control_expr_6589 reference_control_3_positions reference_control_3_safety reference_control_member_6589) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 6589 reference_control_expr_6589 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_6589 left H6582)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_6589 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2634.
 rewrite E6582.
 reflexivity.
Qed.
Lemma reference_control_ready_6595 old :
 (exists value ground, VM.find 6582 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 6589 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_6595.
Proof.
 intros H6582 H6589.
 destruct H6582 as [v6582 [G6582 [V6582 T6582]]].
 destruct H6589 as [v6589 [G6589 [V6589 T6589]]].
 unfold reference_control_expr_6595.
apply rc_mux.
{ eapply rc_ref; [exact V6589|exists G6589; exact T6589].
}
{ eapply rc_ref; [exact V6582|exists G6582; exact T6582].
}
Qed.
Lemma reference_control_member_6595 : List.In (6595,reference_control_expr_6595) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 240%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_6595_ground inputs path old current result :
 (exists value ground, VM.find 6582 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 6589 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 6595 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H6582 H6589 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 6595 reference_control_expr_6595 reference_control_3_positions reference_control_3_safety reference_control_member_6595) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 6595 reference_control_expr_6595 inputs path old current result Position Safe Nonreg (reference_control_ready_6595 old H6582 H6589) Step).
Qed.
Theorem reference_control_node_6595_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 6582 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 6589 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1958 left = VM.find 1958 right ->
 VM.find 6582 left = VM.find 6582 right ->
 VM.find 6589 left = VM.find 6589 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 6595 next_left = VM.find 6595 next_right.
Proof.
 intros H6582 H6589 E1958 E6582 E6589 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 6595 reference_control_expr_6595 reference_control_3_positions reference_control_3_safety reference_control_member_6595) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 6595 reference_control_expr_6595 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_6595 left H6582 H6589)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_6595 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1958.
 rewrite E6582.
 rewrite E6589.
 reflexivity.
Qed.
Lemma reference_control_ready_6614 old :
 (exists value ground, VM.find 6595 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_6614.
Proof.
 intros H6595.
 destruct H6595 as [v6595 [G6595 [V6595 T6595]]].
 unfold reference_control_expr_6614.
apply rc_mux.
{ eapply rc_ref; [exact V6595|exists G6595; exact T6595].
}
{ apply rc_const.
}
Qed.
Lemma reference_control_member_6614 : List.In (6614,reference_control_expr_6614) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 241%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_6614_ground inputs path old current result :
 (exists value ground, VM.find 6595 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 6614 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H6595 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 6614 reference_control_expr_6614 reference_control_3_positions reference_control_3_safety reference_control_member_6614) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 6614 reference_control_expr_6614 inputs path old current result Position Safe Nonreg (reference_control_ready_6614 old H6595) Step).
Qed.
Theorem reference_control_node_6614_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 6595 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2565 left = VM.find 2565 right ->
 VM.find 6595 left = VM.find 6595 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 6614 next_left = VM.find 6614 next_right.
Proof.
 intros H6595 E2565 E6595 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 6614 reference_control_expr_6614 reference_control_3_positions reference_control_3_safety reference_control_member_6614) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 6614 reference_control_expr_6614 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_6614 left H6595)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_6614 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2565.
 rewrite E6595.
 reflexivity.
Qed.
Lemma reference_control_ready_6623 old :
 (exists value ground, VM.find 6595 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 6614 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_6623.
Proof.
 intros H6595 H6614.
 destruct H6595 as [v6595 [G6595 [V6595 T6595]]].
 destruct H6614 as [v6614 [G6614 [V6614 T6614]]].
 unfold reference_control_expr_6623.
apply rc_mux.
{ eapply rc_ref; [exact V6614|exists G6614; exact T6614].
}
{ eapply rc_ref; [exact V6595|exists G6595; exact T6595].
}
Qed.
Lemma reference_control_member_6623 : List.In (6623,reference_control_expr_6623) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 242%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_6623_ground inputs path old current result :
 (exists value ground, VM.find 6595 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 6614 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 6623 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H6595 H6614 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 6623 reference_control_expr_6623 reference_control_3_positions reference_control_3_safety reference_control_member_6623) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 6623 reference_control_expr_6623 inputs path old current result Position Safe Nonreg (reference_control_ready_6623 old H6595 H6614) Step).
Qed.
Theorem reference_control_node_6623_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 6595 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 6614 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1886 left = VM.find 1886 right ->
 VM.find 6595 left = VM.find 6595 right ->
 VM.find 6614 left = VM.find 6614 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 6623 next_left = VM.find 6623 next_right.
Proof.
 intros H6595 H6614 E1886 E6595 E6614 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 6623 reference_control_expr_6623 reference_control_3_positions reference_control_3_safety reference_control_member_6623) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 6623 reference_control_expr_6623 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_6623 left H6595 H6614)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_6623 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1886.
 rewrite E6595.
 rewrite E6614.
 reflexivity.
Qed.
Lemma reference_control_ready_6630 old :
 (exists value ground, VM.find 6623 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_6630.
Proof.
 intros H6623.
 destruct H6623 as [v6623 [G6623 [V6623 T6623]]].
 unfold reference_control_expr_6630.
apply rc_mux.
{ apply rc_const.
}
{ eapply rc_ref; [exact V6623|exists G6623; exact T6623].
}
Qed.
Lemma reference_control_member_6630 : List.In (6630,reference_control_expr_6630) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 243%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_6630_ground inputs path old current result :
 (exists value ground, VM.find 6623 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 6630 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H6623 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 6630 reference_control_expr_6630 reference_control_3_positions reference_control_3_safety reference_control_member_6630) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 6630 reference_control_expr_6630 inputs path old current result Position Safe Nonreg (reference_control_ready_6630 old H6623) Step).
Qed.
Theorem reference_control_node_6630_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 6623 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2736 left = VM.find 2736 right ->
 VM.find 6623 left = VM.find 6623 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 6630 next_left = VM.find 6630 next_right.
Proof.
 intros H6623 E2736 E6623 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 6630 reference_control_expr_6630 reference_control_3_positions reference_control_3_safety reference_control_member_6630) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 6630 reference_control_expr_6630 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_6630 left H6623)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_6630 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2736.
 rewrite E6623.
 reflexivity.
Qed.
Lemma reference_control_ready_6640 old :
 (exists value ground, VM.find 6623 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 6630 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_6640.
Proof.
 intros H6623 H6630.
 destruct H6623 as [v6623 [G6623 [V6623 T6623]]].
 destruct H6630 as [v6630 [G6630 [V6630 T6630]]].
 unfold reference_control_expr_6640.
apply rc_mux.
{ eapply rc_ref; [exact V6630|exists G6630; exact T6630].
}
{ eapply rc_ref; [exact V6623|exists G6623; exact T6623].
}
Qed.
Lemma reference_control_member_6640 : List.In (6640,reference_control_expr_6640) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 244%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_6640_ground inputs path old current result :
 (exists value ground, VM.find 6623 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 6630 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 6640 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H6623 H6630 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 6640 reference_control_expr_6640 reference_control_3_positions reference_control_3_safety reference_control_member_6640) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 6640 reference_control_expr_6640 inputs path old current result Position Safe Nonreg (reference_control_ready_6640 old H6623 H6630) Step).
Qed.
Theorem reference_control_node_6640_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 6623 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 6630 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1951 left = VM.find 1951 right ->
 VM.find 6623 left = VM.find 6623 right ->
 VM.find 6630 left = VM.find 6630 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 6640 next_left = VM.find 6640 next_right.
Proof.
 intros H6623 H6630 E1951 E6623 E6630 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 6640 reference_control_expr_6640 reference_control_3_positions reference_control_3_safety reference_control_member_6640) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 6640 reference_control_expr_6640 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_6640 left H6623 H6630)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_6640 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1951.
 rewrite E6623.
 rewrite E6630.
 reflexivity.
Qed.
Lemma reference_control_ready_6663 old :
 (exists value ground, VM.find 6640 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_6663.
Proof.
 intros H6640.
 destruct H6640 as [v6640 [G6640 [V6640 T6640]]].
 unfold reference_control_expr_6663.
apply rc_mux.
{ eapply rc_ref; [exact V6640|exists G6640; exact T6640].
}
{ apply rc_const.
}
Qed.
Lemma reference_control_member_6663 : List.In (6663,reference_control_expr_6663) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 245%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_6663_ground inputs path old current result :
 (exists value ground, VM.find 6640 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 6663 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H6640 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 6663 reference_control_expr_6663 reference_control_3_positions reference_control_3_safety reference_control_member_6663) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 6663 reference_control_expr_6663 inputs path old current result Position Safe Nonreg (reference_control_ready_6663 old H6640) Step).
Qed.
Theorem reference_control_node_6663_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 6640 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2723 left = VM.find 2723 right ->
 VM.find 6640 left = VM.find 6640 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 6663 next_left = VM.find 6663 next_right.
Proof.
 intros H6640 E2723 E6640 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 6663 reference_control_expr_6663 reference_control_3_positions reference_control_3_safety reference_control_member_6663) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 6663 reference_control_expr_6663 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_6663 left H6640)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_6663 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2723.
 rewrite E6640.
 reflexivity.
Qed.
Lemma reference_control_ready_6672 old :
 (exists value ground, VM.find 6640 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 6663 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_6672.
Proof.
 intros H6640 H6663.
 destruct H6640 as [v6640 [G6640 [V6640 T6640]]].
 destruct H6663 as [v6663 [G6663 [V6663 T6663]]].
 unfold reference_control_expr_6672.
apply rc_mux.
{ eapply rc_ref; [exact V6663|exists G6663; exact T6663].
}
{ eapply rc_ref; [exact V6640|exists G6640; exact T6640].
}
Qed.
Lemma reference_control_member_6672 : List.In (6672,reference_control_expr_6672) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 246%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_6672_ground inputs path old current result :
 (exists value ground, VM.find 6640 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 6663 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 6672 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H6640 H6663 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 6672 reference_control_expr_6672 reference_control_3_positions reference_control_3_safety reference_control_member_6672) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 6672 reference_control_expr_6672 inputs path old current result Position Safe Nonreg (reference_control_ready_6672 old H6640 H6663) Step).
Qed.
Theorem reference_control_node_6672_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 6640 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 6663 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1946 left = VM.find 1946 right ->
 VM.find 6640 left = VM.find 6640 right ->
 VM.find 6663 left = VM.find 6663 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 6672 next_left = VM.find 6672 next_right.
Proof.
 intros H6640 H6663 E1946 E6640 E6663 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 6672 reference_control_expr_6672 reference_control_3_positions reference_control_3_safety reference_control_member_6672) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 6672 reference_control_expr_6672 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_6672 left H6640 H6663)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_6672 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1946.
 rewrite E6640.
 rewrite E6663.
 reflexivity.
Qed.
Lemma reference_control_ready_6687 old :
 (exists value ground, VM.find 6672 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_6687.
Proof.
 intros H6672.
 destruct H6672 as [v6672 [G6672 [V6672 T6672]]].
 unfold reference_control_expr_6687.
apply rc_mux.
{ eapply rc_ref; [exact V6672|exists G6672; exact T6672].
}
{ apply rc_const.
}
Qed.
Lemma reference_control_member_6687 : List.In (6687,reference_control_expr_6687) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 247%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_6687_ground inputs path old current result :
 (exists value ground, VM.find 6672 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 6687 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H6672 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 6687 reference_control_expr_6687 reference_control_3_positions reference_control_3_safety reference_control_member_6687) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 6687 reference_control_expr_6687 inputs path old current result Position Safe Nonreg (reference_control_ready_6687 old H6672) Step).
Qed.
Theorem reference_control_node_6687_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 6672 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2708 left = VM.find 2708 right ->
 VM.find 6672 left = VM.find 6672 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 6687 next_left = VM.find 6687 next_right.
Proof.
 intros H6672 E2708 E6672 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 6687 reference_control_expr_6687 reference_control_3_positions reference_control_3_safety reference_control_member_6687) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 6687 reference_control_expr_6687 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_6687 left H6672)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_6687 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2708.
 rewrite E6672.
 reflexivity.
Qed.
Lemma reference_control_ready_6696 old :
 (exists value ground, VM.find 6672 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 6687 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_6696.
Proof.
 intros H6672 H6687.
 destruct H6672 as [v6672 [G6672 [V6672 T6672]]].
 destruct H6687 as [v6687 [G6687 [V6687 T6687]]].
 unfold reference_control_expr_6696.
apply rc_mux.
{ eapply rc_ref; [exact V6687|exists G6687; exact T6687].
}
{ eapply rc_ref; [exact V6672|exists G6672; exact T6672].
}
Qed.
Lemma reference_control_member_6696 : List.In (6696,reference_control_expr_6696) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 248%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_6696_ground inputs path old current result :
 (exists value ground, VM.find 6672 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 6687 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 6696 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H6672 H6687 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 6696 reference_control_expr_6696 reference_control_3_positions reference_control_3_safety reference_control_member_6696) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 6696 reference_control_expr_6696 inputs path old current result Position Safe Nonreg (reference_control_ready_6696 old H6672 H6687) Step).
Qed.
Theorem reference_control_node_6696_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 6672 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 6687 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1941 left = VM.find 1941 right ->
 VM.find 6672 left = VM.find 6672 right ->
 VM.find 6687 left = VM.find 6687 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 6696 next_left = VM.find 6696 next_right.
Proof.
 intros H6672 H6687 E1941 E6672 E6687 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 6696 reference_control_expr_6696 reference_control_3_positions reference_control_3_safety reference_control_member_6696) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 6696 reference_control_expr_6696 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_6696 left H6672 H6687)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_6696 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1941.
 rewrite E6672.
 rewrite E6687.
 reflexivity.
Qed.
Lemma reference_control_ready_6701 old :
 (exists value ground, VM.find 6696 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_6701.
Proof.
 intros H6696.
 destruct H6696 as [v6696 [G6696 [V6696 T6696]]].
 unfold reference_control_expr_6701.
apply rc_mux.
{ apply rc_const.
}
{ eapply rc_ref; [exact V6696|exists G6696; exact T6696].
}
Qed.
Lemma reference_control_member_6701 : List.In (6701,reference_control_expr_6701) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 249%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_6701_ground inputs path old current result :
 (exists value ground, VM.find 6696 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 6701 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H6696 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 6701 reference_control_expr_6701 reference_control_3_positions reference_control_3_safety reference_control_member_6701) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 6701 reference_control_expr_6701 inputs path old current result Position Safe Nonreg (reference_control_ready_6701 old H6696) Step).
Qed.
Theorem reference_control_node_6701_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 6696 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1937 left = VM.find 1937 right ->
 VM.find 6696 left = VM.find 6696 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 6701 next_left = VM.find 6701 next_right.
Proof.
 intros H6696 E1937 E6696 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 6701 reference_control_expr_6701 reference_control_3_positions reference_control_3_safety reference_control_member_6701) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 6701 reference_control_expr_6701 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_6701 left H6696)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_6701 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1937.
 rewrite E6696.
 reflexivity.
Qed.
Lemma reference_control_ready_6704 old :
 (exists value ground, VM.find 6701 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_6704.
Proof.
 intros H6701.
 destruct H6701 as [v6701 [G6701 [V6701 T6701]]].
 unfold reference_control_expr_6704.
apply rc_mux.
{ apply rc_const.
}
{ eapply rc_ref; [exact V6701|exists G6701; exact T6701].
}
Qed.
Lemma reference_control_member_6704 : List.In (6704,reference_control_expr_6704) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 250%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_6704_ground inputs path old current result :
 (exists value ground, VM.find 6701 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 6704 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H6701 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 6704 reference_control_expr_6704 reference_control_3_positions reference_control_3_safety reference_control_member_6704) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 6704 reference_control_expr_6704 inputs path old current result Position Safe Nonreg (reference_control_ready_6704 old H6701) Step).
Qed.
Theorem reference_control_node_6704_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 6701 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2751 left = VM.find 2751 right ->
 VM.find 6701 left = VM.find 6701 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 6704 next_left = VM.find 6704 next_right.
Proof.
 intros H6701 E2751 E6701 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 6704 reference_control_expr_6704 reference_control_3_positions reference_control_3_safety reference_control_member_6704) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 6704 reference_control_expr_6704 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_6704 left H6701)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_6704 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2751.
 rewrite E6701.
 reflexivity.
Qed.
Lemma reference_control_ready_6705 old :
 (exists value ground, VM.find 6704 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_6705.
Proof.
 intros H6704.
 destruct H6704 as [v6704 [G6704 [V6704 T6704]]].
 unfold reference_control_expr_6705.
apply rc_mux.
{ apply rc_const.
}
{ eapply rc_ref; [exact V6704|exists G6704; exact T6704].
}
Qed.
Lemma reference_control_member_6705 : List.In (6705,reference_control_expr_6705) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 251%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_6705_ground inputs path old current result :
 (exists value ground, VM.find 6704 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 6705 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H6704 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 6705 reference_control_expr_6705 reference_control_3_positions reference_control_3_safety reference_control_member_6705) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 6705 reference_control_expr_6705 inputs path old current result Position Safe Nonreg (reference_control_ready_6705 old H6704) Step).
Qed.
Theorem reference_control_node_6705_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 6704 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2750 left = VM.find 2750 right ->
 VM.find 6704 left = VM.find 6704 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 6705 next_left = VM.find 6705 next_right.
Proof.
 intros H6704 E2750 E6704 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 6705 reference_control_expr_6705 reference_control_3_positions reference_control_3_safety reference_control_member_6705) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 6705 reference_control_expr_6705 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_6705 left H6704)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_6705 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2750.
 rewrite E6704.
 reflexivity.
Qed.
Lemma reference_control_ready_6706 old :
 (exists value ground, VM.find 6705 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_6706.
Proof.
 intros H6705.
 destruct H6705 as [v6705 [G6705 [V6705 T6705]]].
 unfold reference_control_expr_6706.
apply rc_mux.
{ apply rc_const.
}
{ eapply rc_ref; [exact V6705|exists G6705; exact T6705].
}
Qed.
Lemma reference_control_member_6706 : List.In (6706,reference_control_expr_6706) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 252%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_6706_ground inputs path old current result :
 (exists value ground, VM.find 6705 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 6706 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H6705 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 6706 reference_control_expr_6706 reference_control_3_positions reference_control_3_safety reference_control_member_6706) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 6706 reference_control_expr_6706 inputs path old current result Position Safe Nonreg (reference_control_ready_6706 old H6705) Step).
Qed.
Theorem reference_control_node_6706_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 6705 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2748 left = VM.find 2748 right ->
 VM.find 6705 left = VM.find 6705 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 6706 next_left = VM.find 6706 next_right.
Proof.
 intros H6705 E2748 E6705 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 6706 reference_control_expr_6706 reference_control_3_positions reference_control_3_safety reference_control_member_6706) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 6706 reference_control_expr_6706 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_6706 left H6705)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_6706 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2748.
 rewrite E6705.
 reflexivity.
Qed.
Lemma reference_control_ready_6709 old :
 (exists value ground, VM.find 6701 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 6706 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_6709.
Proof.
 intros H6701 H6706.
 destruct H6701 as [v6701 [G6701 [V6701 T6701]]].
 destruct H6706 as [v6706 [G6706 [V6706 T6706]]].
 unfold reference_control_expr_6709.
apply rc_mux.
{ eapply rc_ref; [exact V6706|exists G6706; exact T6706].
}
{ eapply rc_ref; [exact V6701|exists G6701; exact T6701].
}
Qed.
Lemma reference_control_member_6709 : List.In (6709,reference_control_expr_6709) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 253%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_6709_ground inputs path old current result :
 (exists value ground, VM.find 6701 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 6706 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 6709 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H6701 H6706 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 6709 reference_control_expr_6709 reference_control_3_positions reference_control_3_safety reference_control_member_6709) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 6709 reference_control_expr_6709 inputs path old current result Position Safe Nonreg (reference_control_ready_6709 old H6701 H6706) Step).
Qed.
Theorem reference_control_node_6709_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 6701 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 6706 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1933 left = VM.find 1933 right ->
 VM.find 6701 left = VM.find 6701 right ->
 VM.find 6706 left = VM.find 6706 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 6709 next_left = VM.find 6709 next_right.
Proof.
 intros H6701 H6706 E1933 E6701 E6706 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 6709 reference_control_expr_6709 reference_control_3_positions reference_control_3_safety reference_control_member_6709) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 6709 reference_control_expr_6709 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_6709 left H6701 H6706)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_6709 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1933.
 rewrite E6701.
 rewrite E6706.
 reflexivity.
Qed.
Lemma reference_control_ready_6778 old :
 (exists value ground, VM.find 6709 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_6778.
Proof.
 intros H6709.
 destruct H6709 as [v6709 [G6709 [V6709 T6709]]].
 unfold reference_control_expr_6778.
apply rc_mux.
{ apply rc_const.
}
{ eapply rc_ref; [exact V6709|exists G6709; exact T6709].
}
Qed.
Lemma reference_control_member_6778 : List.In (6778,reference_control_expr_6778) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 254%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_6778_ground inputs path old current result :
 (exists value ground, VM.find 6709 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 6778 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H6709 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 6778 reference_control_expr_6778 reference_control_3_positions reference_control_3_safety reference_control_member_6778) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 6778 reference_control_expr_6778 inputs path old current result Position Safe Nonreg (reference_control_ready_6778 old H6709) Step).
Qed.
Theorem reference_control_node_6778_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 6709 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 3042 left = VM.find 3042 right ->
 VM.find 6709 left = VM.find 6709 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 6778 next_left = VM.find 6778 next_right.
Proof.
 intros H6709 E3042 E6709 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 6778 reference_control_expr_6778 reference_control_3_positions reference_control_3_safety reference_control_member_6778) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 6778 reference_control_expr_6778 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_6778 left H6709)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_6778 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E3042.
 rewrite E6709.
 reflexivity.
Qed.
Lemma reference_control_ready_6779 old :
 (exists value ground, VM.find 6778 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_6779.
Proof.
 intros H6778.
 destruct H6778 as [v6778 [G6778 [V6778 T6778]]].
 unfold reference_control_expr_6779.
apply rc_mux.
{ eapply rc_ref; [exact V6778|exists G6778; exact T6778].
}
{ apply rc_const.
}
Qed.
Lemma reference_control_member_6779 : List.In (6779,reference_control_expr_6779) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 255%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_6779_ground inputs path old current result :
 (exists value ground, VM.find 6778 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 6779 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H6778 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 6779 reference_control_expr_6779 reference_control_3_positions reference_control_3_safety reference_control_member_6779) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 6779 reference_control_expr_6779 inputs path old current result Position Safe Nonreg (reference_control_ready_6779 old H6778) Step).
Qed.
Theorem reference_control_node_6779_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 6778 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1707 left = VM.find 1707 right ->
 VM.find 6778 left = VM.find 6778 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 6779 next_left = VM.find 6779 next_right.
Proof.
 intros H6778 E1707 E6778 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 6779 reference_control_expr_6779 reference_control_3_positions reference_control_3_safety reference_control_member_6779) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 6779 reference_control_expr_6779 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_6779 left H6778)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_6779 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1707.
 rewrite E6778.
 reflexivity.
Qed.
Lemma reference_control_ready_6780 old :
 (exists value ground, VM.find 6779 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_6780.
Proof.
 intros H6779.
 destruct H6779 as [v6779 [G6779 [V6779 T6779]]].
 unfold reference_control_expr_6780.
eapply rc_ref; [exact V6779|exists G6779; exact T6779].
Qed.
Lemma reference_control_member_6780 : List.In (6780,reference_control_expr_6780) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 256%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_6780_ground inputs path old current result :
 (exists value ground, VM.find 6779 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 6780 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H6779 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 6780 reference_control_expr_6780 reference_control_3_positions reference_control_3_safety reference_control_member_6780) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 6780 reference_control_expr_6780 inputs path old current result Position Safe Nonreg (reference_control_ready_6780 old H6779) Step).
Qed.
Theorem reference_control_node_6780_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 6779 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 6779 left = VM.find 6779 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 6780 next_left = VM.find 6780 next_right.
Proof.
 intros H6779 E6779 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 6780 reference_control_expr_6780 reference_control_3_positions reference_control_3_safety reference_control_member_6780) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 6780 reference_control_expr_6780 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_6780 left H6779)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_6780 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E6779.
 reflexivity.
Qed.
Lemma reference_control_ready_7763 old :
 reference_control_ready old reference_control_expr_7763.
Proof.
 unfold reference_control_expr_7763.
apply rc_binary.
Qed.
Lemma reference_control_member_7763 : List.In (7763,reference_control_expr_7763) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 257%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_7763_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 7763 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 7763 reference_control_expr_7763 reference_control_3_positions reference_control_3_safety reference_control_member_7763) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 7763 reference_control_expr_7763 inputs path old current result Position Safe Nonreg (reference_control_ready_7763 old ) Step).
Qed.
Theorem reference_control_node_7763_congruent inputs path left right next_left next_right :
 VM.find 74 left = VM.find 74 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 7763 next_left = VM.find 7763 next_right.
Proof.
 intros  E74 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 7763 reference_control_expr_7763 reference_control_3_positions reference_control_3_safety reference_control_member_7763) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 7763 reference_control_expr_7763 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_7763 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_7763 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E74.
 reflexivity.
Qed.
Lemma reference_control_ready_7764 old :
 reference_control_ready old reference_control_expr_7764.
Proof.
 unfold reference_control_expr_7764.
apply rc_binary.
Qed.
Lemma reference_control_member_7764 : List.In (7764,reference_control_expr_7764) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 258%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_7764_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 7764 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 7764 reference_control_expr_7764 reference_control_3_positions reference_control_3_safety reference_control_member_7764) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 7764 reference_control_expr_7764 inputs path old current result Position Safe Nonreg (reference_control_ready_7764 old ) Step).
Qed.
Theorem reference_control_node_7764_congruent inputs path left right next_left next_right :
 VM.find 81 left = VM.find 81 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 7764 next_left = VM.find 7764 next_right.
Proof.
 intros  E81 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 7764 reference_control_expr_7764 reference_control_3_positions reference_control_3_safety reference_control_member_7764) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 7764 reference_control_expr_7764 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_7764 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_7764 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E81.
 reflexivity.
Qed.
Lemma reference_control_ready_7765 old :
 reference_control_ready old reference_control_expr_7765.
Proof.
 unfold reference_control_expr_7765.
apply rc_binary.
Qed.
Lemma reference_control_member_7765 : List.In (7765,reference_control_expr_7765) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 259%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_7765_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 7765 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 7765 reference_control_expr_7765 reference_control_3_positions reference_control_3_safety reference_control_member_7765) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 7765 reference_control_expr_7765 inputs path old current result Position Safe Nonreg (reference_control_ready_7765 old ) Step).
Qed.
Theorem reference_control_node_7765_congruent inputs path left right next_left next_right :
 VM.find 7763 left = VM.find 7763 right ->
 VM.find 7764 left = VM.find 7764 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 7765 next_left = VM.find 7765 next_right.
Proof.
 intros  E7763 E7764 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 7765 reference_control_expr_7765 reference_control_3_positions reference_control_3_safety reference_control_member_7765) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 7765 reference_control_expr_7765 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_7765 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_7765 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E7763.
 rewrite E7764.
 reflexivity.
Qed.
Lemma reference_control_ready_7948 old :
 reference_control_ready old reference_control_expr_7948.
Proof.
 unfold reference_control_expr_7948.
apply rc_binary.
Qed.
Lemma reference_control_member_7948 : List.In (7948,reference_control_expr_7948) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 260%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_7948_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 7948 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 7948 reference_control_expr_7948 reference_control_3_positions reference_control_3_safety reference_control_member_7948) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 7948 reference_control_expr_7948 inputs path old current result Position Safe Nonreg (reference_control_ready_7948 old ) Step).
Qed.
Theorem reference_control_node_7948_congruent inputs path left right next_left next_right :
 VM.find 7765 left = VM.find 7765 right ->
 VM.find 7947 left = VM.find 7947 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 7948 next_left = VM.find 7948 next_right.
Proof.
 intros  E7765 E7947 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 7948 reference_control_expr_7948 reference_control_3_positions reference_control_3_safety reference_control_member_7948) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 7948 reference_control_expr_7948 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_7948 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_7948 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E7765.
 rewrite E7947.
 reflexivity.
Qed.
Lemma reference_control_ready_7949 old :
 reference_control_ready old reference_control_expr_7949.
Proof.
 unfold reference_control_expr_7949.
apply rc_cast.
Qed.
Lemma reference_control_member_7949 : List.In (7949,reference_control_expr_7949) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 261%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_7949_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 7949 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 7949 reference_control_expr_7949 reference_control_3_positions reference_control_3_safety reference_control_member_7949) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 7949 reference_control_expr_7949 inputs path old current result Position Safe Nonreg (reference_control_ready_7949 old ) Step).
Qed.
Theorem reference_control_node_7949_congruent inputs path left right next_left next_right :
 VM.find 65 left = VM.find 65 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 7949 next_left = VM.find 7949 next_right.
Proof.
 intros  E65 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 7949 reference_control_expr_7949 reference_control_3_positions reference_control_3_safety reference_control_member_7949) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 7949 reference_control_expr_7949 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_7949 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_7949 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E65.
 reflexivity.
Qed.
Lemma reference_control_ready_7950 old :
 reference_control_ready old reference_control_expr_7950.
Proof.
 unfold reference_control_expr_7950.
apply rc_binary.
Qed.
Lemma reference_control_member_7950 : List.In (7950,reference_control_expr_7950) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 262%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_7950_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 7950 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 7950 reference_control_expr_7950 reference_control_3_positions reference_control_3_safety reference_control_member_7950) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 7950 reference_control_expr_7950 inputs path old current result Position Safe Nonreg (reference_control_ready_7950 old ) Step).
Qed.
Theorem reference_control_node_7950_congruent inputs path left right next_left next_right :
 VM.find 7948 left = VM.find 7948 right ->
 VM.find 7949 left = VM.find 7949 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 7950 next_left = VM.find 7950 next_right.
Proof.
 intros  E7948 E7949 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 7950 reference_control_expr_7950 reference_control_3_positions reference_control_3_safety reference_control_member_7950) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 7950 reference_control_expr_7950 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_7950 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_7950 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E7948.
 rewrite E7949.
 reflexivity.
Qed.
Lemma reference_control_ready_7951 old :
 (exists value ground, VM.find 7950 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_7951.
Proof.
 intros H7950.
 destruct H7950 as [v7950 [G7950 [V7950 T7950]]].
 unfold reference_control_expr_7951.
eapply rc_ref; [exact V7950|exists G7950; exact T7950].
Qed.
Lemma reference_control_member_7951 : List.In (7951,reference_control_expr_7951) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 263%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_7951_ground inputs path old current result :
 (exists value ground, VM.find 7950 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 7951 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H7950 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 7951 reference_control_expr_7951 reference_control_3_positions reference_control_3_safety reference_control_member_7951) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 7951 reference_control_expr_7951 inputs path old current result Position Safe Nonreg (reference_control_ready_7951 old H7950) Step).
Qed.
Theorem reference_control_node_7951_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 7950 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 7950 left = VM.find 7950 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 7951 next_left = VM.find 7951 next_right.
Proof.
 intros H7950 E7950 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 7951 reference_control_expr_7951 reference_control_3_positions reference_control_3_safety reference_control_member_7951) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 7951 reference_control_expr_7951 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_7951 left H7950)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_7951 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E7950.
 reflexivity.
Qed.
Lemma reference_control_ready_7952 old :
 reference_control_ready old reference_control_expr_7952.
Proof.
 unfold reference_control_expr_7952.
apply rc_binary.
Qed.
Lemma reference_control_member_7952 : List.In (7952,reference_control_expr_7952) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 264%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_7952_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 7952 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 7952 reference_control_expr_7952 reference_control_3_positions reference_control_3_safety reference_control_member_7952) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 7952 reference_control_expr_7952 inputs path old current result Position Safe Nonreg (reference_control_ready_7952 old ) Step).
Qed.
Theorem reference_control_node_7952_congruent inputs path left right next_left next_right :
 VM.find 7951 left = VM.find 7951 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 7952 next_left = VM.find 7952 next_right.
Proof.
 intros  E7951 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 7952 reference_control_expr_7952 reference_control_3_positions reference_control_3_safety reference_control_member_7952) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 7952 reference_control_expr_7952 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_7952 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_7952 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E7951.
 reflexivity.
Qed.
Lemma reference_control_ready_7956 old :
 (exists value ground, VM.find 7952 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_7956.
Proof.
 intros H7952.
 destruct H7952 as [v7952 [G7952 [V7952 T7952]]].
 unfold reference_control_expr_7956.
eapply rc_ref; [exact V7952|exists G7952; exact T7952].
Qed.
Lemma reference_control_member_7956 : List.In (7956,reference_control_expr_7956) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 265%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_7956_ground inputs path old current result :
 (exists value ground, VM.find 7952 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 7956 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H7952 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 7956 reference_control_expr_7956 reference_control_3_positions reference_control_3_safety reference_control_member_7956) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 7956 reference_control_expr_7956 inputs path old current result Position Safe Nonreg (reference_control_ready_7956 old H7952) Step).
Qed.
Theorem reference_control_node_7956_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 7952 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 7952 left = VM.find 7952 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 7956 next_left = VM.find 7956 next_right.
Proof.
 intros H7952 E7952 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 7956 reference_control_expr_7956 reference_control_3_positions reference_control_3_safety reference_control_member_7956) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 7956 reference_control_expr_7956 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_7956 left H7952)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_7956 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E7952.
 reflexivity.
Qed.
Lemma reference_control_ready_9215 old :
 reference_control_ready old reference_control_expr_9215.
Proof.
 unfold reference_control_expr_9215.
apply rc_unary.
Qed.
Lemma reference_control_member_9215 : List.In (9215,reference_control_expr_9215) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 266%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_9215_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 9215 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 9215 reference_control_expr_9215 reference_control_3_positions reference_control_3_safety reference_control_member_9215) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 9215 reference_control_expr_9215 inputs path old current result Position Safe Nonreg (reference_control_ready_9215 old ) Step).
Qed.
Theorem reference_control_node_9215_congruent inputs path left right next_left next_right :
 VM.find 1 left = VM.find 1 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 9215 next_left = VM.find 9215 next_right.
Proof.
 intros  E1 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 9215 reference_control_expr_9215 reference_control_3_positions reference_control_3_safety reference_control_member_9215) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 9215 reference_control_expr_9215 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_9215 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_9215 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1.
 reflexivity.
Qed.
Lemma reference_control_ready_9216 old :
 reference_control_ready old reference_control_expr_9216.
Proof.
 unfold reference_control_expr_9216.
apply rc_binary.
Qed.
Lemma reference_control_member_9216 : List.In (9216,reference_control_expr_9216) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 267%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_9216_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 9216 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 9216 reference_control_expr_9216 reference_control_3_positions reference_control_3_safety reference_control_member_9216) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 9216 reference_control_expr_9216 inputs path old current result Position Safe Nonreg (reference_control_ready_9216 old ) Step).
Qed.
Theorem reference_control_node_9216_congruent inputs path left right next_left next_right :
 VM.find 9215 left = VM.find 9215 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 9216 next_left = VM.find 9216 next_right.
Proof.
 intros  E9215 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 9216 reference_control_expr_9216 reference_control_3_positions reference_control_3_safety reference_control_member_9216) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 9216 reference_control_expr_9216 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_9216 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_9216 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E9215.
 reflexivity.
Qed.
Lemma reference_control_ready_9217 old :
 reference_control_ready old reference_control_expr_9217.
Proof.
 unfold reference_control_expr_9217.
apply rc_unary.
Qed.
Lemma reference_control_member_9217 : List.In (9217,reference_control_expr_9217) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 268%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_9217_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 9217 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 9217 reference_control_expr_9217 reference_control_3_positions reference_control_3_safety reference_control_member_9217) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 9217 reference_control_expr_9217 inputs path old current result Position Safe Nonreg (reference_control_ready_9217 old ) Step).
Qed.
Theorem reference_control_node_9217_congruent inputs path left right next_left next_right :
 VM.find 1 left = VM.find 1 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 9217 next_left = VM.find 9217 next_right.
Proof.
 intros  E1 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 9217 reference_control_expr_9217 reference_control_3_positions reference_control_3_safety reference_control_member_9217) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 9217 reference_control_expr_9217 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_9217 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_9217 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1.
 reflexivity.
Qed.
Lemma reference_control_ready_9218 old :
 reference_control_ready old reference_control_expr_9218.
Proof.
 unfold reference_control_expr_9218.
apply rc_binary.
Qed.
Lemma reference_control_member_9218 : List.In (9218,reference_control_expr_9218) reference_control_3_nodes.
Proof. apply (List.nth_error_In reference_control_3_nodes 269%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_9218_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 9218 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 9218 reference_control_expr_9218 reference_control_3_positions reference_control_3_safety reference_control_member_9218) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 9218 reference_control_expr_9218 inputs path old current result Position Safe Nonreg (reference_control_ready_9218 old ) Step).
Qed.
Theorem reference_control_node_9218_congruent inputs path left right next_left next_right :
 VM.find 9217 left = VM.find 9217 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 9218 next_left = VM.find 9218 next_right.
Proof.
 intros  E9217 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes 9218 reference_control_expr_9218 reference_control_3_positions reference_control_3_safety reference_control_member_9218) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 9218 reference_control_expr_9218 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_9218 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_9218 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E9217.
 reflexivity.
Qed.
Print Assumptions reference_control_node_9218_congruent.
