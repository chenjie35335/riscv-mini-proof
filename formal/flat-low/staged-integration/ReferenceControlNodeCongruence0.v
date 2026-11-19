Require Import CoreSocModel ComparisonNodes ReferenceControlExpressions ReferenceControlGroundOperations ReferenceControlGroundExpressions ReferenceControlNodeGeneric SelectedNodeSafety.
From Coq Require Import ZArith List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Require Import ReferenceControlNodeCertificates0.
Lemma reference_control_ready_1883 old :
 (exists value ground, VM.find 1706 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_1883.
Proof.
 intros H1706.
 destruct H1706 as [v1706 [G1706 [V1706 T1706]]].
 unfold reference_control_expr_1883.
apply rc_mux.
{ eapply rc_ref; [exact V1706|exists G1706; exact T1706].
}
{ apply rc_const.
}
Qed.
Lemma reference_control_member_1883 : List.In (1883,reference_control_expr_1883) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 0%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_1883_ground inputs path old current result :
 (exists value ground, VM.find 1706 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 1883 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H1706 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1883 reference_control_expr_1883 reference_control_0_positions reference_control_0_safety reference_control_member_1883) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 1883 reference_control_expr_1883 inputs path old current result Position Safe Nonreg (reference_control_ready_1883 old H1706) Step).
Qed.
Theorem reference_control_node_1883_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 1706 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1706 left = VM.find 1706 right ->
 VM.find 1707 left = VM.find 1707 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 1883 next_left = VM.find 1883 next_right.
Proof.
 intros H1706 E1706 E1707 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1883 reference_control_expr_1883 reference_control_0_positions reference_control_0_safety reference_control_member_1883) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 1883 reference_control_expr_1883 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_1883 left H1706)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_1883 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1706.
 rewrite E1707.
 reflexivity.
Qed.
Lemma reference_control_ready_1884 old :
 (exists value ground, VM.find 1883 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_1884.
Proof.
 intros H1883.
 destruct H1883 as [v1883 [G1883 [V1883 T1883]]].
 unfold reference_control_expr_1884.
eapply rc_ref; [exact V1883|exists G1883; exact T1883].
Qed.
Lemma reference_control_member_1884 : List.In (1884,reference_control_expr_1884) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 1%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_1884_ground inputs path old current result :
 (exists value ground, VM.find 1883 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 1884 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H1883 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1884 reference_control_expr_1884 reference_control_0_positions reference_control_0_safety reference_control_member_1884) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 1884 reference_control_expr_1884 inputs path old current result Position Safe Nonreg (reference_control_ready_1884 old H1883) Step).
Qed.
Theorem reference_control_node_1884_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 1883 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1883 left = VM.find 1883 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 1884 next_left = VM.find 1884 next_right.
Proof.
 intros H1883 E1883 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1884 reference_control_expr_1884 reference_control_0_positions reference_control_0_safety reference_control_member_1884) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 1884 reference_control_expr_1884 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_1884 left H1883)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_1884 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1883.
 reflexivity.
Qed.
Lemma reference_control_ready_1885 old :
 reference_control_ready old reference_control_expr_1885.
Proof.
 unfold reference_control_expr_1885.
apply rc_binary.
Qed.
Lemma reference_control_member_1885 : List.In (1885,reference_control_expr_1885) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 2%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_1885_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 1885 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1885 reference_control_expr_1885 reference_control_0_positions reference_control_0_safety reference_control_member_1885) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 1885 reference_control_expr_1885 inputs path old current result Position Safe Nonreg (reference_control_ready_1885 old ) Step).
Qed.
Theorem reference_control_node_1885_congruent inputs path left right next_left next_right :
 VM.find 1884 left = VM.find 1884 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 1885 next_left = VM.find 1885 next_right.
Proof.
 intros  E1884 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1885 reference_control_expr_1885 reference_control_0_positions reference_control_0_safety reference_control_member_1885) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 1885 reference_control_expr_1885 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_1885 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_1885 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1884.
 reflexivity.
Qed.
Lemma reference_control_ready_1886 old :
 reference_control_ready old reference_control_expr_1886.
Proof.
 unfold reference_control_expr_1886.
apply rc_binary.
Qed.
Lemma reference_control_member_1886 : List.In (1886,reference_control_expr_1886) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 3%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_1886_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 1886 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1886 reference_control_expr_1886 reference_control_0_positions reference_control_0_safety reference_control_member_1886) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 1886 reference_control_expr_1886 inputs path old current result Position Safe Nonreg (reference_control_ready_1886 old ) Step).
Qed.
Theorem reference_control_node_1886_congruent inputs path left right next_left next_right :
 VM.find 1885 left = VM.find 1885 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 1886 next_left = VM.find 1886 next_right.
Proof.
 intros  E1885 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1886 reference_control_expr_1886 reference_control_0_positions reference_control_0_safety reference_control_member_1886) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 1886 reference_control_expr_1886 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_1886 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_1886 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1885.
 reflexivity.
Qed.
Lemma reference_control_ready_1887 old :
 reference_control_ready old reference_control_expr_1887.
Proof.
 unfold reference_control_expr_1887.
apply rc_binary.
Qed.
Lemma reference_control_member_1887 : List.In (1887,reference_control_expr_1887) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 4%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_1887_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 1887 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1887 reference_control_expr_1887 reference_control_0_positions reference_control_0_safety reference_control_member_1887) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 1887 reference_control_expr_1887 inputs path old current result Position Safe Nonreg (reference_control_ready_1887 old ) Step).
Qed.
Theorem reference_control_node_1887_congruent inputs path left right next_left next_right :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 1887 next_left = VM.find 1887 next_right.
Proof.
 intros   L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1887 reference_control_expr_1887 reference_control_0_positions reference_control_0_safety reference_control_member_1887) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 1887 reference_control_expr_1887 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_1887 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_1887 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 reflexivity.
Qed.
Lemma reference_control_ready_1888 old :
 reference_control_ready old reference_control_expr_1888.
Proof.
 unfold reference_control_expr_1888.
apply rc_binary.
Qed.
Lemma reference_control_member_1888 : List.In (1888,reference_control_expr_1888) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 5%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_1888_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 1888 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1888 reference_control_expr_1888 reference_control_0_positions reference_control_0_safety reference_control_member_1888) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 1888 reference_control_expr_1888 inputs path old current result Position Safe Nonreg (reference_control_ready_1888 old ) Step).
Qed.
Theorem reference_control_node_1888_congruent inputs path left right next_left next_right :
 VM.find 1884 left = VM.find 1884 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 1888 next_left = VM.find 1888 next_right.
Proof.
 intros  E1884 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1888 reference_control_expr_1888 reference_control_0_positions reference_control_0_safety reference_control_member_1888) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 1888 reference_control_expr_1888 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_1888 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_1888 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1884.
 reflexivity.
Qed.
Lemma reference_control_ready_1889 old :
 reference_control_ready old reference_control_expr_1889.
Proof.
 unfold reference_control_expr_1889.
apply rc_binary.
Qed.
Lemma reference_control_member_1889 : List.In (1889,reference_control_expr_1889) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 6%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_1889_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 1889 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1889 reference_control_expr_1889 reference_control_0_positions reference_control_0_safety reference_control_member_1889) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 1889 reference_control_expr_1889 inputs path old current result Position Safe Nonreg (reference_control_ready_1889 old ) Step).
Qed.
Theorem reference_control_node_1889_congruent inputs path left right next_left next_right :
 VM.find 1888 left = VM.find 1888 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 1889 next_left = VM.find 1889 next_right.
Proof.
 intros  E1888 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1889 reference_control_expr_1889 reference_control_0_positions reference_control_0_safety reference_control_member_1889) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 1889 reference_control_expr_1889 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_1889 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_1889 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1888.
 reflexivity.
Qed.
Lemma reference_control_ready_1890 old :
 reference_control_ready old reference_control_expr_1890.
Proof.
 unfold reference_control_expr_1890.
apply rc_unary.
Qed.
Lemma reference_control_member_1890 : List.In (1890,reference_control_expr_1890) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 7%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_1890_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 1890 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1890 reference_control_expr_1890 reference_control_0_positions reference_control_0_safety reference_control_member_1890) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 1890 reference_control_expr_1890 inputs path old current result Position Safe Nonreg (reference_control_ready_1890 old ) Step).
Qed.
Theorem reference_control_node_1890_congruent inputs path left right next_left next_right :
 VM.find 1884 left = VM.find 1884 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 1890 next_left = VM.find 1890 next_right.
Proof.
 intros  E1884 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1890 reference_control_expr_1890 reference_control_0_positions reference_control_0_safety reference_control_member_1890) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 1890 reference_control_expr_1890 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_1890 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_1890 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1884.
 reflexivity.
Qed.
Lemma reference_control_ready_1891 old :
 reference_control_ready old reference_control_expr_1891.
Proof.
 unfold reference_control_expr_1891.
apply rc_unary.
Qed.
Lemma reference_control_member_1891 : List.In (1891,reference_control_expr_1891) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 8%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_1891_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 1891 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1891 reference_control_expr_1891 reference_control_0_positions reference_control_0_safety reference_control_member_1891) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 1891 reference_control_expr_1891 inputs path old current result Position Safe Nonreg (reference_control_ready_1891 old ) Step).
Qed.
Theorem reference_control_node_1891_congruent inputs path left right next_left next_right :
 VM.find 1890 left = VM.find 1890 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 1891 next_left = VM.find 1891 next_right.
Proof.
 intros  E1890 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1891 reference_control_expr_1891 reference_control_0_positions reference_control_0_safety reference_control_member_1891) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 1891 reference_control_expr_1891 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_1891 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_1891 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1890.
 reflexivity.
Qed.
Lemma reference_control_ready_1892 old :
 reference_control_ready old reference_control_expr_1892.
Proof.
 unfold reference_control_expr_1892.
apply rc_unary.
Qed.
Lemma reference_control_member_1892 : List.In (1892,reference_control_expr_1892) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 9%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_1892_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 1892 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1892 reference_control_expr_1892 reference_control_0_positions reference_control_0_safety reference_control_member_1892) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 1892 reference_control_expr_1892 inputs path old current result Position Safe Nonreg (reference_control_ready_1892 old ) Step).
Qed.
Theorem reference_control_node_1892_congruent inputs path left right next_left next_right :
 VM.find 1891 left = VM.find 1891 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 1892 next_left = VM.find 1892 next_right.
Proof.
 intros  E1891 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1892 reference_control_expr_1892 reference_control_0_positions reference_control_0_safety reference_control_member_1892) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 1892 reference_control_expr_1892 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_1892 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_1892 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1891.
 reflexivity.
Qed.
Lemma reference_control_ready_1893 old :
 reference_control_ready old reference_control_expr_1893.
Proof.
 unfold reference_control_expr_1893.
apply rc_binary.
Qed.
Lemma reference_control_member_1893 : List.In (1893,reference_control_expr_1893) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 10%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_1893_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 1893 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1893 reference_control_expr_1893 reference_control_0_positions reference_control_0_safety reference_control_member_1893) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 1893 reference_control_expr_1893 inputs path old current result Position Safe Nonreg (reference_control_ready_1893 old ) Step).
Qed.
Theorem reference_control_node_1893_congruent inputs path left right next_left next_right :
 VM.find 1884 left = VM.find 1884 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 1893 next_left = VM.find 1893 next_right.
Proof.
 intros  E1884 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1893 reference_control_expr_1893 reference_control_0_positions reference_control_0_safety reference_control_member_1893) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 1893 reference_control_expr_1893 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_1893 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_1893 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1884.
 reflexivity.
Qed.
Lemma reference_control_ready_1894 old :
 reference_control_ready old reference_control_expr_1894.
Proof.
 unfold reference_control_expr_1894.
apply rc_binary.
Qed.
Lemma reference_control_member_1894 : List.In (1894,reference_control_expr_1894) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 11%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_1894_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 1894 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1894 reference_control_expr_1894 reference_control_0_positions reference_control_0_safety reference_control_member_1894) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 1894 reference_control_expr_1894 inputs path old current result Position Safe Nonreg (reference_control_ready_1894 old ) Step).
Qed.
Theorem reference_control_node_1894_congruent inputs path left right next_left next_right :
 VM.find 1893 left = VM.find 1893 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 1894 next_left = VM.find 1894 next_right.
Proof.
 intros  E1893 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1894 reference_control_expr_1894 reference_control_0_positions reference_control_0_safety reference_control_member_1894) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 1894 reference_control_expr_1894 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_1894 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_1894 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1893.
 reflexivity.
Qed.
Lemma reference_control_ready_1895 old :
 reference_control_ready old reference_control_expr_1895.
Proof.
 unfold reference_control_expr_1895.
apply rc_unary.
Qed.
Lemma reference_control_member_1895 : List.In (1895,reference_control_expr_1895) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 12%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_1895_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 1895 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1895 reference_control_expr_1895 reference_control_0_positions reference_control_0_safety reference_control_member_1895) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 1895 reference_control_expr_1895 inputs path old current result Position Safe Nonreg (reference_control_ready_1895 old ) Step).
Qed.
Theorem reference_control_node_1895_congruent inputs path left right next_left next_right :
 VM.find 1884 left = VM.find 1884 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 1895 next_left = VM.find 1895 next_right.
Proof.
 intros  E1884 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1895 reference_control_expr_1895 reference_control_0_positions reference_control_0_safety reference_control_member_1895) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 1895 reference_control_expr_1895 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_1895 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_1895 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1884.
 reflexivity.
Qed.
Lemma reference_control_ready_1896 old :
 reference_control_ready old reference_control_expr_1896.
Proof.
 unfold reference_control_expr_1896.
apply rc_unary.
Qed.
Lemma reference_control_member_1896 : List.In (1896,reference_control_expr_1896) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 13%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_1896_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 1896 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1896 reference_control_expr_1896 reference_control_0_positions reference_control_0_safety reference_control_member_1896) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 1896 reference_control_expr_1896 inputs path old current result Position Safe Nonreg (reference_control_ready_1896 old ) Step).
Qed.
Theorem reference_control_node_1896_congruent inputs path left right next_left next_right :
 VM.find 1895 left = VM.find 1895 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 1896 next_left = VM.find 1896 next_right.
Proof.
 intros  E1895 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1896 reference_control_expr_1896 reference_control_0_positions reference_control_0_safety reference_control_member_1896) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 1896 reference_control_expr_1896 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_1896 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_1896 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1895.
 reflexivity.
Qed.
Lemma reference_control_ready_1897 old :
 reference_control_ready old reference_control_expr_1897.
Proof.
 unfold reference_control_expr_1897.
apply rc_unary.
Qed.
Lemma reference_control_member_1897 : List.In (1897,reference_control_expr_1897) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 14%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_1897_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 1897 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1897 reference_control_expr_1897 reference_control_0_positions reference_control_0_safety reference_control_member_1897) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 1897 reference_control_expr_1897 inputs path old current result Position Safe Nonreg (reference_control_ready_1897 old ) Step).
Qed.
Theorem reference_control_node_1897_congruent inputs path left right next_left next_right :
 VM.find 1896 left = VM.find 1896 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 1897 next_left = VM.find 1897 next_right.
Proof.
 intros  E1896 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1897 reference_control_expr_1897 reference_control_0_positions reference_control_0_safety reference_control_member_1897) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 1897 reference_control_expr_1897 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_1897 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_1897 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1896.
 reflexivity.
Qed.
Lemma reference_control_ready_1898 old :
 reference_control_ready old reference_control_expr_1898.
Proof.
 unfold reference_control_expr_1898.
apply rc_binary.
Qed.
Lemma reference_control_member_1898 : List.In (1898,reference_control_expr_1898) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 15%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_1898_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 1898 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1898 reference_control_expr_1898 reference_control_0_positions reference_control_0_safety reference_control_member_1898) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 1898 reference_control_expr_1898 inputs path old current result Position Safe Nonreg (reference_control_ready_1898 old ) Step).
Qed.
Theorem reference_control_node_1898_congruent inputs path left right next_left next_right :
 VM.find 1884 left = VM.find 1884 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 1898 next_left = VM.find 1898 next_right.
Proof.
 intros  E1884 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1898 reference_control_expr_1898 reference_control_0_positions reference_control_0_safety reference_control_member_1898) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 1898 reference_control_expr_1898 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_1898 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_1898 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1884.
 reflexivity.
Qed.
Lemma reference_control_ready_1899 old :
 reference_control_ready old reference_control_expr_1899.
Proof.
 unfold reference_control_expr_1899.
apply rc_binary.
Qed.
Lemma reference_control_member_1899 : List.In (1899,reference_control_expr_1899) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 16%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_1899_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 1899 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1899 reference_control_expr_1899 reference_control_0_positions reference_control_0_safety reference_control_member_1899) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 1899 reference_control_expr_1899 inputs path old current result Position Safe Nonreg (reference_control_ready_1899 old ) Step).
Qed.
Theorem reference_control_node_1899_congruent inputs path left right next_left next_right :
 VM.find 1898 left = VM.find 1898 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 1899 next_left = VM.find 1899 next_right.
Proof.
 intros  E1898 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1899 reference_control_expr_1899 reference_control_0_positions reference_control_0_safety reference_control_member_1899) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 1899 reference_control_expr_1899 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_1899 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_1899 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1898.
 reflexivity.
Qed.
Lemma reference_control_ready_1900 old :
 reference_control_ready old reference_control_expr_1900.
Proof.
 unfold reference_control_expr_1900.
apply rc_unary.
Qed.
Lemma reference_control_member_1900 : List.In (1900,reference_control_expr_1900) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 17%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_1900_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 1900 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1900 reference_control_expr_1900 reference_control_0_positions reference_control_0_safety reference_control_member_1900) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 1900 reference_control_expr_1900 inputs path old current result Position Safe Nonreg (reference_control_ready_1900 old ) Step).
Qed.
Theorem reference_control_node_1900_congruent inputs path left right next_left next_right :
 VM.find 1884 left = VM.find 1884 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 1900 next_left = VM.find 1900 next_right.
Proof.
 intros  E1884 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1900 reference_control_expr_1900 reference_control_0_positions reference_control_0_safety reference_control_member_1900) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 1900 reference_control_expr_1900 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_1900 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_1900 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1884.
 reflexivity.
Qed.
Lemma reference_control_ready_1901 old :
 reference_control_ready old reference_control_expr_1901.
Proof.
 unfold reference_control_expr_1901.
apply rc_unary.
Qed.
Lemma reference_control_member_1901 : List.In (1901,reference_control_expr_1901) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 18%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_1901_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 1901 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1901 reference_control_expr_1901 reference_control_0_positions reference_control_0_safety reference_control_member_1901) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 1901 reference_control_expr_1901 inputs path old current result Position Safe Nonreg (reference_control_ready_1901 old ) Step).
Qed.
Theorem reference_control_node_1901_congruent inputs path left right next_left next_right :
 VM.find 1900 left = VM.find 1900 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 1901 next_left = VM.find 1901 next_right.
Proof.
 intros  E1900 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1901 reference_control_expr_1901 reference_control_0_positions reference_control_0_safety reference_control_member_1901) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 1901 reference_control_expr_1901 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_1901 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_1901 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1900.
 reflexivity.
Qed.
Lemma reference_control_ready_1902 old :
 reference_control_ready old reference_control_expr_1902.
Proof.
 unfold reference_control_expr_1902.
apply rc_unary.
Qed.
Lemma reference_control_member_1902 : List.In (1902,reference_control_expr_1902) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 19%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_1902_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 1902 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1902 reference_control_expr_1902 reference_control_0_positions reference_control_0_safety reference_control_member_1902) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 1902 reference_control_expr_1902 inputs path old current result Position Safe Nonreg (reference_control_ready_1902 old ) Step).
Qed.
Theorem reference_control_node_1902_congruent inputs path left right next_left next_right :
 VM.find 1901 left = VM.find 1901 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 1902 next_left = VM.find 1902 next_right.
Proof.
 intros  E1901 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1902 reference_control_expr_1902 reference_control_0_positions reference_control_0_safety reference_control_member_1902) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 1902 reference_control_expr_1902 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_1902 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_1902 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1901.
 reflexivity.
Qed.
Lemma reference_control_ready_1903 old :
 reference_control_ready old reference_control_expr_1903.
Proof.
 unfold reference_control_expr_1903.
apply rc_binary.
Qed.
Lemma reference_control_member_1903 : List.In (1903,reference_control_expr_1903) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 20%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_1903_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 1903 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1903 reference_control_expr_1903 reference_control_0_positions reference_control_0_safety reference_control_member_1903) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 1903 reference_control_expr_1903 inputs path old current result Position Safe Nonreg (reference_control_ready_1903 old ) Step).
Qed.
Theorem reference_control_node_1903_congruent inputs path left right next_left next_right :
 VM.find 1884 left = VM.find 1884 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 1903 next_left = VM.find 1903 next_right.
Proof.
 intros  E1884 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1903 reference_control_expr_1903 reference_control_0_positions reference_control_0_safety reference_control_member_1903) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 1903 reference_control_expr_1903 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_1903 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_1903 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1884.
 reflexivity.
Qed.
Lemma reference_control_ready_1904 old :
 reference_control_ready old reference_control_expr_1904.
Proof.
 unfold reference_control_expr_1904.
apply rc_binary.
Qed.
Lemma reference_control_member_1904 : List.In (1904,reference_control_expr_1904) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 21%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_1904_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 1904 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1904 reference_control_expr_1904 reference_control_0_positions reference_control_0_safety reference_control_member_1904) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 1904 reference_control_expr_1904 inputs path old current result Position Safe Nonreg (reference_control_ready_1904 old ) Step).
Qed.
Theorem reference_control_node_1904_congruent inputs path left right next_left next_right :
 VM.find 1903 left = VM.find 1903 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 1904 next_left = VM.find 1904 next_right.
Proof.
 intros  E1903 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1904 reference_control_expr_1904 reference_control_0_positions reference_control_0_safety reference_control_member_1904) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 1904 reference_control_expr_1904 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_1904 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_1904 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1903.
 reflexivity.
Qed.
Lemma reference_control_ready_1905 old :
 reference_control_ready old reference_control_expr_1905.
Proof.
 unfold reference_control_expr_1905.
apply rc_unary.
Qed.
Lemma reference_control_member_1905 : List.In (1905,reference_control_expr_1905) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 22%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_1905_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 1905 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1905 reference_control_expr_1905 reference_control_0_positions reference_control_0_safety reference_control_member_1905) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 1905 reference_control_expr_1905 inputs path old current result Position Safe Nonreg (reference_control_ready_1905 old ) Step).
Qed.
Theorem reference_control_node_1905_congruent inputs path left right next_left next_right :
 VM.find 1884 left = VM.find 1884 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 1905 next_left = VM.find 1905 next_right.
Proof.
 intros  E1884 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1905 reference_control_expr_1905 reference_control_0_positions reference_control_0_safety reference_control_member_1905) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 1905 reference_control_expr_1905 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_1905 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_1905 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1884.
 reflexivity.
Qed.
Lemma reference_control_ready_1906 old :
 reference_control_ready old reference_control_expr_1906.
Proof.
 unfold reference_control_expr_1906.
apply rc_unary.
Qed.
Lemma reference_control_member_1906 : List.In (1906,reference_control_expr_1906) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 23%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_1906_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 1906 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1906 reference_control_expr_1906 reference_control_0_positions reference_control_0_safety reference_control_member_1906) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 1906 reference_control_expr_1906 inputs path old current result Position Safe Nonreg (reference_control_ready_1906 old ) Step).
Qed.
Theorem reference_control_node_1906_congruent inputs path left right next_left next_right :
 VM.find 1905 left = VM.find 1905 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 1906 next_left = VM.find 1906 next_right.
Proof.
 intros  E1905 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1906 reference_control_expr_1906 reference_control_0_positions reference_control_0_safety reference_control_member_1906) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 1906 reference_control_expr_1906 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_1906 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_1906 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1905.
 reflexivity.
Qed.
Lemma reference_control_ready_1907 old :
 reference_control_ready old reference_control_expr_1907.
Proof.
 unfold reference_control_expr_1907.
apply rc_unary.
Qed.
Lemma reference_control_member_1907 : List.In (1907,reference_control_expr_1907) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 24%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_1907_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 1907 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1907 reference_control_expr_1907 reference_control_0_positions reference_control_0_safety reference_control_member_1907) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 1907 reference_control_expr_1907 inputs path old current result Position Safe Nonreg (reference_control_ready_1907 old ) Step).
Qed.
Theorem reference_control_node_1907_congruent inputs path left right next_left next_right :
 VM.find 1906 left = VM.find 1906 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 1907 next_left = VM.find 1907 next_right.
Proof.
 intros  E1906 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1907 reference_control_expr_1907 reference_control_0_positions reference_control_0_safety reference_control_member_1907) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 1907 reference_control_expr_1907 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_1907 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_1907 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1906.
 reflexivity.
Qed.
Lemma reference_control_ready_1908 old :
 reference_control_ready old reference_control_expr_1908.
Proof.
 unfold reference_control_expr_1908.
apply rc_binary.
Qed.
Lemma reference_control_member_1908 : List.In (1908,reference_control_expr_1908) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 25%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_1908_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 1908 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1908 reference_control_expr_1908 reference_control_0_positions reference_control_0_safety reference_control_member_1908) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 1908 reference_control_expr_1908 inputs path old current result Position Safe Nonreg (reference_control_ready_1908 old ) Step).
Qed.
Theorem reference_control_node_1908_congruent inputs path left right next_left next_right :
 VM.find 1884 left = VM.find 1884 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 1908 next_left = VM.find 1908 next_right.
Proof.
 intros  E1884 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1908 reference_control_expr_1908 reference_control_0_positions reference_control_0_safety reference_control_member_1908) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 1908 reference_control_expr_1908 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_1908 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_1908 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1884.
 reflexivity.
Qed.
Lemma reference_control_ready_1909 old :
 reference_control_ready old reference_control_expr_1909.
Proof.
 unfold reference_control_expr_1909.
apply rc_binary.
Qed.
Lemma reference_control_member_1909 : List.In (1909,reference_control_expr_1909) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 26%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_1909_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 1909 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1909 reference_control_expr_1909 reference_control_0_positions reference_control_0_safety reference_control_member_1909) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 1909 reference_control_expr_1909 inputs path old current result Position Safe Nonreg (reference_control_ready_1909 old ) Step).
Qed.
Theorem reference_control_node_1909_congruent inputs path left right next_left next_right :
 VM.find 1908 left = VM.find 1908 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 1909 next_left = VM.find 1909 next_right.
Proof.
 intros  E1908 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1909 reference_control_expr_1909 reference_control_0_positions reference_control_0_safety reference_control_member_1909) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 1909 reference_control_expr_1909 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_1909 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_1909 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1908.
 reflexivity.
Qed.
Lemma reference_control_ready_1910 old :
 reference_control_ready old reference_control_expr_1910.
Proof.
 unfold reference_control_expr_1910.
apply rc_unary.
Qed.
Lemma reference_control_member_1910 : List.In (1910,reference_control_expr_1910) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 27%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_1910_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 1910 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1910 reference_control_expr_1910 reference_control_0_positions reference_control_0_safety reference_control_member_1910) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 1910 reference_control_expr_1910 inputs path old current result Position Safe Nonreg (reference_control_ready_1910 old ) Step).
Qed.
Theorem reference_control_node_1910_congruent inputs path left right next_left next_right :
 VM.find 1884 left = VM.find 1884 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 1910 next_left = VM.find 1910 next_right.
Proof.
 intros  E1884 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1910 reference_control_expr_1910 reference_control_0_positions reference_control_0_safety reference_control_member_1910) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 1910 reference_control_expr_1910 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_1910 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_1910 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1884.
 reflexivity.
Qed.
Lemma reference_control_ready_1911 old :
 reference_control_ready old reference_control_expr_1911.
Proof.
 unfold reference_control_expr_1911.
apply rc_unary.
Qed.
Lemma reference_control_member_1911 : List.In (1911,reference_control_expr_1911) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 28%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_1911_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 1911 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1911 reference_control_expr_1911 reference_control_0_positions reference_control_0_safety reference_control_member_1911) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 1911 reference_control_expr_1911 inputs path old current result Position Safe Nonreg (reference_control_ready_1911 old ) Step).
Qed.
Theorem reference_control_node_1911_congruent inputs path left right next_left next_right :
 VM.find 1910 left = VM.find 1910 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 1911 next_left = VM.find 1911 next_right.
Proof.
 intros  E1910 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1911 reference_control_expr_1911 reference_control_0_positions reference_control_0_safety reference_control_member_1911) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 1911 reference_control_expr_1911 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_1911 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_1911 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1910.
 reflexivity.
Qed.
Lemma reference_control_ready_1912 old :
 reference_control_ready old reference_control_expr_1912.
Proof.
 unfold reference_control_expr_1912.
apply rc_unary.
Qed.
Lemma reference_control_member_1912 : List.In (1912,reference_control_expr_1912) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 29%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_1912_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 1912 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1912 reference_control_expr_1912 reference_control_0_positions reference_control_0_safety reference_control_member_1912) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 1912 reference_control_expr_1912 inputs path old current result Position Safe Nonreg (reference_control_ready_1912 old ) Step).
Qed.
Theorem reference_control_node_1912_congruent inputs path left right next_left next_right :
 VM.find 1911 left = VM.find 1911 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 1912 next_left = VM.find 1912 next_right.
Proof.
 intros  E1911 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1912 reference_control_expr_1912 reference_control_0_positions reference_control_0_safety reference_control_member_1912) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 1912 reference_control_expr_1912 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_1912 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_1912 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1911.
 reflexivity.
Qed.
Lemma reference_control_ready_1913 old :
 reference_control_ready old reference_control_expr_1913.
Proof.
 unfold reference_control_expr_1913.
apply rc_binary.
Qed.
Lemma reference_control_member_1913 : List.In (1913,reference_control_expr_1913) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 30%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_1913_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 1913 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1913 reference_control_expr_1913 reference_control_0_positions reference_control_0_safety reference_control_member_1913) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 1913 reference_control_expr_1913 inputs path old current result Position Safe Nonreg (reference_control_ready_1913 old ) Step).
Qed.
Theorem reference_control_node_1913_congruent inputs path left right next_left next_right :
 VM.find 1884 left = VM.find 1884 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 1913 next_left = VM.find 1913 next_right.
Proof.
 intros  E1884 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1913 reference_control_expr_1913 reference_control_0_positions reference_control_0_safety reference_control_member_1913) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 1913 reference_control_expr_1913 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_1913 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_1913 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1884.
 reflexivity.
Qed.
Lemma reference_control_ready_1914 old :
 reference_control_ready old reference_control_expr_1914.
Proof.
 unfold reference_control_expr_1914.
apply rc_binary.
Qed.
Lemma reference_control_member_1914 : List.In (1914,reference_control_expr_1914) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 31%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_1914_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 1914 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1914 reference_control_expr_1914 reference_control_0_positions reference_control_0_safety reference_control_member_1914) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 1914 reference_control_expr_1914 inputs path old current result Position Safe Nonreg (reference_control_ready_1914 old ) Step).
Qed.
Theorem reference_control_node_1914_congruent inputs path left right next_left next_right :
 VM.find 1913 left = VM.find 1913 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 1914 next_left = VM.find 1914 next_right.
Proof.
 intros  E1913 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1914 reference_control_expr_1914 reference_control_0_positions reference_control_0_safety reference_control_member_1914) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 1914 reference_control_expr_1914 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_1914 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_1914 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1913.
 reflexivity.
Qed.
Lemma reference_control_ready_1915 old :
 reference_control_ready old reference_control_expr_1915.
Proof.
 unfold reference_control_expr_1915.
apply rc_unary.
Qed.
Lemma reference_control_member_1915 : List.In (1915,reference_control_expr_1915) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 32%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_1915_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 1915 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1915 reference_control_expr_1915 reference_control_0_positions reference_control_0_safety reference_control_member_1915) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 1915 reference_control_expr_1915 inputs path old current result Position Safe Nonreg (reference_control_ready_1915 old ) Step).
Qed.
Theorem reference_control_node_1915_congruent inputs path left right next_left next_right :
 VM.find 1884 left = VM.find 1884 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 1915 next_left = VM.find 1915 next_right.
Proof.
 intros  E1884 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1915 reference_control_expr_1915 reference_control_0_positions reference_control_0_safety reference_control_member_1915) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 1915 reference_control_expr_1915 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_1915 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_1915 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1884.
 reflexivity.
Qed.
Lemma reference_control_ready_1916 old :
 reference_control_ready old reference_control_expr_1916.
Proof.
 unfold reference_control_expr_1916.
apply rc_unary.
Qed.
Lemma reference_control_member_1916 : List.In (1916,reference_control_expr_1916) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 33%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_1916_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 1916 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1916 reference_control_expr_1916 reference_control_0_positions reference_control_0_safety reference_control_member_1916) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 1916 reference_control_expr_1916 inputs path old current result Position Safe Nonreg (reference_control_ready_1916 old ) Step).
Qed.
Theorem reference_control_node_1916_congruent inputs path left right next_left next_right :
 VM.find 1915 left = VM.find 1915 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 1916 next_left = VM.find 1916 next_right.
Proof.
 intros  E1915 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1916 reference_control_expr_1916 reference_control_0_positions reference_control_0_safety reference_control_member_1916) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 1916 reference_control_expr_1916 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_1916 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_1916 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1915.
 reflexivity.
Qed.
Lemma reference_control_ready_1917 old :
 reference_control_ready old reference_control_expr_1917.
Proof.
 unfold reference_control_expr_1917.
apply rc_unary.
Qed.
Lemma reference_control_member_1917 : List.In (1917,reference_control_expr_1917) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 34%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_1917_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 1917 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1917 reference_control_expr_1917 reference_control_0_positions reference_control_0_safety reference_control_member_1917) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 1917 reference_control_expr_1917 inputs path old current result Position Safe Nonreg (reference_control_ready_1917 old ) Step).
Qed.
Theorem reference_control_node_1917_congruent inputs path left right next_left next_right :
 VM.find 1916 left = VM.find 1916 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 1917 next_left = VM.find 1917 next_right.
Proof.
 intros  E1916 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1917 reference_control_expr_1917 reference_control_0_positions reference_control_0_safety reference_control_member_1917) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 1917 reference_control_expr_1917 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_1917 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_1917 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1916.
 reflexivity.
Qed.
Lemma reference_control_ready_1918 old :
 reference_control_ready old reference_control_expr_1918.
Proof.
 unfold reference_control_expr_1918.
apply rc_binary.
Qed.
Lemma reference_control_member_1918 : List.In (1918,reference_control_expr_1918) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 35%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_1918_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 1918 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1918 reference_control_expr_1918 reference_control_0_positions reference_control_0_safety reference_control_member_1918) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 1918 reference_control_expr_1918 inputs path old current result Position Safe Nonreg (reference_control_ready_1918 old ) Step).
Qed.
Theorem reference_control_node_1918_congruent inputs path left right next_left next_right :
 VM.find 1884 left = VM.find 1884 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 1918 next_left = VM.find 1918 next_right.
Proof.
 intros  E1884 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1918 reference_control_expr_1918 reference_control_0_positions reference_control_0_safety reference_control_member_1918) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 1918 reference_control_expr_1918 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_1918 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_1918 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1884.
 reflexivity.
Qed.
Lemma reference_control_ready_1919 old :
 reference_control_ready old reference_control_expr_1919.
Proof.
 unfold reference_control_expr_1919.
apply rc_binary.
Qed.
Lemma reference_control_member_1919 : List.In (1919,reference_control_expr_1919) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 36%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_1919_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 1919 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1919 reference_control_expr_1919 reference_control_0_positions reference_control_0_safety reference_control_member_1919) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 1919 reference_control_expr_1919 inputs path old current result Position Safe Nonreg (reference_control_ready_1919 old ) Step).
Qed.
Theorem reference_control_node_1919_congruent inputs path left right next_left next_right :
 VM.find 1918 left = VM.find 1918 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 1919 next_left = VM.find 1919 next_right.
Proof.
 intros  E1918 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1919 reference_control_expr_1919 reference_control_0_positions reference_control_0_safety reference_control_member_1919) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 1919 reference_control_expr_1919 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_1919 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_1919 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1918.
 reflexivity.
Qed.
Lemma reference_control_ready_1920 old :
 reference_control_ready old reference_control_expr_1920.
Proof.
 unfold reference_control_expr_1920.
apply rc_unary.
Qed.
Lemma reference_control_member_1920 : List.In (1920,reference_control_expr_1920) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 37%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_1920_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 1920 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1920 reference_control_expr_1920 reference_control_0_positions reference_control_0_safety reference_control_member_1920) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 1920 reference_control_expr_1920 inputs path old current result Position Safe Nonreg (reference_control_ready_1920 old ) Step).
Qed.
Theorem reference_control_node_1920_congruent inputs path left right next_left next_right :
 VM.find 1884 left = VM.find 1884 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 1920 next_left = VM.find 1920 next_right.
Proof.
 intros  E1884 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1920 reference_control_expr_1920 reference_control_0_positions reference_control_0_safety reference_control_member_1920) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 1920 reference_control_expr_1920 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_1920 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_1920 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1884.
 reflexivity.
Qed.
Lemma reference_control_ready_1921 old :
 reference_control_ready old reference_control_expr_1921.
Proof.
 unfold reference_control_expr_1921.
apply rc_unary.
Qed.
Lemma reference_control_member_1921 : List.In (1921,reference_control_expr_1921) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 38%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_1921_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 1921 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1921 reference_control_expr_1921 reference_control_0_positions reference_control_0_safety reference_control_member_1921) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 1921 reference_control_expr_1921 inputs path old current result Position Safe Nonreg (reference_control_ready_1921 old ) Step).
Qed.
Theorem reference_control_node_1921_congruent inputs path left right next_left next_right :
 VM.find 1920 left = VM.find 1920 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 1921 next_left = VM.find 1921 next_right.
Proof.
 intros  E1920 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1921 reference_control_expr_1921 reference_control_0_positions reference_control_0_safety reference_control_member_1921) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 1921 reference_control_expr_1921 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_1921 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_1921 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1920.
 reflexivity.
Qed.
Lemma reference_control_ready_1922 old :
 reference_control_ready old reference_control_expr_1922.
Proof.
 unfold reference_control_expr_1922.
apply rc_unary.
Qed.
Lemma reference_control_member_1922 : List.In (1922,reference_control_expr_1922) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 39%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_1922_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 1922 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1922 reference_control_expr_1922 reference_control_0_positions reference_control_0_safety reference_control_member_1922) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 1922 reference_control_expr_1922 inputs path old current result Position Safe Nonreg (reference_control_ready_1922 old ) Step).
Qed.
Theorem reference_control_node_1922_congruent inputs path left right next_left next_right :
 VM.find 1921 left = VM.find 1921 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 1922 next_left = VM.find 1922 next_right.
Proof.
 intros  E1921 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1922 reference_control_expr_1922 reference_control_0_positions reference_control_0_safety reference_control_member_1922) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 1922 reference_control_expr_1922 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_1922 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_1922 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1921.
 reflexivity.
Qed.
Lemma reference_control_ready_1923 old :
 reference_control_ready old reference_control_expr_1923.
Proof.
 unfold reference_control_expr_1923.
apply rc_binary.
Qed.
Lemma reference_control_member_1923 : List.In (1923,reference_control_expr_1923) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 40%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_1923_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 1923 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1923 reference_control_expr_1923 reference_control_0_positions reference_control_0_safety reference_control_member_1923) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 1923 reference_control_expr_1923 inputs path old current result Position Safe Nonreg (reference_control_ready_1923 old ) Step).
Qed.
Theorem reference_control_node_1923_congruent inputs path left right next_left next_right :
 VM.find 1884 left = VM.find 1884 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 1923 next_left = VM.find 1923 next_right.
Proof.
 intros  E1884 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1923 reference_control_expr_1923 reference_control_0_positions reference_control_0_safety reference_control_member_1923) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 1923 reference_control_expr_1923 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_1923 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_1923 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1884.
 reflexivity.
Qed.
Lemma reference_control_ready_1924 old :
 reference_control_ready old reference_control_expr_1924.
Proof.
 unfold reference_control_expr_1924.
apply rc_binary.
Qed.
Lemma reference_control_member_1924 : List.In (1924,reference_control_expr_1924) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 41%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_1924_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 1924 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1924 reference_control_expr_1924 reference_control_0_positions reference_control_0_safety reference_control_member_1924) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 1924 reference_control_expr_1924 inputs path old current result Position Safe Nonreg (reference_control_ready_1924 old ) Step).
Qed.
Theorem reference_control_node_1924_congruent inputs path left right next_left next_right :
 VM.find 1923 left = VM.find 1923 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 1924 next_left = VM.find 1924 next_right.
Proof.
 intros  E1923 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1924 reference_control_expr_1924 reference_control_0_positions reference_control_0_safety reference_control_member_1924) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 1924 reference_control_expr_1924 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_1924 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_1924 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1923.
 reflexivity.
Qed.
Lemma reference_control_ready_1925 old :
 reference_control_ready old reference_control_expr_1925.
Proof.
 unfold reference_control_expr_1925.
apply rc_unary.
Qed.
Lemma reference_control_member_1925 : List.In (1925,reference_control_expr_1925) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 42%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_1925_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 1925 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1925 reference_control_expr_1925 reference_control_0_positions reference_control_0_safety reference_control_member_1925) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 1925 reference_control_expr_1925 inputs path old current result Position Safe Nonreg (reference_control_ready_1925 old ) Step).
Qed.
Theorem reference_control_node_1925_congruent inputs path left right next_left next_right :
 VM.find 1884 left = VM.find 1884 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 1925 next_left = VM.find 1925 next_right.
Proof.
 intros  E1884 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1925 reference_control_expr_1925 reference_control_0_positions reference_control_0_safety reference_control_member_1925) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 1925 reference_control_expr_1925 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_1925 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_1925 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1884.
 reflexivity.
Qed.
Lemma reference_control_ready_1926 old :
 reference_control_ready old reference_control_expr_1926.
Proof.
 unfold reference_control_expr_1926.
apply rc_unary.
Qed.
Lemma reference_control_member_1926 : List.In (1926,reference_control_expr_1926) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 43%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_1926_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 1926 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1926 reference_control_expr_1926 reference_control_0_positions reference_control_0_safety reference_control_member_1926) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 1926 reference_control_expr_1926 inputs path old current result Position Safe Nonreg (reference_control_ready_1926 old ) Step).
Qed.
Theorem reference_control_node_1926_congruent inputs path left right next_left next_right :
 VM.find 1925 left = VM.find 1925 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 1926 next_left = VM.find 1926 next_right.
Proof.
 intros  E1925 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1926 reference_control_expr_1926 reference_control_0_positions reference_control_0_safety reference_control_member_1926) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 1926 reference_control_expr_1926 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_1926 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_1926 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1925.
 reflexivity.
Qed.
Lemma reference_control_ready_1927 old :
 reference_control_ready old reference_control_expr_1927.
Proof.
 unfold reference_control_expr_1927.
apply rc_unary.
Qed.
Lemma reference_control_member_1927 : List.In (1927,reference_control_expr_1927) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 44%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_1927_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 1927 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1927 reference_control_expr_1927 reference_control_0_positions reference_control_0_safety reference_control_member_1927) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 1927 reference_control_expr_1927 inputs path old current result Position Safe Nonreg (reference_control_ready_1927 old ) Step).
Qed.
Theorem reference_control_node_1927_congruent inputs path left right next_left next_right :
 VM.find 1926 left = VM.find 1926 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 1927 next_left = VM.find 1927 next_right.
Proof.
 intros  E1926 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1927 reference_control_expr_1927 reference_control_0_positions reference_control_0_safety reference_control_member_1927) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 1927 reference_control_expr_1927 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_1927 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_1927 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1926.
 reflexivity.
Qed.
Lemma reference_control_ready_1928 old :
 reference_control_ready old reference_control_expr_1928.
Proof.
 unfold reference_control_expr_1928.
apply rc_binary.
Qed.
Lemma reference_control_member_1928 : List.In (1928,reference_control_expr_1928) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 45%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_1928_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 1928 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1928 reference_control_expr_1928 reference_control_0_positions reference_control_0_safety reference_control_member_1928) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 1928 reference_control_expr_1928 inputs path old current result Position Safe Nonreg (reference_control_ready_1928 old ) Step).
Qed.
Theorem reference_control_node_1928_congruent inputs path left right next_left next_right :
 VM.find 1884 left = VM.find 1884 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 1928 next_left = VM.find 1928 next_right.
Proof.
 intros  E1884 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1928 reference_control_expr_1928 reference_control_0_positions reference_control_0_safety reference_control_member_1928) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 1928 reference_control_expr_1928 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_1928 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_1928 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1884.
 reflexivity.
Qed.
Lemma reference_control_ready_1929 old :
 reference_control_ready old reference_control_expr_1929.
Proof.
 unfold reference_control_expr_1929.
apply rc_binary.
Qed.
Lemma reference_control_member_1929 : List.In (1929,reference_control_expr_1929) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 46%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_1929_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 1929 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1929 reference_control_expr_1929 reference_control_0_positions reference_control_0_safety reference_control_member_1929) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 1929 reference_control_expr_1929 inputs path old current result Position Safe Nonreg (reference_control_ready_1929 old ) Step).
Qed.
Theorem reference_control_node_1929_congruent inputs path left right next_left next_right :
 VM.find 1928 left = VM.find 1928 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 1929 next_left = VM.find 1929 next_right.
Proof.
 intros  E1928 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1929 reference_control_expr_1929 reference_control_0_positions reference_control_0_safety reference_control_member_1929) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 1929 reference_control_expr_1929 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_1929 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_1929 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1928.
 reflexivity.
Qed.
Lemma reference_control_ready_1930 old :
 reference_control_ready old reference_control_expr_1930.
Proof.
 unfold reference_control_expr_1930.
apply rc_unary.
Qed.
Lemma reference_control_member_1930 : List.In (1930,reference_control_expr_1930) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 47%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_1930_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 1930 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1930 reference_control_expr_1930 reference_control_0_positions reference_control_0_safety reference_control_member_1930) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 1930 reference_control_expr_1930 inputs path old current result Position Safe Nonreg (reference_control_ready_1930 old ) Step).
Qed.
Theorem reference_control_node_1930_congruent inputs path left right next_left next_right :
 VM.find 1884 left = VM.find 1884 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 1930 next_left = VM.find 1930 next_right.
Proof.
 intros  E1884 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1930 reference_control_expr_1930 reference_control_0_positions reference_control_0_safety reference_control_member_1930) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 1930 reference_control_expr_1930 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_1930 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_1930 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1884.
 reflexivity.
Qed.
Lemma reference_control_ready_1931 old :
 reference_control_ready old reference_control_expr_1931.
Proof.
 unfold reference_control_expr_1931.
apply rc_unary.
Qed.
Lemma reference_control_member_1931 : List.In (1931,reference_control_expr_1931) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 48%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_1931_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 1931 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1931 reference_control_expr_1931 reference_control_0_positions reference_control_0_safety reference_control_member_1931) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 1931 reference_control_expr_1931 inputs path old current result Position Safe Nonreg (reference_control_ready_1931 old ) Step).
Qed.
Theorem reference_control_node_1931_congruent inputs path left right next_left next_right :
 VM.find 1930 left = VM.find 1930 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 1931 next_left = VM.find 1931 next_right.
Proof.
 intros  E1930 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1931 reference_control_expr_1931 reference_control_0_positions reference_control_0_safety reference_control_member_1931) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 1931 reference_control_expr_1931 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_1931 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_1931 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1930.
 reflexivity.
Qed.
Lemma reference_control_ready_1932 old :
 reference_control_ready old reference_control_expr_1932.
Proof.
 unfold reference_control_expr_1932.
apply rc_binary.
Qed.
Lemma reference_control_member_1932 : List.In (1932,reference_control_expr_1932) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 49%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_1932_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 1932 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1932 reference_control_expr_1932 reference_control_0_positions reference_control_0_safety reference_control_member_1932) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 1932 reference_control_expr_1932 inputs path old current result Position Safe Nonreg (reference_control_ready_1932 old ) Step).
Qed.
Theorem reference_control_node_1932_congruent inputs path left right next_left next_right :
 VM.find 1884 left = VM.find 1884 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 1932 next_left = VM.find 1932 next_right.
Proof.
 intros  E1884 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1932 reference_control_expr_1932 reference_control_0_positions reference_control_0_safety reference_control_member_1932) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 1932 reference_control_expr_1932 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_1932 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_1932 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1884.
 reflexivity.
Qed.
Lemma reference_control_ready_1933 old :
 reference_control_ready old reference_control_expr_1933.
Proof.
 unfold reference_control_expr_1933.
apply rc_binary.
Qed.
Lemma reference_control_member_1933 : List.In (1933,reference_control_expr_1933) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 50%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_1933_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 1933 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1933 reference_control_expr_1933 reference_control_0_positions reference_control_0_safety reference_control_member_1933) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 1933 reference_control_expr_1933 inputs path old current result Position Safe Nonreg (reference_control_ready_1933 old ) Step).
Qed.
Theorem reference_control_node_1933_congruent inputs path left right next_left next_right :
 VM.find 1932 left = VM.find 1932 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 1933 next_left = VM.find 1933 next_right.
Proof.
 intros  E1932 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1933 reference_control_expr_1933 reference_control_0_positions reference_control_0_safety reference_control_member_1933) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 1933 reference_control_expr_1933 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_1933 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_1933 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1932.
 reflexivity.
Qed.
Lemma reference_control_ready_1934 old :
 reference_control_ready old reference_control_expr_1934.
Proof.
 unfold reference_control_expr_1934.
apply rc_unary.
Qed.
Lemma reference_control_member_1934 : List.In (1934,reference_control_expr_1934) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 51%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_1934_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 1934 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1934 reference_control_expr_1934 reference_control_0_positions reference_control_0_safety reference_control_member_1934) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 1934 reference_control_expr_1934 inputs path old current result Position Safe Nonreg (reference_control_ready_1934 old ) Step).
Qed.
Theorem reference_control_node_1934_congruent inputs path left right next_left next_right :
 VM.find 1884 left = VM.find 1884 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 1934 next_left = VM.find 1934 next_right.
Proof.
 intros  E1884 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1934 reference_control_expr_1934 reference_control_0_positions reference_control_0_safety reference_control_member_1934) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 1934 reference_control_expr_1934 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_1934 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_1934 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1884.
 reflexivity.
Qed.
Lemma reference_control_ready_1935 old :
 reference_control_ready old reference_control_expr_1935.
Proof.
 unfold reference_control_expr_1935.
apply rc_unary.
Qed.
Lemma reference_control_member_1935 : List.In (1935,reference_control_expr_1935) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 52%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_1935_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 1935 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1935 reference_control_expr_1935 reference_control_0_positions reference_control_0_safety reference_control_member_1935) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 1935 reference_control_expr_1935 inputs path old current result Position Safe Nonreg (reference_control_ready_1935 old ) Step).
Qed.
Theorem reference_control_node_1935_congruent inputs path left right next_left next_right :
 VM.find 1934 left = VM.find 1934 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 1935 next_left = VM.find 1935 next_right.
Proof.
 intros  E1934 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1935 reference_control_expr_1935 reference_control_0_positions reference_control_0_safety reference_control_member_1935) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 1935 reference_control_expr_1935 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_1935 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_1935 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1934.
 reflexivity.
Qed.
Lemma reference_control_ready_1936 old :
 reference_control_ready old reference_control_expr_1936.
Proof.
 unfold reference_control_expr_1936.
apply rc_binary.
Qed.
Lemma reference_control_member_1936 : List.In (1936,reference_control_expr_1936) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 53%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_1936_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 1936 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1936 reference_control_expr_1936 reference_control_0_positions reference_control_0_safety reference_control_member_1936) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 1936 reference_control_expr_1936 inputs path old current result Position Safe Nonreg (reference_control_ready_1936 old ) Step).
Qed.
Theorem reference_control_node_1936_congruent inputs path left right next_left next_right :
 VM.find 1884 left = VM.find 1884 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 1936 next_left = VM.find 1936 next_right.
Proof.
 intros  E1884 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1936 reference_control_expr_1936 reference_control_0_positions reference_control_0_safety reference_control_member_1936) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 1936 reference_control_expr_1936 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_1936 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_1936 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1884.
 reflexivity.
Qed.
Lemma reference_control_ready_1937 old :
 reference_control_ready old reference_control_expr_1937.
Proof.
 unfold reference_control_expr_1937.
apply rc_binary.
Qed.
Lemma reference_control_member_1937 : List.In (1937,reference_control_expr_1937) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 54%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_1937_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 1937 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1937 reference_control_expr_1937 reference_control_0_positions reference_control_0_safety reference_control_member_1937) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 1937 reference_control_expr_1937 inputs path old current result Position Safe Nonreg (reference_control_ready_1937 old ) Step).
Qed.
Theorem reference_control_node_1937_congruent inputs path left right next_left next_right :
 VM.find 1936 left = VM.find 1936 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 1937 next_left = VM.find 1937 next_right.
Proof.
 intros  E1936 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1937 reference_control_expr_1937 reference_control_0_positions reference_control_0_safety reference_control_member_1937) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 1937 reference_control_expr_1937 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_1937 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_1937 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1936.
 reflexivity.
Qed.
Lemma reference_control_ready_1938 old :
 reference_control_ready old reference_control_expr_1938.
Proof.
 unfold reference_control_expr_1938.
apply rc_unary.
Qed.
Lemma reference_control_member_1938 : List.In (1938,reference_control_expr_1938) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 55%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_1938_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 1938 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1938 reference_control_expr_1938 reference_control_0_positions reference_control_0_safety reference_control_member_1938) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 1938 reference_control_expr_1938 inputs path old current result Position Safe Nonreg (reference_control_ready_1938 old ) Step).
Qed.
Theorem reference_control_node_1938_congruent inputs path left right next_left next_right :
 VM.find 1884 left = VM.find 1884 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 1938 next_left = VM.find 1938 next_right.
Proof.
 intros  E1884 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1938 reference_control_expr_1938 reference_control_0_positions reference_control_0_safety reference_control_member_1938) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 1938 reference_control_expr_1938 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_1938 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_1938 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1884.
 reflexivity.
Qed.
Lemma reference_control_ready_1939 old :
 reference_control_ready old reference_control_expr_1939.
Proof.
 unfold reference_control_expr_1939.
apply rc_unary.
Qed.
Lemma reference_control_member_1939 : List.In (1939,reference_control_expr_1939) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 56%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_1939_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 1939 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1939 reference_control_expr_1939 reference_control_0_positions reference_control_0_safety reference_control_member_1939) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 1939 reference_control_expr_1939 inputs path old current result Position Safe Nonreg (reference_control_ready_1939 old ) Step).
Qed.
Theorem reference_control_node_1939_congruent inputs path left right next_left next_right :
 VM.find 1938 left = VM.find 1938 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 1939 next_left = VM.find 1939 next_right.
Proof.
 intros  E1938 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1939 reference_control_expr_1939 reference_control_0_positions reference_control_0_safety reference_control_member_1939) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 1939 reference_control_expr_1939 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_1939 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_1939 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1938.
 reflexivity.
Qed.
Lemma reference_control_ready_1940 old :
 reference_control_ready old reference_control_expr_1940.
Proof.
 unfold reference_control_expr_1940.
apply rc_binary.
Qed.
Lemma reference_control_member_1940 : List.In (1940,reference_control_expr_1940) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 57%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_1940_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 1940 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1940 reference_control_expr_1940 reference_control_0_positions reference_control_0_safety reference_control_member_1940) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 1940 reference_control_expr_1940 inputs path old current result Position Safe Nonreg (reference_control_ready_1940 old ) Step).
Qed.
Theorem reference_control_node_1940_congruent inputs path left right next_left next_right :
 VM.find 1884 left = VM.find 1884 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 1940 next_left = VM.find 1940 next_right.
Proof.
 intros  E1884 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1940 reference_control_expr_1940 reference_control_0_positions reference_control_0_safety reference_control_member_1940) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 1940 reference_control_expr_1940 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_1940 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_1940 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1884.
 reflexivity.
Qed.
Lemma reference_control_ready_1941 old :
 reference_control_ready old reference_control_expr_1941.
Proof.
 unfold reference_control_expr_1941.
apply rc_binary.
Qed.
Lemma reference_control_member_1941 : List.In (1941,reference_control_expr_1941) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 58%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_1941_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 1941 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1941 reference_control_expr_1941 reference_control_0_positions reference_control_0_safety reference_control_member_1941) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 1941 reference_control_expr_1941 inputs path old current result Position Safe Nonreg (reference_control_ready_1941 old ) Step).
Qed.
Theorem reference_control_node_1941_congruent inputs path left right next_left next_right :
 VM.find 1940 left = VM.find 1940 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 1941 next_left = VM.find 1941 next_right.
Proof.
 intros  E1940 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1941 reference_control_expr_1941 reference_control_0_positions reference_control_0_safety reference_control_member_1941) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 1941 reference_control_expr_1941 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_1941 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_1941 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1940.
 reflexivity.
Qed.
Lemma reference_control_ready_1942 old :
 reference_control_ready old reference_control_expr_1942.
Proof.
 unfold reference_control_expr_1942.
apply rc_unary.
Qed.
Lemma reference_control_member_1942 : List.In (1942,reference_control_expr_1942) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 59%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_1942_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 1942 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1942 reference_control_expr_1942 reference_control_0_positions reference_control_0_safety reference_control_member_1942) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 1942 reference_control_expr_1942 inputs path old current result Position Safe Nonreg (reference_control_ready_1942 old ) Step).
Qed.
Theorem reference_control_node_1942_congruent inputs path left right next_left next_right :
 VM.find 1884 left = VM.find 1884 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 1942 next_left = VM.find 1942 next_right.
Proof.
 intros  E1884 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1942 reference_control_expr_1942 reference_control_0_positions reference_control_0_safety reference_control_member_1942) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 1942 reference_control_expr_1942 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_1942 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_1942 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1884.
 reflexivity.
Qed.
Lemma reference_control_ready_1943 old :
 reference_control_ready old reference_control_expr_1943.
Proof.
 unfold reference_control_expr_1943.
apply rc_unary.
Qed.
Lemma reference_control_member_1943 : List.In (1943,reference_control_expr_1943) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 60%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_1943_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 1943 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1943 reference_control_expr_1943 reference_control_0_positions reference_control_0_safety reference_control_member_1943) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 1943 reference_control_expr_1943 inputs path old current result Position Safe Nonreg (reference_control_ready_1943 old ) Step).
Qed.
Theorem reference_control_node_1943_congruent inputs path left right next_left next_right :
 VM.find 1942 left = VM.find 1942 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 1943 next_left = VM.find 1943 next_right.
Proof.
 intros  E1942 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1943 reference_control_expr_1943 reference_control_0_positions reference_control_0_safety reference_control_member_1943) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 1943 reference_control_expr_1943 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_1943 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_1943 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1942.
 reflexivity.
Qed.
Lemma reference_control_ready_1944 old :
 reference_control_ready old reference_control_expr_1944.
Proof.
 unfold reference_control_expr_1944.
apply rc_unary.
Qed.
Lemma reference_control_member_1944 : List.In (1944,reference_control_expr_1944) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 61%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_1944_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 1944 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1944 reference_control_expr_1944 reference_control_0_positions reference_control_0_safety reference_control_member_1944) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 1944 reference_control_expr_1944 inputs path old current result Position Safe Nonreg (reference_control_ready_1944 old ) Step).
Qed.
Theorem reference_control_node_1944_congruent inputs path left right next_left next_right :
 VM.find 1943 left = VM.find 1943 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 1944 next_left = VM.find 1944 next_right.
Proof.
 intros  E1943 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1944 reference_control_expr_1944 reference_control_0_positions reference_control_0_safety reference_control_member_1944) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 1944 reference_control_expr_1944 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_1944 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_1944 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1943.
 reflexivity.
Qed.
Lemma reference_control_ready_1945 old :
 reference_control_ready old reference_control_expr_1945.
Proof.
 unfold reference_control_expr_1945.
apply rc_binary.
Qed.
Lemma reference_control_member_1945 : List.In (1945,reference_control_expr_1945) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 62%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_1945_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 1945 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1945 reference_control_expr_1945 reference_control_0_positions reference_control_0_safety reference_control_member_1945) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 1945 reference_control_expr_1945 inputs path old current result Position Safe Nonreg (reference_control_ready_1945 old ) Step).
Qed.
Theorem reference_control_node_1945_congruent inputs path left right next_left next_right :
 VM.find 1884 left = VM.find 1884 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 1945 next_left = VM.find 1945 next_right.
Proof.
 intros  E1884 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1945 reference_control_expr_1945 reference_control_0_positions reference_control_0_safety reference_control_member_1945) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 1945 reference_control_expr_1945 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_1945 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_1945 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1884.
 reflexivity.
Qed.
Lemma reference_control_ready_1946 old :
 reference_control_ready old reference_control_expr_1946.
Proof.
 unfold reference_control_expr_1946.
apply rc_binary.
Qed.
Lemma reference_control_member_1946 : List.In (1946,reference_control_expr_1946) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 63%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_1946_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 1946 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1946 reference_control_expr_1946 reference_control_0_positions reference_control_0_safety reference_control_member_1946) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 1946 reference_control_expr_1946 inputs path old current result Position Safe Nonreg (reference_control_ready_1946 old ) Step).
Qed.
Theorem reference_control_node_1946_congruent inputs path left right next_left next_right :
 VM.find 1945 left = VM.find 1945 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 1946 next_left = VM.find 1946 next_right.
Proof.
 intros  E1945 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1946 reference_control_expr_1946 reference_control_0_positions reference_control_0_safety reference_control_member_1946) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 1946 reference_control_expr_1946 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_1946 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_1946 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1945.
 reflexivity.
Qed.
Lemma reference_control_ready_1947 old :
 reference_control_ready old reference_control_expr_1947.
Proof.
 unfold reference_control_expr_1947.
apply rc_unary.
Qed.
Lemma reference_control_member_1947 : List.In (1947,reference_control_expr_1947) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 64%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_1947_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 1947 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1947 reference_control_expr_1947 reference_control_0_positions reference_control_0_safety reference_control_member_1947) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 1947 reference_control_expr_1947 inputs path old current result Position Safe Nonreg (reference_control_ready_1947 old ) Step).
Qed.
Theorem reference_control_node_1947_congruent inputs path left right next_left next_right :
 VM.find 1884 left = VM.find 1884 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 1947 next_left = VM.find 1947 next_right.
Proof.
 intros  E1884 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1947 reference_control_expr_1947 reference_control_0_positions reference_control_0_safety reference_control_member_1947) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 1947 reference_control_expr_1947 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_1947 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_1947 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1884.
 reflexivity.
Qed.
Lemma reference_control_ready_1948 old :
 reference_control_ready old reference_control_expr_1948.
Proof.
 unfold reference_control_expr_1948.
apply rc_unary.
Qed.
Lemma reference_control_member_1948 : List.In (1948,reference_control_expr_1948) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 65%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_1948_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 1948 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1948 reference_control_expr_1948 reference_control_0_positions reference_control_0_safety reference_control_member_1948) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 1948 reference_control_expr_1948 inputs path old current result Position Safe Nonreg (reference_control_ready_1948 old ) Step).
Qed.
Theorem reference_control_node_1948_congruent inputs path left right next_left next_right :
 VM.find 1947 left = VM.find 1947 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 1948 next_left = VM.find 1948 next_right.
Proof.
 intros  E1947 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1948 reference_control_expr_1948 reference_control_0_positions reference_control_0_safety reference_control_member_1948) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 1948 reference_control_expr_1948 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_1948 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_1948 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1947.
 reflexivity.
Qed.
Lemma reference_control_ready_1949 old :
 reference_control_ready old reference_control_expr_1949.
Proof.
 unfold reference_control_expr_1949.
apply rc_unary.
Qed.
Lemma reference_control_member_1949 : List.In (1949,reference_control_expr_1949) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 66%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_1949_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 1949 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1949 reference_control_expr_1949 reference_control_0_positions reference_control_0_safety reference_control_member_1949) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 1949 reference_control_expr_1949 inputs path old current result Position Safe Nonreg (reference_control_ready_1949 old ) Step).
Qed.
Theorem reference_control_node_1949_congruent inputs path left right next_left next_right :
 VM.find 1948 left = VM.find 1948 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 1949 next_left = VM.find 1949 next_right.
Proof.
 intros  E1948 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1949 reference_control_expr_1949 reference_control_0_positions reference_control_0_safety reference_control_member_1949) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 1949 reference_control_expr_1949 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_1949 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_1949 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1948.
 reflexivity.
Qed.
Lemma reference_control_ready_1950 old :
 reference_control_ready old reference_control_expr_1950.
Proof.
 unfold reference_control_expr_1950.
apply rc_binary.
Qed.
Lemma reference_control_member_1950 : List.In (1950,reference_control_expr_1950) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 67%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_1950_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 1950 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1950 reference_control_expr_1950 reference_control_0_positions reference_control_0_safety reference_control_member_1950) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 1950 reference_control_expr_1950 inputs path old current result Position Safe Nonreg (reference_control_ready_1950 old ) Step).
Qed.
Theorem reference_control_node_1950_congruent inputs path left right next_left next_right :
 VM.find 1884 left = VM.find 1884 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 1950 next_left = VM.find 1950 next_right.
Proof.
 intros  E1884 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1950 reference_control_expr_1950 reference_control_0_positions reference_control_0_safety reference_control_member_1950) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 1950 reference_control_expr_1950 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_1950 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_1950 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1884.
 reflexivity.
Qed.
Lemma reference_control_ready_1951 old :
 reference_control_ready old reference_control_expr_1951.
Proof.
 unfold reference_control_expr_1951.
apply rc_binary.
Qed.
Lemma reference_control_member_1951 : List.In (1951,reference_control_expr_1951) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 68%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_1951_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 1951 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1951 reference_control_expr_1951 reference_control_0_positions reference_control_0_safety reference_control_member_1951) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 1951 reference_control_expr_1951 inputs path old current result Position Safe Nonreg (reference_control_ready_1951 old ) Step).
Qed.
Theorem reference_control_node_1951_congruent inputs path left right next_left next_right :
 VM.find 1950 left = VM.find 1950 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 1951 next_left = VM.find 1951 next_right.
Proof.
 intros  E1950 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1951 reference_control_expr_1951 reference_control_0_positions reference_control_0_safety reference_control_member_1951) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 1951 reference_control_expr_1951 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_1951 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_1951 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1950.
 reflexivity.
Qed.
Lemma reference_control_ready_1952 old :
 reference_control_ready old reference_control_expr_1952.
Proof.
 unfold reference_control_expr_1952.
apply rc_unary.
Qed.
Lemma reference_control_member_1952 : List.In (1952,reference_control_expr_1952) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 69%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_1952_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 1952 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1952 reference_control_expr_1952 reference_control_0_positions reference_control_0_safety reference_control_member_1952) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 1952 reference_control_expr_1952 inputs path old current result Position Safe Nonreg (reference_control_ready_1952 old ) Step).
Qed.
Theorem reference_control_node_1952_congruent inputs path left right next_left next_right :
 VM.find 1884 left = VM.find 1884 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 1952 next_left = VM.find 1952 next_right.
Proof.
 intros  E1884 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1952 reference_control_expr_1952 reference_control_0_positions reference_control_0_safety reference_control_member_1952) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 1952 reference_control_expr_1952 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_1952 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_1952 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1884.
 reflexivity.
Qed.
Lemma reference_control_ready_1953 old :
 reference_control_ready old reference_control_expr_1953.
Proof.
 unfold reference_control_expr_1953.
apply rc_unary.
Qed.
Lemma reference_control_member_1953 : List.In (1953,reference_control_expr_1953) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 70%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_1953_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 1953 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1953 reference_control_expr_1953 reference_control_0_positions reference_control_0_safety reference_control_member_1953) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 1953 reference_control_expr_1953 inputs path old current result Position Safe Nonreg (reference_control_ready_1953 old ) Step).
Qed.
Theorem reference_control_node_1953_congruent inputs path left right next_left next_right :
 VM.find 1952 left = VM.find 1952 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 1953 next_left = VM.find 1953 next_right.
Proof.
 intros  E1952 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1953 reference_control_expr_1953 reference_control_0_positions reference_control_0_safety reference_control_member_1953) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 1953 reference_control_expr_1953 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_1953 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_1953 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1952.
 reflexivity.
Qed.
Lemma reference_control_ready_1954 old :
 reference_control_ready old reference_control_expr_1954.
Proof.
 unfold reference_control_expr_1954.
apply rc_unary.
Qed.
Lemma reference_control_member_1954 : List.In (1954,reference_control_expr_1954) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 71%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_1954_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 1954 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1954 reference_control_expr_1954 reference_control_0_positions reference_control_0_safety reference_control_member_1954) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 1954 reference_control_expr_1954 inputs path old current result Position Safe Nonreg (reference_control_ready_1954 old ) Step).
Qed.
Theorem reference_control_node_1954_congruent inputs path left right next_left next_right :
 VM.find 1953 left = VM.find 1953 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 1954 next_left = VM.find 1954 next_right.
Proof.
 intros  E1953 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1954 reference_control_expr_1954 reference_control_0_positions reference_control_0_safety reference_control_member_1954) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 1954 reference_control_expr_1954 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_1954 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_1954 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1953.
 reflexivity.
Qed.
Lemma reference_control_ready_1955 old :
 reference_control_ready old reference_control_expr_1955.
Proof.
 unfold reference_control_expr_1955.
apply rc_unary.
Qed.
Lemma reference_control_member_1955 : List.In (1955,reference_control_expr_1955) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 72%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_1955_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 1955 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1955 reference_control_expr_1955 reference_control_0_positions reference_control_0_safety reference_control_member_1955) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 1955 reference_control_expr_1955 inputs path old current result Position Safe Nonreg (reference_control_ready_1955 old ) Step).
Qed.
Theorem reference_control_node_1955_congruent inputs path left right next_left next_right :
 VM.find 1884 left = VM.find 1884 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 1955 next_left = VM.find 1955 next_right.
Proof.
 intros  E1884 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1955 reference_control_expr_1955 reference_control_0_positions reference_control_0_safety reference_control_member_1955) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 1955 reference_control_expr_1955 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_1955 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_1955 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1884.
 reflexivity.
Qed.
Lemma reference_control_ready_1956 old :
 reference_control_ready old reference_control_expr_1956.
Proof.
 unfold reference_control_expr_1956.
apply rc_unary.
Qed.
Lemma reference_control_member_1956 : List.In (1956,reference_control_expr_1956) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 73%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_1956_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 1956 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1956 reference_control_expr_1956 reference_control_0_positions reference_control_0_safety reference_control_member_1956) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 1956 reference_control_expr_1956 inputs path old current result Position Safe Nonreg (reference_control_ready_1956 old ) Step).
Qed.
Theorem reference_control_node_1956_congruent inputs path left right next_left next_right :
 VM.find 1955 left = VM.find 1955 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 1956 next_left = VM.find 1956 next_right.
Proof.
 intros  E1955 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1956 reference_control_expr_1956 reference_control_0_positions reference_control_0_safety reference_control_member_1956) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 1956 reference_control_expr_1956 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_1956 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_1956 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1955.
 reflexivity.
Qed.
Lemma reference_control_ready_1957 old :
 reference_control_ready old reference_control_expr_1957.
Proof.
 unfold reference_control_expr_1957.
apply rc_binary.
Qed.
Lemma reference_control_member_1957 : List.In (1957,reference_control_expr_1957) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 74%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_1957_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 1957 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1957 reference_control_expr_1957 reference_control_0_positions reference_control_0_safety reference_control_member_1957) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 1957 reference_control_expr_1957 inputs path old current result Position Safe Nonreg (reference_control_ready_1957 old ) Step).
Qed.
Theorem reference_control_node_1957_congruent inputs path left right next_left next_right :
 VM.find 1884 left = VM.find 1884 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 1957 next_left = VM.find 1957 next_right.
Proof.
 intros  E1884 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1957 reference_control_expr_1957 reference_control_0_positions reference_control_0_safety reference_control_member_1957) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 1957 reference_control_expr_1957 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_1957 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_1957 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1884.
 reflexivity.
Qed.
Lemma reference_control_ready_1958 old :
 reference_control_ready old reference_control_expr_1958.
Proof.
 unfold reference_control_expr_1958.
apply rc_binary.
Qed.
Lemma reference_control_member_1958 : List.In (1958,reference_control_expr_1958) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 75%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_1958_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 1958 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1958 reference_control_expr_1958 reference_control_0_positions reference_control_0_safety reference_control_member_1958) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 1958 reference_control_expr_1958 inputs path old current result Position Safe Nonreg (reference_control_ready_1958 old ) Step).
Qed.
Theorem reference_control_node_1958_congruent inputs path left right next_left next_right :
 VM.find 1957 left = VM.find 1957 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 1958 next_left = VM.find 1958 next_right.
Proof.
 intros  E1957 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1958 reference_control_expr_1958 reference_control_0_positions reference_control_0_safety reference_control_member_1958) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 1958 reference_control_expr_1958 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_1958 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_1958 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1957.
 reflexivity.
Qed.
Lemma reference_control_ready_1959 old :
 reference_control_ready old reference_control_expr_1959.
Proof.
 unfold reference_control_expr_1959.
apply rc_unary.
Qed.
Lemma reference_control_member_1959 : List.In (1959,reference_control_expr_1959) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 76%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_1959_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 1959 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1959 reference_control_expr_1959 reference_control_0_positions reference_control_0_safety reference_control_member_1959) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 1959 reference_control_expr_1959 inputs path old current result Position Safe Nonreg (reference_control_ready_1959 old ) Step).
Qed.
Theorem reference_control_node_1959_congruent inputs path left right next_left next_right :
 VM.find 1884 left = VM.find 1884 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 1959 next_left = VM.find 1959 next_right.
Proof.
 intros  E1884 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1959 reference_control_expr_1959 reference_control_0_positions reference_control_0_safety reference_control_member_1959) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 1959 reference_control_expr_1959 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_1959 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_1959 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1884.
 reflexivity.
Qed.
Lemma reference_control_ready_1960 old :
 reference_control_ready old reference_control_expr_1960.
Proof.
 unfold reference_control_expr_1960.
apply rc_unary.
Qed.
Lemma reference_control_member_1960 : List.In (1960,reference_control_expr_1960) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 77%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_1960_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 1960 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1960 reference_control_expr_1960 reference_control_0_positions reference_control_0_safety reference_control_member_1960) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 1960 reference_control_expr_1960 inputs path old current result Position Safe Nonreg (reference_control_ready_1960 old ) Step).
Qed.
Theorem reference_control_node_1960_congruent inputs path left right next_left next_right :
 VM.find 1959 left = VM.find 1959 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 1960 next_left = VM.find 1960 next_right.
Proof.
 intros  E1959 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1960 reference_control_expr_1960 reference_control_0_positions reference_control_0_safety reference_control_member_1960) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 1960 reference_control_expr_1960 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_1960 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_1960 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1959.
 reflexivity.
Qed.
Lemma reference_control_ready_1961 old :
 reference_control_ready old reference_control_expr_1961.
Proof.
 unfold reference_control_expr_1961.
apply rc_binary.
Qed.
Lemma reference_control_member_1961 : List.In (1961,reference_control_expr_1961) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 78%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_1961_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 1961 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1961 reference_control_expr_1961 reference_control_0_positions reference_control_0_safety reference_control_member_1961) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 1961 reference_control_expr_1961 inputs path old current result Position Safe Nonreg (reference_control_ready_1961 old ) Step).
Qed.
Theorem reference_control_node_1961_congruent inputs path left right next_left next_right :
 VM.find 1884 left = VM.find 1884 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 1961 next_left = VM.find 1961 next_right.
Proof.
 intros  E1884 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1961 reference_control_expr_1961 reference_control_0_positions reference_control_0_safety reference_control_member_1961) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 1961 reference_control_expr_1961 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_1961 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_1961 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1884.
 reflexivity.
Qed.
Lemma reference_control_ready_1962 old :
 reference_control_ready old reference_control_expr_1962.
Proof.
 unfold reference_control_expr_1962.
apply rc_binary.
Qed.
Lemma reference_control_member_1962 : List.In (1962,reference_control_expr_1962) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 79%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_1962_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 1962 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1962 reference_control_expr_1962 reference_control_0_positions reference_control_0_safety reference_control_member_1962) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 1962 reference_control_expr_1962 inputs path old current result Position Safe Nonreg (reference_control_ready_1962 old ) Step).
Qed.
Theorem reference_control_node_1962_congruent inputs path left right next_left next_right :
 VM.find 1961 left = VM.find 1961 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 1962 next_left = VM.find 1962 next_right.
Proof.
 intros  E1961 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1962 reference_control_expr_1962 reference_control_0_positions reference_control_0_safety reference_control_member_1962) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 1962 reference_control_expr_1962 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_1962 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_1962 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1961.
 reflexivity.
Qed.
Lemma reference_control_ready_1963 old :
 reference_control_ready old reference_control_expr_1963.
Proof.
 unfold reference_control_expr_1963.
apply rc_unary.
Qed.
Lemma reference_control_member_1963 : List.In (1963,reference_control_expr_1963) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 80%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_1963_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 1963 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1963 reference_control_expr_1963 reference_control_0_positions reference_control_0_safety reference_control_member_1963) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 1963 reference_control_expr_1963 inputs path old current result Position Safe Nonreg (reference_control_ready_1963 old ) Step).
Qed.
Theorem reference_control_node_1963_congruent inputs path left right next_left next_right :
 VM.find 1884 left = VM.find 1884 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 1963 next_left = VM.find 1963 next_right.
Proof.
 intros  E1884 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1963 reference_control_expr_1963 reference_control_0_positions reference_control_0_safety reference_control_member_1963) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 1963 reference_control_expr_1963 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_1963 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_1963 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1884.
 reflexivity.
Qed.
Lemma reference_control_ready_1964 old :
 reference_control_ready old reference_control_expr_1964.
Proof.
 unfold reference_control_expr_1964.
apply rc_unary.
Qed.
Lemma reference_control_member_1964 : List.In (1964,reference_control_expr_1964) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 81%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_1964_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 1964 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1964 reference_control_expr_1964 reference_control_0_positions reference_control_0_safety reference_control_member_1964) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 1964 reference_control_expr_1964 inputs path old current result Position Safe Nonreg (reference_control_ready_1964 old ) Step).
Qed.
Theorem reference_control_node_1964_congruent inputs path left right next_left next_right :
 VM.find 1963 left = VM.find 1963 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 1964 next_left = VM.find 1964 next_right.
Proof.
 intros  E1963 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1964 reference_control_expr_1964 reference_control_0_positions reference_control_0_safety reference_control_member_1964) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 1964 reference_control_expr_1964 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_1964 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_1964 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1963.
 reflexivity.
Qed.
Lemma reference_control_ready_1965 old :
 reference_control_ready old reference_control_expr_1965.
Proof.
 unfold reference_control_expr_1965.
apply rc_binary.
Qed.
Lemma reference_control_member_1965 : List.In (1965,reference_control_expr_1965) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 82%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_1965_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 1965 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1965 reference_control_expr_1965 reference_control_0_positions reference_control_0_safety reference_control_member_1965) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 1965 reference_control_expr_1965 inputs path old current result Position Safe Nonreg (reference_control_ready_1965 old ) Step).
Qed.
Theorem reference_control_node_1965_congruent inputs path left right next_left next_right :
 VM.find 1884 left = VM.find 1884 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 1965 next_left = VM.find 1965 next_right.
Proof.
 intros  E1884 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1965 reference_control_expr_1965 reference_control_0_positions reference_control_0_safety reference_control_member_1965) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 1965 reference_control_expr_1965 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_1965 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_1965 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1884.
 reflexivity.
Qed.
Lemma reference_control_ready_1966 old :
 reference_control_ready old reference_control_expr_1966.
Proof.
 unfold reference_control_expr_1966.
apply rc_binary.
Qed.
Lemma reference_control_member_1966 : List.In (1966,reference_control_expr_1966) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 83%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_1966_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 1966 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1966 reference_control_expr_1966 reference_control_0_positions reference_control_0_safety reference_control_member_1966) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 1966 reference_control_expr_1966 inputs path old current result Position Safe Nonreg (reference_control_ready_1966 old ) Step).
Qed.
Theorem reference_control_node_1966_congruent inputs path left right next_left next_right :
 VM.find 1965 left = VM.find 1965 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 1966 next_left = VM.find 1966 next_right.
Proof.
 intros  E1965 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1966 reference_control_expr_1966 reference_control_0_positions reference_control_0_safety reference_control_member_1966) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 1966 reference_control_expr_1966 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_1966 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_1966 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1965.
 reflexivity.
Qed.
Lemma reference_control_ready_1967 old :
 reference_control_ready old reference_control_expr_1967.
Proof.
 unfold reference_control_expr_1967.
apply rc_unary.
Qed.
Lemma reference_control_member_1967 : List.In (1967,reference_control_expr_1967) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 84%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_1967_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 1967 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1967 reference_control_expr_1967 reference_control_0_positions reference_control_0_safety reference_control_member_1967) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 1967 reference_control_expr_1967 inputs path old current result Position Safe Nonreg (reference_control_ready_1967 old ) Step).
Qed.
Theorem reference_control_node_1967_congruent inputs path left right next_left next_right :
 VM.find 1884 left = VM.find 1884 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 1967 next_left = VM.find 1967 next_right.
Proof.
 intros  E1884 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1967 reference_control_expr_1967 reference_control_0_positions reference_control_0_safety reference_control_member_1967) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 1967 reference_control_expr_1967 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_1967 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_1967 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1884.
 reflexivity.
Qed.
Lemma reference_control_ready_1968 old :
 reference_control_ready old reference_control_expr_1968.
Proof.
 unfold reference_control_expr_1968.
apply rc_unary.
Qed.
Lemma reference_control_member_1968 : List.In (1968,reference_control_expr_1968) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 85%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_1968_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 1968 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1968 reference_control_expr_1968 reference_control_0_positions reference_control_0_safety reference_control_member_1968) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 1968 reference_control_expr_1968 inputs path old current result Position Safe Nonreg (reference_control_ready_1968 old ) Step).
Qed.
Theorem reference_control_node_1968_congruent inputs path left right next_left next_right :
 VM.find 1967 left = VM.find 1967 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 1968 next_left = VM.find 1968 next_right.
Proof.
 intros  E1967 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1968 reference_control_expr_1968 reference_control_0_positions reference_control_0_safety reference_control_member_1968) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 1968 reference_control_expr_1968 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_1968 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_1968 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1967.
 reflexivity.
Qed.
Lemma reference_control_ready_1969 old :
 reference_control_ready old reference_control_expr_1969.
Proof.
 unfold reference_control_expr_1969.
apply rc_binary.
Qed.
Lemma reference_control_member_1969 : List.In (1969,reference_control_expr_1969) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 86%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_1969_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 1969 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1969 reference_control_expr_1969 reference_control_0_positions reference_control_0_safety reference_control_member_1969) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 1969 reference_control_expr_1969 inputs path old current result Position Safe Nonreg (reference_control_ready_1969 old ) Step).
Qed.
Theorem reference_control_node_1969_congruent inputs path left right next_left next_right :
 VM.find 1884 left = VM.find 1884 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 1969 next_left = VM.find 1969 next_right.
Proof.
 intros  E1884 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1969 reference_control_expr_1969 reference_control_0_positions reference_control_0_safety reference_control_member_1969) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 1969 reference_control_expr_1969 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_1969 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_1969 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1884.
 reflexivity.
Qed.
Lemma reference_control_ready_1970 old :
 reference_control_ready old reference_control_expr_1970.
Proof.
 unfold reference_control_expr_1970.
apply rc_binary.
Qed.
Lemma reference_control_member_1970 : List.In (1970,reference_control_expr_1970) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 87%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_1970_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 1970 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1970 reference_control_expr_1970 reference_control_0_positions reference_control_0_safety reference_control_member_1970) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 1970 reference_control_expr_1970 inputs path old current result Position Safe Nonreg (reference_control_ready_1970 old ) Step).
Qed.
Theorem reference_control_node_1970_congruent inputs path left right next_left next_right :
 VM.find 1969 left = VM.find 1969 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 1970 next_left = VM.find 1970 next_right.
Proof.
 intros  E1969 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1970 reference_control_expr_1970 reference_control_0_positions reference_control_0_safety reference_control_member_1970) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 1970 reference_control_expr_1970 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_1970 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_1970 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1969.
 reflexivity.
Qed.
Lemma reference_control_ready_1971 old :
 reference_control_ready old reference_control_expr_1971.
Proof.
 unfold reference_control_expr_1971.
apply rc_unary.
Qed.
Lemma reference_control_member_1971 : List.In (1971,reference_control_expr_1971) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 88%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_1971_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 1971 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1971 reference_control_expr_1971 reference_control_0_positions reference_control_0_safety reference_control_member_1971) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 1971 reference_control_expr_1971 inputs path old current result Position Safe Nonreg (reference_control_ready_1971 old ) Step).
Qed.
Theorem reference_control_node_1971_congruent inputs path left right next_left next_right :
 VM.find 1884 left = VM.find 1884 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 1971 next_left = VM.find 1971 next_right.
Proof.
 intros  E1884 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1971 reference_control_expr_1971 reference_control_0_positions reference_control_0_safety reference_control_member_1971) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 1971 reference_control_expr_1971 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_1971 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_1971 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1884.
 reflexivity.
Qed.
Lemma reference_control_ready_1972 old :
 reference_control_ready old reference_control_expr_1972.
Proof.
 unfold reference_control_expr_1972.
apply rc_unary.
Qed.
Lemma reference_control_member_1972 : List.In (1972,reference_control_expr_1972) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 89%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_1972_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 1972 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1972 reference_control_expr_1972 reference_control_0_positions reference_control_0_safety reference_control_member_1972) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 1972 reference_control_expr_1972 inputs path old current result Position Safe Nonreg (reference_control_ready_1972 old ) Step).
Qed.
Theorem reference_control_node_1972_congruent inputs path left right next_left next_right :
 VM.find 1971 left = VM.find 1971 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 1972 next_left = VM.find 1972 next_right.
Proof.
 intros  E1971 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1972 reference_control_expr_1972 reference_control_0_positions reference_control_0_safety reference_control_member_1972) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 1972 reference_control_expr_1972 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_1972 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_1972 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1971.
 reflexivity.
Qed.
Lemma reference_control_ready_1973 old :
 reference_control_ready old reference_control_expr_1973.
Proof.
 unfold reference_control_expr_1973.
apply rc_binary.
Qed.
Lemma reference_control_member_1973 : List.In (1973,reference_control_expr_1973) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 90%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_1973_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 1973 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1973 reference_control_expr_1973 reference_control_0_positions reference_control_0_safety reference_control_member_1973) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 1973 reference_control_expr_1973 inputs path old current result Position Safe Nonreg (reference_control_ready_1973 old ) Step).
Qed.
Theorem reference_control_node_1973_congruent inputs path left right next_left next_right :
 VM.find 1884 left = VM.find 1884 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 1973 next_left = VM.find 1973 next_right.
Proof.
 intros  E1884 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1973 reference_control_expr_1973 reference_control_0_positions reference_control_0_safety reference_control_member_1973) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 1973 reference_control_expr_1973 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_1973 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_1973 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1884.
 reflexivity.
Qed.
Lemma reference_control_ready_1974 old :
 reference_control_ready old reference_control_expr_1974.
Proof.
 unfold reference_control_expr_1974.
apply rc_binary.
Qed.
Lemma reference_control_member_1974 : List.In (1974,reference_control_expr_1974) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 91%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_1974_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 1974 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1974 reference_control_expr_1974 reference_control_0_positions reference_control_0_safety reference_control_member_1974) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 1974 reference_control_expr_1974 inputs path old current result Position Safe Nonreg (reference_control_ready_1974 old ) Step).
Qed.
Theorem reference_control_node_1974_congruent inputs path left right next_left next_right :
 VM.find 1973 left = VM.find 1973 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 1974 next_left = VM.find 1974 next_right.
Proof.
 intros  E1973 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1974 reference_control_expr_1974 reference_control_0_positions reference_control_0_safety reference_control_member_1974) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 1974 reference_control_expr_1974 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_1974 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_1974 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1973.
 reflexivity.
Qed.
Lemma reference_control_ready_1975 old :
 reference_control_ready old reference_control_expr_1975.
Proof.
 unfold reference_control_expr_1975.
apply rc_unary.
Qed.
Lemma reference_control_member_1975 : List.In (1975,reference_control_expr_1975) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 92%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_1975_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 1975 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1975 reference_control_expr_1975 reference_control_0_positions reference_control_0_safety reference_control_member_1975) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 1975 reference_control_expr_1975 inputs path old current result Position Safe Nonreg (reference_control_ready_1975 old ) Step).
Qed.
Theorem reference_control_node_1975_congruent inputs path left right next_left next_right :
 VM.find 1884 left = VM.find 1884 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 1975 next_left = VM.find 1975 next_right.
Proof.
 intros  E1884 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1975 reference_control_expr_1975 reference_control_0_positions reference_control_0_safety reference_control_member_1975) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 1975 reference_control_expr_1975 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_1975 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_1975 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1884.
 reflexivity.
Qed.
Lemma reference_control_ready_1976 old :
 reference_control_ready old reference_control_expr_1976.
Proof.
 unfold reference_control_expr_1976.
apply rc_unary.
Qed.
Lemma reference_control_member_1976 : List.In (1976,reference_control_expr_1976) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 93%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_1976_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 1976 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1976 reference_control_expr_1976 reference_control_0_positions reference_control_0_safety reference_control_member_1976) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 1976 reference_control_expr_1976 inputs path old current result Position Safe Nonreg (reference_control_ready_1976 old ) Step).
Qed.
Theorem reference_control_node_1976_congruent inputs path left right next_left next_right :
 VM.find 1975 left = VM.find 1975 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 1976 next_left = VM.find 1976 next_right.
Proof.
 intros  E1975 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1976 reference_control_expr_1976 reference_control_0_positions reference_control_0_safety reference_control_member_1976) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 1976 reference_control_expr_1976 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_1976 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_1976 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1975.
 reflexivity.
Qed.
Lemma reference_control_ready_1977 old :
 reference_control_ready old reference_control_expr_1977.
Proof.
 unfold reference_control_expr_1977.
apply rc_unary.
Qed.
Lemma reference_control_member_1977 : List.In (1977,reference_control_expr_1977) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 94%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_1977_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 1977 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1977 reference_control_expr_1977 reference_control_0_positions reference_control_0_safety reference_control_member_1977) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 1977 reference_control_expr_1977 inputs path old current result Position Safe Nonreg (reference_control_ready_1977 old ) Step).
Qed.
Theorem reference_control_node_1977_congruent inputs path left right next_left next_right :
 VM.find 1976 left = VM.find 1976 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 1977 next_left = VM.find 1977 next_right.
Proof.
 intros  E1976 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1977 reference_control_expr_1977 reference_control_0_positions reference_control_0_safety reference_control_member_1977) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 1977 reference_control_expr_1977 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_1977 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_1977 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1976.
 reflexivity.
Qed.
Lemma reference_control_ready_1978 old :
 reference_control_ready old reference_control_expr_1978.
Proof.
 unfold reference_control_expr_1978.
apply rc_unary.
Qed.
Lemma reference_control_member_1978 : List.In (1978,reference_control_expr_1978) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 95%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_1978_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 1978 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1978 reference_control_expr_1978 reference_control_0_positions reference_control_0_safety reference_control_member_1978) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 1978 reference_control_expr_1978 inputs path old current result Position Safe Nonreg (reference_control_ready_1978 old ) Step).
Qed.
Theorem reference_control_node_1978_congruent inputs path left right next_left next_right :
 VM.find 1977 left = VM.find 1977 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 1978 next_left = VM.find 1978 next_right.
Proof.
 intros  E1977 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1978 reference_control_expr_1978 reference_control_0_positions reference_control_0_safety reference_control_member_1978) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 1978 reference_control_expr_1978 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_1978 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_1978 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1977.
 reflexivity.
Qed.
Lemma reference_control_ready_1979 old :
 reference_control_ready old reference_control_expr_1979.
Proof.
 unfold reference_control_expr_1979.
apply rc_binary.
Qed.
Lemma reference_control_member_1979 : List.In (1979,reference_control_expr_1979) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 96%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_1979_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 1979 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1979 reference_control_expr_1979 reference_control_0_positions reference_control_0_safety reference_control_member_1979) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 1979 reference_control_expr_1979 inputs path old current result Position Safe Nonreg (reference_control_ready_1979 old ) Step).
Qed.
Theorem reference_control_node_1979_congruent inputs path left right next_left next_right :
 VM.find 1884 left = VM.find 1884 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 1979 next_left = VM.find 1979 next_right.
Proof.
 intros  E1884 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1979 reference_control_expr_1979 reference_control_0_positions reference_control_0_safety reference_control_member_1979) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 1979 reference_control_expr_1979 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_1979 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_1979 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1884.
 reflexivity.
Qed.
Lemma reference_control_ready_1980 old :
 reference_control_ready old reference_control_expr_1980.
Proof.
 unfold reference_control_expr_1980.
apply rc_binary.
Qed.
Lemma reference_control_member_1980 : List.In (1980,reference_control_expr_1980) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 97%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_1980_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 1980 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1980 reference_control_expr_1980 reference_control_0_positions reference_control_0_safety reference_control_member_1980) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 1980 reference_control_expr_1980 inputs path old current result Position Safe Nonreg (reference_control_ready_1980 old ) Step).
Qed.
Theorem reference_control_node_1980_congruent inputs path left right next_left next_right :
 VM.find 1979 left = VM.find 1979 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 1980 next_left = VM.find 1980 next_right.
Proof.
 intros  E1979 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1980 reference_control_expr_1980 reference_control_0_positions reference_control_0_safety reference_control_member_1980) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 1980 reference_control_expr_1980 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_1980 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_1980 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1979.
 reflexivity.
Qed.
Lemma reference_control_ready_1981 old :
 reference_control_ready old reference_control_expr_1981.
Proof.
 unfold reference_control_expr_1981.
apply rc_unary.
Qed.
Lemma reference_control_member_1981 : List.In (1981,reference_control_expr_1981) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 98%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_1981_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 1981 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1981 reference_control_expr_1981 reference_control_0_positions reference_control_0_safety reference_control_member_1981) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 1981 reference_control_expr_1981 inputs path old current result Position Safe Nonreg (reference_control_ready_1981 old ) Step).
Qed.
Theorem reference_control_node_1981_congruent inputs path left right next_left next_right :
 VM.find 1884 left = VM.find 1884 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 1981 next_left = VM.find 1981 next_right.
Proof.
 intros  E1884 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1981 reference_control_expr_1981 reference_control_0_positions reference_control_0_safety reference_control_member_1981) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 1981 reference_control_expr_1981 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_1981 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_1981 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1884.
 reflexivity.
Qed.
Lemma reference_control_ready_1982 old :
 reference_control_ready old reference_control_expr_1982.
Proof.
 unfold reference_control_expr_1982.
apply rc_unary.
Qed.
Lemma reference_control_member_1982 : List.In (1982,reference_control_expr_1982) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 99%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_1982_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 1982 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1982 reference_control_expr_1982 reference_control_0_positions reference_control_0_safety reference_control_member_1982) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 1982 reference_control_expr_1982 inputs path old current result Position Safe Nonreg (reference_control_ready_1982 old ) Step).
Qed.
Theorem reference_control_node_1982_congruent inputs path left right next_left next_right :
 VM.find 1981 left = VM.find 1981 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 1982 next_left = VM.find 1982 next_right.
Proof.
 intros  E1981 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1982 reference_control_expr_1982 reference_control_0_positions reference_control_0_safety reference_control_member_1982) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 1982 reference_control_expr_1982 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_1982 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_1982 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1981.
 reflexivity.
Qed.
Lemma reference_control_ready_1983 old :
 reference_control_ready old reference_control_expr_1983.
Proof.
 unfold reference_control_expr_1983.
apply rc_unary.
Qed.
Lemma reference_control_member_1983 : List.In (1983,reference_control_expr_1983) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 100%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_1983_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 1983 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1983 reference_control_expr_1983 reference_control_0_positions reference_control_0_safety reference_control_member_1983) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 1983 reference_control_expr_1983 inputs path old current result Position Safe Nonreg (reference_control_ready_1983 old ) Step).
Qed.
Theorem reference_control_node_1983_congruent inputs path left right next_left next_right :
 VM.find 1982 left = VM.find 1982 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 1983 next_left = VM.find 1983 next_right.
Proof.
 intros  E1982 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1983 reference_control_expr_1983 reference_control_0_positions reference_control_0_safety reference_control_member_1983) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 1983 reference_control_expr_1983 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_1983 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_1983 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1982.
 reflexivity.
Qed.
Lemma reference_control_ready_1984 old :
 reference_control_ready old reference_control_expr_1984.
Proof.
 unfold reference_control_expr_1984.
apply rc_unary.
Qed.
Lemma reference_control_member_1984 : List.In (1984,reference_control_expr_1984) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 101%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_1984_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 1984 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1984 reference_control_expr_1984 reference_control_0_positions reference_control_0_safety reference_control_member_1984) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 1984 reference_control_expr_1984 inputs path old current result Position Safe Nonreg (reference_control_ready_1984 old ) Step).
Qed.
Theorem reference_control_node_1984_congruent inputs path left right next_left next_right :
 VM.find 1983 left = VM.find 1983 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 1984 next_left = VM.find 1984 next_right.
Proof.
 intros  E1983 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1984 reference_control_expr_1984 reference_control_0_positions reference_control_0_safety reference_control_member_1984) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 1984 reference_control_expr_1984 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_1984 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_1984 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1983.
 reflexivity.
Qed.
Lemma reference_control_ready_1985 old :
 reference_control_ready old reference_control_expr_1985.
Proof.
 unfold reference_control_expr_1985.
apply rc_binary.
Qed.
Lemma reference_control_member_1985 : List.In (1985,reference_control_expr_1985) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 102%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_1985_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 1985 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1985 reference_control_expr_1985 reference_control_0_positions reference_control_0_safety reference_control_member_1985) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 1985 reference_control_expr_1985 inputs path old current result Position Safe Nonreg (reference_control_ready_1985 old ) Step).
Qed.
Theorem reference_control_node_1985_congruent inputs path left right next_left next_right :
 VM.find 1884 left = VM.find 1884 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 1985 next_left = VM.find 1985 next_right.
Proof.
 intros  E1884 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1985 reference_control_expr_1985 reference_control_0_positions reference_control_0_safety reference_control_member_1985) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 1985 reference_control_expr_1985 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_1985 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_1985 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1884.
 reflexivity.
Qed.
Lemma reference_control_ready_1986 old :
 reference_control_ready old reference_control_expr_1986.
Proof.
 unfold reference_control_expr_1986.
apply rc_binary.
Qed.
Lemma reference_control_member_1986 : List.In (1986,reference_control_expr_1986) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 103%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_1986_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 1986 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1986 reference_control_expr_1986 reference_control_0_positions reference_control_0_safety reference_control_member_1986) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 1986 reference_control_expr_1986 inputs path old current result Position Safe Nonreg (reference_control_ready_1986 old ) Step).
Qed.
Theorem reference_control_node_1986_congruent inputs path left right next_left next_right :
 VM.find 1985 left = VM.find 1985 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 1986 next_left = VM.find 1986 next_right.
Proof.
 intros  E1985 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1986 reference_control_expr_1986 reference_control_0_positions reference_control_0_safety reference_control_member_1986) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 1986 reference_control_expr_1986 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_1986 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_1986 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1985.
 reflexivity.
Qed.
Lemma reference_control_ready_1987 old :
 reference_control_ready old reference_control_expr_1987.
Proof.
 unfold reference_control_expr_1987.
apply rc_unary.
Qed.
Lemma reference_control_member_1987 : List.In (1987,reference_control_expr_1987) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 104%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_1987_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 1987 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1987 reference_control_expr_1987 reference_control_0_positions reference_control_0_safety reference_control_member_1987) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 1987 reference_control_expr_1987 inputs path old current result Position Safe Nonreg (reference_control_ready_1987 old ) Step).
Qed.
Theorem reference_control_node_1987_congruent inputs path left right next_left next_right :
 VM.find 1884 left = VM.find 1884 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 1987 next_left = VM.find 1987 next_right.
Proof.
 intros  E1884 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1987 reference_control_expr_1987 reference_control_0_positions reference_control_0_safety reference_control_member_1987) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 1987 reference_control_expr_1987 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_1987 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_1987 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1884.
 reflexivity.
Qed.
Lemma reference_control_ready_1988 old :
 reference_control_ready old reference_control_expr_1988.
Proof.
 unfold reference_control_expr_1988.
apply rc_unary.
Qed.
Lemma reference_control_member_1988 : List.In (1988,reference_control_expr_1988) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 105%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_1988_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 1988 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1988 reference_control_expr_1988 reference_control_0_positions reference_control_0_safety reference_control_member_1988) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 1988 reference_control_expr_1988 inputs path old current result Position Safe Nonreg (reference_control_ready_1988 old ) Step).
Qed.
Theorem reference_control_node_1988_congruent inputs path left right next_left next_right :
 VM.find 1987 left = VM.find 1987 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 1988 next_left = VM.find 1988 next_right.
Proof.
 intros  E1987 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1988 reference_control_expr_1988 reference_control_0_positions reference_control_0_safety reference_control_member_1988) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 1988 reference_control_expr_1988 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_1988 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_1988 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1987.
 reflexivity.
Qed.
Lemma reference_control_ready_1989 old :
 reference_control_ready old reference_control_expr_1989.
Proof.
 unfold reference_control_expr_1989.
apply rc_unary.
Qed.
Lemma reference_control_member_1989 : List.In (1989,reference_control_expr_1989) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 106%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_1989_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 1989 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1989 reference_control_expr_1989 reference_control_0_positions reference_control_0_safety reference_control_member_1989) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 1989 reference_control_expr_1989 inputs path old current result Position Safe Nonreg (reference_control_ready_1989 old ) Step).
Qed.
Theorem reference_control_node_1989_congruent inputs path left right next_left next_right :
 VM.find 1988 left = VM.find 1988 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 1989 next_left = VM.find 1989 next_right.
Proof.
 intros  E1988 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1989 reference_control_expr_1989 reference_control_0_positions reference_control_0_safety reference_control_member_1989) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 1989 reference_control_expr_1989 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_1989 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_1989 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1988.
 reflexivity.
Qed.
Lemma reference_control_ready_1990 old :
 reference_control_ready old reference_control_expr_1990.
Proof.
 unfold reference_control_expr_1990.
apply rc_unary.
Qed.
Lemma reference_control_member_1990 : List.In (1990,reference_control_expr_1990) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 107%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_1990_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 1990 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1990 reference_control_expr_1990 reference_control_0_positions reference_control_0_safety reference_control_member_1990) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 1990 reference_control_expr_1990 inputs path old current result Position Safe Nonreg (reference_control_ready_1990 old ) Step).
Qed.
Theorem reference_control_node_1990_congruent inputs path left right next_left next_right :
 VM.find 1989 left = VM.find 1989 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 1990 next_left = VM.find 1990 next_right.
Proof.
 intros  E1989 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1990 reference_control_expr_1990 reference_control_0_positions reference_control_0_safety reference_control_member_1990) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 1990 reference_control_expr_1990 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_1990 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_1990 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1989.
 reflexivity.
Qed.
Lemma reference_control_ready_1991 old :
 reference_control_ready old reference_control_expr_1991.
Proof.
 unfold reference_control_expr_1991.
apply rc_binary.
Qed.
Lemma reference_control_member_1991 : List.In (1991,reference_control_expr_1991) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 108%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_1991_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 1991 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1991 reference_control_expr_1991 reference_control_0_positions reference_control_0_safety reference_control_member_1991) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 1991 reference_control_expr_1991 inputs path old current result Position Safe Nonreg (reference_control_ready_1991 old ) Step).
Qed.
Theorem reference_control_node_1991_congruent inputs path left right next_left next_right :
 VM.find 1884 left = VM.find 1884 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 1991 next_left = VM.find 1991 next_right.
Proof.
 intros  E1884 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1991 reference_control_expr_1991 reference_control_0_positions reference_control_0_safety reference_control_member_1991) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 1991 reference_control_expr_1991 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_1991 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_1991 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1884.
 reflexivity.
Qed.
Lemma reference_control_ready_1992 old :
 reference_control_ready old reference_control_expr_1992.
Proof.
 unfold reference_control_expr_1992.
apply rc_binary.
Qed.
Lemma reference_control_member_1992 : List.In (1992,reference_control_expr_1992) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 109%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_1992_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 1992 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1992 reference_control_expr_1992 reference_control_0_positions reference_control_0_safety reference_control_member_1992) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 1992 reference_control_expr_1992 inputs path old current result Position Safe Nonreg (reference_control_ready_1992 old ) Step).
Qed.
Theorem reference_control_node_1992_congruent inputs path left right next_left next_right :
 VM.find 1991 left = VM.find 1991 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 1992 next_left = VM.find 1992 next_right.
Proof.
 intros  E1991 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1992 reference_control_expr_1992 reference_control_0_positions reference_control_0_safety reference_control_member_1992) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 1992 reference_control_expr_1992 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_1992 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_1992 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1991.
 reflexivity.
Qed.
Lemma reference_control_ready_1993 old :
 reference_control_ready old reference_control_expr_1993.
Proof.
 unfold reference_control_expr_1993.
apply rc_unary.
Qed.
Lemma reference_control_member_1993 : List.In (1993,reference_control_expr_1993) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 110%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_1993_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 1993 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1993 reference_control_expr_1993 reference_control_0_positions reference_control_0_safety reference_control_member_1993) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 1993 reference_control_expr_1993 inputs path old current result Position Safe Nonreg (reference_control_ready_1993 old ) Step).
Qed.
Theorem reference_control_node_1993_congruent inputs path left right next_left next_right :
 VM.find 1884 left = VM.find 1884 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 1993 next_left = VM.find 1993 next_right.
Proof.
 intros  E1884 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1993 reference_control_expr_1993 reference_control_0_positions reference_control_0_safety reference_control_member_1993) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 1993 reference_control_expr_1993 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_1993 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_1993 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1884.
 reflexivity.
Qed.
Lemma reference_control_ready_1994 old :
 reference_control_ready old reference_control_expr_1994.
Proof.
 unfold reference_control_expr_1994.
apply rc_unary.
Qed.
Lemma reference_control_member_1994 : List.In (1994,reference_control_expr_1994) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 111%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_1994_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 1994 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1994 reference_control_expr_1994 reference_control_0_positions reference_control_0_safety reference_control_member_1994) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 1994 reference_control_expr_1994 inputs path old current result Position Safe Nonreg (reference_control_ready_1994 old ) Step).
Qed.
Theorem reference_control_node_1994_congruent inputs path left right next_left next_right :
 VM.find 1993 left = VM.find 1993 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 1994 next_left = VM.find 1994 next_right.
Proof.
 intros  E1993 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1994 reference_control_expr_1994 reference_control_0_positions reference_control_0_safety reference_control_member_1994) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 1994 reference_control_expr_1994 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_1994 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_1994 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1993.
 reflexivity.
Qed.
Lemma reference_control_ready_1995 old :
 reference_control_ready old reference_control_expr_1995.
Proof.
 unfold reference_control_expr_1995.
apply rc_unary.
Qed.
Lemma reference_control_member_1995 : List.In (1995,reference_control_expr_1995) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 112%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_1995_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 1995 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1995 reference_control_expr_1995 reference_control_0_positions reference_control_0_safety reference_control_member_1995) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 1995 reference_control_expr_1995 inputs path old current result Position Safe Nonreg (reference_control_ready_1995 old ) Step).
Qed.
Theorem reference_control_node_1995_congruent inputs path left right next_left next_right :
 VM.find 1994 left = VM.find 1994 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 1995 next_left = VM.find 1995 next_right.
Proof.
 intros  E1994 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1995 reference_control_expr_1995 reference_control_0_positions reference_control_0_safety reference_control_member_1995) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 1995 reference_control_expr_1995 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_1995 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_1995 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1994.
 reflexivity.
Qed.
Lemma reference_control_ready_1996 old :
 reference_control_ready old reference_control_expr_1996.
Proof.
 unfold reference_control_expr_1996.
apply rc_unary.
Qed.
Lemma reference_control_member_1996 : List.In (1996,reference_control_expr_1996) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 113%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_1996_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 1996 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1996 reference_control_expr_1996 reference_control_0_positions reference_control_0_safety reference_control_member_1996) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 1996 reference_control_expr_1996 inputs path old current result Position Safe Nonreg (reference_control_ready_1996 old ) Step).
Qed.
Theorem reference_control_node_1996_congruent inputs path left right next_left next_right :
 VM.find 1995 left = VM.find 1995 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 1996 next_left = VM.find 1996 next_right.
Proof.
 intros  E1995 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1996 reference_control_expr_1996 reference_control_0_positions reference_control_0_safety reference_control_member_1996) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 1996 reference_control_expr_1996 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_1996 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_1996 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1995.
 reflexivity.
Qed.
Lemma reference_control_ready_1997 old :
 reference_control_ready old reference_control_expr_1997.
Proof.
 unfold reference_control_expr_1997.
apply rc_binary.
Qed.
Lemma reference_control_member_1997 : List.In (1997,reference_control_expr_1997) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 114%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_1997_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 1997 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1997 reference_control_expr_1997 reference_control_0_positions reference_control_0_safety reference_control_member_1997) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 1997 reference_control_expr_1997 inputs path old current result Position Safe Nonreg (reference_control_ready_1997 old ) Step).
Qed.
Theorem reference_control_node_1997_congruent inputs path left right next_left next_right :
 VM.find 1884 left = VM.find 1884 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 1997 next_left = VM.find 1997 next_right.
Proof.
 intros  E1884 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1997 reference_control_expr_1997 reference_control_0_positions reference_control_0_safety reference_control_member_1997) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 1997 reference_control_expr_1997 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_1997 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_1997 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1884.
 reflexivity.
Qed.
Lemma reference_control_ready_1998 old :
 reference_control_ready old reference_control_expr_1998.
Proof.
 unfold reference_control_expr_1998.
apply rc_binary.
Qed.
Lemma reference_control_member_1998 : List.In (1998,reference_control_expr_1998) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 115%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_1998_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 1998 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1998 reference_control_expr_1998 reference_control_0_positions reference_control_0_safety reference_control_member_1998) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 1998 reference_control_expr_1998 inputs path old current result Position Safe Nonreg (reference_control_ready_1998 old ) Step).
Qed.
Theorem reference_control_node_1998_congruent inputs path left right next_left next_right :
 VM.find 1997 left = VM.find 1997 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 1998 next_left = VM.find 1998 next_right.
Proof.
 intros  E1997 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1998 reference_control_expr_1998 reference_control_0_positions reference_control_0_safety reference_control_member_1998) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 1998 reference_control_expr_1998 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_1998 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_1998 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1997.
 reflexivity.
Qed.
Lemma reference_control_ready_1999 old :
 reference_control_ready old reference_control_expr_1999.
Proof.
 unfold reference_control_expr_1999.
apply rc_unary.
Qed.
Lemma reference_control_member_1999 : List.In (1999,reference_control_expr_1999) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 116%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_1999_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 1999 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1999 reference_control_expr_1999 reference_control_0_positions reference_control_0_safety reference_control_member_1999) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 1999 reference_control_expr_1999 inputs path old current result Position Safe Nonreg (reference_control_ready_1999 old ) Step).
Qed.
Theorem reference_control_node_1999_congruent inputs path left right next_left next_right :
 VM.find 1884 left = VM.find 1884 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 1999 next_left = VM.find 1999 next_right.
Proof.
 intros  E1884 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 1999 reference_control_expr_1999 reference_control_0_positions reference_control_0_safety reference_control_member_1999) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 1999 reference_control_expr_1999 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_1999 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_1999 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1884.
 reflexivity.
Qed.
Lemma reference_control_ready_2000 old :
 reference_control_ready old reference_control_expr_2000.
Proof.
 unfold reference_control_expr_2000.
apply rc_unary.
Qed.
Lemma reference_control_member_2000 : List.In (2000,reference_control_expr_2000) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 117%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2000_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2000 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2000 reference_control_expr_2000 reference_control_0_positions reference_control_0_safety reference_control_member_2000) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2000 reference_control_expr_2000 inputs path old current result Position Safe Nonreg (reference_control_ready_2000 old ) Step).
Qed.
Theorem reference_control_node_2000_congruent inputs path left right next_left next_right :
 VM.find 1999 left = VM.find 1999 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2000 next_left = VM.find 2000 next_right.
Proof.
 intros  E1999 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2000 reference_control_expr_2000 reference_control_0_positions reference_control_0_safety reference_control_member_2000) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2000 reference_control_expr_2000 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2000 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2000 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1999.
 reflexivity.
Qed.
Lemma reference_control_ready_2001 old :
 reference_control_ready old reference_control_expr_2001.
Proof.
 unfold reference_control_expr_2001.
apply rc_unary.
Qed.
Lemma reference_control_member_2001 : List.In (2001,reference_control_expr_2001) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 118%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2001_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2001 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2001 reference_control_expr_2001 reference_control_0_positions reference_control_0_safety reference_control_member_2001) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2001 reference_control_expr_2001 inputs path old current result Position Safe Nonreg (reference_control_ready_2001 old ) Step).
Qed.
Theorem reference_control_node_2001_congruent inputs path left right next_left next_right :
 VM.find 2000 left = VM.find 2000 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2001 next_left = VM.find 2001 next_right.
Proof.
 intros  E2000 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2001 reference_control_expr_2001 reference_control_0_positions reference_control_0_safety reference_control_member_2001) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2001 reference_control_expr_2001 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2001 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2001 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2000.
 reflexivity.
Qed.
Lemma reference_control_ready_2002 old :
 reference_control_ready old reference_control_expr_2002.
Proof.
 unfold reference_control_expr_2002.
apply rc_unary.
Qed.
Lemma reference_control_member_2002 : List.In (2002,reference_control_expr_2002) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 119%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2002_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2002 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2002 reference_control_expr_2002 reference_control_0_positions reference_control_0_safety reference_control_member_2002) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2002 reference_control_expr_2002 inputs path old current result Position Safe Nonreg (reference_control_ready_2002 old ) Step).
Qed.
Theorem reference_control_node_2002_congruent inputs path left right next_left next_right :
 VM.find 2001 left = VM.find 2001 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2002 next_left = VM.find 2002 next_right.
Proof.
 intros  E2001 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2002 reference_control_expr_2002 reference_control_0_positions reference_control_0_safety reference_control_member_2002) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2002 reference_control_expr_2002 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2002 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2002 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2001.
 reflexivity.
Qed.
Lemma reference_control_ready_2003 old :
 reference_control_ready old reference_control_expr_2003.
Proof.
 unfold reference_control_expr_2003.
apply rc_binary.
Qed.
Lemma reference_control_member_2003 : List.In (2003,reference_control_expr_2003) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 120%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2003_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2003 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2003 reference_control_expr_2003 reference_control_0_positions reference_control_0_safety reference_control_member_2003) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2003 reference_control_expr_2003 inputs path old current result Position Safe Nonreg (reference_control_ready_2003 old ) Step).
Qed.
Theorem reference_control_node_2003_congruent inputs path left right next_left next_right :
 VM.find 1884 left = VM.find 1884 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2003 next_left = VM.find 2003 next_right.
Proof.
 intros  E1884 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2003 reference_control_expr_2003 reference_control_0_positions reference_control_0_safety reference_control_member_2003) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2003 reference_control_expr_2003 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2003 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2003 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1884.
 reflexivity.
Qed.
Lemma reference_control_ready_2004 old :
 reference_control_ready old reference_control_expr_2004.
Proof.
 unfold reference_control_expr_2004.
apply rc_binary.
Qed.
Lemma reference_control_member_2004 : List.In (2004,reference_control_expr_2004) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 121%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2004_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2004 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2004 reference_control_expr_2004 reference_control_0_positions reference_control_0_safety reference_control_member_2004) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2004 reference_control_expr_2004 inputs path old current result Position Safe Nonreg (reference_control_ready_2004 old ) Step).
Qed.
Theorem reference_control_node_2004_congruent inputs path left right next_left next_right :
 VM.find 2003 left = VM.find 2003 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2004 next_left = VM.find 2004 next_right.
Proof.
 intros  E2003 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2004 reference_control_expr_2004 reference_control_0_positions reference_control_0_safety reference_control_member_2004) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2004 reference_control_expr_2004 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2004 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2004 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2003.
 reflexivity.
Qed.
Lemma reference_control_ready_2005 old :
 reference_control_ready old reference_control_expr_2005.
Proof.
 unfold reference_control_expr_2005.
apply rc_unary.
Qed.
Lemma reference_control_member_2005 : List.In (2005,reference_control_expr_2005) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 122%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2005_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2005 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2005 reference_control_expr_2005 reference_control_0_positions reference_control_0_safety reference_control_member_2005) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2005 reference_control_expr_2005 inputs path old current result Position Safe Nonreg (reference_control_ready_2005 old ) Step).
Qed.
Theorem reference_control_node_2005_congruent inputs path left right next_left next_right :
 VM.find 1884 left = VM.find 1884 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2005 next_left = VM.find 2005 next_right.
Proof.
 intros  E1884 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2005 reference_control_expr_2005 reference_control_0_positions reference_control_0_safety reference_control_member_2005) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2005 reference_control_expr_2005 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2005 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2005 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1884.
 reflexivity.
Qed.
Lemma reference_control_ready_2006 old :
 reference_control_ready old reference_control_expr_2006.
Proof.
 unfold reference_control_expr_2006.
apply rc_unary.
Qed.
Lemma reference_control_member_2006 : List.In (2006,reference_control_expr_2006) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 123%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2006_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2006 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2006 reference_control_expr_2006 reference_control_0_positions reference_control_0_safety reference_control_member_2006) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2006 reference_control_expr_2006 inputs path old current result Position Safe Nonreg (reference_control_ready_2006 old ) Step).
Qed.
Theorem reference_control_node_2006_congruent inputs path left right next_left next_right :
 VM.find 2005 left = VM.find 2005 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2006 next_left = VM.find 2006 next_right.
Proof.
 intros  E2005 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2006 reference_control_expr_2006 reference_control_0_positions reference_control_0_safety reference_control_member_2006) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2006 reference_control_expr_2006 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2006 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2006 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2005.
 reflexivity.
Qed.
Lemma reference_control_ready_2007 old :
 reference_control_ready old reference_control_expr_2007.
Proof.
 unfold reference_control_expr_2007.
apply rc_unary.
Qed.
Lemma reference_control_member_2007 : List.In (2007,reference_control_expr_2007) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 124%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2007_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2007 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2007 reference_control_expr_2007 reference_control_0_positions reference_control_0_safety reference_control_member_2007) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2007 reference_control_expr_2007 inputs path old current result Position Safe Nonreg (reference_control_ready_2007 old ) Step).
Qed.
Theorem reference_control_node_2007_congruent inputs path left right next_left next_right :
 VM.find 2006 left = VM.find 2006 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2007 next_left = VM.find 2007 next_right.
Proof.
 intros  E2006 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2007 reference_control_expr_2007 reference_control_0_positions reference_control_0_safety reference_control_member_2007) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2007 reference_control_expr_2007 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2007 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2007 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2006.
 reflexivity.
Qed.
Lemma reference_control_ready_2008 old :
 reference_control_ready old reference_control_expr_2008.
Proof.
 unfold reference_control_expr_2008.
apply rc_unary.
Qed.
Lemma reference_control_member_2008 : List.In (2008,reference_control_expr_2008) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 125%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2008_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2008 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2008 reference_control_expr_2008 reference_control_0_positions reference_control_0_safety reference_control_member_2008) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2008 reference_control_expr_2008 inputs path old current result Position Safe Nonreg (reference_control_ready_2008 old ) Step).
Qed.
Theorem reference_control_node_2008_congruent inputs path left right next_left next_right :
 VM.find 2007 left = VM.find 2007 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2008 next_left = VM.find 2008 next_right.
Proof.
 intros  E2007 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2008 reference_control_expr_2008 reference_control_0_positions reference_control_0_safety reference_control_member_2008) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2008 reference_control_expr_2008 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2008 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2008 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2007.
 reflexivity.
Qed.
Lemma reference_control_ready_2009 old :
 reference_control_ready old reference_control_expr_2009.
Proof.
 unfold reference_control_expr_2009.
apply rc_binary.
Qed.
Lemma reference_control_member_2009 : List.In (2009,reference_control_expr_2009) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 126%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2009_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2009 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2009 reference_control_expr_2009 reference_control_0_positions reference_control_0_safety reference_control_member_2009) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2009 reference_control_expr_2009 inputs path old current result Position Safe Nonreg (reference_control_ready_2009 old ) Step).
Qed.
Theorem reference_control_node_2009_congruent inputs path left right next_left next_right :
 VM.find 1884 left = VM.find 1884 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2009 next_left = VM.find 2009 next_right.
Proof.
 intros  E1884 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2009 reference_control_expr_2009 reference_control_0_positions reference_control_0_safety reference_control_member_2009) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2009 reference_control_expr_2009 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2009 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2009 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1884.
 reflexivity.
Qed.
Lemma reference_control_ready_2010 old :
 reference_control_ready old reference_control_expr_2010.
Proof.
 unfold reference_control_expr_2010.
apply rc_binary.
Qed.
Lemma reference_control_member_2010 : List.In (2010,reference_control_expr_2010) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 127%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2010_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2010 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2010 reference_control_expr_2010 reference_control_0_positions reference_control_0_safety reference_control_member_2010) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2010 reference_control_expr_2010 inputs path old current result Position Safe Nonreg (reference_control_ready_2010 old ) Step).
Qed.
Theorem reference_control_node_2010_congruent inputs path left right next_left next_right :
 VM.find 2009 left = VM.find 2009 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2010 next_left = VM.find 2010 next_right.
Proof.
 intros  E2009 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2010 reference_control_expr_2010 reference_control_0_positions reference_control_0_safety reference_control_member_2010) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2010 reference_control_expr_2010 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2010 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2010 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2009.
 reflexivity.
Qed.
Lemma reference_control_ready_2011 old :
 reference_control_ready old reference_control_expr_2011.
Proof.
 unfold reference_control_expr_2011.
apply rc_unary.
Qed.
Lemma reference_control_member_2011 : List.In (2011,reference_control_expr_2011) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 128%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2011_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2011 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2011 reference_control_expr_2011 reference_control_0_positions reference_control_0_safety reference_control_member_2011) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2011 reference_control_expr_2011 inputs path old current result Position Safe Nonreg (reference_control_ready_2011 old ) Step).
Qed.
Theorem reference_control_node_2011_congruent inputs path left right next_left next_right :
 VM.find 1884 left = VM.find 1884 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2011 next_left = VM.find 2011 next_right.
Proof.
 intros  E1884 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2011 reference_control_expr_2011 reference_control_0_positions reference_control_0_safety reference_control_member_2011) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2011 reference_control_expr_2011 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2011 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2011 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1884.
 reflexivity.
Qed.
Lemma reference_control_ready_2012 old :
 reference_control_ready old reference_control_expr_2012.
Proof.
 unfold reference_control_expr_2012.
apply rc_unary.
Qed.
Lemma reference_control_member_2012 : List.In (2012,reference_control_expr_2012) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 129%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2012_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2012 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2012 reference_control_expr_2012 reference_control_0_positions reference_control_0_safety reference_control_member_2012) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2012 reference_control_expr_2012 inputs path old current result Position Safe Nonreg (reference_control_ready_2012 old ) Step).
Qed.
Theorem reference_control_node_2012_congruent inputs path left right next_left next_right :
 VM.find 2011 left = VM.find 2011 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2012 next_left = VM.find 2012 next_right.
Proof.
 intros  E2011 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2012 reference_control_expr_2012 reference_control_0_positions reference_control_0_safety reference_control_member_2012) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2012 reference_control_expr_2012 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2012 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2012 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2011.
 reflexivity.
Qed.
Lemma reference_control_ready_2013 old :
 reference_control_ready old reference_control_expr_2013.
Proof.
 unfold reference_control_expr_2013.
apply rc_binary.
Qed.
Lemma reference_control_member_2013 : List.In (2013,reference_control_expr_2013) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 130%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2013_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2013 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2013 reference_control_expr_2013 reference_control_0_positions reference_control_0_safety reference_control_member_2013) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2013 reference_control_expr_2013 inputs path old current result Position Safe Nonreg (reference_control_ready_2013 old ) Step).
Qed.
Theorem reference_control_node_2013_congruent inputs path left right next_left next_right :
 VM.find 1884 left = VM.find 1884 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2013 next_left = VM.find 2013 next_right.
Proof.
 intros  E1884 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2013 reference_control_expr_2013 reference_control_0_positions reference_control_0_safety reference_control_member_2013) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2013 reference_control_expr_2013 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2013 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2013 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1884.
 reflexivity.
Qed.
Lemma reference_control_ready_2014 old :
 reference_control_ready old reference_control_expr_2014.
Proof.
 unfold reference_control_expr_2014.
apply rc_binary.
Qed.
Lemma reference_control_member_2014 : List.In (2014,reference_control_expr_2014) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 131%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2014_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2014 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2014 reference_control_expr_2014 reference_control_0_positions reference_control_0_safety reference_control_member_2014) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2014 reference_control_expr_2014 inputs path old current result Position Safe Nonreg (reference_control_ready_2014 old ) Step).
Qed.
Theorem reference_control_node_2014_congruent inputs path left right next_left next_right :
 VM.find 2013 left = VM.find 2013 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2014 next_left = VM.find 2014 next_right.
Proof.
 intros  E2013 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2014 reference_control_expr_2014 reference_control_0_positions reference_control_0_safety reference_control_member_2014) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2014 reference_control_expr_2014 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2014 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2014 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2013.
 reflexivity.
Qed.
Lemma reference_control_ready_2015 old :
 reference_control_ready old reference_control_expr_2015.
Proof.
 unfold reference_control_expr_2015.
apply rc_unary.
Qed.
Lemma reference_control_member_2015 : List.In (2015,reference_control_expr_2015) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 132%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2015_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2015 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2015 reference_control_expr_2015 reference_control_0_positions reference_control_0_safety reference_control_member_2015) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2015 reference_control_expr_2015 inputs path old current result Position Safe Nonreg (reference_control_ready_2015 old ) Step).
Qed.
Theorem reference_control_node_2015_congruent inputs path left right next_left next_right :
 VM.find 1884 left = VM.find 1884 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2015 next_left = VM.find 2015 next_right.
Proof.
 intros  E1884 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2015 reference_control_expr_2015 reference_control_0_positions reference_control_0_safety reference_control_member_2015) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2015 reference_control_expr_2015 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2015 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2015 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1884.
 reflexivity.
Qed.
Lemma reference_control_ready_2016 old :
 reference_control_ready old reference_control_expr_2016.
Proof.
 unfold reference_control_expr_2016.
apply rc_unary.
Qed.
Lemma reference_control_member_2016 : List.In (2016,reference_control_expr_2016) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 133%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2016_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2016 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2016 reference_control_expr_2016 reference_control_0_positions reference_control_0_safety reference_control_member_2016) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2016 reference_control_expr_2016 inputs path old current result Position Safe Nonreg (reference_control_ready_2016 old ) Step).
Qed.
Theorem reference_control_node_2016_congruent inputs path left right next_left next_right :
 VM.find 2015 left = VM.find 2015 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2016 next_left = VM.find 2016 next_right.
Proof.
 intros  E2015 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2016 reference_control_expr_2016 reference_control_0_positions reference_control_0_safety reference_control_member_2016) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2016 reference_control_expr_2016 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2016 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2016 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2015.
 reflexivity.
Qed.
Lemma reference_control_ready_2017 old :
 reference_control_ready old reference_control_expr_2017.
Proof.
 unfold reference_control_expr_2017.
apply rc_unary.
Qed.
Lemma reference_control_member_2017 : List.In (2017,reference_control_expr_2017) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 134%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2017_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2017 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2017 reference_control_expr_2017 reference_control_0_positions reference_control_0_safety reference_control_member_2017) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2017 reference_control_expr_2017 inputs path old current result Position Safe Nonreg (reference_control_ready_2017 old ) Step).
Qed.
Theorem reference_control_node_2017_congruent inputs path left right next_left next_right :
 VM.find 2016 left = VM.find 2016 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2017 next_left = VM.find 2017 next_right.
Proof.
 intros  E2016 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2017 reference_control_expr_2017 reference_control_0_positions reference_control_0_safety reference_control_member_2017) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2017 reference_control_expr_2017 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2017 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2017 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2016.
 reflexivity.
Qed.
Lemma reference_control_ready_2018 old :
 reference_control_ready old reference_control_expr_2018.
Proof.
 unfold reference_control_expr_2018.
apply rc_binary.
Qed.
Lemma reference_control_member_2018 : List.In (2018,reference_control_expr_2018) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 135%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2018_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2018 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2018 reference_control_expr_2018 reference_control_0_positions reference_control_0_safety reference_control_member_2018) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2018 reference_control_expr_2018 inputs path old current result Position Safe Nonreg (reference_control_ready_2018 old ) Step).
Qed.
Theorem reference_control_node_2018_congruent inputs path left right next_left next_right :
 VM.find 1884 left = VM.find 1884 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2018 next_left = VM.find 2018 next_right.
Proof.
 intros  E1884 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2018 reference_control_expr_2018 reference_control_0_positions reference_control_0_safety reference_control_member_2018) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2018 reference_control_expr_2018 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2018 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2018 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1884.
 reflexivity.
Qed.
Lemma reference_control_ready_2019 old :
 reference_control_ready old reference_control_expr_2019.
Proof.
 unfold reference_control_expr_2019.
apply rc_binary.
Qed.
Lemma reference_control_member_2019 : List.In (2019,reference_control_expr_2019) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 136%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2019_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2019 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2019 reference_control_expr_2019 reference_control_0_positions reference_control_0_safety reference_control_member_2019) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2019 reference_control_expr_2019 inputs path old current result Position Safe Nonreg (reference_control_ready_2019 old ) Step).
Qed.
Theorem reference_control_node_2019_congruent inputs path left right next_left next_right :
 VM.find 2018 left = VM.find 2018 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2019 next_left = VM.find 2019 next_right.
Proof.
 intros  E2018 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2019 reference_control_expr_2019 reference_control_0_positions reference_control_0_safety reference_control_member_2019) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2019 reference_control_expr_2019 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2019 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2019 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2018.
 reflexivity.
Qed.
Lemma reference_control_ready_2020 old :
 reference_control_ready old reference_control_expr_2020.
Proof.
 unfold reference_control_expr_2020.
apply rc_unary.
Qed.
Lemma reference_control_member_2020 : List.In (2020,reference_control_expr_2020) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 137%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2020_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2020 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2020 reference_control_expr_2020 reference_control_0_positions reference_control_0_safety reference_control_member_2020) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2020 reference_control_expr_2020 inputs path old current result Position Safe Nonreg (reference_control_ready_2020 old ) Step).
Qed.
Theorem reference_control_node_2020_congruent inputs path left right next_left next_right :
 VM.find 1884 left = VM.find 1884 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2020 next_left = VM.find 2020 next_right.
Proof.
 intros  E1884 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2020 reference_control_expr_2020 reference_control_0_positions reference_control_0_safety reference_control_member_2020) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2020 reference_control_expr_2020 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2020 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2020 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1884.
 reflexivity.
Qed.
Lemma reference_control_ready_2021 old :
 reference_control_ready old reference_control_expr_2021.
Proof.
 unfold reference_control_expr_2021.
apply rc_unary.
Qed.
Lemma reference_control_member_2021 : List.In (2021,reference_control_expr_2021) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 138%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2021_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2021 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2021 reference_control_expr_2021 reference_control_0_positions reference_control_0_safety reference_control_member_2021) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2021 reference_control_expr_2021 inputs path old current result Position Safe Nonreg (reference_control_ready_2021 old ) Step).
Qed.
Theorem reference_control_node_2021_congruent inputs path left right next_left next_right :
 VM.find 2020 left = VM.find 2020 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2021 next_left = VM.find 2021 next_right.
Proof.
 intros  E2020 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2021 reference_control_expr_2021 reference_control_0_positions reference_control_0_safety reference_control_member_2021) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2021 reference_control_expr_2021 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2021 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2021 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2020.
 reflexivity.
Qed.
Lemma reference_control_ready_2022 old :
 reference_control_ready old reference_control_expr_2022.
Proof.
 unfold reference_control_expr_2022.
apply rc_unary.
Qed.
Lemma reference_control_member_2022 : List.In (2022,reference_control_expr_2022) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 139%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2022_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2022 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2022 reference_control_expr_2022 reference_control_0_positions reference_control_0_safety reference_control_member_2022) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2022 reference_control_expr_2022 inputs path old current result Position Safe Nonreg (reference_control_ready_2022 old ) Step).
Qed.
Theorem reference_control_node_2022_congruent inputs path left right next_left next_right :
 VM.find 2021 left = VM.find 2021 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2022 next_left = VM.find 2022 next_right.
Proof.
 intros  E2021 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2022 reference_control_expr_2022 reference_control_0_positions reference_control_0_safety reference_control_member_2022) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2022 reference_control_expr_2022 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2022 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2022 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2021.
 reflexivity.
Qed.
Lemma reference_control_ready_2023 old :
 reference_control_ready old reference_control_expr_2023.
Proof.
 unfold reference_control_expr_2023.
apply rc_binary.
Qed.
Lemma reference_control_member_2023 : List.In (2023,reference_control_expr_2023) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 140%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2023_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2023 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2023 reference_control_expr_2023 reference_control_0_positions reference_control_0_safety reference_control_member_2023) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2023 reference_control_expr_2023 inputs path old current result Position Safe Nonreg (reference_control_ready_2023 old ) Step).
Qed.
Theorem reference_control_node_2023_congruent inputs path left right next_left next_right :
 VM.find 1884 left = VM.find 1884 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2023 next_left = VM.find 2023 next_right.
Proof.
 intros  E1884 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2023 reference_control_expr_2023 reference_control_0_positions reference_control_0_safety reference_control_member_2023) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2023 reference_control_expr_2023 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2023 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2023 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1884.
 reflexivity.
Qed.
Lemma reference_control_ready_2024 old :
 reference_control_ready old reference_control_expr_2024.
Proof.
 unfold reference_control_expr_2024.
apply rc_binary.
Qed.
Lemma reference_control_member_2024 : List.In (2024,reference_control_expr_2024) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 141%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2024_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2024 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2024 reference_control_expr_2024 reference_control_0_positions reference_control_0_safety reference_control_member_2024) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2024 reference_control_expr_2024 inputs path old current result Position Safe Nonreg (reference_control_ready_2024 old ) Step).
Qed.
Theorem reference_control_node_2024_congruent inputs path left right next_left next_right :
 VM.find 2023 left = VM.find 2023 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2024 next_left = VM.find 2024 next_right.
Proof.
 intros  E2023 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2024 reference_control_expr_2024 reference_control_0_positions reference_control_0_safety reference_control_member_2024) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2024 reference_control_expr_2024 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2024 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2024 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2023.
 reflexivity.
Qed.
Lemma reference_control_ready_2025 old :
 reference_control_ready old reference_control_expr_2025.
Proof.
 unfold reference_control_expr_2025.
apply rc_unary.
Qed.
Lemma reference_control_member_2025 : List.In (2025,reference_control_expr_2025) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 142%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2025_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2025 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2025 reference_control_expr_2025 reference_control_0_positions reference_control_0_safety reference_control_member_2025) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2025 reference_control_expr_2025 inputs path old current result Position Safe Nonreg (reference_control_ready_2025 old ) Step).
Qed.
Theorem reference_control_node_2025_congruent inputs path left right next_left next_right :
 VM.find 1884 left = VM.find 1884 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2025 next_left = VM.find 2025 next_right.
Proof.
 intros  E1884 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2025 reference_control_expr_2025 reference_control_0_positions reference_control_0_safety reference_control_member_2025) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2025 reference_control_expr_2025 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2025 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2025 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1884.
 reflexivity.
Qed.
Lemma reference_control_ready_2026 old :
 reference_control_ready old reference_control_expr_2026.
Proof.
 unfold reference_control_expr_2026.
apply rc_unary.
Qed.
Lemma reference_control_member_2026 : List.In (2026,reference_control_expr_2026) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 143%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2026_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2026 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2026 reference_control_expr_2026 reference_control_0_positions reference_control_0_safety reference_control_member_2026) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2026 reference_control_expr_2026 inputs path old current result Position Safe Nonreg (reference_control_ready_2026 old ) Step).
Qed.
Theorem reference_control_node_2026_congruent inputs path left right next_left next_right :
 VM.find 2025 left = VM.find 2025 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2026 next_left = VM.find 2026 next_right.
Proof.
 intros  E2025 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2026 reference_control_expr_2026 reference_control_0_positions reference_control_0_safety reference_control_member_2026) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2026 reference_control_expr_2026 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2026 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2026 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2025.
 reflexivity.
Qed.
Lemma reference_control_ready_2027 old :
 reference_control_ready old reference_control_expr_2027.
Proof.
 unfold reference_control_expr_2027.
apply rc_unary.
Qed.
Lemma reference_control_member_2027 : List.In (2027,reference_control_expr_2027) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 144%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2027_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2027 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2027 reference_control_expr_2027 reference_control_0_positions reference_control_0_safety reference_control_member_2027) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2027 reference_control_expr_2027 inputs path old current result Position Safe Nonreg (reference_control_ready_2027 old ) Step).
Qed.
Theorem reference_control_node_2027_congruent inputs path left right next_left next_right :
 VM.find 2026 left = VM.find 2026 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2027 next_left = VM.find 2027 next_right.
Proof.
 intros  E2026 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2027 reference_control_expr_2027 reference_control_0_positions reference_control_0_safety reference_control_member_2027) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2027 reference_control_expr_2027 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2027 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2027 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2026.
 reflexivity.
Qed.
Lemma reference_control_ready_2028 old :
 reference_control_ready old reference_control_expr_2028.
Proof.
 unfold reference_control_expr_2028.
apply rc_binary.
Qed.
Lemma reference_control_member_2028 : List.In (2028,reference_control_expr_2028) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 145%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2028_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2028 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2028 reference_control_expr_2028 reference_control_0_positions reference_control_0_safety reference_control_member_2028) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2028 reference_control_expr_2028 inputs path old current result Position Safe Nonreg (reference_control_ready_2028 old ) Step).
Qed.
Theorem reference_control_node_2028_congruent inputs path left right next_left next_right :
 VM.find 1884 left = VM.find 1884 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2028 next_left = VM.find 2028 next_right.
Proof.
 intros  E1884 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2028 reference_control_expr_2028 reference_control_0_positions reference_control_0_safety reference_control_member_2028) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2028 reference_control_expr_2028 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2028 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2028 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1884.
 reflexivity.
Qed.
Lemma reference_control_ready_2029 old :
 reference_control_ready old reference_control_expr_2029.
Proof.
 unfold reference_control_expr_2029.
apply rc_binary.
Qed.
Lemma reference_control_member_2029 : List.In (2029,reference_control_expr_2029) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 146%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2029_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2029 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2029 reference_control_expr_2029 reference_control_0_positions reference_control_0_safety reference_control_member_2029) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2029 reference_control_expr_2029 inputs path old current result Position Safe Nonreg (reference_control_ready_2029 old ) Step).
Qed.
Theorem reference_control_node_2029_congruent inputs path left right next_left next_right :
 VM.find 2028 left = VM.find 2028 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2029 next_left = VM.find 2029 next_right.
Proof.
 intros  E2028 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2029 reference_control_expr_2029 reference_control_0_positions reference_control_0_safety reference_control_member_2029) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2029 reference_control_expr_2029 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2029 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2029 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2028.
 reflexivity.
Qed.
Lemma reference_control_ready_2030 old :
 reference_control_ready old reference_control_expr_2030.
Proof.
 unfold reference_control_expr_2030.
apply rc_unary.
Qed.
Lemma reference_control_member_2030 : List.In (2030,reference_control_expr_2030) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 147%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2030_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2030 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2030 reference_control_expr_2030 reference_control_0_positions reference_control_0_safety reference_control_member_2030) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2030 reference_control_expr_2030 inputs path old current result Position Safe Nonreg (reference_control_ready_2030 old ) Step).
Qed.
Theorem reference_control_node_2030_congruent inputs path left right next_left next_right :
 VM.find 1884 left = VM.find 1884 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2030 next_left = VM.find 2030 next_right.
Proof.
 intros  E1884 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2030 reference_control_expr_2030 reference_control_0_positions reference_control_0_safety reference_control_member_2030) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2030 reference_control_expr_2030 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2030 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2030 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1884.
 reflexivity.
Qed.
Lemma reference_control_ready_2031 old :
 reference_control_ready old reference_control_expr_2031.
Proof.
 unfold reference_control_expr_2031.
apply rc_unary.
Qed.
Lemma reference_control_member_2031 : List.In (2031,reference_control_expr_2031) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 148%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2031_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2031 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2031 reference_control_expr_2031 reference_control_0_positions reference_control_0_safety reference_control_member_2031) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2031 reference_control_expr_2031 inputs path old current result Position Safe Nonreg (reference_control_ready_2031 old ) Step).
Qed.
Theorem reference_control_node_2031_congruent inputs path left right next_left next_right :
 VM.find 2030 left = VM.find 2030 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2031 next_left = VM.find 2031 next_right.
Proof.
 intros  E2030 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2031 reference_control_expr_2031 reference_control_0_positions reference_control_0_safety reference_control_member_2031) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2031 reference_control_expr_2031 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2031 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2031 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2030.
 reflexivity.
Qed.
Lemma reference_control_ready_2032 old :
 reference_control_ready old reference_control_expr_2032.
Proof.
 unfold reference_control_expr_2032.
apply rc_unary.
Qed.
Lemma reference_control_member_2032 : List.In (2032,reference_control_expr_2032) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 149%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2032_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2032 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2032 reference_control_expr_2032 reference_control_0_positions reference_control_0_safety reference_control_member_2032) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2032 reference_control_expr_2032 inputs path old current result Position Safe Nonreg (reference_control_ready_2032 old ) Step).
Qed.
Theorem reference_control_node_2032_congruent inputs path left right next_left next_right :
 VM.find 2031 left = VM.find 2031 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2032 next_left = VM.find 2032 next_right.
Proof.
 intros  E2031 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2032 reference_control_expr_2032 reference_control_0_positions reference_control_0_safety reference_control_member_2032) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2032 reference_control_expr_2032 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2032 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2032 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2031.
 reflexivity.
Qed.
Lemma reference_control_ready_2033 old :
 reference_control_ready old reference_control_expr_2033.
Proof.
 unfold reference_control_expr_2033.
apply rc_binary.
Qed.
Lemma reference_control_member_2033 : List.In (2033,reference_control_expr_2033) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 150%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2033_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2033 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2033 reference_control_expr_2033 reference_control_0_positions reference_control_0_safety reference_control_member_2033) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2033 reference_control_expr_2033 inputs path old current result Position Safe Nonreg (reference_control_ready_2033 old ) Step).
Qed.
Theorem reference_control_node_2033_congruent inputs path left right next_left next_right :
 VM.find 1884 left = VM.find 1884 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2033 next_left = VM.find 2033 next_right.
Proof.
 intros  E1884 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2033 reference_control_expr_2033 reference_control_0_positions reference_control_0_safety reference_control_member_2033) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2033 reference_control_expr_2033 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2033 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2033 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1884.
 reflexivity.
Qed.
Lemma reference_control_ready_2034 old :
 reference_control_ready old reference_control_expr_2034.
Proof.
 unfold reference_control_expr_2034.
apply rc_binary.
Qed.
Lemma reference_control_member_2034 : List.In (2034,reference_control_expr_2034) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 151%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2034_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2034 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2034 reference_control_expr_2034 reference_control_0_positions reference_control_0_safety reference_control_member_2034) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2034 reference_control_expr_2034 inputs path old current result Position Safe Nonreg (reference_control_ready_2034 old ) Step).
Qed.
Theorem reference_control_node_2034_congruent inputs path left right next_left next_right :
 VM.find 2033 left = VM.find 2033 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2034 next_left = VM.find 2034 next_right.
Proof.
 intros  E2033 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2034 reference_control_expr_2034 reference_control_0_positions reference_control_0_safety reference_control_member_2034) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2034 reference_control_expr_2034 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2034 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2034 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2033.
 reflexivity.
Qed.
Lemma reference_control_ready_2035 old :
 reference_control_ready old reference_control_expr_2035.
Proof.
 unfold reference_control_expr_2035.
apply rc_unary.
Qed.
Lemma reference_control_member_2035 : List.In (2035,reference_control_expr_2035) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 152%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2035_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2035 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2035 reference_control_expr_2035 reference_control_0_positions reference_control_0_safety reference_control_member_2035) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2035 reference_control_expr_2035 inputs path old current result Position Safe Nonreg (reference_control_ready_2035 old ) Step).
Qed.
Theorem reference_control_node_2035_congruent inputs path left right next_left next_right :
 VM.find 1884 left = VM.find 1884 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2035 next_left = VM.find 2035 next_right.
Proof.
 intros  E1884 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2035 reference_control_expr_2035 reference_control_0_positions reference_control_0_safety reference_control_member_2035) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2035 reference_control_expr_2035 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2035 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2035 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1884.
 reflexivity.
Qed.
Lemma reference_control_ready_2036 old :
 reference_control_ready old reference_control_expr_2036.
Proof.
 unfold reference_control_expr_2036.
apply rc_unary.
Qed.
Lemma reference_control_member_2036 : List.In (2036,reference_control_expr_2036) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 153%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2036_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2036 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2036 reference_control_expr_2036 reference_control_0_positions reference_control_0_safety reference_control_member_2036) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2036 reference_control_expr_2036 inputs path old current result Position Safe Nonreg (reference_control_ready_2036 old ) Step).
Qed.
Theorem reference_control_node_2036_congruent inputs path left right next_left next_right :
 VM.find 2035 left = VM.find 2035 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2036 next_left = VM.find 2036 next_right.
Proof.
 intros  E2035 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2036 reference_control_expr_2036 reference_control_0_positions reference_control_0_safety reference_control_member_2036) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2036 reference_control_expr_2036 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2036 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2036 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2035.
 reflexivity.
Qed.
Lemma reference_control_ready_2037 old :
 reference_control_ready old reference_control_expr_2037.
Proof.
 unfold reference_control_expr_2037.
apply rc_unary.
Qed.
Lemma reference_control_member_2037 : List.In (2037,reference_control_expr_2037) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 154%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2037_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2037 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2037 reference_control_expr_2037 reference_control_0_positions reference_control_0_safety reference_control_member_2037) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2037 reference_control_expr_2037 inputs path old current result Position Safe Nonreg (reference_control_ready_2037 old ) Step).
Qed.
Theorem reference_control_node_2037_congruent inputs path left right next_left next_right :
 VM.find 2036 left = VM.find 2036 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2037 next_left = VM.find 2037 next_right.
Proof.
 intros  E2036 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2037 reference_control_expr_2037 reference_control_0_positions reference_control_0_safety reference_control_member_2037) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2037 reference_control_expr_2037 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2037 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2037 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2036.
 reflexivity.
Qed.
Lemma reference_control_ready_2038 old :
 reference_control_ready old reference_control_expr_2038.
Proof.
 unfold reference_control_expr_2038.
apply rc_binary.
Qed.
Lemma reference_control_member_2038 : List.In (2038,reference_control_expr_2038) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 155%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2038_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2038 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2038 reference_control_expr_2038 reference_control_0_positions reference_control_0_safety reference_control_member_2038) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2038 reference_control_expr_2038 inputs path old current result Position Safe Nonreg (reference_control_ready_2038 old ) Step).
Qed.
Theorem reference_control_node_2038_congruent inputs path left right next_left next_right :
 VM.find 1884 left = VM.find 1884 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2038 next_left = VM.find 2038 next_right.
Proof.
 intros  E1884 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2038 reference_control_expr_2038 reference_control_0_positions reference_control_0_safety reference_control_member_2038) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2038 reference_control_expr_2038 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2038 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2038 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1884.
 reflexivity.
Qed.
Lemma reference_control_ready_2039 old :
 reference_control_ready old reference_control_expr_2039.
Proof.
 unfold reference_control_expr_2039.
apply rc_binary.
Qed.
Lemma reference_control_member_2039 : List.In (2039,reference_control_expr_2039) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 156%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2039_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2039 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2039 reference_control_expr_2039 reference_control_0_positions reference_control_0_safety reference_control_member_2039) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2039 reference_control_expr_2039 inputs path old current result Position Safe Nonreg (reference_control_ready_2039 old ) Step).
Qed.
Theorem reference_control_node_2039_congruent inputs path left right next_left next_right :
 VM.find 2038 left = VM.find 2038 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2039 next_left = VM.find 2039 next_right.
Proof.
 intros  E2038 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2039 reference_control_expr_2039 reference_control_0_positions reference_control_0_safety reference_control_member_2039) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2039 reference_control_expr_2039 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2039 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2039 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2038.
 reflexivity.
Qed.
Lemma reference_control_ready_2040 old :
 reference_control_ready old reference_control_expr_2040.
Proof.
 unfold reference_control_expr_2040.
apply rc_unary.
Qed.
Lemma reference_control_member_2040 : List.In (2040,reference_control_expr_2040) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 157%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2040_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2040 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2040 reference_control_expr_2040 reference_control_0_positions reference_control_0_safety reference_control_member_2040) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2040 reference_control_expr_2040 inputs path old current result Position Safe Nonreg (reference_control_ready_2040 old ) Step).
Qed.
Theorem reference_control_node_2040_congruent inputs path left right next_left next_right :
 VM.find 1884 left = VM.find 1884 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2040 next_left = VM.find 2040 next_right.
Proof.
 intros  E1884 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2040 reference_control_expr_2040 reference_control_0_positions reference_control_0_safety reference_control_member_2040) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2040 reference_control_expr_2040 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2040 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2040 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1884.
 reflexivity.
Qed.
Lemma reference_control_ready_2041 old :
 reference_control_ready old reference_control_expr_2041.
Proof.
 unfold reference_control_expr_2041.
apply rc_unary.
Qed.
Lemma reference_control_member_2041 : List.In (2041,reference_control_expr_2041) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 158%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2041_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2041 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2041 reference_control_expr_2041 reference_control_0_positions reference_control_0_safety reference_control_member_2041) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2041 reference_control_expr_2041 inputs path old current result Position Safe Nonreg (reference_control_ready_2041 old ) Step).
Qed.
Theorem reference_control_node_2041_congruent inputs path left right next_left next_right :
 VM.find 2040 left = VM.find 2040 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2041 next_left = VM.find 2041 next_right.
Proof.
 intros  E2040 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2041 reference_control_expr_2041 reference_control_0_positions reference_control_0_safety reference_control_member_2041) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2041 reference_control_expr_2041 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2041 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2041 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2040.
 reflexivity.
Qed.
Lemma reference_control_ready_2042 old :
 reference_control_ready old reference_control_expr_2042.
Proof.
 unfold reference_control_expr_2042.
apply rc_unary.
Qed.
Lemma reference_control_member_2042 : List.In (2042,reference_control_expr_2042) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 159%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2042_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2042 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2042 reference_control_expr_2042 reference_control_0_positions reference_control_0_safety reference_control_member_2042) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2042 reference_control_expr_2042 inputs path old current result Position Safe Nonreg (reference_control_ready_2042 old ) Step).
Qed.
Theorem reference_control_node_2042_congruent inputs path left right next_left next_right :
 VM.find 2041 left = VM.find 2041 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2042 next_left = VM.find 2042 next_right.
Proof.
 intros  E2041 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2042 reference_control_expr_2042 reference_control_0_positions reference_control_0_safety reference_control_member_2042) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2042 reference_control_expr_2042 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2042 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2042 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2041.
 reflexivity.
Qed.
Lemma reference_control_ready_2043 old :
 reference_control_ready old reference_control_expr_2043.
Proof.
 unfold reference_control_expr_2043.
apply rc_binary.
Qed.
Lemma reference_control_member_2043 : List.In (2043,reference_control_expr_2043) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 160%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2043_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2043 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2043 reference_control_expr_2043 reference_control_0_positions reference_control_0_safety reference_control_member_2043) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2043 reference_control_expr_2043 inputs path old current result Position Safe Nonreg (reference_control_ready_2043 old ) Step).
Qed.
Theorem reference_control_node_2043_congruent inputs path left right next_left next_right :
 VM.find 1884 left = VM.find 1884 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2043 next_left = VM.find 2043 next_right.
Proof.
 intros  E1884 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2043 reference_control_expr_2043 reference_control_0_positions reference_control_0_safety reference_control_member_2043) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2043 reference_control_expr_2043 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2043 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2043 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1884.
 reflexivity.
Qed.
Lemma reference_control_ready_2044 old :
 reference_control_ready old reference_control_expr_2044.
Proof.
 unfold reference_control_expr_2044.
apply rc_binary.
Qed.
Lemma reference_control_member_2044 : List.In (2044,reference_control_expr_2044) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 161%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2044_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2044 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2044 reference_control_expr_2044 reference_control_0_positions reference_control_0_safety reference_control_member_2044) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2044 reference_control_expr_2044 inputs path old current result Position Safe Nonreg (reference_control_ready_2044 old ) Step).
Qed.
Theorem reference_control_node_2044_congruent inputs path left right next_left next_right :
 VM.find 2043 left = VM.find 2043 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2044 next_left = VM.find 2044 next_right.
Proof.
 intros  E2043 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2044 reference_control_expr_2044 reference_control_0_positions reference_control_0_safety reference_control_member_2044) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2044 reference_control_expr_2044 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2044 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2044 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2043.
 reflexivity.
Qed.
Lemma reference_control_ready_2045 old :
 reference_control_ready old reference_control_expr_2045.
Proof.
 unfold reference_control_expr_2045.
apply rc_unary.
Qed.
Lemma reference_control_member_2045 : List.In (2045,reference_control_expr_2045) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 162%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2045_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2045 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2045 reference_control_expr_2045 reference_control_0_positions reference_control_0_safety reference_control_member_2045) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2045 reference_control_expr_2045 inputs path old current result Position Safe Nonreg (reference_control_ready_2045 old ) Step).
Qed.
Theorem reference_control_node_2045_congruent inputs path left right next_left next_right :
 VM.find 1884 left = VM.find 1884 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2045 next_left = VM.find 2045 next_right.
Proof.
 intros  E1884 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2045 reference_control_expr_2045 reference_control_0_positions reference_control_0_safety reference_control_member_2045) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2045 reference_control_expr_2045 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2045 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2045 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1884.
 reflexivity.
Qed.
Lemma reference_control_ready_2046 old :
 reference_control_ready old reference_control_expr_2046.
Proof.
 unfold reference_control_expr_2046.
apply rc_unary.
Qed.
Lemma reference_control_member_2046 : List.In (2046,reference_control_expr_2046) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 163%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2046_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2046 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2046 reference_control_expr_2046 reference_control_0_positions reference_control_0_safety reference_control_member_2046) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2046 reference_control_expr_2046 inputs path old current result Position Safe Nonreg (reference_control_ready_2046 old ) Step).
Qed.
Theorem reference_control_node_2046_congruent inputs path left right next_left next_right :
 VM.find 2045 left = VM.find 2045 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2046 next_left = VM.find 2046 next_right.
Proof.
 intros  E2045 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2046 reference_control_expr_2046 reference_control_0_positions reference_control_0_safety reference_control_member_2046) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2046 reference_control_expr_2046 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2046 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2046 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2045.
 reflexivity.
Qed.
Lemma reference_control_ready_2047 old :
 reference_control_ready old reference_control_expr_2047.
Proof.
 unfold reference_control_expr_2047.
apply rc_unary.
Qed.
Lemma reference_control_member_2047 : List.In (2047,reference_control_expr_2047) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 164%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2047_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2047 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2047 reference_control_expr_2047 reference_control_0_positions reference_control_0_safety reference_control_member_2047) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2047 reference_control_expr_2047 inputs path old current result Position Safe Nonreg (reference_control_ready_2047 old ) Step).
Qed.
Theorem reference_control_node_2047_congruent inputs path left right next_left next_right :
 VM.find 2046 left = VM.find 2046 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2047 next_left = VM.find 2047 next_right.
Proof.
 intros  E2046 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2047 reference_control_expr_2047 reference_control_0_positions reference_control_0_safety reference_control_member_2047) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2047 reference_control_expr_2047 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2047 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2047 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2046.
 reflexivity.
Qed.
Lemma reference_control_ready_2048 old :
 reference_control_ready old reference_control_expr_2048.
Proof.
 unfold reference_control_expr_2048.
apply rc_binary.
Qed.
Lemma reference_control_member_2048 : List.In (2048,reference_control_expr_2048) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 165%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2048_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2048 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2048 reference_control_expr_2048 reference_control_0_positions reference_control_0_safety reference_control_member_2048) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2048 reference_control_expr_2048 inputs path old current result Position Safe Nonreg (reference_control_ready_2048 old ) Step).
Qed.
Theorem reference_control_node_2048_congruent inputs path left right next_left next_right :
 VM.find 1884 left = VM.find 1884 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2048 next_left = VM.find 2048 next_right.
Proof.
 intros  E1884 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2048 reference_control_expr_2048 reference_control_0_positions reference_control_0_safety reference_control_member_2048) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2048 reference_control_expr_2048 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2048 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2048 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1884.
 reflexivity.
Qed.
Lemma reference_control_ready_2049 old :
 reference_control_ready old reference_control_expr_2049.
Proof.
 unfold reference_control_expr_2049.
apply rc_binary.
Qed.
Lemma reference_control_member_2049 : List.In (2049,reference_control_expr_2049) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 166%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2049_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2049 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2049 reference_control_expr_2049 reference_control_0_positions reference_control_0_safety reference_control_member_2049) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2049 reference_control_expr_2049 inputs path old current result Position Safe Nonreg (reference_control_ready_2049 old ) Step).
Qed.
Theorem reference_control_node_2049_congruent inputs path left right next_left next_right :
 VM.find 2048 left = VM.find 2048 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2049 next_left = VM.find 2049 next_right.
Proof.
 intros  E2048 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2049 reference_control_expr_2049 reference_control_0_positions reference_control_0_safety reference_control_member_2049) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2049 reference_control_expr_2049 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2049 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2049 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2048.
 reflexivity.
Qed.
Lemma reference_control_ready_2050 old :
 reference_control_ready old reference_control_expr_2050.
Proof.
 unfold reference_control_expr_2050.
apply rc_unary.
Qed.
Lemma reference_control_member_2050 : List.In (2050,reference_control_expr_2050) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 167%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2050_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2050 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2050 reference_control_expr_2050 reference_control_0_positions reference_control_0_safety reference_control_member_2050) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2050 reference_control_expr_2050 inputs path old current result Position Safe Nonreg (reference_control_ready_2050 old ) Step).
Qed.
Theorem reference_control_node_2050_congruent inputs path left right next_left next_right :
 VM.find 1884 left = VM.find 1884 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2050 next_left = VM.find 2050 next_right.
Proof.
 intros  E1884 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2050 reference_control_expr_2050 reference_control_0_positions reference_control_0_safety reference_control_member_2050) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2050 reference_control_expr_2050 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2050 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2050 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1884.
 reflexivity.
Qed.
Lemma reference_control_ready_2051 old :
 reference_control_ready old reference_control_expr_2051.
Proof.
 unfold reference_control_expr_2051.
apply rc_unary.
Qed.
Lemma reference_control_member_2051 : List.In (2051,reference_control_expr_2051) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 168%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2051_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2051 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2051 reference_control_expr_2051 reference_control_0_positions reference_control_0_safety reference_control_member_2051) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2051 reference_control_expr_2051 inputs path old current result Position Safe Nonreg (reference_control_ready_2051 old ) Step).
Qed.
Theorem reference_control_node_2051_congruent inputs path left right next_left next_right :
 VM.find 2050 left = VM.find 2050 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2051 next_left = VM.find 2051 next_right.
Proof.
 intros  E2050 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2051 reference_control_expr_2051 reference_control_0_positions reference_control_0_safety reference_control_member_2051) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2051 reference_control_expr_2051 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2051 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2051 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2050.
 reflexivity.
Qed.
Lemma reference_control_ready_2052 old :
 reference_control_ready old reference_control_expr_2052.
Proof.
 unfold reference_control_expr_2052.
apply rc_unary.
Qed.
Lemma reference_control_member_2052 : List.In (2052,reference_control_expr_2052) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 169%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2052_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2052 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2052 reference_control_expr_2052 reference_control_0_positions reference_control_0_safety reference_control_member_2052) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2052 reference_control_expr_2052 inputs path old current result Position Safe Nonreg (reference_control_ready_2052 old ) Step).
Qed.
Theorem reference_control_node_2052_congruent inputs path left right next_left next_right :
 VM.find 2051 left = VM.find 2051 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2052 next_left = VM.find 2052 next_right.
Proof.
 intros  E2051 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2052 reference_control_expr_2052 reference_control_0_positions reference_control_0_safety reference_control_member_2052) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2052 reference_control_expr_2052 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2052 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2052 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2051.
 reflexivity.
Qed.
Lemma reference_control_ready_2053 old :
 reference_control_ready old reference_control_expr_2053.
Proof.
 unfold reference_control_expr_2053.
apply rc_binary.
Qed.
Lemma reference_control_member_2053 : List.In (2053,reference_control_expr_2053) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 170%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2053_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2053 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2053 reference_control_expr_2053 reference_control_0_positions reference_control_0_safety reference_control_member_2053) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2053 reference_control_expr_2053 inputs path old current result Position Safe Nonreg (reference_control_ready_2053 old ) Step).
Qed.
Theorem reference_control_node_2053_congruent inputs path left right next_left next_right :
 VM.find 1884 left = VM.find 1884 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2053 next_left = VM.find 2053 next_right.
Proof.
 intros  E1884 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2053 reference_control_expr_2053 reference_control_0_positions reference_control_0_safety reference_control_member_2053) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2053 reference_control_expr_2053 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2053 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2053 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1884.
 reflexivity.
Qed.
Lemma reference_control_ready_2054 old :
 reference_control_ready old reference_control_expr_2054.
Proof.
 unfold reference_control_expr_2054.
apply rc_binary.
Qed.
Lemma reference_control_member_2054 : List.In (2054,reference_control_expr_2054) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 171%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2054_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2054 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2054 reference_control_expr_2054 reference_control_0_positions reference_control_0_safety reference_control_member_2054) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2054 reference_control_expr_2054 inputs path old current result Position Safe Nonreg (reference_control_ready_2054 old ) Step).
Qed.
Theorem reference_control_node_2054_congruent inputs path left right next_left next_right :
 VM.find 2053 left = VM.find 2053 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2054 next_left = VM.find 2054 next_right.
Proof.
 intros  E2053 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2054 reference_control_expr_2054 reference_control_0_positions reference_control_0_safety reference_control_member_2054) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2054 reference_control_expr_2054 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2054 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2054 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2053.
 reflexivity.
Qed.
Lemma reference_control_ready_2055 old :
 reference_control_ready old reference_control_expr_2055.
Proof.
 unfold reference_control_expr_2055.
apply rc_unary.
Qed.
Lemma reference_control_member_2055 : List.In (2055,reference_control_expr_2055) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 172%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2055_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2055 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2055 reference_control_expr_2055 reference_control_0_positions reference_control_0_safety reference_control_member_2055) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2055 reference_control_expr_2055 inputs path old current result Position Safe Nonreg (reference_control_ready_2055 old ) Step).
Qed.
Theorem reference_control_node_2055_congruent inputs path left right next_left next_right :
 VM.find 1884 left = VM.find 1884 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2055 next_left = VM.find 2055 next_right.
Proof.
 intros  E1884 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2055 reference_control_expr_2055 reference_control_0_positions reference_control_0_safety reference_control_member_2055) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2055 reference_control_expr_2055 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2055 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2055 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1884.
 reflexivity.
Qed.
Lemma reference_control_ready_2056 old :
 reference_control_ready old reference_control_expr_2056.
Proof.
 unfold reference_control_expr_2056.
apply rc_unary.
Qed.
Lemma reference_control_member_2056 : List.In (2056,reference_control_expr_2056) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 173%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2056_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2056 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2056 reference_control_expr_2056 reference_control_0_positions reference_control_0_safety reference_control_member_2056) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2056 reference_control_expr_2056 inputs path old current result Position Safe Nonreg (reference_control_ready_2056 old ) Step).
Qed.
Theorem reference_control_node_2056_congruent inputs path left right next_left next_right :
 VM.find 2055 left = VM.find 2055 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2056 next_left = VM.find 2056 next_right.
Proof.
 intros  E2055 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2056 reference_control_expr_2056 reference_control_0_positions reference_control_0_safety reference_control_member_2056) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2056 reference_control_expr_2056 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2056 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2056 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2055.
 reflexivity.
Qed.
Lemma reference_control_ready_2057 old :
 reference_control_ready old reference_control_expr_2057.
Proof.
 unfold reference_control_expr_2057.
apply rc_unary.
Qed.
Lemma reference_control_member_2057 : List.In (2057,reference_control_expr_2057) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 174%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2057_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2057 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2057 reference_control_expr_2057 reference_control_0_positions reference_control_0_safety reference_control_member_2057) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2057 reference_control_expr_2057 inputs path old current result Position Safe Nonreg (reference_control_ready_2057 old ) Step).
Qed.
Theorem reference_control_node_2057_congruent inputs path left right next_left next_right :
 VM.find 2056 left = VM.find 2056 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2057 next_left = VM.find 2057 next_right.
Proof.
 intros  E2056 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2057 reference_control_expr_2057 reference_control_0_positions reference_control_0_safety reference_control_member_2057) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2057 reference_control_expr_2057 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2057 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2057 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2056.
 reflexivity.
Qed.
Lemma reference_control_ready_2058 old :
 reference_control_ready old reference_control_expr_2058.
Proof.
 unfold reference_control_expr_2058.
apply rc_binary.
Qed.
Lemma reference_control_member_2058 : List.In (2058,reference_control_expr_2058) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 175%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2058_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2058 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2058 reference_control_expr_2058 reference_control_0_positions reference_control_0_safety reference_control_member_2058) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2058 reference_control_expr_2058 inputs path old current result Position Safe Nonreg (reference_control_ready_2058 old ) Step).
Qed.
Theorem reference_control_node_2058_congruent inputs path left right next_left next_right :
 VM.find 1884 left = VM.find 1884 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2058 next_left = VM.find 2058 next_right.
Proof.
 intros  E1884 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2058 reference_control_expr_2058 reference_control_0_positions reference_control_0_safety reference_control_member_2058) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2058 reference_control_expr_2058 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2058 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2058 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1884.
 reflexivity.
Qed.
Lemma reference_control_ready_2059 old :
 reference_control_ready old reference_control_expr_2059.
Proof.
 unfold reference_control_expr_2059.
apply rc_binary.
Qed.
Lemma reference_control_member_2059 : List.In (2059,reference_control_expr_2059) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 176%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2059_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2059 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2059 reference_control_expr_2059 reference_control_0_positions reference_control_0_safety reference_control_member_2059) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2059 reference_control_expr_2059 inputs path old current result Position Safe Nonreg (reference_control_ready_2059 old ) Step).
Qed.
Theorem reference_control_node_2059_congruent inputs path left right next_left next_right :
 VM.find 2058 left = VM.find 2058 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2059 next_left = VM.find 2059 next_right.
Proof.
 intros  E2058 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2059 reference_control_expr_2059 reference_control_0_positions reference_control_0_safety reference_control_member_2059) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2059 reference_control_expr_2059 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2059 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2059 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2058.
 reflexivity.
Qed.
Lemma reference_control_ready_2060 old :
 reference_control_ready old reference_control_expr_2060.
Proof.
 unfold reference_control_expr_2060.
apply rc_unary.
Qed.
Lemma reference_control_member_2060 : List.In (2060,reference_control_expr_2060) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 177%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2060_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2060 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2060 reference_control_expr_2060 reference_control_0_positions reference_control_0_safety reference_control_member_2060) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2060 reference_control_expr_2060 inputs path old current result Position Safe Nonreg (reference_control_ready_2060 old ) Step).
Qed.
Theorem reference_control_node_2060_congruent inputs path left right next_left next_right :
 VM.find 1884 left = VM.find 1884 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2060 next_left = VM.find 2060 next_right.
Proof.
 intros  E1884 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2060 reference_control_expr_2060 reference_control_0_positions reference_control_0_safety reference_control_member_2060) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2060 reference_control_expr_2060 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2060 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2060 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1884.
 reflexivity.
Qed.
Lemma reference_control_ready_2061 old :
 reference_control_ready old reference_control_expr_2061.
Proof.
 unfold reference_control_expr_2061.
apply rc_unary.
Qed.
Lemma reference_control_member_2061 : List.In (2061,reference_control_expr_2061) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 178%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2061_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2061 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2061 reference_control_expr_2061 reference_control_0_positions reference_control_0_safety reference_control_member_2061) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2061 reference_control_expr_2061 inputs path old current result Position Safe Nonreg (reference_control_ready_2061 old ) Step).
Qed.
Theorem reference_control_node_2061_congruent inputs path left right next_left next_right :
 VM.find 2060 left = VM.find 2060 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2061 next_left = VM.find 2061 next_right.
Proof.
 intros  E2060 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2061 reference_control_expr_2061 reference_control_0_positions reference_control_0_safety reference_control_member_2061) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2061 reference_control_expr_2061 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2061 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2061 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2060.
 reflexivity.
Qed.
Lemma reference_control_ready_2062 old :
 reference_control_ready old reference_control_expr_2062.
Proof.
 unfold reference_control_expr_2062.
apply rc_unary.
Qed.
Lemma reference_control_member_2062 : List.In (2062,reference_control_expr_2062) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 179%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2062_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2062 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2062 reference_control_expr_2062 reference_control_0_positions reference_control_0_safety reference_control_member_2062) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2062 reference_control_expr_2062 inputs path old current result Position Safe Nonreg (reference_control_ready_2062 old ) Step).
Qed.
Theorem reference_control_node_2062_congruent inputs path left right next_left next_right :
 VM.find 2061 left = VM.find 2061 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2062 next_left = VM.find 2062 next_right.
Proof.
 intros  E2061 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2062 reference_control_expr_2062 reference_control_0_positions reference_control_0_safety reference_control_member_2062) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2062 reference_control_expr_2062 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2062 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2062 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2061.
 reflexivity.
Qed.
Lemma reference_control_ready_2063 old :
 reference_control_ready old reference_control_expr_2063.
Proof.
 unfold reference_control_expr_2063.
apply rc_binary.
Qed.
Lemma reference_control_member_2063 : List.In (2063,reference_control_expr_2063) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 180%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2063_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2063 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2063 reference_control_expr_2063 reference_control_0_positions reference_control_0_safety reference_control_member_2063) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2063 reference_control_expr_2063 inputs path old current result Position Safe Nonreg (reference_control_ready_2063 old ) Step).
Qed.
Theorem reference_control_node_2063_congruent inputs path left right next_left next_right :
 VM.find 1884 left = VM.find 1884 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2063 next_left = VM.find 2063 next_right.
Proof.
 intros  E1884 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2063 reference_control_expr_2063 reference_control_0_positions reference_control_0_safety reference_control_member_2063) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2063 reference_control_expr_2063 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2063 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2063 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1884.
 reflexivity.
Qed.
Lemma reference_control_ready_2064 old :
 reference_control_ready old reference_control_expr_2064.
Proof.
 unfold reference_control_expr_2064.
apply rc_binary.
Qed.
Lemma reference_control_member_2064 : List.In (2064,reference_control_expr_2064) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 181%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2064_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2064 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2064 reference_control_expr_2064 reference_control_0_positions reference_control_0_safety reference_control_member_2064) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2064 reference_control_expr_2064 inputs path old current result Position Safe Nonreg (reference_control_ready_2064 old ) Step).
Qed.
Theorem reference_control_node_2064_congruent inputs path left right next_left next_right :
 VM.find 2063 left = VM.find 2063 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2064 next_left = VM.find 2064 next_right.
Proof.
 intros  E2063 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2064 reference_control_expr_2064 reference_control_0_positions reference_control_0_safety reference_control_member_2064) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2064 reference_control_expr_2064 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2064 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2064 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2063.
 reflexivity.
Qed.
Lemma reference_control_ready_2065 old :
 reference_control_ready old reference_control_expr_2065.
Proof.
 unfold reference_control_expr_2065.
apply rc_unary.
Qed.
Lemma reference_control_member_2065 : List.In (2065,reference_control_expr_2065) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 182%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2065_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2065 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2065 reference_control_expr_2065 reference_control_0_positions reference_control_0_safety reference_control_member_2065) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2065 reference_control_expr_2065 inputs path old current result Position Safe Nonreg (reference_control_ready_2065 old ) Step).
Qed.
Theorem reference_control_node_2065_congruent inputs path left right next_left next_right :
 VM.find 1884 left = VM.find 1884 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2065 next_left = VM.find 2065 next_right.
Proof.
 intros  E1884 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2065 reference_control_expr_2065 reference_control_0_positions reference_control_0_safety reference_control_member_2065) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2065 reference_control_expr_2065 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2065 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2065 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1884.
 reflexivity.
Qed.
Lemma reference_control_ready_2066 old :
 reference_control_ready old reference_control_expr_2066.
Proof.
 unfold reference_control_expr_2066.
apply rc_unary.
Qed.
Lemma reference_control_member_2066 : List.In (2066,reference_control_expr_2066) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 183%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2066_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2066 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2066 reference_control_expr_2066 reference_control_0_positions reference_control_0_safety reference_control_member_2066) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2066 reference_control_expr_2066 inputs path old current result Position Safe Nonreg (reference_control_ready_2066 old ) Step).
Qed.
Theorem reference_control_node_2066_congruent inputs path left right next_left next_right :
 VM.find 2065 left = VM.find 2065 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2066 next_left = VM.find 2066 next_right.
Proof.
 intros  E2065 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2066 reference_control_expr_2066 reference_control_0_positions reference_control_0_safety reference_control_member_2066) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2066 reference_control_expr_2066 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2066 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2066 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2065.
 reflexivity.
Qed.
Lemma reference_control_ready_2067 old :
 reference_control_ready old reference_control_expr_2067.
Proof.
 unfold reference_control_expr_2067.
apply rc_binary.
Qed.
Lemma reference_control_member_2067 : List.In (2067,reference_control_expr_2067) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 184%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2067_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2067 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2067 reference_control_expr_2067 reference_control_0_positions reference_control_0_safety reference_control_member_2067) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2067 reference_control_expr_2067 inputs path old current result Position Safe Nonreg (reference_control_ready_2067 old ) Step).
Qed.
Theorem reference_control_node_2067_congruent inputs path left right next_left next_right :
 VM.find 1884 left = VM.find 1884 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2067 next_left = VM.find 2067 next_right.
Proof.
 intros  E1884 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2067 reference_control_expr_2067 reference_control_0_positions reference_control_0_safety reference_control_member_2067) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2067 reference_control_expr_2067 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2067 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2067 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1884.
 reflexivity.
Qed.
Lemma reference_control_ready_2068 old :
 reference_control_ready old reference_control_expr_2068.
Proof.
 unfold reference_control_expr_2068.
apply rc_binary.
Qed.
Lemma reference_control_member_2068 : List.In (2068,reference_control_expr_2068) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 185%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2068_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2068 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2068 reference_control_expr_2068 reference_control_0_positions reference_control_0_safety reference_control_member_2068) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2068 reference_control_expr_2068 inputs path old current result Position Safe Nonreg (reference_control_ready_2068 old ) Step).
Qed.
Theorem reference_control_node_2068_congruent inputs path left right next_left next_right :
 VM.find 2067 left = VM.find 2067 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2068 next_left = VM.find 2068 next_right.
Proof.
 intros  E2067 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2068 reference_control_expr_2068 reference_control_0_positions reference_control_0_safety reference_control_member_2068) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2068 reference_control_expr_2068 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2068 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2068 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2067.
 reflexivity.
Qed.
Lemma reference_control_ready_2069 old :
 reference_control_ready old reference_control_expr_2069.
Proof.
 unfold reference_control_expr_2069.
apply rc_unary.
Qed.
Lemma reference_control_member_2069 : List.In (2069,reference_control_expr_2069) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 186%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2069_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2069 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2069 reference_control_expr_2069 reference_control_0_positions reference_control_0_safety reference_control_member_2069) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2069 reference_control_expr_2069 inputs path old current result Position Safe Nonreg (reference_control_ready_2069 old ) Step).
Qed.
Theorem reference_control_node_2069_congruent inputs path left right next_left next_right :
 VM.find 1884 left = VM.find 1884 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2069 next_left = VM.find 2069 next_right.
Proof.
 intros  E1884 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2069 reference_control_expr_2069 reference_control_0_positions reference_control_0_safety reference_control_member_2069) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2069 reference_control_expr_2069 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2069 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2069 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1884.
 reflexivity.
Qed.
Lemma reference_control_ready_2070 old :
 reference_control_ready old reference_control_expr_2070.
Proof.
 unfold reference_control_expr_2070.
apply rc_unary.
Qed.
Lemma reference_control_member_2070 : List.In (2070,reference_control_expr_2070) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 187%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2070_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2070 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2070 reference_control_expr_2070 reference_control_0_positions reference_control_0_safety reference_control_member_2070) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2070 reference_control_expr_2070 inputs path old current result Position Safe Nonreg (reference_control_ready_2070 old ) Step).
Qed.
Theorem reference_control_node_2070_congruent inputs path left right next_left next_right :
 VM.find 2069 left = VM.find 2069 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2070 next_left = VM.find 2070 next_right.
Proof.
 intros  E2069 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2070 reference_control_expr_2070 reference_control_0_positions reference_control_0_safety reference_control_member_2070) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2070 reference_control_expr_2070 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2070 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2070 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2069.
 reflexivity.
Qed.
Lemma reference_control_ready_2071 old :
 reference_control_ready old reference_control_expr_2071.
Proof.
 unfold reference_control_expr_2071.
apply rc_binary.
Qed.
Lemma reference_control_member_2071 : List.In (2071,reference_control_expr_2071) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 188%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2071_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2071 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2071 reference_control_expr_2071 reference_control_0_positions reference_control_0_safety reference_control_member_2071) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2071 reference_control_expr_2071 inputs path old current result Position Safe Nonreg (reference_control_ready_2071 old ) Step).
Qed.
Theorem reference_control_node_2071_congruent inputs path left right next_left next_right :
 VM.find 1884 left = VM.find 1884 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2071 next_left = VM.find 2071 next_right.
Proof.
 intros  E1884 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2071 reference_control_expr_2071 reference_control_0_positions reference_control_0_safety reference_control_member_2071) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2071 reference_control_expr_2071 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2071 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2071 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1884.
 reflexivity.
Qed.
Lemma reference_control_ready_2072 old :
 reference_control_ready old reference_control_expr_2072.
Proof.
 unfold reference_control_expr_2072.
apply rc_binary.
Qed.
Lemma reference_control_member_2072 : List.In (2072,reference_control_expr_2072) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 189%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2072_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2072 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2072 reference_control_expr_2072 reference_control_0_positions reference_control_0_safety reference_control_member_2072) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2072 reference_control_expr_2072 inputs path old current result Position Safe Nonreg (reference_control_ready_2072 old ) Step).
Qed.
Theorem reference_control_node_2072_congruent inputs path left right next_left next_right :
 VM.find 2071 left = VM.find 2071 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2072 next_left = VM.find 2072 next_right.
Proof.
 intros  E2071 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2072 reference_control_expr_2072 reference_control_0_positions reference_control_0_safety reference_control_member_2072) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2072 reference_control_expr_2072 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2072 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2072 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2071.
 reflexivity.
Qed.
Lemma reference_control_ready_2073 old :
 reference_control_ready old reference_control_expr_2073.
Proof.
 unfold reference_control_expr_2073.
apply rc_unary.
Qed.
Lemma reference_control_member_2073 : List.In (2073,reference_control_expr_2073) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 190%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2073_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2073 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2073 reference_control_expr_2073 reference_control_0_positions reference_control_0_safety reference_control_member_2073) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2073 reference_control_expr_2073 inputs path old current result Position Safe Nonreg (reference_control_ready_2073 old ) Step).
Qed.
Theorem reference_control_node_2073_congruent inputs path left right next_left next_right :
 VM.find 1884 left = VM.find 1884 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2073 next_left = VM.find 2073 next_right.
Proof.
 intros  E1884 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2073 reference_control_expr_2073 reference_control_0_positions reference_control_0_safety reference_control_member_2073) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2073 reference_control_expr_2073 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2073 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2073 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1884.
 reflexivity.
Qed.
Lemma reference_control_ready_2074 old :
 reference_control_ready old reference_control_expr_2074.
Proof.
 unfold reference_control_expr_2074.
apply rc_unary.
Qed.
Lemma reference_control_member_2074 : List.In (2074,reference_control_expr_2074) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 191%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2074_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2074 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2074 reference_control_expr_2074 reference_control_0_positions reference_control_0_safety reference_control_member_2074) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2074 reference_control_expr_2074 inputs path old current result Position Safe Nonreg (reference_control_ready_2074 old ) Step).
Qed.
Theorem reference_control_node_2074_congruent inputs path left right next_left next_right :
 VM.find 2073 left = VM.find 2073 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2074 next_left = VM.find 2074 next_right.
Proof.
 intros  E2073 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2074 reference_control_expr_2074 reference_control_0_positions reference_control_0_safety reference_control_member_2074) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2074 reference_control_expr_2074 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2074 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2074 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2073.
 reflexivity.
Qed.
Lemma reference_control_ready_2075 old :
 reference_control_ready old reference_control_expr_2075.
Proof.
 unfold reference_control_expr_2075.
apply rc_binary.
Qed.
Lemma reference_control_member_2075 : List.In (2075,reference_control_expr_2075) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 192%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2075_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2075 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2075 reference_control_expr_2075 reference_control_0_positions reference_control_0_safety reference_control_member_2075) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2075 reference_control_expr_2075 inputs path old current result Position Safe Nonreg (reference_control_ready_2075 old ) Step).
Qed.
Theorem reference_control_node_2075_congruent inputs path left right next_left next_right :
 VM.find 1884 left = VM.find 1884 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2075 next_left = VM.find 2075 next_right.
Proof.
 intros  E1884 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2075 reference_control_expr_2075 reference_control_0_positions reference_control_0_safety reference_control_member_2075) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2075 reference_control_expr_2075 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2075 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2075 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1884.
 reflexivity.
Qed.
Lemma reference_control_ready_2076 old :
 reference_control_ready old reference_control_expr_2076.
Proof.
 unfold reference_control_expr_2076.
apply rc_binary.
Qed.
Lemma reference_control_member_2076 : List.In (2076,reference_control_expr_2076) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 193%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2076_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2076 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2076 reference_control_expr_2076 reference_control_0_positions reference_control_0_safety reference_control_member_2076) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2076 reference_control_expr_2076 inputs path old current result Position Safe Nonreg (reference_control_ready_2076 old ) Step).
Qed.
Theorem reference_control_node_2076_congruent inputs path left right next_left next_right :
 VM.find 2075 left = VM.find 2075 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2076 next_left = VM.find 2076 next_right.
Proof.
 intros  E2075 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2076 reference_control_expr_2076 reference_control_0_positions reference_control_0_safety reference_control_member_2076) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2076 reference_control_expr_2076 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2076 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2076 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2075.
 reflexivity.
Qed.
Lemma reference_control_ready_2077 old :
 reference_control_ready old reference_control_expr_2077.
Proof.
 unfold reference_control_expr_2077.
apply rc_unary.
Qed.
Lemma reference_control_member_2077 : List.In (2077,reference_control_expr_2077) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 194%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2077_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2077 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2077 reference_control_expr_2077 reference_control_0_positions reference_control_0_safety reference_control_member_2077) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2077 reference_control_expr_2077 inputs path old current result Position Safe Nonreg (reference_control_ready_2077 old ) Step).
Qed.
Theorem reference_control_node_2077_congruent inputs path left right next_left next_right :
 VM.find 1884 left = VM.find 1884 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2077 next_left = VM.find 2077 next_right.
Proof.
 intros  E1884 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2077 reference_control_expr_2077 reference_control_0_positions reference_control_0_safety reference_control_member_2077) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2077 reference_control_expr_2077 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2077 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2077 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1884.
 reflexivity.
Qed.
Lemma reference_control_ready_2078 old :
 reference_control_ready old reference_control_expr_2078.
Proof.
 unfold reference_control_expr_2078.
apply rc_unary.
Qed.
Lemma reference_control_member_2078 : List.In (2078,reference_control_expr_2078) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 195%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2078_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2078 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2078 reference_control_expr_2078 reference_control_0_positions reference_control_0_safety reference_control_member_2078) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2078 reference_control_expr_2078 inputs path old current result Position Safe Nonreg (reference_control_ready_2078 old ) Step).
Qed.
Theorem reference_control_node_2078_congruent inputs path left right next_left next_right :
 VM.find 2077 left = VM.find 2077 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2078 next_left = VM.find 2078 next_right.
Proof.
 intros  E2077 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2078 reference_control_expr_2078 reference_control_0_positions reference_control_0_safety reference_control_member_2078) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2078 reference_control_expr_2078 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2078 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2078 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2077.
 reflexivity.
Qed.
Lemma reference_control_ready_2079 old :
 reference_control_ready old reference_control_expr_2079.
Proof.
 unfold reference_control_expr_2079.
apply rc_binary.
Qed.
Lemma reference_control_member_2079 : List.In (2079,reference_control_expr_2079) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 196%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2079_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2079 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2079 reference_control_expr_2079 reference_control_0_positions reference_control_0_safety reference_control_member_2079) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2079 reference_control_expr_2079 inputs path old current result Position Safe Nonreg (reference_control_ready_2079 old ) Step).
Qed.
Theorem reference_control_node_2079_congruent inputs path left right next_left next_right :
 VM.find 1884 left = VM.find 1884 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2079 next_left = VM.find 2079 next_right.
Proof.
 intros  E1884 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2079 reference_control_expr_2079 reference_control_0_positions reference_control_0_safety reference_control_member_2079) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2079 reference_control_expr_2079 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2079 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2079 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1884.
 reflexivity.
Qed.
Lemma reference_control_ready_2080 old :
 reference_control_ready old reference_control_expr_2080.
Proof.
 unfold reference_control_expr_2080.
apply rc_binary.
Qed.
Lemma reference_control_member_2080 : List.In (2080,reference_control_expr_2080) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 197%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2080_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2080 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2080 reference_control_expr_2080 reference_control_0_positions reference_control_0_safety reference_control_member_2080) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2080 reference_control_expr_2080 inputs path old current result Position Safe Nonreg (reference_control_ready_2080 old ) Step).
Qed.
Theorem reference_control_node_2080_congruent inputs path left right next_left next_right :
 VM.find 2079 left = VM.find 2079 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2080 next_left = VM.find 2080 next_right.
Proof.
 intros  E2079 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2080 reference_control_expr_2080 reference_control_0_positions reference_control_0_safety reference_control_member_2080) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2080 reference_control_expr_2080 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2080 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2080 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2079.
 reflexivity.
Qed.
Lemma reference_control_ready_2081 old :
 reference_control_ready old reference_control_expr_2081.
Proof.
 unfold reference_control_expr_2081.
apply rc_unary.
Qed.
Lemma reference_control_member_2081 : List.In (2081,reference_control_expr_2081) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 198%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2081_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2081 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2081 reference_control_expr_2081 reference_control_0_positions reference_control_0_safety reference_control_member_2081) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2081 reference_control_expr_2081 inputs path old current result Position Safe Nonreg (reference_control_ready_2081 old ) Step).
Qed.
Theorem reference_control_node_2081_congruent inputs path left right next_left next_right :
 VM.find 1884 left = VM.find 1884 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2081 next_left = VM.find 2081 next_right.
Proof.
 intros  E1884 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2081 reference_control_expr_2081 reference_control_0_positions reference_control_0_safety reference_control_member_2081) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2081 reference_control_expr_2081 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2081 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2081 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1884.
 reflexivity.
Qed.
Lemma reference_control_ready_2082 old :
 reference_control_ready old reference_control_expr_2082.
Proof.
 unfold reference_control_expr_2082.
apply rc_unary.
Qed.
Lemma reference_control_member_2082 : List.In (2082,reference_control_expr_2082) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 199%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2082_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2082 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2082 reference_control_expr_2082 reference_control_0_positions reference_control_0_safety reference_control_member_2082) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2082 reference_control_expr_2082 inputs path old current result Position Safe Nonreg (reference_control_ready_2082 old ) Step).
Qed.
Theorem reference_control_node_2082_congruent inputs path left right next_left next_right :
 VM.find 2081 left = VM.find 2081 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2082 next_left = VM.find 2082 next_right.
Proof.
 intros  E2081 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2082 reference_control_expr_2082 reference_control_0_positions reference_control_0_safety reference_control_member_2082) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2082 reference_control_expr_2082 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2082 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2082 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2081.
 reflexivity.
Qed.
Lemma reference_control_ready_2083 old :
 reference_control_ready old reference_control_expr_2083.
Proof.
 unfold reference_control_expr_2083.
apply rc_binary.
Qed.
Lemma reference_control_member_2083 : List.In (2083,reference_control_expr_2083) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 200%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2083_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2083 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2083 reference_control_expr_2083 reference_control_0_positions reference_control_0_safety reference_control_member_2083) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2083 reference_control_expr_2083 inputs path old current result Position Safe Nonreg (reference_control_ready_2083 old ) Step).
Qed.
Theorem reference_control_node_2083_congruent inputs path left right next_left next_right :
 VM.find 1884 left = VM.find 1884 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2083 next_left = VM.find 2083 next_right.
Proof.
 intros  E1884 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2083 reference_control_expr_2083 reference_control_0_positions reference_control_0_safety reference_control_member_2083) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2083 reference_control_expr_2083 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2083 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2083 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1884.
 reflexivity.
Qed.
Lemma reference_control_ready_2084 old :
 reference_control_ready old reference_control_expr_2084.
Proof.
 unfold reference_control_expr_2084.
apply rc_binary.
Qed.
Lemma reference_control_member_2084 : List.In (2084,reference_control_expr_2084) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 201%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2084_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2084 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2084 reference_control_expr_2084 reference_control_0_positions reference_control_0_safety reference_control_member_2084) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2084 reference_control_expr_2084 inputs path old current result Position Safe Nonreg (reference_control_ready_2084 old ) Step).
Qed.
Theorem reference_control_node_2084_congruent inputs path left right next_left next_right :
 VM.find 2083 left = VM.find 2083 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2084 next_left = VM.find 2084 next_right.
Proof.
 intros  E2083 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2084 reference_control_expr_2084 reference_control_0_positions reference_control_0_safety reference_control_member_2084) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2084 reference_control_expr_2084 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2084 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2084 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2083.
 reflexivity.
Qed.
Lemma reference_control_ready_2085 old :
 reference_control_ready old reference_control_expr_2085.
Proof.
 unfold reference_control_expr_2085.
apply rc_unary.
Qed.
Lemma reference_control_member_2085 : List.In (2085,reference_control_expr_2085) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 202%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2085_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2085 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2085 reference_control_expr_2085 reference_control_0_positions reference_control_0_safety reference_control_member_2085) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2085 reference_control_expr_2085 inputs path old current result Position Safe Nonreg (reference_control_ready_2085 old ) Step).
Qed.
Theorem reference_control_node_2085_congruent inputs path left right next_left next_right :
 VM.find 1884 left = VM.find 1884 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2085 next_left = VM.find 2085 next_right.
Proof.
 intros  E1884 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2085 reference_control_expr_2085 reference_control_0_positions reference_control_0_safety reference_control_member_2085) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2085 reference_control_expr_2085 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2085 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2085 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1884.
 reflexivity.
Qed.
Lemma reference_control_ready_2086 old :
 reference_control_ready old reference_control_expr_2086.
Proof.
 unfold reference_control_expr_2086.
apply rc_unary.
Qed.
Lemma reference_control_member_2086 : List.In (2086,reference_control_expr_2086) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 203%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2086_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2086 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2086 reference_control_expr_2086 reference_control_0_positions reference_control_0_safety reference_control_member_2086) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2086 reference_control_expr_2086 inputs path old current result Position Safe Nonreg (reference_control_ready_2086 old ) Step).
Qed.
Theorem reference_control_node_2086_congruent inputs path left right next_left next_right :
 VM.find 2085 left = VM.find 2085 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2086 next_left = VM.find 2086 next_right.
Proof.
 intros  E2085 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2086 reference_control_expr_2086 reference_control_0_positions reference_control_0_safety reference_control_member_2086) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2086 reference_control_expr_2086 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2086 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2086 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2085.
 reflexivity.
Qed.
Lemma reference_control_ready_2087 old :
 reference_control_ready old reference_control_expr_2087.
Proof.
 unfold reference_control_expr_2087.
apply rc_binary.
Qed.
Lemma reference_control_member_2087 : List.In (2087,reference_control_expr_2087) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 204%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2087_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2087 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2087 reference_control_expr_2087 reference_control_0_positions reference_control_0_safety reference_control_member_2087) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2087 reference_control_expr_2087 inputs path old current result Position Safe Nonreg (reference_control_ready_2087 old ) Step).
Qed.
Theorem reference_control_node_2087_congruent inputs path left right next_left next_right :
 VM.find 1884 left = VM.find 1884 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2087 next_left = VM.find 2087 next_right.
Proof.
 intros  E1884 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2087 reference_control_expr_2087 reference_control_0_positions reference_control_0_safety reference_control_member_2087) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2087 reference_control_expr_2087 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2087 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2087 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1884.
 reflexivity.
Qed.
Lemma reference_control_ready_2088 old :
 reference_control_ready old reference_control_expr_2088.
Proof.
 unfold reference_control_expr_2088.
apply rc_binary.
Qed.
Lemma reference_control_member_2088 : List.In (2088,reference_control_expr_2088) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 205%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2088_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2088 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2088 reference_control_expr_2088 reference_control_0_positions reference_control_0_safety reference_control_member_2088) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2088 reference_control_expr_2088 inputs path old current result Position Safe Nonreg (reference_control_ready_2088 old ) Step).
Qed.
Theorem reference_control_node_2088_congruent inputs path left right next_left next_right :
 VM.find 2087 left = VM.find 2087 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2088 next_left = VM.find 2088 next_right.
Proof.
 intros  E2087 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2088 reference_control_expr_2088 reference_control_0_positions reference_control_0_safety reference_control_member_2088) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2088 reference_control_expr_2088 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2088 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2088 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2087.
 reflexivity.
Qed.
Lemma reference_control_ready_2089 old :
 reference_control_ready old reference_control_expr_2089.
Proof.
 unfold reference_control_expr_2089.
apply rc_unary.
Qed.
Lemma reference_control_member_2089 : List.In (2089,reference_control_expr_2089) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 206%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2089_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2089 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2089 reference_control_expr_2089 reference_control_0_positions reference_control_0_safety reference_control_member_2089) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2089 reference_control_expr_2089 inputs path old current result Position Safe Nonreg (reference_control_ready_2089 old ) Step).
Qed.
Theorem reference_control_node_2089_congruent inputs path left right next_left next_right :
 VM.find 1884 left = VM.find 1884 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2089 next_left = VM.find 2089 next_right.
Proof.
 intros  E1884 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2089 reference_control_expr_2089 reference_control_0_positions reference_control_0_safety reference_control_member_2089) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2089 reference_control_expr_2089 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2089 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2089 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1884.
 reflexivity.
Qed.
Lemma reference_control_ready_2090 old :
 reference_control_ready old reference_control_expr_2090.
Proof.
 unfold reference_control_expr_2090.
apply rc_unary.
Qed.
Lemma reference_control_member_2090 : List.In (2090,reference_control_expr_2090) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 207%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2090_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2090 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2090 reference_control_expr_2090 reference_control_0_positions reference_control_0_safety reference_control_member_2090) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2090 reference_control_expr_2090 inputs path old current result Position Safe Nonreg (reference_control_ready_2090 old ) Step).
Qed.
Theorem reference_control_node_2090_congruent inputs path left right next_left next_right :
 VM.find 2089 left = VM.find 2089 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2090 next_left = VM.find 2090 next_right.
Proof.
 intros  E2089 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2090 reference_control_expr_2090 reference_control_0_positions reference_control_0_safety reference_control_member_2090) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2090 reference_control_expr_2090 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2090 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2090 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2089.
 reflexivity.
Qed.
Lemma reference_control_ready_2091 old :
 reference_control_ready old reference_control_expr_2091.
Proof.
 unfold reference_control_expr_2091.
apply rc_binary.
Qed.
Lemma reference_control_member_2091 : List.In (2091,reference_control_expr_2091) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 208%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2091_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2091 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2091 reference_control_expr_2091 reference_control_0_positions reference_control_0_safety reference_control_member_2091) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2091 reference_control_expr_2091 inputs path old current result Position Safe Nonreg (reference_control_ready_2091 old ) Step).
Qed.
Theorem reference_control_node_2091_congruent inputs path left right next_left next_right :
 VM.find 1884 left = VM.find 1884 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2091 next_left = VM.find 2091 next_right.
Proof.
 intros  E1884 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2091 reference_control_expr_2091 reference_control_0_positions reference_control_0_safety reference_control_member_2091) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2091 reference_control_expr_2091 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2091 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2091 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1884.
 reflexivity.
Qed.
Lemma reference_control_ready_2092 old :
 reference_control_ready old reference_control_expr_2092.
Proof.
 unfold reference_control_expr_2092.
apply rc_binary.
Qed.
Lemma reference_control_member_2092 : List.In (2092,reference_control_expr_2092) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 209%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2092_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2092 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2092 reference_control_expr_2092 reference_control_0_positions reference_control_0_safety reference_control_member_2092) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2092 reference_control_expr_2092 inputs path old current result Position Safe Nonreg (reference_control_ready_2092 old ) Step).
Qed.
Theorem reference_control_node_2092_congruent inputs path left right next_left next_right :
 VM.find 2091 left = VM.find 2091 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2092 next_left = VM.find 2092 next_right.
Proof.
 intros  E2091 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2092 reference_control_expr_2092 reference_control_0_positions reference_control_0_safety reference_control_member_2092) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2092 reference_control_expr_2092 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2092 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2092 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2091.
 reflexivity.
Qed.
Lemma reference_control_ready_2093 old :
 reference_control_ready old reference_control_expr_2093.
Proof.
 unfold reference_control_expr_2093.
apply rc_unary.
Qed.
Lemma reference_control_member_2093 : List.In (2093,reference_control_expr_2093) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 210%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2093_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2093 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2093 reference_control_expr_2093 reference_control_0_positions reference_control_0_safety reference_control_member_2093) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2093 reference_control_expr_2093 inputs path old current result Position Safe Nonreg (reference_control_ready_2093 old ) Step).
Qed.
Theorem reference_control_node_2093_congruent inputs path left right next_left next_right :
 VM.find 1884 left = VM.find 1884 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2093 next_left = VM.find 2093 next_right.
Proof.
 intros  E1884 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2093 reference_control_expr_2093 reference_control_0_positions reference_control_0_safety reference_control_member_2093) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2093 reference_control_expr_2093 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2093 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2093 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1884.
 reflexivity.
Qed.
Lemma reference_control_ready_2094 old :
 reference_control_ready old reference_control_expr_2094.
Proof.
 unfold reference_control_expr_2094.
apply rc_unary.
Qed.
Lemma reference_control_member_2094 : List.In (2094,reference_control_expr_2094) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 211%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2094_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2094 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2094 reference_control_expr_2094 reference_control_0_positions reference_control_0_safety reference_control_member_2094) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2094 reference_control_expr_2094 inputs path old current result Position Safe Nonreg (reference_control_ready_2094 old ) Step).
Qed.
Theorem reference_control_node_2094_congruent inputs path left right next_left next_right :
 VM.find 2093 left = VM.find 2093 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2094 next_left = VM.find 2094 next_right.
Proof.
 intros  E2093 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2094 reference_control_expr_2094 reference_control_0_positions reference_control_0_safety reference_control_member_2094) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2094 reference_control_expr_2094 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2094 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2094 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2093.
 reflexivity.
Qed.
Lemma reference_control_ready_2095 old :
 reference_control_ready old reference_control_expr_2095.
Proof.
 unfold reference_control_expr_2095.
apply rc_binary.
Qed.
Lemma reference_control_member_2095 : List.In (2095,reference_control_expr_2095) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 212%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2095_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2095 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2095 reference_control_expr_2095 reference_control_0_positions reference_control_0_safety reference_control_member_2095) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2095 reference_control_expr_2095 inputs path old current result Position Safe Nonreg (reference_control_ready_2095 old ) Step).
Qed.
Theorem reference_control_node_2095_congruent inputs path left right next_left next_right :
 VM.find 1884 left = VM.find 1884 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2095 next_left = VM.find 2095 next_right.
Proof.
 intros  E1884 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2095 reference_control_expr_2095 reference_control_0_positions reference_control_0_safety reference_control_member_2095) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2095 reference_control_expr_2095 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2095 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2095 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1884.
 reflexivity.
Qed.
Lemma reference_control_ready_2096 old :
 reference_control_ready old reference_control_expr_2096.
Proof.
 unfold reference_control_expr_2096.
apply rc_binary.
Qed.
Lemma reference_control_member_2096 : List.In (2096,reference_control_expr_2096) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 213%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2096_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2096 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2096 reference_control_expr_2096 reference_control_0_positions reference_control_0_safety reference_control_member_2096) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2096 reference_control_expr_2096 inputs path old current result Position Safe Nonreg (reference_control_ready_2096 old ) Step).
Qed.
Theorem reference_control_node_2096_congruent inputs path left right next_left next_right :
 VM.find 2095 left = VM.find 2095 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2096 next_left = VM.find 2096 next_right.
Proof.
 intros  E2095 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2096 reference_control_expr_2096 reference_control_0_positions reference_control_0_safety reference_control_member_2096) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2096 reference_control_expr_2096 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2096 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2096 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2095.
 reflexivity.
Qed.
Lemma reference_control_ready_2097 old :
 reference_control_ready old reference_control_expr_2097.
Proof.
 unfold reference_control_expr_2097.
apply rc_unary.
Qed.
Lemma reference_control_member_2097 : List.In (2097,reference_control_expr_2097) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 214%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2097_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2097 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2097 reference_control_expr_2097 reference_control_0_positions reference_control_0_safety reference_control_member_2097) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2097 reference_control_expr_2097 inputs path old current result Position Safe Nonreg (reference_control_ready_2097 old ) Step).
Qed.
Theorem reference_control_node_2097_congruent inputs path left right next_left next_right :
 VM.find 1884 left = VM.find 1884 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2097 next_left = VM.find 2097 next_right.
Proof.
 intros  E1884 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2097 reference_control_expr_2097 reference_control_0_positions reference_control_0_safety reference_control_member_2097) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2097 reference_control_expr_2097 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2097 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2097 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1884.
 reflexivity.
Qed.
Lemma reference_control_ready_2098 old :
 reference_control_ready old reference_control_expr_2098.
Proof.
 unfold reference_control_expr_2098.
apply rc_unary.
Qed.
Lemma reference_control_member_2098 : List.In (2098,reference_control_expr_2098) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 215%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2098_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2098 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2098 reference_control_expr_2098 reference_control_0_positions reference_control_0_safety reference_control_member_2098) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2098 reference_control_expr_2098 inputs path old current result Position Safe Nonreg (reference_control_ready_2098 old ) Step).
Qed.
Theorem reference_control_node_2098_congruent inputs path left right next_left next_right :
 VM.find 2097 left = VM.find 2097 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2098 next_left = VM.find 2098 next_right.
Proof.
 intros  E2097 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2098 reference_control_expr_2098 reference_control_0_positions reference_control_0_safety reference_control_member_2098) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2098 reference_control_expr_2098 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2098 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2098 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2097.
 reflexivity.
Qed.
Lemma reference_control_ready_2099 old :
 (exists value ground, VM.find 2098 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2099.
Proof.
 intros H2098.
 destruct H2098 as [v2098 [G2098 [V2098 T2098]]].
 unfold reference_control_expr_2099.
apply rc_mux.
{ eapply rc_ref; [exact V2098|exists G2098; exact T2098].
}
{ apply rc_const.
}
Qed.
Lemma reference_control_member_2099 : List.In (2099,reference_control_expr_2099) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 216%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2099_ground inputs path old current result :
 (exists value ground, VM.find 2098 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2099 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2098 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2099 reference_control_expr_2099 reference_control_0_positions reference_control_0_safety reference_control_member_2099) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2099 reference_control_expr_2099 inputs path old current result Position Safe Nonreg (reference_control_ready_2099 old H2098) Step).
Qed.
Theorem reference_control_node_2099_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2098 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2096 left = VM.find 2096 right ->
 VM.find 2098 left = VM.find 2098 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2099 next_left = VM.find 2099 next_right.
Proof.
 intros H2098 E2096 E2098 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2099 reference_control_expr_2099 reference_control_0_positions reference_control_0_safety reference_control_member_2099) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2099 reference_control_expr_2099 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2099 left H2098)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2099 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2096.
 rewrite E2098.
 reflexivity.
Qed.
Lemma reference_control_ready_2100 old :
 (exists value ground, VM.find 2094 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2099 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2100.
Proof.
 intros H2094 H2099.
 destruct H2094 as [v2094 [G2094 [V2094 T2094]]].
 destruct H2099 as [v2099 [G2099 [V2099 T2099]]].
 unfold reference_control_expr_2100.
apply rc_mux.
{ eapply rc_ref; [exact V2094|exists G2094; exact T2094].
}
{ eapply rc_ref; [exact V2099|exists G2099; exact T2099].
}
Qed.
Lemma reference_control_member_2100 : List.In (2100,reference_control_expr_2100) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 217%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2100_ground inputs path old current result :
 (exists value ground, VM.find 2094 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2099 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2100 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2094 H2099 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2100 reference_control_expr_2100 reference_control_0_positions reference_control_0_safety reference_control_member_2100) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2100 reference_control_expr_2100 inputs path old current result Position Safe Nonreg (reference_control_ready_2100 old H2094 H2099) Step).
Qed.
Theorem reference_control_node_2100_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2094 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2099 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2092 left = VM.find 2092 right ->
 VM.find 2094 left = VM.find 2094 right ->
 VM.find 2099 left = VM.find 2099 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2100 next_left = VM.find 2100 next_right.
Proof.
 intros H2094 H2099 E2092 E2094 E2099 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2100 reference_control_expr_2100 reference_control_0_positions reference_control_0_safety reference_control_member_2100) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2100 reference_control_expr_2100 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2100 left H2094 H2099)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2100 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2092.
 rewrite E2094.
 rewrite E2099.
 reflexivity.
Qed.
Lemma reference_control_ready_2101 old :
 (exists value ground, VM.find 2090 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2100 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2101.
Proof.
 intros H2090 H2100.
 destruct H2090 as [v2090 [G2090 [V2090 T2090]]].
 destruct H2100 as [v2100 [G2100 [V2100 T2100]]].
 unfold reference_control_expr_2101.
apply rc_mux.
{ eapply rc_ref; [exact V2090|exists G2090; exact T2090].
}
{ eapply rc_ref; [exact V2100|exists G2100; exact T2100].
}
Qed.
Lemma reference_control_member_2101 : List.In (2101,reference_control_expr_2101) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 218%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2101_ground inputs path old current result :
 (exists value ground, VM.find 2090 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2100 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2101 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2090 H2100 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2101 reference_control_expr_2101 reference_control_0_positions reference_control_0_safety reference_control_member_2101) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2101 reference_control_expr_2101 inputs path old current result Position Safe Nonreg (reference_control_ready_2101 old H2090 H2100) Step).
Qed.
Theorem reference_control_node_2101_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2090 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2100 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2088 left = VM.find 2088 right ->
 VM.find 2090 left = VM.find 2090 right ->
 VM.find 2100 left = VM.find 2100 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2101 next_left = VM.find 2101 next_right.
Proof.
 intros H2090 H2100 E2088 E2090 E2100 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2101 reference_control_expr_2101 reference_control_0_positions reference_control_0_safety reference_control_member_2101) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2101 reference_control_expr_2101 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2101 left H2090 H2100)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2101 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2088.
 rewrite E2090.
 rewrite E2100.
 reflexivity.
Qed.
Lemma reference_control_ready_2102 old :
 (exists value ground, VM.find 2086 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2101 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2102.
Proof.
 intros H2086 H2101.
 destruct H2086 as [v2086 [G2086 [V2086 T2086]]].
 destruct H2101 as [v2101 [G2101 [V2101 T2101]]].
 unfold reference_control_expr_2102.
apply rc_mux.
{ eapply rc_ref; [exact V2086|exists G2086; exact T2086].
}
{ eapply rc_ref; [exact V2101|exists G2101; exact T2101].
}
Qed.
Lemma reference_control_member_2102 : List.In (2102,reference_control_expr_2102) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 219%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2102_ground inputs path old current result :
 (exists value ground, VM.find 2086 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2101 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2102 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2086 H2101 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2102 reference_control_expr_2102 reference_control_0_positions reference_control_0_safety reference_control_member_2102) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2102 reference_control_expr_2102 inputs path old current result Position Safe Nonreg (reference_control_ready_2102 old H2086 H2101) Step).
Qed.
Theorem reference_control_node_2102_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2086 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2101 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2084 left = VM.find 2084 right ->
 VM.find 2086 left = VM.find 2086 right ->
 VM.find 2101 left = VM.find 2101 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2102 next_left = VM.find 2102 next_right.
Proof.
 intros H2086 H2101 E2084 E2086 E2101 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2102 reference_control_expr_2102 reference_control_0_positions reference_control_0_safety reference_control_member_2102) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2102 reference_control_expr_2102 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2102 left H2086 H2101)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2102 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2084.
 rewrite E2086.
 rewrite E2101.
 reflexivity.
Qed.
Lemma reference_control_ready_2103 old :
 (exists value ground, VM.find 2082 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2102 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2103.
Proof.
 intros H2082 H2102.
 destruct H2082 as [v2082 [G2082 [V2082 T2082]]].
 destruct H2102 as [v2102 [G2102 [V2102 T2102]]].
 unfold reference_control_expr_2103.
apply rc_mux.
{ eapply rc_ref; [exact V2082|exists G2082; exact T2082].
}
{ eapply rc_ref; [exact V2102|exists G2102; exact T2102].
}
Qed.
Lemma reference_control_member_2103 : List.In (2103,reference_control_expr_2103) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 220%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2103_ground inputs path old current result :
 (exists value ground, VM.find 2082 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2102 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2103 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2082 H2102 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2103 reference_control_expr_2103 reference_control_0_positions reference_control_0_safety reference_control_member_2103) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2103 reference_control_expr_2103 inputs path old current result Position Safe Nonreg (reference_control_ready_2103 old H2082 H2102) Step).
Qed.
Theorem reference_control_node_2103_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2082 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2102 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2080 left = VM.find 2080 right ->
 VM.find 2082 left = VM.find 2082 right ->
 VM.find 2102 left = VM.find 2102 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2103 next_left = VM.find 2103 next_right.
Proof.
 intros H2082 H2102 E2080 E2082 E2102 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2103 reference_control_expr_2103 reference_control_0_positions reference_control_0_safety reference_control_member_2103) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2103 reference_control_expr_2103 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2103 left H2082 H2102)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2103 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2080.
 rewrite E2082.
 rewrite E2102.
 reflexivity.
Qed.
Lemma reference_control_ready_2104 old :
 (exists value ground, VM.find 2078 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2103 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2104.
Proof.
 intros H2078 H2103.
 destruct H2078 as [v2078 [G2078 [V2078 T2078]]].
 destruct H2103 as [v2103 [G2103 [V2103 T2103]]].
 unfold reference_control_expr_2104.
apply rc_mux.
{ eapply rc_ref; [exact V2078|exists G2078; exact T2078].
}
{ eapply rc_ref; [exact V2103|exists G2103; exact T2103].
}
Qed.
Lemma reference_control_member_2104 : List.In (2104,reference_control_expr_2104) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 221%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2104_ground inputs path old current result :
 (exists value ground, VM.find 2078 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2103 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2104 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2078 H2103 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2104 reference_control_expr_2104 reference_control_0_positions reference_control_0_safety reference_control_member_2104) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2104 reference_control_expr_2104 inputs path old current result Position Safe Nonreg (reference_control_ready_2104 old H2078 H2103) Step).
Qed.
Theorem reference_control_node_2104_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2078 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2103 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2076 left = VM.find 2076 right ->
 VM.find 2078 left = VM.find 2078 right ->
 VM.find 2103 left = VM.find 2103 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2104 next_left = VM.find 2104 next_right.
Proof.
 intros H2078 H2103 E2076 E2078 E2103 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2104 reference_control_expr_2104 reference_control_0_positions reference_control_0_safety reference_control_member_2104) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2104 reference_control_expr_2104 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2104 left H2078 H2103)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2104 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2076.
 rewrite E2078.
 rewrite E2103.
 reflexivity.
Qed.
Lemma reference_control_ready_2105 old :
 (exists value ground, VM.find 2074 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2104 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2105.
Proof.
 intros H2074 H2104.
 destruct H2074 as [v2074 [G2074 [V2074 T2074]]].
 destruct H2104 as [v2104 [G2104 [V2104 T2104]]].
 unfold reference_control_expr_2105.
apply rc_mux.
{ eapply rc_ref; [exact V2074|exists G2074; exact T2074].
}
{ eapply rc_ref; [exact V2104|exists G2104; exact T2104].
}
Qed.
Lemma reference_control_member_2105 : List.In (2105,reference_control_expr_2105) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 222%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2105_ground inputs path old current result :
 (exists value ground, VM.find 2074 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2104 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2105 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2074 H2104 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2105 reference_control_expr_2105 reference_control_0_positions reference_control_0_safety reference_control_member_2105) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2105 reference_control_expr_2105 inputs path old current result Position Safe Nonreg (reference_control_ready_2105 old H2074 H2104) Step).
Qed.
Theorem reference_control_node_2105_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2074 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2104 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2072 left = VM.find 2072 right ->
 VM.find 2074 left = VM.find 2074 right ->
 VM.find 2104 left = VM.find 2104 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2105 next_left = VM.find 2105 next_right.
Proof.
 intros H2074 H2104 E2072 E2074 E2104 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2105 reference_control_expr_2105 reference_control_0_positions reference_control_0_safety reference_control_member_2105) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2105 reference_control_expr_2105 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2105 left H2074 H2104)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2105 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2072.
 rewrite E2074.
 rewrite E2104.
 reflexivity.
Qed.
Lemma reference_control_ready_2106 old :
 (exists value ground, VM.find 2070 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2105 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2106.
Proof.
 intros H2070 H2105.
 destruct H2070 as [v2070 [G2070 [V2070 T2070]]].
 destruct H2105 as [v2105 [G2105 [V2105 T2105]]].
 unfold reference_control_expr_2106.
apply rc_mux.
{ eapply rc_ref; [exact V2070|exists G2070; exact T2070].
}
{ eapply rc_ref; [exact V2105|exists G2105; exact T2105].
}
Qed.
Lemma reference_control_member_2106 : List.In (2106,reference_control_expr_2106) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 223%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2106_ground inputs path old current result :
 (exists value ground, VM.find 2070 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2105 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2106 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2070 H2105 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2106 reference_control_expr_2106 reference_control_0_positions reference_control_0_safety reference_control_member_2106) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2106 reference_control_expr_2106 inputs path old current result Position Safe Nonreg (reference_control_ready_2106 old H2070 H2105) Step).
Qed.
Theorem reference_control_node_2106_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2070 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2105 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2068 left = VM.find 2068 right ->
 VM.find 2070 left = VM.find 2070 right ->
 VM.find 2105 left = VM.find 2105 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2106 next_left = VM.find 2106 next_right.
Proof.
 intros H2070 H2105 E2068 E2070 E2105 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2106 reference_control_expr_2106 reference_control_0_positions reference_control_0_safety reference_control_member_2106) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2106 reference_control_expr_2106 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2106 left H2070 H2105)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2106 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2068.
 rewrite E2070.
 rewrite E2105.
 reflexivity.
Qed.
Lemma reference_control_ready_2107 old :
 (exists value ground, VM.find 2066 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2106 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2107.
Proof.
 intros H2066 H2106.
 destruct H2066 as [v2066 [G2066 [V2066 T2066]]].
 destruct H2106 as [v2106 [G2106 [V2106 T2106]]].
 unfold reference_control_expr_2107.
apply rc_mux.
{ eapply rc_ref; [exact V2066|exists G2066; exact T2066].
}
{ eapply rc_ref; [exact V2106|exists G2106; exact T2106].
}
Qed.
Lemma reference_control_member_2107 : List.In (2107,reference_control_expr_2107) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 224%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2107_ground inputs path old current result :
 (exists value ground, VM.find 2066 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2106 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2107 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2066 H2106 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2107 reference_control_expr_2107 reference_control_0_positions reference_control_0_safety reference_control_member_2107) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2107 reference_control_expr_2107 inputs path old current result Position Safe Nonreg (reference_control_ready_2107 old H2066 H2106) Step).
Qed.
Theorem reference_control_node_2107_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2066 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2106 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2064 left = VM.find 2064 right ->
 VM.find 2066 left = VM.find 2066 right ->
 VM.find 2106 left = VM.find 2106 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2107 next_left = VM.find 2107 next_right.
Proof.
 intros H2066 H2106 E2064 E2066 E2106 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2107 reference_control_expr_2107 reference_control_0_positions reference_control_0_safety reference_control_member_2107) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2107 reference_control_expr_2107 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2107 left H2066 H2106)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2107 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2064.
 rewrite E2066.
 rewrite E2106.
 reflexivity.
Qed.
Lemma reference_control_ready_2108 old :
 (exists value ground, VM.find 2062 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2107 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2108.
Proof.
 intros H2062 H2107.
 destruct H2062 as [v2062 [G2062 [V2062 T2062]]].
 destruct H2107 as [v2107 [G2107 [V2107 T2107]]].
 unfold reference_control_expr_2108.
apply rc_mux.
{ eapply rc_ref; [exact V2062|exists G2062; exact T2062].
}
{ eapply rc_ref; [exact V2107|exists G2107; exact T2107].
}
Qed.
Lemma reference_control_member_2108 : List.In (2108,reference_control_expr_2108) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 225%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2108_ground inputs path old current result :
 (exists value ground, VM.find 2062 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2107 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2108 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2062 H2107 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2108 reference_control_expr_2108 reference_control_0_positions reference_control_0_safety reference_control_member_2108) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2108 reference_control_expr_2108 inputs path old current result Position Safe Nonreg (reference_control_ready_2108 old H2062 H2107) Step).
Qed.
Theorem reference_control_node_2108_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2062 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2107 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2059 left = VM.find 2059 right ->
 VM.find 2062 left = VM.find 2062 right ->
 VM.find 2107 left = VM.find 2107 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2108 next_left = VM.find 2108 next_right.
Proof.
 intros H2062 H2107 E2059 E2062 E2107 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2108 reference_control_expr_2108 reference_control_0_positions reference_control_0_safety reference_control_member_2108) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2108 reference_control_expr_2108 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2108 left H2062 H2107)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2108 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2059.
 rewrite E2062.
 rewrite E2107.
 reflexivity.
Qed.
Lemma reference_control_ready_2109 old :
 (exists value ground, VM.find 2057 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2108 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2109.
Proof.
 intros H2057 H2108.
 destruct H2057 as [v2057 [G2057 [V2057 T2057]]].
 destruct H2108 as [v2108 [G2108 [V2108 T2108]]].
 unfold reference_control_expr_2109.
apply rc_mux.
{ eapply rc_ref; [exact V2057|exists G2057; exact T2057].
}
{ eapply rc_ref; [exact V2108|exists G2108; exact T2108].
}
Qed.
Lemma reference_control_member_2109 : List.In (2109,reference_control_expr_2109) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 226%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2109_ground inputs path old current result :
 (exists value ground, VM.find 2057 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2108 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2109 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2057 H2108 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2109 reference_control_expr_2109 reference_control_0_positions reference_control_0_safety reference_control_member_2109) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2109 reference_control_expr_2109 inputs path old current result Position Safe Nonreg (reference_control_ready_2109 old H2057 H2108) Step).
Qed.
Theorem reference_control_node_2109_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2057 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2108 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2054 left = VM.find 2054 right ->
 VM.find 2057 left = VM.find 2057 right ->
 VM.find 2108 left = VM.find 2108 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2109 next_left = VM.find 2109 next_right.
Proof.
 intros H2057 H2108 E2054 E2057 E2108 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2109 reference_control_expr_2109 reference_control_0_positions reference_control_0_safety reference_control_member_2109) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2109 reference_control_expr_2109 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2109 left H2057 H2108)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2109 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2054.
 rewrite E2057.
 rewrite E2108.
 reflexivity.
Qed.
Lemma reference_control_ready_2110 old :
 (exists value ground, VM.find 2052 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2109 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2110.
Proof.
 intros H2052 H2109.
 destruct H2052 as [v2052 [G2052 [V2052 T2052]]].
 destruct H2109 as [v2109 [G2109 [V2109 T2109]]].
 unfold reference_control_expr_2110.
apply rc_mux.
{ eapply rc_ref; [exact V2052|exists G2052; exact T2052].
}
{ eapply rc_ref; [exact V2109|exists G2109; exact T2109].
}
Qed.
Lemma reference_control_member_2110 : List.In (2110,reference_control_expr_2110) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 227%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2110_ground inputs path old current result :
 (exists value ground, VM.find 2052 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2109 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2110 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2052 H2109 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2110 reference_control_expr_2110 reference_control_0_positions reference_control_0_safety reference_control_member_2110) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2110 reference_control_expr_2110 inputs path old current result Position Safe Nonreg (reference_control_ready_2110 old H2052 H2109) Step).
Qed.
Theorem reference_control_node_2110_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2052 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2109 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2049 left = VM.find 2049 right ->
 VM.find 2052 left = VM.find 2052 right ->
 VM.find 2109 left = VM.find 2109 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2110 next_left = VM.find 2110 next_right.
Proof.
 intros H2052 H2109 E2049 E2052 E2109 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2110 reference_control_expr_2110 reference_control_0_positions reference_control_0_safety reference_control_member_2110) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2110 reference_control_expr_2110 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2110 left H2052 H2109)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2110 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2049.
 rewrite E2052.
 rewrite E2109.
 reflexivity.
Qed.
Lemma reference_control_ready_2111 old :
 (exists value ground, VM.find 2047 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2110 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2111.
Proof.
 intros H2047 H2110.
 destruct H2047 as [v2047 [G2047 [V2047 T2047]]].
 destruct H2110 as [v2110 [G2110 [V2110 T2110]]].
 unfold reference_control_expr_2111.
apply rc_mux.
{ eapply rc_ref; [exact V2047|exists G2047; exact T2047].
}
{ eapply rc_ref; [exact V2110|exists G2110; exact T2110].
}
Qed.
Lemma reference_control_member_2111 : List.In (2111,reference_control_expr_2111) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 228%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2111_ground inputs path old current result :
 (exists value ground, VM.find 2047 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2110 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2111 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2047 H2110 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2111 reference_control_expr_2111 reference_control_0_positions reference_control_0_safety reference_control_member_2111) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2111 reference_control_expr_2111 inputs path old current result Position Safe Nonreg (reference_control_ready_2111 old H2047 H2110) Step).
Qed.
Theorem reference_control_node_2111_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2047 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2110 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2044 left = VM.find 2044 right ->
 VM.find 2047 left = VM.find 2047 right ->
 VM.find 2110 left = VM.find 2110 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2111 next_left = VM.find 2111 next_right.
Proof.
 intros H2047 H2110 E2044 E2047 E2110 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2111 reference_control_expr_2111 reference_control_0_positions reference_control_0_safety reference_control_member_2111) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2111 reference_control_expr_2111 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2111 left H2047 H2110)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2111 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2044.
 rewrite E2047.
 rewrite E2110.
 reflexivity.
Qed.
Lemma reference_control_ready_2112 old :
 (exists value ground, VM.find 2042 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2111 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2112.
Proof.
 intros H2042 H2111.
 destruct H2042 as [v2042 [G2042 [V2042 T2042]]].
 destruct H2111 as [v2111 [G2111 [V2111 T2111]]].
 unfold reference_control_expr_2112.
apply rc_mux.
{ eapply rc_ref; [exact V2042|exists G2042; exact T2042].
}
{ eapply rc_ref; [exact V2111|exists G2111; exact T2111].
}
Qed.
Lemma reference_control_member_2112 : List.In (2112,reference_control_expr_2112) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 229%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2112_ground inputs path old current result :
 (exists value ground, VM.find 2042 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2111 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2112 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2042 H2111 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2112 reference_control_expr_2112 reference_control_0_positions reference_control_0_safety reference_control_member_2112) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2112 reference_control_expr_2112 inputs path old current result Position Safe Nonreg (reference_control_ready_2112 old H2042 H2111) Step).
Qed.
Theorem reference_control_node_2112_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2042 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2111 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2039 left = VM.find 2039 right ->
 VM.find 2042 left = VM.find 2042 right ->
 VM.find 2111 left = VM.find 2111 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2112 next_left = VM.find 2112 next_right.
Proof.
 intros H2042 H2111 E2039 E2042 E2111 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2112 reference_control_expr_2112 reference_control_0_positions reference_control_0_safety reference_control_member_2112) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2112 reference_control_expr_2112 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2112 left H2042 H2111)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2112 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2039.
 rewrite E2042.
 rewrite E2111.
 reflexivity.
Qed.
Lemma reference_control_ready_2113 old :
 (exists value ground, VM.find 2037 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2112 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2113.
Proof.
 intros H2037 H2112.
 destruct H2037 as [v2037 [G2037 [V2037 T2037]]].
 destruct H2112 as [v2112 [G2112 [V2112 T2112]]].
 unfold reference_control_expr_2113.
apply rc_mux.
{ eapply rc_ref; [exact V2037|exists G2037; exact T2037].
}
{ eapply rc_ref; [exact V2112|exists G2112; exact T2112].
}
Qed.
Lemma reference_control_member_2113 : List.In (2113,reference_control_expr_2113) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 230%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2113_ground inputs path old current result :
 (exists value ground, VM.find 2037 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2112 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2113 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2037 H2112 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2113 reference_control_expr_2113 reference_control_0_positions reference_control_0_safety reference_control_member_2113) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2113 reference_control_expr_2113 inputs path old current result Position Safe Nonreg (reference_control_ready_2113 old H2037 H2112) Step).
Qed.
Theorem reference_control_node_2113_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2037 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2112 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2034 left = VM.find 2034 right ->
 VM.find 2037 left = VM.find 2037 right ->
 VM.find 2112 left = VM.find 2112 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2113 next_left = VM.find 2113 next_right.
Proof.
 intros H2037 H2112 E2034 E2037 E2112 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2113 reference_control_expr_2113 reference_control_0_positions reference_control_0_safety reference_control_member_2113) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2113 reference_control_expr_2113 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2113 left H2037 H2112)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2113 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2034.
 rewrite E2037.
 rewrite E2112.
 reflexivity.
Qed.
Lemma reference_control_ready_2114 old :
 (exists value ground, VM.find 2032 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2113 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2114.
Proof.
 intros H2032 H2113.
 destruct H2032 as [v2032 [G2032 [V2032 T2032]]].
 destruct H2113 as [v2113 [G2113 [V2113 T2113]]].
 unfold reference_control_expr_2114.
apply rc_mux.
{ eapply rc_ref; [exact V2032|exists G2032; exact T2032].
}
{ eapply rc_ref; [exact V2113|exists G2113; exact T2113].
}
Qed.
Lemma reference_control_member_2114 : List.In (2114,reference_control_expr_2114) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 231%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2114_ground inputs path old current result :
 (exists value ground, VM.find 2032 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2113 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2114 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2032 H2113 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2114 reference_control_expr_2114 reference_control_0_positions reference_control_0_safety reference_control_member_2114) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2114 reference_control_expr_2114 inputs path old current result Position Safe Nonreg (reference_control_ready_2114 old H2032 H2113) Step).
Qed.
Theorem reference_control_node_2114_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2032 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2113 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2029 left = VM.find 2029 right ->
 VM.find 2032 left = VM.find 2032 right ->
 VM.find 2113 left = VM.find 2113 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2114 next_left = VM.find 2114 next_right.
Proof.
 intros H2032 H2113 E2029 E2032 E2113 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2114 reference_control_expr_2114 reference_control_0_positions reference_control_0_safety reference_control_member_2114) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2114 reference_control_expr_2114 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2114 left H2032 H2113)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2114 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2029.
 rewrite E2032.
 rewrite E2113.
 reflexivity.
Qed.
Lemma reference_control_ready_2115 old :
 (exists value ground, VM.find 2027 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2114 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2115.
Proof.
 intros H2027 H2114.
 destruct H2027 as [v2027 [G2027 [V2027 T2027]]].
 destruct H2114 as [v2114 [G2114 [V2114 T2114]]].
 unfold reference_control_expr_2115.
apply rc_mux.
{ eapply rc_ref; [exact V2027|exists G2027; exact T2027].
}
{ eapply rc_ref; [exact V2114|exists G2114; exact T2114].
}
Qed.
Lemma reference_control_member_2115 : List.In (2115,reference_control_expr_2115) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 232%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2115_ground inputs path old current result :
 (exists value ground, VM.find 2027 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2114 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2115 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2027 H2114 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2115 reference_control_expr_2115 reference_control_0_positions reference_control_0_safety reference_control_member_2115) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2115 reference_control_expr_2115 inputs path old current result Position Safe Nonreg (reference_control_ready_2115 old H2027 H2114) Step).
Qed.
Theorem reference_control_node_2115_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2027 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2114 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2024 left = VM.find 2024 right ->
 VM.find 2027 left = VM.find 2027 right ->
 VM.find 2114 left = VM.find 2114 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2115 next_left = VM.find 2115 next_right.
Proof.
 intros H2027 H2114 E2024 E2027 E2114 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2115 reference_control_expr_2115 reference_control_0_positions reference_control_0_safety reference_control_member_2115) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2115 reference_control_expr_2115 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2115 left H2027 H2114)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2115 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2024.
 rewrite E2027.
 rewrite E2114.
 reflexivity.
Qed.
Lemma reference_control_ready_2116 old :
 (exists value ground, VM.find 2022 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2115 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2116.
Proof.
 intros H2022 H2115.
 destruct H2022 as [v2022 [G2022 [V2022 T2022]]].
 destruct H2115 as [v2115 [G2115 [V2115 T2115]]].
 unfold reference_control_expr_2116.
apply rc_mux.
{ eapply rc_ref; [exact V2022|exists G2022; exact T2022].
}
{ eapply rc_ref; [exact V2115|exists G2115; exact T2115].
}
Qed.
Lemma reference_control_member_2116 : List.In (2116,reference_control_expr_2116) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 233%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2116_ground inputs path old current result :
 (exists value ground, VM.find 2022 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2115 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2116 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2022 H2115 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2116 reference_control_expr_2116 reference_control_0_positions reference_control_0_safety reference_control_member_2116) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2116 reference_control_expr_2116 inputs path old current result Position Safe Nonreg (reference_control_ready_2116 old H2022 H2115) Step).
Qed.
Theorem reference_control_node_2116_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2022 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2115 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2019 left = VM.find 2019 right ->
 VM.find 2022 left = VM.find 2022 right ->
 VM.find 2115 left = VM.find 2115 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2116 next_left = VM.find 2116 next_right.
Proof.
 intros H2022 H2115 E2019 E2022 E2115 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2116 reference_control_expr_2116 reference_control_0_positions reference_control_0_safety reference_control_member_2116) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2116 reference_control_expr_2116 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2116 left H2022 H2115)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2116 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2019.
 rewrite E2022.
 rewrite E2115.
 reflexivity.
Qed.
Lemma reference_control_ready_2117 old :
 (exists value ground, VM.find 2017 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2116 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2117.
Proof.
 intros H2017 H2116.
 destruct H2017 as [v2017 [G2017 [V2017 T2017]]].
 destruct H2116 as [v2116 [G2116 [V2116 T2116]]].
 unfold reference_control_expr_2117.
apply rc_mux.
{ eapply rc_ref; [exact V2017|exists G2017; exact T2017].
}
{ eapply rc_ref; [exact V2116|exists G2116; exact T2116].
}
Qed.
Lemma reference_control_member_2117 : List.In (2117,reference_control_expr_2117) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 234%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2117_ground inputs path old current result :
 (exists value ground, VM.find 2017 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2116 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2117 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2017 H2116 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2117 reference_control_expr_2117 reference_control_0_positions reference_control_0_safety reference_control_member_2117) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2117 reference_control_expr_2117 inputs path old current result Position Safe Nonreg (reference_control_ready_2117 old H2017 H2116) Step).
Qed.
Theorem reference_control_node_2117_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2017 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2116 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2014 left = VM.find 2014 right ->
 VM.find 2017 left = VM.find 2017 right ->
 VM.find 2116 left = VM.find 2116 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2117 next_left = VM.find 2117 next_right.
Proof.
 intros H2017 H2116 E2014 E2017 E2116 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2117 reference_control_expr_2117 reference_control_0_positions reference_control_0_safety reference_control_member_2117) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2117 reference_control_expr_2117 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2117 left H2017 H2116)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2117 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2014.
 rewrite E2017.
 rewrite E2116.
 reflexivity.
Qed.
Lemma reference_control_ready_2118 old :
 (exists value ground, VM.find 2012 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2117 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2118.
Proof.
 intros H2012 H2117.
 destruct H2012 as [v2012 [G2012 [V2012 T2012]]].
 destruct H2117 as [v2117 [G2117 [V2117 T2117]]].
 unfold reference_control_expr_2118.
apply rc_mux.
{ eapply rc_ref; [exact V2012|exists G2012; exact T2012].
}
{ eapply rc_ref; [exact V2117|exists G2117; exact T2117].
}
Qed.
Lemma reference_control_member_2118 : List.In (2118,reference_control_expr_2118) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 235%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2118_ground inputs path old current result :
 (exists value ground, VM.find 2012 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2117 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2118 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2012 H2117 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2118 reference_control_expr_2118 reference_control_0_positions reference_control_0_safety reference_control_member_2118) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2118 reference_control_expr_2118 inputs path old current result Position Safe Nonreg (reference_control_ready_2118 old H2012 H2117) Step).
Qed.
Theorem reference_control_node_2118_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2012 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2117 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2010 left = VM.find 2010 right ->
 VM.find 2012 left = VM.find 2012 right ->
 VM.find 2117 left = VM.find 2117 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2118 next_left = VM.find 2118 next_right.
Proof.
 intros H2012 H2117 E2010 E2012 E2117 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2118 reference_control_expr_2118 reference_control_0_positions reference_control_0_safety reference_control_member_2118) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2118 reference_control_expr_2118 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2118 left H2012 H2117)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2118 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2010.
 rewrite E2012.
 rewrite E2117.
 reflexivity.
Qed.
Lemma reference_control_ready_2119 old :
 (exists value ground, VM.find 2008 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2118 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2119.
Proof.
 intros H2008 H2118.
 destruct H2008 as [v2008 [G2008 [V2008 T2008]]].
 destruct H2118 as [v2118 [G2118 [V2118 T2118]]].
 unfold reference_control_expr_2119.
apply rc_mux.
{ eapply rc_ref; [exact V2008|exists G2008; exact T2008].
}
{ eapply rc_ref; [exact V2118|exists G2118; exact T2118].
}
Qed.
Lemma reference_control_member_2119 : List.In (2119,reference_control_expr_2119) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 236%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2119_ground inputs path old current result :
 (exists value ground, VM.find 2008 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2118 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2119 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2008 H2118 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2119 reference_control_expr_2119 reference_control_0_positions reference_control_0_safety reference_control_member_2119) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2119 reference_control_expr_2119 inputs path old current result Position Safe Nonreg (reference_control_ready_2119 old H2008 H2118) Step).
Qed.
Theorem reference_control_node_2119_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2008 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2118 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2004 left = VM.find 2004 right ->
 VM.find 2008 left = VM.find 2008 right ->
 VM.find 2118 left = VM.find 2118 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2119 next_left = VM.find 2119 next_right.
Proof.
 intros H2008 H2118 E2004 E2008 E2118 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2119 reference_control_expr_2119 reference_control_0_positions reference_control_0_safety reference_control_member_2119) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2119 reference_control_expr_2119 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2119 left H2008 H2118)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2119 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2004.
 rewrite E2008.
 rewrite E2118.
 reflexivity.
Qed.
Lemma reference_control_ready_2120 old :
 (exists value ground, VM.find 2002 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2119 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2120.
Proof.
 intros H2002 H2119.
 destruct H2002 as [v2002 [G2002 [V2002 T2002]]].
 destruct H2119 as [v2119 [G2119 [V2119 T2119]]].
 unfold reference_control_expr_2120.
apply rc_mux.
{ eapply rc_ref; [exact V2002|exists G2002; exact T2002].
}
{ eapply rc_ref; [exact V2119|exists G2119; exact T2119].
}
Qed.
Lemma reference_control_member_2120 : List.In (2120,reference_control_expr_2120) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 237%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2120_ground inputs path old current result :
 (exists value ground, VM.find 2002 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2119 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2120 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2002 H2119 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2120 reference_control_expr_2120 reference_control_0_positions reference_control_0_safety reference_control_member_2120) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2120 reference_control_expr_2120 inputs path old current result Position Safe Nonreg (reference_control_ready_2120 old H2002 H2119) Step).
Qed.
Theorem reference_control_node_2120_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2002 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2119 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1998 left = VM.find 1998 right ->
 VM.find 2002 left = VM.find 2002 right ->
 VM.find 2119 left = VM.find 2119 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2120 next_left = VM.find 2120 next_right.
Proof.
 intros H2002 H2119 E1998 E2002 E2119 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2120 reference_control_expr_2120 reference_control_0_positions reference_control_0_safety reference_control_member_2120) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2120 reference_control_expr_2120 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2120 left H2002 H2119)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2120 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1998.
 rewrite E2002.
 rewrite E2119.
 reflexivity.
Qed.
Lemma reference_control_ready_2121 old :
 (exists value ground, VM.find 1996 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2120 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2121.
Proof.
 intros H1996 H2120.
 destruct H1996 as [v1996 [G1996 [V1996 T1996]]].
 destruct H2120 as [v2120 [G2120 [V2120 T2120]]].
 unfold reference_control_expr_2121.
apply rc_mux.
{ eapply rc_ref; [exact V1996|exists G1996; exact T1996].
}
{ eapply rc_ref; [exact V2120|exists G2120; exact T2120].
}
Qed.
Lemma reference_control_member_2121 : List.In (2121,reference_control_expr_2121) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 238%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2121_ground inputs path old current result :
 (exists value ground, VM.find 1996 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2120 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2121 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H1996 H2120 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2121 reference_control_expr_2121 reference_control_0_positions reference_control_0_safety reference_control_member_2121) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2121 reference_control_expr_2121 inputs path old current result Position Safe Nonreg (reference_control_ready_2121 old H1996 H2120) Step).
Qed.
Theorem reference_control_node_2121_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 1996 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2120 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1992 left = VM.find 1992 right ->
 VM.find 1996 left = VM.find 1996 right ->
 VM.find 2120 left = VM.find 2120 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2121 next_left = VM.find 2121 next_right.
Proof.
 intros H1996 H2120 E1992 E1996 E2120 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2121 reference_control_expr_2121 reference_control_0_positions reference_control_0_safety reference_control_member_2121) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2121 reference_control_expr_2121 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2121 left H1996 H2120)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2121 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1992.
 rewrite E1996.
 rewrite E2120.
 reflexivity.
Qed.
Lemma reference_control_ready_2122 old :
 (exists value ground, VM.find 1990 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2121 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2122.
Proof.
 intros H1990 H2121.
 destruct H1990 as [v1990 [G1990 [V1990 T1990]]].
 destruct H2121 as [v2121 [G2121 [V2121 T2121]]].
 unfold reference_control_expr_2122.
apply rc_mux.
{ eapply rc_ref; [exact V1990|exists G1990; exact T1990].
}
{ eapply rc_ref; [exact V2121|exists G2121; exact T2121].
}
Qed.
Lemma reference_control_member_2122 : List.In (2122,reference_control_expr_2122) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 239%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2122_ground inputs path old current result :
 (exists value ground, VM.find 1990 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2121 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2122 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H1990 H2121 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2122 reference_control_expr_2122 reference_control_0_positions reference_control_0_safety reference_control_member_2122) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2122 reference_control_expr_2122 inputs path old current result Position Safe Nonreg (reference_control_ready_2122 old H1990 H2121) Step).
Qed.
Theorem reference_control_node_2122_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 1990 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2121 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1986 left = VM.find 1986 right ->
 VM.find 1990 left = VM.find 1990 right ->
 VM.find 2121 left = VM.find 2121 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2122 next_left = VM.find 2122 next_right.
Proof.
 intros H1990 H2121 E1986 E1990 E2121 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2122 reference_control_expr_2122 reference_control_0_positions reference_control_0_safety reference_control_member_2122) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2122 reference_control_expr_2122 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2122 left H1990 H2121)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2122 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1986.
 rewrite E1990.
 rewrite E2121.
 reflexivity.
Qed.
Lemma reference_control_ready_2123 old :
 (exists value ground, VM.find 1984 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2122 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2123.
Proof.
 intros H1984 H2122.
 destruct H1984 as [v1984 [G1984 [V1984 T1984]]].
 destruct H2122 as [v2122 [G2122 [V2122 T2122]]].
 unfold reference_control_expr_2123.
apply rc_mux.
{ eapply rc_ref; [exact V1984|exists G1984; exact T1984].
}
{ eapply rc_ref; [exact V2122|exists G2122; exact T2122].
}
Qed.
Lemma reference_control_member_2123 : List.In (2123,reference_control_expr_2123) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 240%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2123_ground inputs path old current result :
 (exists value ground, VM.find 1984 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2122 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2123 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H1984 H2122 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2123 reference_control_expr_2123 reference_control_0_positions reference_control_0_safety reference_control_member_2123) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2123 reference_control_expr_2123 inputs path old current result Position Safe Nonreg (reference_control_ready_2123 old H1984 H2122) Step).
Qed.
Theorem reference_control_node_2123_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 1984 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2122 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1980 left = VM.find 1980 right ->
 VM.find 1984 left = VM.find 1984 right ->
 VM.find 2122 left = VM.find 2122 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2123 next_left = VM.find 2123 next_right.
Proof.
 intros H1984 H2122 E1980 E1984 E2122 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2123 reference_control_expr_2123 reference_control_0_positions reference_control_0_safety reference_control_member_2123) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2123 reference_control_expr_2123 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2123 left H1984 H2122)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2123 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1980.
 rewrite E1984.
 rewrite E2122.
 reflexivity.
Qed.
Lemma reference_control_ready_2124 old :
 (exists value ground, VM.find 1978 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2123 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2124.
Proof.
 intros H1978 H2123.
 destruct H1978 as [v1978 [G1978 [V1978 T1978]]].
 destruct H2123 as [v2123 [G2123 [V2123 T2123]]].
 unfold reference_control_expr_2124.
apply rc_mux.
{ eapply rc_ref; [exact V1978|exists G1978; exact T1978].
}
{ eapply rc_ref; [exact V2123|exists G2123; exact T2123].
}
Qed.
Lemma reference_control_member_2124 : List.In (2124,reference_control_expr_2124) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 241%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2124_ground inputs path old current result :
 (exists value ground, VM.find 1978 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2123 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2124 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H1978 H2123 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2124 reference_control_expr_2124 reference_control_0_positions reference_control_0_safety reference_control_member_2124) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2124 reference_control_expr_2124 inputs path old current result Position Safe Nonreg (reference_control_ready_2124 old H1978 H2123) Step).
Qed.
Theorem reference_control_node_2124_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 1978 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2123 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1974 left = VM.find 1974 right ->
 VM.find 1978 left = VM.find 1978 right ->
 VM.find 2123 left = VM.find 2123 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2124 next_left = VM.find 2124 next_right.
Proof.
 intros H1978 H2123 E1974 E1978 E2123 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2124 reference_control_expr_2124 reference_control_0_positions reference_control_0_safety reference_control_member_2124) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2124 reference_control_expr_2124 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2124 left H1978 H2123)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2124 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1974.
 rewrite E1978.
 rewrite E2123.
 reflexivity.
Qed.
Lemma reference_control_ready_2125 old :
 (exists value ground, VM.find 1972 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2124 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2125.
Proof.
 intros H1972 H2124.
 destruct H1972 as [v1972 [G1972 [V1972 T1972]]].
 destruct H2124 as [v2124 [G2124 [V2124 T2124]]].
 unfold reference_control_expr_2125.
apply rc_mux.
{ eapply rc_ref; [exact V1972|exists G1972; exact T1972].
}
{ eapply rc_ref; [exact V2124|exists G2124; exact T2124].
}
Qed.
Lemma reference_control_member_2125 : List.In (2125,reference_control_expr_2125) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 242%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2125_ground inputs path old current result :
 (exists value ground, VM.find 1972 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2124 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2125 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H1972 H2124 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2125 reference_control_expr_2125 reference_control_0_positions reference_control_0_safety reference_control_member_2125) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2125 reference_control_expr_2125 inputs path old current result Position Safe Nonreg (reference_control_ready_2125 old H1972 H2124) Step).
Qed.
Theorem reference_control_node_2125_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 1972 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2124 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1970 left = VM.find 1970 right ->
 VM.find 1972 left = VM.find 1972 right ->
 VM.find 2124 left = VM.find 2124 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2125 next_left = VM.find 2125 next_right.
Proof.
 intros H1972 H2124 E1970 E1972 E2124 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2125 reference_control_expr_2125 reference_control_0_positions reference_control_0_safety reference_control_member_2125) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2125 reference_control_expr_2125 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2125 left H1972 H2124)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2125 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1970.
 rewrite E1972.
 rewrite E2124.
 reflexivity.
Qed.
Lemma reference_control_ready_2126 old :
 (exists value ground, VM.find 1968 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2125 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2126.
Proof.
 intros H1968 H2125.
 destruct H1968 as [v1968 [G1968 [V1968 T1968]]].
 destruct H2125 as [v2125 [G2125 [V2125 T2125]]].
 unfold reference_control_expr_2126.
apply rc_mux.
{ eapply rc_ref; [exact V1968|exists G1968; exact T1968].
}
{ eapply rc_ref; [exact V2125|exists G2125; exact T2125].
}
Qed.
Lemma reference_control_member_2126 : List.In (2126,reference_control_expr_2126) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 243%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2126_ground inputs path old current result :
 (exists value ground, VM.find 1968 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2125 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2126 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H1968 H2125 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2126 reference_control_expr_2126 reference_control_0_positions reference_control_0_safety reference_control_member_2126) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2126 reference_control_expr_2126 inputs path old current result Position Safe Nonreg (reference_control_ready_2126 old H1968 H2125) Step).
Qed.
Theorem reference_control_node_2126_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 1968 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2125 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1966 left = VM.find 1966 right ->
 VM.find 1968 left = VM.find 1968 right ->
 VM.find 2125 left = VM.find 2125 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2126 next_left = VM.find 2126 next_right.
Proof.
 intros H1968 H2125 E1966 E1968 E2125 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2126 reference_control_expr_2126 reference_control_0_positions reference_control_0_safety reference_control_member_2126) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2126 reference_control_expr_2126 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2126 left H1968 H2125)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2126 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1966.
 rewrite E1968.
 rewrite E2125.
 reflexivity.
Qed.
Lemma reference_control_ready_2127 old :
 (exists value ground, VM.find 1964 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2126 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2127.
Proof.
 intros H1964 H2126.
 destruct H1964 as [v1964 [G1964 [V1964 T1964]]].
 destruct H2126 as [v2126 [G2126 [V2126 T2126]]].
 unfold reference_control_expr_2127.
apply rc_mux.
{ eapply rc_ref; [exact V1964|exists G1964; exact T1964].
}
{ eapply rc_ref; [exact V2126|exists G2126; exact T2126].
}
Qed.
Lemma reference_control_member_2127 : List.In (2127,reference_control_expr_2127) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 244%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2127_ground inputs path old current result :
 (exists value ground, VM.find 1964 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2126 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2127 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H1964 H2126 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2127 reference_control_expr_2127 reference_control_0_positions reference_control_0_safety reference_control_member_2127) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2127 reference_control_expr_2127 inputs path old current result Position Safe Nonreg (reference_control_ready_2127 old H1964 H2126) Step).
Qed.
Theorem reference_control_node_2127_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 1964 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2126 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1962 left = VM.find 1962 right ->
 VM.find 1964 left = VM.find 1964 right ->
 VM.find 2126 left = VM.find 2126 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2127 next_left = VM.find 2127 next_right.
Proof.
 intros H1964 H2126 E1962 E1964 E2126 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2127 reference_control_expr_2127 reference_control_0_positions reference_control_0_safety reference_control_member_2127) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2127 reference_control_expr_2127 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2127 left H1964 H2126)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2127 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1962.
 rewrite E1964.
 rewrite E2126.
 reflexivity.
Qed.
Lemma reference_control_ready_2128 old :
 (exists value ground, VM.find 1960 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2127 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2128.
Proof.
 intros H1960 H2127.
 destruct H1960 as [v1960 [G1960 [V1960 T1960]]].
 destruct H2127 as [v2127 [G2127 [V2127 T2127]]].
 unfold reference_control_expr_2128.
apply rc_mux.
{ eapply rc_ref; [exact V1960|exists G1960; exact T1960].
}
{ eapply rc_ref; [exact V2127|exists G2127; exact T2127].
}
Qed.
Lemma reference_control_member_2128 : List.In (2128,reference_control_expr_2128) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 245%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2128_ground inputs path old current result :
 (exists value ground, VM.find 1960 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2127 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2128 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H1960 H2127 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2128 reference_control_expr_2128 reference_control_0_positions reference_control_0_safety reference_control_member_2128) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2128 reference_control_expr_2128 inputs path old current result Position Safe Nonreg (reference_control_ready_2128 old H1960 H2127) Step).
Qed.
Theorem reference_control_node_2128_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 1960 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2127 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1958 left = VM.find 1958 right ->
 VM.find 1960 left = VM.find 1960 right ->
 VM.find 2127 left = VM.find 2127 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2128 next_left = VM.find 2128 next_right.
Proof.
 intros H1960 H2127 E1958 E1960 E2127 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2128 reference_control_expr_2128 reference_control_0_positions reference_control_0_safety reference_control_member_2128) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2128 reference_control_expr_2128 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2128 left H1960 H2127)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2128 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1958.
 rewrite E1960.
 rewrite E2127.
 reflexivity.
Qed.
Lemma reference_control_ready_2129 old :
 (exists value ground, VM.find 1956 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2128 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2129.
Proof.
 intros H1956 H2128.
 destruct H1956 as [v1956 [G1956 [V1956 T1956]]].
 destruct H2128 as [v2128 [G2128 [V2128 T2128]]].
 unfold reference_control_expr_2129.
apply rc_mux.
{ eapply rc_ref; [exact V1956|exists G1956; exact T1956].
}
{ eapply rc_ref; [exact V2128|exists G2128; exact T2128].
}
Qed.
Lemma reference_control_member_2129 : List.In (2129,reference_control_expr_2129) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 246%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2129_ground inputs path old current result :
 (exists value ground, VM.find 1956 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2128 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2129 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H1956 H2128 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2129 reference_control_expr_2129 reference_control_0_positions reference_control_0_safety reference_control_member_2129) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2129 reference_control_expr_2129 inputs path old current result Position Safe Nonreg (reference_control_ready_2129 old H1956 H2128) Step).
Qed.
Theorem reference_control_node_2129_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 1956 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2128 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1886 left = VM.find 1886 right ->
 VM.find 1956 left = VM.find 1956 right ->
 VM.find 2128 left = VM.find 2128 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2129 next_left = VM.find 2129 next_right.
Proof.
 intros H1956 H2128 E1886 E1956 E2128 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2129 reference_control_expr_2129 reference_control_0_positions reference_control_0_safety reference_control_member_2129) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2129 reference_control_expr_2129 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2129 left H1956 H2128)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2129 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1886.
 rewrite E1956.
 rewrite E2128.
 reflexivity.
Qed.
Lemma reference_control_ready_2130 old :
 (exists value ground, VM.find 1954 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2129 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2130.
Proof.
 intros H1954 H2129.
 destruct H1954 as [v1954 [G1954 [V1954 T1954]]].
 destruct H2129 as [v2129 [G2129 [V2129 T2129]]].
 unfold reference_control_expr_2130.
apply rc_mux.
{ eapply rc_ref; [exact V1954|exists G1954; exact T1954].
}
{ eapply rc_ref; [exact V2129|exists G2129; exact T2129].
}
Qed.
Lemma reference_control_member_2130 : List.In (2130,reference_control_expr_2130) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 247%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2130_ground inputs path old current result :
 (exists value ground, VM.find 1954 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2129 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2130 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H1954 H2129 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2130 reference_control_expr_2130 reference_control_0_positions reference_control_0_safety reference_control_member_2130) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2130 reference_control_expr_2130 inputs path old current result Position Safe Nonreg (reference_control_ready_2130 old H1954 H2129) Step).
Qed.
Theorem reference_control_node_2130_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 1954 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2129 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1951 left = VM.find 1951 right ->
 VM.find 1954 left = VM.find 1954 right ->
 VM.find 2129 left = VM.find 2129 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2130 next_left = VM.find 2130 next_right.
Proof.
 intros H1954 H2129 E1951 E1954 E2129 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2130 reference_control_expr_2130 reference_control_0_positions reference_control_0_safety reference_control_member_2130) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2130 reference_control_expr_2130 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2130 left H1954 H2129)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2130 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1951.
 rewrite E1954.
 rewrite E2129.
 reflexivity.
Qed.
Lemma reference_control_ready_2131 old :
 (exists value ground, VM.find 1949 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2130 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2131.
Proof.
 intros H1949 H2130.
 destruct H1949 as [v1949 [G1949 [V1949 T1949]]].
 destruct H2130 as [v2130 [G2130 [V2130 T2130]]].
 unfold reference_control_expr_2131.
apply rc_mux.
{ eapply rc_ref; [exact V1949|exists G1949; exact T1949].
}
{ eapply rc_ref; [exact V2130|exists G2130; exact T2130].
}
Qed.
Lemma reference_control_member_2131 : List.In (2131,reference_control_expr_2131) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 248%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2131_ground inputs path old current result :
 (exists value ground, VM.find 1949 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2130 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2131 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H1949 H2130 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2131 reference_control_expr_2131 reference_control_0_positions reference_control_0_safety reference_control_member_2131) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2131 reference_control_expr_2131 inputs path old current result Position Safe Nonreg (reference_control_ready_2131 old H1949 H2130) Step).
Qed.
Theorem reference_control_node_2131_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 1949 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2130 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1946 left = VM.find 1946 right ->
 VM.find 1949 left = VM.find 1949 right ->
 VM.find 2130 left = VM.find 2130 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2131 next_left = VM.find 2131 next_right.
Proof.
 intros H1949 H2130 E1946 E1949 E2130 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2131 reference_control_expr_2131 reference_control_0_positions reference_control_0_safety reference_control_member_2131) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2131 reference_control_expr_2131 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2131 left H1949 H2130)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2131 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1946.
 rewrite E1949.
 rewrite E2130.
 reflexivity.
Qed.
Lemma reference_control_ready_2132 old :
 (exists value ground, VM.find 1944 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2131 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2132.
Proof.
 intros H1944 H2131.
 destruct H1944 as [v1944 [G1944 [V1944 T1944]]].
 destruct H2131 as [v2131 [G2131 [V2131 T2131]]].
 unfold reference_control_expr_2132.
apply rc_mux.
{ eapply rc_ref; [exact V1944|exists G1944; exact T1944].
}
{ eapply rc_ref; [exact V2131|exists G2131; exact T2131].
}
Qed.
Lemma reference_control_member_2132 : List.In (2132,reference_control_expr_2132) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 249%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2132_ground inputs path old current result :
 (exists value ground, VM.find 1944 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2131 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2132 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H1944 H2131 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2132 reference_control_expr_2132 reference_control_0_positions reference_control_0_safety reference_control_member_2132) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2132 reference_control_expr_2132 inputs path old current result Position Safe Nonreg (reference_control_ready_2132 old H1944 H2131) Step).
Qed.
Theorem reference_control_node_2132_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 1944 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2131 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1941 left = VM.find 1941 right ->
 VM.find 1944 left = VM.find 1944 right ->
 VM.find 2131 left = VM.find 2131 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2132 next_left = VM.find 2132 next_right.
Proof.
 intros H1944 H2131 E1941 E1944 E2131 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2132 reference_control_expr_2132 reference_control_0_positions reference_control_0_safety reference_control_member_2132) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2132 reference_control_expr_2132 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2132 left H1944 H2131)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2132 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1941.
 rewrite E1944.
 rewrite E2131.
 reflexivity.
Qed.
Lemma reference_control_ready_2133 old :
 (exists value ground, VM.find 1939 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2132 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2133.
Proof.
 intros H1939 H2132.
 destruct H1939 as [v1939 [G1939 [V1939 T1939]]].
 destruct H2132 as [v2132 [G2132 [V2132 T2132]]].
 unfold reference_control_expr_2133.
apply rc_mux.
{ eapply rc_ref; [exact V1939|exists G1939; exact T1939].
}
{ eapply rc_ref; [exact V2132|exists G2132; exact T2132].
}
Qed.
Lemma reference_control_member_2133 : List.In (2133,reference_control_expr_2133) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 250%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2133_ground inputs path old current result :
 (exists value ground, VM.find 1939 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2132 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2133 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H1939 H2132 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2133 reference_control_expr_2133 reference_control_0_positions reference_control_0_safety reference_control_member_2133) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2133 reference_control_expr_2133 inputs path old current result Position Safe Nonreg (reference_control_ready_2133 old H1939 H2132) Step).
Qed.
Theorem reference_control_node_2133_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 1939 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2132 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1937 left = VM.find 1937 right ->
 VM.find 1939 left = VM.find 1939 right ->
 VM.find 2132 left = VM.find 2132 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2133 next_left = VM.find 2133 next_right.
Proof.
 intros H1939 H2132 E1937 E1939 E2132 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2133 reference_control_expr_2133 reference_control_0_positions reference_control_0_safety reference_control_member_2133) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2133 reference_control_expr_2133 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2133 left H1939 H2132)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2133 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1937.
 rewrite E1939.
 rewrite E2132.
 reflexivity.
Qed.
Lemma reference_control_ready_2134 old :
 (exists value ground, VM.find 1935 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2133 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2134.
Proof.
 intros H1935 H2133.
 destruct H1935 as [v1935 [G1935 [V1935 T1935]]].
 destruct H2133 as [v2133 [G2133 [V2133 T2133]]].
 unfold reference_control_expr_2134.
apply rc_mux.
{ eapply rc_ref; [exact V1935|exists G1935; exact T1935].
}
{ eapply rc_ref; [exact V2133|exists G2133; exact T2133].
}
Qed.
Lemma reference_control_member_2134 : List.In (2134,reference_control_expr_2134) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 251%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2134_ground inputs path old current result :
 (exists value ground, VM.find 1935 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2133 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2134 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H1935 H2133 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2134 reference_control_expr_2134 reference_control_0_positions reference_control_0_safety reference_control_member_2134) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2134 reference_control_expr_2134 inputs path old current result Position Safe Nonreg (reference_control_ready_2134 old H1935 H2133) Step).
Qed.
Theorem reference_control_node_2134_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 1935 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2133 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1933 left = VM.find 1933 right ->
 VM.find 1935 left = VM.find 1935 right ->
 VM.find 2133 left = VM.find 2133 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2134 next_left = VM.find 2134 next_right.
Proof.
 intros H1935 H2133 E1933 E1935 E2133 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2134 reference_control_expr_2134 reference_control_0_positions reference_control_0_safety reference_control_member_2134) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2134 reference_control_expr_2134 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2134 left H1935 H2133)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2134 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1933.
 rewrite E1935.
 rewrite E2133.
 reflexivity.
Qed.
Lemma reference_control_ready_2135 old :
 (exists value ground, VM.find 1931 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2134 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2135.
Proof.
 intros H1931 H2134.
 destruct H1931 as [v1931 [G1931 [V1931 T1931]]].
 destruct H2134 as [v2134 [G2134 [V2134 T2134]]].
 unfold reference_control_expr_2135.
apply rc_mux.
{ eapply rc_ref; [exact V1931|exists G1931; exact T1931].
}
{ eapply rc_ref; [exact V2134|exists G2134; exact T2134].
}
Qed.
Lemma reference_control_member_2135 : List.In (2135,reference_control_expr_2135) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 252%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2135_ground inputs path old current result :
 (exists value ground, VM.find 1931 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2134 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2135 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H1931 H2134 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2135 reference_control_expr_2135 reference_control_0_positions reference_control_0_safety reference_control_member_2135) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2135 reference_control_expr_2135 inputs path old current result Position Safe Nonreg (reference_control_ready_2135 old H1931 H2134) Step).
Qed.
Theorem reference_control_node_2135_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 1931 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2134 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1929 left = VM.find 1929 right ->
 VM.find 1931 left = VM.find 1931 right ->
 VM.find 2134 left = VM.find 2134 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2135 next_left = VM.find 2135 next_right.
Proof.
 intros H1931 H2134 E1929 E1931 E2134 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2135 reference_control_expr_2135 reference_control_0_positions reference_control_0_safety reference_control_member_2135) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2135 reference_control_expr_2135 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2135 left H1931 H2134)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2135 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1929.
 rewrite E1931.
 rewrite E2134.
 reflexivity.
Qed.
Lemma reference_control_ready_2136 old :
 (exists value ground, VM.find 1927 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2135 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2136.
Proof.
 intros H1927 H2135.
 destruct H1927 as [v1927 [G1927 [V1927 T1927]]].
 destruct H2135 as [v2135 [G2135 [V2135 T2135]]].
 unfold reference_control_expr_2136.
apply rc_mux.
{ eapply rc_ref; [exact V1927|exists G1927; exact T1927].
}
{ eapply rc_ref; [exact V2135|exists G2135; exact T2135].
}
Qed.
Lemma reference_control_member_2136 : List.In (2136,reference_control_expr_2136) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 253%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2136_ground inputs path old current result :
 (exists value ground, VM.find 1927 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2135 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2136 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H1927 H2135 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2136 reference_control_expr_2136 reference_control_0_positions reference_control_0_safety reference_control_member_2136) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2136 reference_control_expr_2136 inputs path old current result Position Safe Nonreg (reference_control_ready_2136 old H1927 H2135) Step).
Qed.
Theorem reference_control_node_2136_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 1927 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2135 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1924 left = VM.find 1924 right ->
 VM.find 1927 left = VM.find 1927 right ->
 VM.find 2135 left = VM.find 2135 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2136 next_left = VM.find 2136 next_right.
Proof.
 intros H1927 H2135 E1924 E1927 E2135 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2136 reference_control_expr_2136 reference_control_0_positions reference_control_0_safety reference_control_member_2136) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2136 reference_control_expr_2136 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2136 left H1927 H2135)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2136 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1924.
 rewrite E1927.
 rewrite E2135.
 reflexivity.
Qed.
Lemma reference_control_ready_2137 old :
 (exists value ground, VM.find 1922 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2136 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2137.
Proof.
 intros H1922 H2136.
 destruct H1922 as [v1922 [G1922 [V1922 T1922]]].
 destruct H2136 as [v2136 [G2136 [V2136 T2136]]].
 unfold reference_control_expr_2137.
apply rc_mux.
{ eapply rc_ref; [exact V1922|exists G1922; exact T1922].
}
{ eapply rc_ref; [exact V2136|exists G2136; exact T2136].
}
Qed.
Lemma reference_control_member_2137 : List.In (2137,reference_control_expr_2137) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 254%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2137_ground inputs path old current result :
 (exists value ground, VM.find 1922 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2136 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2137 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H1922 H2136 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2137 reference_control_expr_2137 reference_control_0_positions reference_control_0_safety reference_control_member_2137) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2137 reference_control_expr_2137 inputs path old current result Position Safe Nonreg (reference_control_ready_2137 old H1922 H2136) Step).
Qed.
Theorem reference_control_node_2137_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 1922 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2136 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1919 left = VM.find 1919 right ->
 VM.find 1922 left = VM.find 1922 right ->
 VM.find 2136 left = VM.find 2136 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2137 next_left = VM.find 2137 next_right.
Proof.
 intros H1922 H2136 E1919 E1922 E2136 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2137 reference_control_expr_2137 reference_control_0_positions reference_control_0_safety reference_control_member_2137) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2137 reference_control_expr_2137 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2137 left H1922 H2136)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2137 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1919.
 rewrite E1922.
 rewrite E2136.
 reflexivity.
Qed.
Lemma reference_control_ready_2138 old :
 (exists value ground, VM.find 1917 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2137 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2138.
Proof.
 intros H1917 H2137.
 destruct H1917 as [v1917 [G1917 [V1917 T1917]]].
 destruct H2137 as [v2137 [G2137 [V2137 T2137]]].
 unfold reference_control_expr_2138.
apply rc_mux.
{ eapply rc_ref; [exact V1917|exists G1917; exact T1917].
}
{ eapply rc_ref; [exact V2137|exists G2137; exact T2137].
}
Qed.
Lemma reference_control_member_2138 : List.In (2138,reference_control_expr_2138) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 255%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2138_ground inputs path old current result :
 (exists value ground, VM.find 1917 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2137 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2138 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H1917 H2137 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2138 reference_control_expr_2138 reference_control_0_positions reference_control_0_safety reference_control_member_2138) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2138 reference_control_expr_2138 inputs path old current result Position Safe Nonreg (reference_control_ready_2138 old H1917 H2137) Step).
Qed.
Theorem reference_control_node_2138_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 1917 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2137 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1914 left = VM.find 1914 right ->
 VM.find 1917 left = VM.find 1917 right ->
 VM.find 2137 left = VM.find 2137 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2138 next_left = VM.find 2138 next_right.
Proof.
 intros H1917 H2137 E1914 E1917 E2137 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2138 reference_control_expr_2138 reference_control_0_positions reference_control_0_safety reference_control_member_2138) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2138 reference_control_expr_2138 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2138 left H1917 H2137)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2138 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1914.
 rewrite E1917.
 rewrite E2137.
 reflexivity.
Qed.
Lemma reference_control_ready_2139 old :
 (exists value ground, VM.find 1912 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2138 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2139.
Proof.
 intros H1912 H2138.
 destruct H1912 as [v1912 [G1912 [V1912 T1912]]].
 destruct H2138 as [v2138 [G2138 [V2138 T2138]]].
 unfold reference_control_expr_2139.
apply rc_mux.
{ eapply rc_ref; [exact V1912|exists G1912; exact T1912].
}
{ eapply rc_ref; [exact V2138|exists G2138; exact T2138].
}
Qed.
Lemma reference_control_member_2139 : List.In (2139,reference_control_expr_2139) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 256%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2139_ground inputs path old current result :
 (exists value ground, VM.find 1912 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2138 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2139 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H1912 H2138 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2139 reference_control_expr_2139 reference_control_0_positions reference_control_0_safety reference_control_member_2139) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2139 reference_control_expr_2139 inputs path old current result Position Safe Nonreg (reference_control_ready_2139 old H1912 H2138) Step).
Qed.
Theorem reference_control_node_2139_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 1912 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2138 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1909 left = VM.find 1909 right ->
 VM.find 1912 left = VM.find 1912 right ->
 VM.find 2138 left = VM.find 2138 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2139 next_left = VM.find 2139 next_right.
Proof.
 intros H1912 H2138 E1909 E1912 E2138 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2139 reference_control_expr_2139 reference_control_0_positions reference_control_0_safety reference_control_member_2139) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2139 reference_control_expr_2139 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2139 left H1912 H2138)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2139 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1909.
 rewrite E1912.
 rewrite E2138.
 reflexivity.
Qed.
Lemma reference_control_ready_2140 old :
 (exists value ground, VM.find 1907 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2139 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2140.
Proof.
 intros H1907 H2139.
 destruct H1907 as [v1907 [G1907 [V1907 T1907]]].
 destruct H2139 as [v2139 [G2139 [V2139 T2139]]].
 unfold reference_control_expr_2140.
apply rc_mux.
{ eapply rc_ref; [exact V1907|exists G1907; exact T1907].
}
{ eapply rc_ref; [exact V2139|exists G2139; exact T2139].
}
Qed.
Lemma reference_control_member_2140 : List.In (2140,reference_control_expr_2140) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 257%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2140_ground inputs path old current result :
 (exists value ground, VM.find 1907 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2139 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2140 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H1907 H2139 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2140 reference_control_expr_2140 reference_control_0_positions reference_control_0_safety reference_control_member_2140) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2140 reference_control_expr_2140 inputs path old current result Position Safe Nonreg (reference_control_ready_2140 old H1907 H2139) Step).
Qed.
Theorem reference_control_node_2140_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 1907 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2139 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1904 left = VM.find 1904 right ->
 VM.find 1907 left = VM.find 1907 right ->
 VM.find 2139 left = VM.find 2139 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2140 next_left = VM.find 2140 next_right.
Proof.
 intros H1907 H2139 E1904 E1907 E2139 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2140 reference_control_expr_2140 reference_control_0_positions reference_control_0_safety reference_control_member_2140) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2140 reference_control_expr_2140 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2140 left H1907 H2139)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2140 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1904.
 rewrite E1907.
 rewrite E2139.
 reflexivity.
Qed.
Lemma reference_control_ready_2141 old :
 (exists value ground, VM.find 1902 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2140 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2141.
Proof.
 intros H1902 H2140.
 destruct H1902 as [v1902 [G1902 [V1902 T1902]]].
 destruct H2140 as [v2140 [G2140 [V2140 T2140]]].
 unfold reference_control_expr_2141.
apply rc_mux.
{ eapply rc_ref; [exact V1902|exists G1902; exact T1902].
}
{ eapply rc_ref; [exact V2140|exists G2140; exact T2140].
}
Qed.
Lemma reference_control_member_2141 : List.In (2141,reference_control_expr_2141) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 258%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2141_ground inputs path old current result :
 (exists value ground, VM.find 1902 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2140 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2141 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H1902 H2140 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2141 reference_control_expr_2141 reference_control_0_positions reference_control_0_safety reference_control_member_2141) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2141 reference_control_expr_2141 inputs path old current result Position Safe Nonreg (reference_control_ready_2141 old H1902 H2140) Step).
Qed.
Theorem reference_control_node_2141_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 1902 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2140 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1899 left = VM.find 1899 right ->
 VM.find 1902 left = VM.find 1902 right ->
 VM.find 2140 left = VM.find 2140 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2141 next_left = VM.find 2141 next_right.
Proof.
 intros H1902 H2140 E1899 E1902 E2140 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2141 reference_control_expr_2141 reference_control_0_positions reference_control_0_safety reference_control_member_2141) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2141 reference_control_expr_2141 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2141 left H1902 H2140)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2141 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1899.
 rewrite E1902.
 rewrite E2140.
 reflexivity.
Qed.
Lemma reference_control_ready_2142 old :
 (exists value ground, VM.find 1897 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2141 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2142.
Proof.
 intros H1897 H2141.
 destruct H1897 as [v1897 [G1897 [V1897 T1897]]].
 destruct H2141 as [v2141 [G2141 [V2141 T2141]]].
 unfold reference_control_expr_2142.
apply rc_mux.
{ eapply rc_ref; [exact V1897|exists G1897; exact T1897].
}
{ eapply rc_ref; [exact V2141|exists G2141; exact T2141].
}
Qed.
Lemma reference_control_member_2142 : List.In (2142,reference_control_expr_2142) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 259%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2142_ground inputs path old current result :
 (exists value ground, VM.find 1897 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2141 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2142 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H1897 H2141 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2142 reference_control_expr_2142 reference_control_0_positions reference_control_0_safety reference_control_member_2142) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2142 reference_control_expr_2142 inputs path old current result Position Safe Nonreg (reference_control_ready_2142 old H1897 H2141) Step).
Qed.
Theorem reference_control_node_2142_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 1897 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2141 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1894 left = VM.find 1894 right ->
 VM.find 1897 left = VM.find 1897 right ->
 VM.find 2141 left = VM.find 2141 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2142 next_left = VM.find 2142 next_right.
Proof.
 intros H1897 H2141 E1894 E1897 E2141 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2142 reference_control_expr_2142 reference_control_0_positions reference_control_0_safety reference_control_member_2142) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2142 reference_control_expr_2142 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2142 left H1897 H2141)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2142 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1894.
 rewrite E1897.
 rewrite E2141.
 reflexivity.
Qed.
Lemma reference_control_ready_2143 old :
 (exists value ground, VM.find 1892 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2142 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2143.
Proof.
 intros H1892 H2142.
 destruct H1892 as [v1892 [G1892 [V1892 T1892]]].
 destruct H2142 as [v2142 [G2142 [V2142 T2142]]].
 unfold reference_control_expr_2143.
apply rc_mux.
{ eapply rc_ref; [exact V1892|exists G1892; exact T1892].
}
{ eapply rc_ref; [exact V2142|exists G2142; exact T2142].
}
Qed.
Lemma reference_control_member_2143 : List.In (2143,reference_control_expr_2143) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 260%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2143_ground inputs path old current result :
 (exists value ground, VM.find 1892 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2142 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2143 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H1892 H2142 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2143 reference_control_expr_2143 reference_control_0_positions reference_control_0_safety reference_control_member_2143) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2143 reference_control_expr_2143 inputs path old current result Position Safe Nonreg (reference_control_ready_2143 old H1892 H2142) Step).
Qed.
Theorem reference_control_node_2143_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 1892 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2142 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1889 left = VM.find 1889 right ->
 VM.find 1892 left = VM.find 1892 right ->
 VM.find 2142 left = VM.find 2142 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2143 next_left = VM.find 2143 next_right.
Proof.
 intros H1892 H2142 E1889 E1892 E2142 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2143 reference_control_expr_2143 reference_control_0_positions reference_control_0_safety reference_control_member_2143) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2143 reference_control_expr_2143 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2143 left H1892 H2142)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2143 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1889.
 rewrite E1892.
 rewrite E2142.
 reflexivity.
Qed.
Lemma reference_control_ready_2144 old :
 (exists value ground, VM.find 2143 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2144.
Proof.
 intros H2143.
 destruct H2143 as [v2143 [G2143 [V2143 T2143]]].
 unfold reference_control_expr_2144.
apply rc_mux.
{ eapply rc_ref; [exact V2143|exists G2143; exact T2143].
}
{ apply rc_const.
}
Qed.
Lemma reference_control_member_2144 : List.In (2144,reference_control_expr_2144) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 261%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2144_ground inputs path old current result :
 (exists value ground, VM.find 2143 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2144 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2143 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2144 reference_control_expr_2144 reference_control_0_positions reference_control_0_safety reference_control_member_2144) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2144 reference_control_expr_2144 inputs path old current result Position Safe Nonreg (reference_control_ready_2144 old H2143) Step).
Qed.
Theorem reference_control_node_2144_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2143 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1707 left = VM.find 1707 right ->
 VM.find 2143 left = VM.find 2143 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2144 next_left = VM.find 2144 next_right.
Proof.
 intros H2143 E1707 E2143 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2144 reference_control_expr_2144 reference_control_0_positions reference_control_0_safety reference_control_member_2144) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2144 reference_control_expr_2144 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2144 left H2143)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2144 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1707.
 rewrite E2143.
 reflexivity.
Qed.
Lemma reference_control_ready_2145 old :
 (exists value ground, VM.find 2144 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2145.
Proof.
 intros H2144.
 destruct H2144 as [v2144 [G2144 [V2144 T2144]]].
 unfold reference_control_expr_2145.
eapply rc_ref; [exact V2144|exists G2144; exact T2144].
Qed.
Lemma reference_control_member_2145 : List.In (2145,reference_control_expr_2145) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 262%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2145_ground inputs path old current result :
 (exists value ground, VM.find 2144 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2145 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2144 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2145 reference_control_expr_2145 reference_control_0_positions reference_control_0_safety reference_control_member_2145) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2145 reference_control_expr_2145 inputs path old current result Position Safe Nonreg (reference_control_ready_2145 old H2144) Step).
Qed.
Theorem reference_control_node_2145_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2144 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2144 left = VM.find 2144 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2145 next_left = VM.find 2145 next_right.
Proof.
 intros H2144 E2144 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2145 reference_control_expr_2145 reference_control_0_positions reference_control_0_safety reference_control_member_2145) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2145 reference_control_expr_2145 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2145 left H2144)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2145 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2144.
 reflexivity.
Qed.
Lemma reference_control_ready_2146 old :
 (exists value ground, VM.find 1748 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2146.
Proof.
 intros H1748.
 destruct H1748 as [v1748 [G1748 [V1748 T1748]]].
 unfold reference_control_expr_2146.
eapply rc_ref; [exact V1748|exists G1748; exact T1748].
Qed.
Lemma reference_control_member_2146 : List.In (2146,reference_control_expr_2146) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 263%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2146_ground inputs path old current result :
 (exists value ground, VM.find 1748 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2146 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H1748 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2146 reference_control_expr_2146 reference_control_0_positions reference_control_0_safety reference_control_member_2146) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2146 reference_control_expr_2146 inputs path old current result Position Safe Nonreg (reference_control_ready_2146 old H1748) Step).
Qed.
Theorem reference_control_node_2146_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 1748 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1748 left = VM.find 1748 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2146 next_left = VM.find 2146 next_right.
Proof.
 intros H1748 E1748 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2146 reference_control_expr_2146 reference_control_0_positions reference_control_0_safety reference_control_member_2146) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2146 reference_control_expr_2146 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2146 left H1748)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2146 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1748.
 reflexivity.
Qed.
Lemma reference_control_ready_2147 old :
 (exists value ground, VM.find 1747 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2147.
Proof.
 intros H1747.
 destruct H1747 as [v1747 [G1747 [V1747 T1747]]].
 unfold reference_control_expr_2147.
eapply rc_ref; [exact V1747|exists G1747; exact T1747].
Qed.
Lemma reference_control_member_2147 : List.In (2147,reference_control_expr_2147) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 264%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2147_ground inputs path old current result :
 (exists value ground, VM.find 1747 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2147 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H1747 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2147 reference_control_expr_2147 reference_control_0_positions reference_control_0_safety reference_control_member_2147) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2147 reference_control_expr_2147 inputs path old current result Position Safe Nonreg (reference_control_ready_2147 old H1747) Step).
Qed.
Theorem reference_control_node_2147_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 1747 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1747 left = VM.find 1747 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2147 next_left = VM.find 2147 next_right.
Proof.
 intros H1747 E1747 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2147 reference_control_expr_2147 reference_control_0_positions reference_control_0_safety reference_control_member_2147) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2147 reference_control_expr_2147 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2147 left H1747)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2147 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1747.
 reflexivity.
Qed.
Lemma reference_control_ready_2148 old :
 (exists value ground, VM.find 1746 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2148.
Proof.
 intros H1746.
 destruct H1746 as [v1746 [G1746 [V1746 T1746]]].
 unfold reference_control_expr_2148.
eapply rc_ref; [exact V1746|exists G1746; exact T1746].
Qed.
Lemma reference_control_member_2148 : List.In (2148,reference_control_expr_2148) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 265%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2148_ground inputs path old current result :
 (exists value ground, VM.find 1746 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2148 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H1746 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2148 reference_control_expr_2148 reference_control_0_positions reference_control_0_safety reference_control_member_2148) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2148 reference_control_expr_2148 inputs path old current result Position Safe Nonreg (reference_control_ready_2148 old H1746) Step).
Qed.
Theorem reference_control_node_2148_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 1746 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1746 left = VM.find 1746 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2148 next_left = VM.find 2148 next_right.
Proof.
 intros H1746 E1746 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2148 reference_control_expr_2148 reference_control_0_positions reference_control_0_safety reference_control_member_2148) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2148 reference_control_expr_2148 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2148 left H1746)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2148 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1746.
 reflexivity.
Qed.
Lemma reference_control_ready_2149 old :
 (exists value ground, VM.find 1745 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2149.
Proof.
 intros H1745.
 destruct H1745 as [v1745 [G1745 [V1745 T1745]]].
 unfold reference_control_expr_2149.
eapply rc_ref; [exact V1745|exists G1745; exact T1745].
Qed.
Lemma reference_control_member_2149 : List.In (2149,reference_control_expr_2149) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 266%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2149_ground inputs path old current result :
 (exists value ground, VM.find 1745 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2149 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H1745 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2149 reference_control_expr_2149 reference_control_0_positions reference_control_0_safety reference_control_member_2149) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2149 reference_control_expr_2149 inputs path old current result Position Safe Nonreg (reference_control_ready_2149 old H1745) Step).
Qed.
Theorem reference_control_node_2149_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 1745 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1745 left = VM.find 1745 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2149 next_left = VM.find 2149 next_right.
Proof.
 intros H1745 E1745 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2149 reference_control_expr_2149 reference_control_0_positions reference_control_0_safety reference_control_member_2149) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2149 reference_control_expr_2149 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2149 left H1745)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2149 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1745.
 reflexivity.
Qed.
Lemma reference_control_ready_2150 old :
 (exists value ground, VM.find 1744 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2150.
Proof.
 intros H1744.
 destruct H1744 as [v1744 [G1744 [V1744 T1744]]].
 unfold reference_control_expr_2150.
eapply rc_ref; [exact V1744|exists G1744; exact T1744].
Qed.
Lemma reference_control_member_2150 : List.In (2150,reference_control_expr_2150) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 267%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2150_ground inputs path old current result :
 (exists value ground, VM.find 1744 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2150 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H1744 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2150 reference_control_expr_2150 reference_control_0_positions reference_control_0_safety reference_control_member_2150) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2150 reference_control_expr_2150 inputs path old current result Position Safe Nonreg (reference_control_ready_2150 old H1744) Step).
Qed.
Theorem reference_control_node_2150_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 1744 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1744 left = VM.find 1744 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2150 next_left = VM.find 2150 next_right.
Proof.
 intros H1744 E1744 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2150 reference_control_expr_2150 reference_control_0_positions reference_control_0_safety reference_control_member_2150) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2150 reference_control_expr_2150 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2150 left H1744)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2150 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1744.
 reflexivity.
Qed.
Lemma reference_control_ready_2151 old :
 (exists value ground, VM.find 1743 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2151.
Proof.
 intros H1743.
 destruct H1743 as [v1743 [G1743 [V1743 T1743]]].
 unfold reference_control_expr_2151.
eapply rc_ref; [exact V1743|exists G1743; exact T1743].
Qed.
Lemma reference_control_member_2151 : List.In (2151,reference_control_expr_2151) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 268%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2151_ground inputs path old current result :
 (exists value ground, VM.find 1743 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2151 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H1743 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2151 reference_control_expr_2151 reference_control_0_positions reference_control_0_safety reference_control_member_2151) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2151 reference_control_expr_2151 inputs path old current result Position Safe Nonreg (reference_control_ready_2151 old H1743) Step).
Qed.
Theorem reference_control_node_2151_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 1743 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1743 left = VM.find 1743 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2151 next_left = VM.find 2151 next_right.
Proof.
 intros H1743 E1743 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2151 reference_control_expr_2151 reference_control_0_positions reference_control_0_safety reference_control_member_2151) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2151 reference_control_expr_2151 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2151 left H1743)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2151 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1743.
 reflexivity.
Qed.
Lemma reference_control_ready_2152 old :
 (exists value ground, VM.find 1742 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2152.
Proof.
 intros H1742.
 destruct H1742 as [v1742 [G1742 [V1742 T1742]]].
 unfold reference_control_expr_2152.
eapply rc_ref; [exact V1742|exists G1742; exact T1742].
Qed.
Lemma reference_control_member_2152 : List.In (2152,reference_control_expr_2152) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 269%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2152_ground inputs path old current result :
 (exists value ground, VM.find 1742 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2152 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H1742 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2152 reference_control_expr_2152 reference_control_0_positions reference_control_0_safety reference_control_member_2152) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2152 reference_control_expr_2152 inputs path old current result Position Safe Nonreg (reference_control_ready_2152 old H1742) Step).
Qed.
Theorem reference_control_node_2152_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 1742 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1742 left = VM.find 1742 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2152 next_left = VM.find 2152 next_right.
Proof.
 intros H1742 E1742 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2152 reference_control_expr_2152 reference_control_0_positions reference_control_0_safety reference_control_member_2152) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2152 reference_control_expr_2152 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2152 left H1742)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2152 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1742.
 reflexivity.
Qed.
Lemma reference_control_ready_2153 old :
 (exists value ground, VM.find 1741 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2153.
Proof.
 intros H1741.
 destruct H1741 as [v1741 [G1741 [V1741 T1741]]].
 unfold reference_control_expr_2153.
eapply rc_ref; [exact V1741|exists G1741; exact T1741].
Qed.
Lemma reference_control_member_2153 : List.In (2153,reference_control_expr_2153) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 270%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2153_ground inputs path old current result :
 (exists value ground, VM.find 1741 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2153 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H1741 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2153 reference_control_expr_2153 reference_control_0_positions reference_control_0_safety reference_control_member_2153) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2153 reference_control_expr_2153 inputs path old current result Position Safe Nonreg (reference_control_ready_2153 old H1741) Step).
Qed.
Theorem reference_control_node_2153_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 1741 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1741 left = VM.find 1741 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2153 next_left = VM.find 2153 next_right.
Proof.
 intros H1741 E1741 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2153 reference_control_expr_2153 reference_control_0_positions reference_control_0_safety reference_control_member_2153) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2153 reference_control_expr_2153 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2153 left H1741)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2153 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1741.
 reflexivity.
Qed.
Lemma reference_control_ready_2154 old :
 (exists value ground, VM.find 1740 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2154.
Proof.
 intros H1740.
 destruct H1740 as [v1740 [G1740 [V1740 T1740]]].
 unfold reference_control_expr_2154.
eapply rc_ref; [exact V1740|exists G1740; exact T1740].
Qed.
Lemma reference_control_member_2154 : List.In (2154,reference_control_expr_2154) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 271%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2154_ground inputs path old current result :
 (exists value ground, VM.find 1740 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2154 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H1740 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2154 reference_control_expr_2154 reference_control_0_positions reference_control_0_safety reference_control_member_2154) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2154 reference_control_expr_2154 inputs path old current result Position Safe Nonreg (reference_control_ready_2154 old H1740) Step).
Qed.
Theorem reference_control_node_2154_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 1740 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1740 left = VM.find 1740 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2154 next_left = VM.find 2154 next_right.
Proof.
 intros H1740 E1740 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2154 reference_control_expr_2154 reference_control_0_positions reference_control_0_safety reference_control_member_2154) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2154 reference_control_expr_2154 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2154 left H1740)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2154 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1740.
 reflexivity.
Qed.
Lemma reference_control_ready_2155 old :
 (exists value ground, VM.find 1739 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2155.
Proof.
 intros H1739.
 destruct H1739 as [v1739 [G1739 [V1739 T1739]]].
 unfold reference_control_expr_2155.
eapply rc_ref; [exact V1739|exists G1739; exact T1739].
Qed.
Lemma reference_control_member_2155 : List.In (2155,reference_control_expr_2155) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 272%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2155_ground inputs path old current result :
 (exists value ground, VM.find 1739 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2155 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H1739 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2155 reference_control_expr_2155 reference_control_0_positions reference_control_0_safety reference_control_member_2155) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2155 reference_control_expr_2155 inputs path old current result Position Safe Nonreg (reference_control_ready_2155 old H1739) Step).
Qed.
Theorem reference_control_node_2155_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 1739 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1739 left = VM.find 1739 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2155 next_left = VM.find 2155 next_right.
Proof.
 intros H1739 E1739 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2155 reference_control_expr_2155 reference_control_0_positions reference_control_0_safety reference_control_member_2155) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2155 reference_control_expr_2155 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2155 left H1739)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2155 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1739.
 reflexivity.
Qed.
Lemma reference_control_ready_2156 old :
 (exists value ground, VM.find 1738 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2156.
Proof.
 intros H1738.
 destruct H1738 as [v1738 [G1738 [V1738 T1738]]].
 unfold reference_control_expr_2156.
eapply rc_ref; [exact V1738|exists G1738; exact T1738].
Qed.
Lemma reference_control_member_2156 : List.In (2156,reference_control_expr_2156) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 273%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2156_ground inputs path old current result :
 (exists value ground, VM.find 1738 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2156 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H1738 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2156 reference_control_expr_2156 reference_control_0_positions reference_control_0_safety reference_control_member_2156) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2156 reference_control_expr_2156 inputs path old current result Position Safe Nonreg (reference_control_ready_2156 old H1738) Step).
Qed.
Theorem reference_control_node_2156_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 1738 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1738 left = VM.find 1738 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2156 next_left = VM.find 2156 next_right.
Proof.
 intros H1738 E1738 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2156 reference_control_expr_2156 reference_control_0_positions reference_control_0_safety reference_control_member_2156) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2156 reference_control_expr_2156 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2156 left H1738)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2156 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1738.
 reflexivity.
Qed.
Lemma reference_control_ready_2157 old :
 (exists value ground, VM.find 1737 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2157.
Proof.
 intros H1737.
 destruct H1737 as [v1737 [G1737 [V1737 T1737]]].
 unfold reference_control_expr_2157.
eapply rc_ref; [exact V1737|exists G1737; exact T1737].
Qed.
Lemma reference_control_member_2157 : List.In (2157,reference_control_expr_2157) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 274%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2157_ground inputs path old current result :
 (exists value ground, VM.find 1737 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2157 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H1737 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2157 reference_control_expr_2157 reference_control_0_positions reference_control_0_safety reference_control_member_2157) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2157 reference_control_expr_2157 inputs path old current result Position Safe Nonreg (reference_control_ready_2157 old H1737) Step).
Qed.
Theorem reference_control_node_2157_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 1737 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1737 left = VM.find 1737 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2157 next_left = VM.find 2157 next_right.
Proof.
 intros H1737 E1737 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2157 reference_control_expr_2157 reference_control_0_positions reference_control_0_safety reference_control_member_2157) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2157 reference_control_expr_2157 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2157 left H1737)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2157 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1737.
 reflexivity.
Qed.
Lemma reference_control_ready_2158 old :
 (exists value ground, VM.find 1736 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2158.
Proof.
 intros H1736.
 destruct H1736 as [v1736 [G1736 [V1736 T1736]]].
 unfold reference_control_expr_2158.
eapply rc_ref; [exact V1736|exists G1736; exact T1736].
Qed.
Lemma reference_control_member_2158 : List.In (2158,reference_control_expr_2158) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 275%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2158_ground inputs path old current result :
 (exists value ground, VM.find 1736 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2158 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H1736 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2158 reference_control_expr_2158 reference_control_0_positions reference_control_0_safety reference_control_member_2158) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2158 reference_control_expr_2158 inputs path old current result Position Safe Nonreg (reference_control_ready_2158 old H1736) Step).
Qed.
Theorem reference_control_node_2158_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 1736 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1736 left = VM.find 1736 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2158 next_left = VM.find 2158 next_right.
Proof.
 intros H1736 E1736 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2158 reference_control_expr_2158 reference_control_0_positions reference_control_0_safety reference_control_member_2158) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2158 reference_control_expr_2158 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2158 left H1736)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2158 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1736.
 reflexivity.
Qed.
Lemma reference_control_ready_2159 old :
 (exists value ground, VM.find 1735 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2159.
Proof.
 intros H1735.
 destruct H1735 as [v1735 [G1735 [V1735 T1735]]].
 unfold reference_control_expr_2159.
eapply rc_ref; [exact V1735|exists G1735; exact T1735].
Qed.
Lemma reference_control_member_2159 : List.In (2159,reference_control_expr_2159) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 276%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2159_ground inputs path old current result :
 (exists value ground, VM.find 1735 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2159 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H1735 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2159 reference_control_expr_2159 reference_control_0_positions reference_control_0_safety reference_control_member_2159) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2159 reference_control_expr_2159 inputs path old current result Position Safe Nonreg (reference_control_ready_2159 old H1735) Step).
Qed.
Theorem reference_control_node_2159_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 1735 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1735 left = VM.find 1735 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2159 next_left = VM.find 2159 next_right.
Proof.
 intros H1735 E1735 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2159 reference_control_expr_2159 reference_control_0_positions reference_control_0_safety reference_control_member_2159) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2159 reference_control_expr_2159 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2159 left H1735)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2159 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1735.
 reflexivity.
Qed.
Lemma reference_control_ready_2160 old :
 (exists value ground, VM.find 1734 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2160.
Proof.
 intros H1734.
 destruct H1734 as [v1734 [G1734 [V1734 T1734]]].
 unfold reference_control_expr_2160.
eapply rc_ref; [exact V1734|exists G1734; exact T1734].
Qed.
Lemma reference_control_member_2160 : List.In (2160,reference_control_expr_2160) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 277%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2160_ground inputs path old current result :
 (exists value ground, VM.find 1734 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2160 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H1734 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2160 reference_control_expr_2160 reference_control_0_positions reference_control_0_safety reference_control_member_2160) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2160 reference_control_expr_2160 inputs path old current result Position Safe Nonreg (reference_control_ready_2160 old H1734) Step).
Qed.
Theorem reference_control_node_2160_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 1734 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1734 left = VM.find 1734 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2160 next_left = VM.find 2160 next_right.
Proof.
 intros H1734 E1734 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2160 reference_control_expr_2160 reference_control_0_positions reference_control_0_safety reference_control_member_2160) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2160 reference_control_expr_2160 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2160 left H1734)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2160 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1734.
 reflexivity.
Qed.
Lemma reference_control_ready_2161 old :
 (exists value ground, VM.find 1733 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2161.
Proof.
 intros H1733.
 destruct H1733 as [v1733 [G1733 [V1733 T1733]]].
 unfold reference_control_expr_2161.
eapply rc_ref; [exact V1733|exists G1733; exact T1733].
Qed.
Lemma reference_control_member_2161 : List.In (2161,reference_control_expr_2161) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 278%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2161_ground inputs path old current result :
 (exists value ground, VM.find 1733 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2161 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H1733 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2161 reference_control_expr_2161 reference_control_0_positions reference_control_0_safety reference_control_member_2161) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2161 reference_control_expr_2161 inputs path old current result Position Safe Nonreg (reference_control_ready_2161 old H1733) Step).
Qed.
Theorem reference_control_node_2161_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 1733 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1733 left = VM.find 1733 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2161 next_left = VM.find 2161 next_right.
Proof.
 intros H1733 E1733 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2161 reference_control_expr_2161 reference_control_0_positions reference_control_0_safety reference_control_member_2161) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2161 reference_control_expr_2161 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2161 left H1733)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2161 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1733.
 reflexivity.
Qed.
Lemma reference_control_ready_2162 old :
 (exists value ground, VM.find 1732 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2162.
Proof.
 intros H1732.
 destruct H1732 as [v1732 [G1732 [V1732 T1732]]].
 unfold reference_control_expr_2162.
eapply rc_ref; [exact V1732|exists G1732; exact T1732].
Qed.
Lemma reference_control_member_2162 : List.In (2162,reference_control_expr_2162) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 279%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2162_ground inputs path old current result :
 (exists value ground, VM.find 1732 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2162 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H1732 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2162 reference_control_expr_2162 reference_control_0_positions reference_control_0_safety reference_control_member_2162) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2162 reference_control_expr_2162 inputs path old current result Position Safe Nonreg (reference_control_ready_2162 old H1732) Step).
Qed.
Theorem reference_control_node_2162_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 1732 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1732 left = VM.find 1732 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2162 next_left = VM.find 2162 next_right.
Proof.
 intros H1732 E1732 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2162 reference_control_expr_2162 reference_control_0_positions reference_control_0_safety reference_control_member_2162) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2162 reference_control_expr_2162 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2162 left H1732)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2162 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1732.
 reflexivity.
Qed.
Lemma reference_control_ready_2163 old :
 (exists value ground, VM.find 1731 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2163.
Proof.
 intros H1731.
 destruct H1731 as [v1731 [G1731 [V1731 T1731]]].
 unfold reference_control_expr_2163.
eapply rc_ref; [exact V1731|exists G1731; exact T1731].
Qed.
Lemma reference_control_member_2163 : List.In (2163,reference_control_expr_2163) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 280%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2163_ground inputs path old current result :
 (exists value ground, VM.find 1731 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2163 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H1731 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2163 reference_control_expr_2163 reference_control_0_positions reference_control_0_safety reference_control_member_2163) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2163 reference_control_expr_2163 inputs path old current result Position Safe Nonreg (reference_control_ready_2163 old H1731) Step).
Qed.
Theorem reference_control_node_2163_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 1731 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1731 left = VM.find 1731 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2163 next_left = VM.find 2163 next_right.
Proof.
 intros H1731 E1731 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2163 reference_control_expr_2163 reference_control_0_positions reference_control_0_safety reference_control_member_2163) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2163 reference_control_expr_2163 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2163 left H1731)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2163 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1731.
 reflexivity.
Qed.
Lemma reference_control_ready_2164 old :
 (exists value ground, VM.find 1730 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2164.
Proof.
 intros H1730.
 destruct H1730 as [v1730 [G1730 [V1730 T1730]]].
 unfold reference_control_expr_2164.
eapply rc_ref; [exact V1730|exists G1730; exact T1730].
Qed.
Lemma reference_control_member_2164 : List.In (2164,reference_control_expr_2164) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 281%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2164_ground inputs path old current result :
 (exists value ground, VM.find 1730 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2164 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H1730 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2164 reference_control_expr_2164 reference_control_0_positions reference_control_0_safety reference_control_member_2164) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2164 reference_control_expr_2164 inputs path old current result Position Safe Nonreg (reference_control_ready_2164 old H1730) Step).
Qed.
Theorem reference_control_node_2164_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 1730 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1730 left = VM.find 1730 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2164 next_left = VM.find 2164 next_right.
Proof.
 intros H1730 E1730 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2164 reference_control_expr_2164 reference_control_0_positions reference_control_0_safety reference_control_member_2164) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2164 reference_control_expr_2164 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2164 left H1730)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2164 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1730.
 reflexivity.
Qed.
Lemma reference_control_ready_2165 old :
 (exists value ground, VM.find 1729 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2165.
Proof.
 intros H1729.
 destruct H1729 as [v1729 [G1729 [V1729 T1729]]].
 unfold reference_control_expr_2165.
eapply rc_ref; [exact V1729|exists G1729; exact T1729].
Qed.
Lemma reference_control_member_2165 : List.In (2165,reference_control_expr_2165) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 282%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2165_ground inputs path old current result :
 (exists value ground, VM.find 1729 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2165 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H1729 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2165 reference_control_expr_2165 reference_control_0_positions reference_control_0_safety reference_control_member_2165) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2165 reference_control_expr_2165 inputs path old current result Position Safe Nonreg (reference_control_ready_2165 old H1729) Step).
Qed.
Theorem reference_control_node_2165_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 1729 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1729 left = VM.find 1729 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2165 next_left = VM.find 2165 next_right.
Proof.
 intros H1729 E1729 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2165 reference_control_expr_2165 reference_control_0_positions reference_control_0_safety reference_control_member_2165) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2165 reference_control_expr_2165 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2165 left H1729)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2165 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1729.
 reflexivity.
Qed.
Lemma reference_control_ready_2166 old :
 (exists value ground, VM.find 1728 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2166.
Proof.
 intros H1728.
 destruct H1728 as [v1728 [G1728 [V1728 T1728]]].
 unfold reference_control_expr_2166.
eapply rc_ref; [exact V1728|exists G1728; exact T1728].
Qed.
Lemma reference_control_member_2166 : List.In (2166,reference_control_expr_2166) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 283%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2166_ground inputs path old current result :
 (exists value ground, VM.find 1728 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2166 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H1728 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2166 reference_control_expr_2166 reference_control_0_positions reference_control_0_safety reference_control_member_2166) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2166 reference_control_expr_2166 inputs path old current result Position Safe Nonreg (reference_control_ready_2166 old H1728) Step).
Qed.
Theorem reference_control_node_2166_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 1728 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1728 left = VM.find 1728 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2166 next_left = VM.find 2166 next_right.
Proof.
 intros H1728 E1728 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2166 reference_control_expr_2166 reference_control_0_positions reference_control_0_safety reference_control_member_2166) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2166 reference_control_expr_2166 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2166 left H1728)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2166 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1728.
 reflexivity.
Qed.
Lemma reference_control_ready_2167 old :
 (exists value ground, VM.find 1727 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2167.
Proof.
 intros H1727.
 destruct H1727 as [v1727 [G1727 [V1727 T1727]]].
 unfold reference_control_expr_2167.
eapply rc_ref; [exact V1727|exists G1727; exact T1727].
Qed.
Lemma reference_control_member_2167 : List.In (2167,reference_control_expr_2167) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 284%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2167_ground inputs path old current result :
 (exists value ground, VM.find 1727 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2167 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H1727 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2167 reference_control_expr_2167 reference_control_0_positions reference_control_0_safety reference_control_member_2167) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2167 reference_control_expr_2167 inputs path old current result Position Safe Nonreg (reference_control_ready_2167 old H1727) Step).
Qed.
Theorem reference_control_node_2167_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 1727 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1727 left = VM.find 1727 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2167 next_left = VM.find 2167 next_right.
Proof.
 intros H1727 E1727 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2167 reference_control_expr_2167 reference_control_0_positions reference_control_0_safety reference_control_member_2167) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2167 reference_control_expr_2167 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2167 left H1727)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2167 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1727.
 reflexivity.
Qed.
Lemma reference_control_ready_2168 old :
 (exists value ground, VM.find 1726 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2168.
Proof.
 intros H1726.
 destruct H1726 as [v1726 [G1726 [V1726 T1726]]].
 unfold reference_control_expr_2168.
eapply rc_ref; [exact V1726|exists G1726; exact T1726].
Qed.
Lemma reference_control_member_2168 : List.In (2168,reference_control_expr_2168) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 285%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2168_ground inputs path old current result :
 (exists value ground, VM.find 1726 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2168 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H1726 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2168 reference_control_expr_2168 reference_control_0_positions reference_control_0_safety reference_control_member_2168) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2168 reference_control_expr_2168 inputs path old current result Position Safe Nonreg (reference_control_ready_2168 old H1726) Step).
Qed.
Theorem reference_control_node_2168_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 1726 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1726 left = VM.find 1726 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2168 next_left = VM.find 2168 next_right.
Proof.
 intros H1726 E1726 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2168 reference_control_expr_2168 reference_control_0_positions reference_control_0_safety reference_control_member_2168) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2168 reference_control_expr_2168 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2168 left H1726)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2168 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1726.
 reflexivity.
Qed.
Lemma reference_control_ready_2169 old :
 (exists value ground, VM.find 1725 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2169.
Proof.
 intros H1725.
 destruct H1725 as [v1725 [G1725 [V1725 T1725]]].
 unfold reference_control_expr_2169.
eapply rc_ref; [exact V1725|exists G1725; exact T1725].
Qed.
Lemma reference_control_member_2169 : List.In (2169,reference_control_expr_2169) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 286%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2169_ground inputs path old current result :
 (exists value ground, VM.find 1725 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2169 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H1725 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2169 reference_control_expr_2169 reference_control_0_positions reference_control_0_safety reference_control_member_2169) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2169 reference_control_expr_2169 inputs path old current result Position Safe Nonreg (reference_control_ready_2169 old H1725) Step).
Qed.
Theorem reference_control_node_2169_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 1725 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1725 left = VM.find 1725 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2169 next_left = VM.find 2169 next_right.
Proof.
 intros H1725 E1725 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2169 reference_control_expr_2169 reference_control_0_positions reference_control_0_safety reference_control_member_2169) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2169 reference_control_expr_2169 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2169 left H1725)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2169 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1725.
 reflexivity.
Qed.
Lemma reference_control_ready_2170 old :
 (exists value ground, VM.find 1724 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2170.
Proof.
 intros H1724.
 destruct H1724 as [v1724 [G1724 [V1724 T1724]]].
 unfold reference_control_expr_2170.
eapply rc_ref; [exact V1724|exists G1724; exact T1724].
Qed.
Lemma reference_control_member_2170 : List.In (2170,reference_control_expr_2170) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 287%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2170_ground inputs path old current result :
 (exists value ground, VM.find 1724 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2170 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H1724 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2170 reference_control_expr_2170 reference_control_0_positions reference_control_0_safety reference_control_member_2170) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2170 reference_control_expr_2170 inputs path old current result Position Safe Nonreg (reference_control_ready_2170 old H1724) Step).
Qed.
Theorem reference_control_node_2170_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 1724 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1724 left = VM.find 1724 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2170 next_left = VM.find 2170 next_right.
Proof.
 intros H1724 E1724 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2170 reference_control_expr_2170 reference_control_0_positions reference_control_0_safety reference_control_member_2170) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2170 reference_control_expr_2170 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2170 left H1724)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2170 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1724.
 reflexivity.
Qed.
Lemma reference_control_ready_2171 old :
 (exists value ground, VM.find 1723 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2171.
Proof.
 intros H1723.
 destruct H1723 as [v1723 [G1723 [V1723 T1723]]].
 unfold reference_control_expr_2171.
eapply rc_ref; [exact V1723|exists G1723; exact T1723].
Qed.
Lemma reference_control_member_2171 : List.In (2171,reference_control_expr_2171) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 288%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2171_ground inputs path old current result :
 (exists value ground, VM.find 1723 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2171 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H1723 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2171 reference_control_expr_2171 reference_control_0_positions reference_control_0_safety reference_control_member_2171) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2171 reference_control_expr_2171 inputs path old current result Position Safe Nonreg (reference_control_ready_2171 old H1723) Step).
Qed.
Theorem reference_control_node_2171_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 1723 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1723 left = VM.find 1723 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2171 next_left = VM.find 2171 next_right.
Proof.
 intros H1723 E1723 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2171 reference_control_expr_2171 reference_control_0_positions reference_control_0_safety reference_control_member_2171) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2171 reference_control_expr_2171 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2171 left H1723)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2171 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1723.
 reflexivity.
Qed.
Lemma reference_control_ready_2172 old :
 (exists value ground, VM.find 1722 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2172.
Proof.
 intros H1722.
 destruct H1722 as [v1722 [G1722 [V1722 T1722]]].
 unfold reference_control_expr_2172.
eapply rc_ref; [exact V1722|exists G1722; exact T1722].
Qed.
Lemma reference_control_member_2172 : List.In (2172,reference_control_expr_2172) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 289%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2172_ground inputs path old current result :
 (exists value ground, VM.find 1722 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2172 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H1722 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2172 reference_control_expr_2172 reference_control_0_positions reference_control_0_safety reference_control_member_2172) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2172 reference_control_expr_2172 inputs path old current result Position Safe Nonreg (reference_control_ready_2172 old H1722) Step).
Qed.
Theorem reference_control_node_2172_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 1722 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1722 left = VM.find 1722 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2172 next_left = VM.find 2172 next_right.
Proof.
 intros H1722 E1722 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2172 reference_control_expr_2172 reference_control_0_positions reference_control_0_safety reference_control_member_2172) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2172 reference_control_expr_2172 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2172 left H1722)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2172 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1722.
 reflexivity.
Qed.
Lemma reference_control_ready_2173 old :
 (exists value ground, VM.find 1721 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2173.
Proof.
 intros H1721.
 destruct H1721 as [v1721 [G1721 [V1721 T1721]]].
 unfold reference_control_expr_2173.
eapply rc_ref; [exact V1721|exists G1721; exact T1721].
Qed.
Lemma reference_control_member_2173 : List.In (2173,reference_control_expr_2173) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 290%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2173_ground inputs path old current result :
 (exists value ground, VM.find 1721 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2173 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H1721 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2173 reference_control_expr_2173 reference_control_0_positions reference_control_0_safety reference_control_member_2173) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2173 reference_control_expr_2173 inputs path old current result Position Safe Nonreg (reference_control_ready_2173 old H1721) Step).
Qed.
Theorem reference_control_node_2173_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 1721 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1721 left = VM.find 1721 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2173 next_left = VM.find 2173 next_right.
Proof.
 intros H1721 E1721 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2173 reference_control_expr_2173 reference_control_0_positions reference_control_0_safety reference_control_member_2173) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2173 reference_control_expr_2173 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2173 left H1721)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2173 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1721.
 reflexivity.
Qed.
Lemma reference_control_ready_2174 old :
 (exists value ground, VM.find 1720 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2174.
Proof.
 intros H1720.
 destruct H1720 as [v1720 [G1720 [V1720 T1720]]].
 unfold reference_control_expr_2174.
eapply rc_ref; [exact V1720|exists G1720; exact T1720].
Qed.
Lemma reference_control_member_2174 : List.In (2174,reference_control_expr_2174) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 291%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2174_ground inputs path old current result :
 (exists value ground, VM.find 1720 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2174 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H1720 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2174 reference_control_expr_2174 reference_control_0_positions reference_control_0_safety reference_control_member_2174) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2174 reference_control_expr_2174 inputs path old current result Position Safe Nonreg (reference_control_ready_2174 old H1720) Step).
Qed.
Theorem reference_control_node_2174_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 1720 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1720 left = VM.find 1720 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2174 next_left = VM.find 2174 next_right.
Proof.
 intros H1720 E1720 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2174 reference_control_expr_2174 reference_control_0_positions reference_control_0_safety reference_control_member_2174) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2174 reference_control_expr_2174 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2174 left H1720)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2174 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1720.
 reflexivity.
Qed.
Lemma reference_control_ready_2175 old :
 (exists value ground, VM.find 1719 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2175.
Proof.
 intros H1719.
 destruct H1719 as [v1719 [G1719 [V1719 T1719]]].
 unfold reference_control_expr_2175.
eapply rc_ref; [exact V1719|exists G1719; exact T1719].
Qed.
Lemma reference_control_member_2175 : List.In (2175,reference_control_expr_2175) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 292%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2175_ground inputs path old current result :
 (exists value ground, VM.find 1719 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2175 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H1719 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2175 reference_control_expr_2175 reference_control_0_positions reference_control_0_safety reference_control_member_2175) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2175 reference_control_expr_2175 inputs path old current result Position Safe Nonreg (reference_control_ready_2175 old H1719) Step).
Qed.
Theorem reference_control_node_2175_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 1719 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1719 left = VM.find 1719 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2175 next_left = VM.find 2175 next_right.
Proof.
 intros H1719 E1719 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2175 reference_control_expr_2175 reference_control_0_positions reference_control_0_safety reference_control_member_2175) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2175 reference_control_expr_2175 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2175 left H1719)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2175 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1719.
 reflexivity.
Qed.
Lemma reference_control_ready_2176 old :
 (exists value ground, VM.find 1718 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2176.
Proof.
 intros H1718.
 destruct H1718 as [v1718 [G1718 [V1718 T1718]]].
 unfold reference_control_expr_2176.
eapply rc_ref; [exact V1718|exists G1718; exact T1718].
Qed.
Lemma reference_control_member_2176 : List.In (2176,reference_control_expr_2176) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 293%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2176_ground inputs path old current result :
 (exists value ground, VM.find 1718 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2176 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H1718 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2176 reference_control_expr_2176 reference_control_0_positions reference_control_0_safety reference_control_member_2176) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2176 reference_control_expr_2176 inputs path old current result Position Safe Nonreg (reference_control_ready_2176 old H1718) Step).
Qed.
Theorem reference_control_node_2176_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 1718 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1718 left = VM.find 1718 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2176 next_left = VM.find 2176 next_right.
Proof.
 intros H1718 E1718 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2176 reference_control_expr_2176 reference_control_0_positions reference_control_0_safety reference_control_member_2176) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2176 reference_control_expr_2176 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2176 left H1718)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2176 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1718.
 reflexivity.
Qed.
Lemma reference_control_ready_2177 old :
 (exists value ground, VM.find 1717 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2177.
Proof.
 intros H1717.
 destruct H1717 as [v1717 [G1717 [V1717 T1717]]].
 unfold reference_control_expr_2177.
eapply rc_ref; [exact V1717|exists G1717; exact T1717].
Qed.
Lemma reference_control_member_2177 : List.In (2177,reference_control_expr_2177) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 294%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2177_ground inputs path old current result :
 (exists value ground, VM.find 1717 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2177 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H1717 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2177 reference_control_expr_2177 reference_control_0_positions reference_control_0_safety reference_control_member_2177) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2177 reference_control_expr_2177 inputs path old current result Position Safe Nonreg (reference_control_ready_2177 old H1717) Step).
Qed.
Theorem reference_control_node_2177_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 1717 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1717 left = VM.find 1717 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2177 next_left = VM.find 2177 next_right.
Proof.
 intros H1717 E1717 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2177 reference_control_expr_2177 reference_control_0_positions reference_control_0_safety reference_control_member_2177) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2177 reference_control_expr_2177 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2177 left H1717)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2177 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1717.
 reflexivity.
Qed.
Lemma reference_control_ready_2178 old :
 (exists value ground, VM.find 2177 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2178.
Proof.
 intros H2177.
 destruct H2177 as [v2177 [G2177 [V2177 T2177]]].
 unfold reference_control_expr_2178.
apply rc_validif.
eapply rc_ref; [exact V2177|exists G2177; exact T2177].
Qed.
Lemma reference_control_member_2178 : List.In (2178,reference_control_expr_2178) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 295%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2178_ground inputs path old current result :
 (exists value ground, VM.find 2177 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2178 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2177 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2178 reference_control_expr_2178 reference_control_0_positions reference_control_0_safety reference_control_member_2178) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2178 reference_control_expr_2178 inputs path old current result Position Safe Nonreg (reference_control_ready_2178 old H2177) Step).
Qed.
Theorem reference_control_node_2178_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2177 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2145 left = VM.find 2145 right ->
 VM.find 2177 left = VM.find 2177 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2178 next_left = VM.find 2178 next_right.
Proof.
 intros H2177 E2145 E2177 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2178 reference_control_expr_2178 reference_control_0_positions reference_control_0_safety reference_control_member_2178) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2178 reference_control_expr_2178 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2178 left H2177)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2178 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2145.
 rewrite E2177.
 reflexivity.
Qed.
Lemma reference_control_ready_2179 old :
 (exists value ground, VM.find 2176 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2178 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2179.
Proof.
 intros H2176 H2178.
 destruct H2176 as [v2176 [G2176 [V2176 T2176]]].
 destruct H2178 as [v2178 [G2178 [V2178 T2178]]].
 unfold reference_control_expr_2179.
apply rc_mux.
{ eapply rc_ref; [exact V2176|exists G2176; exact T2176].
}
{ eapply rc_ref; [exact V2178|exists G2178; exact T2178].
}
Qed.
Lemma reference_control_member_2179 : List.In (2179,reference_control_expr_2179) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 296%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2179_ground inputs path old current result :
 (exists value ground, VM.find 2176 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2178 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2179 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2176 H2178 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2179 reference_control_expr_2179 reference_control_0_positions reference_control_0_safety reference_control_member_2179) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2179 reference_control_expr_2179 inputs path old current result Position Safe Nonreg (reference_control_ready_2179 old H2176 H2178) Step).
Qed.
Theorem reference_control_node_2179_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2176 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2178 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2145 left = VM.find 2145 right ->
 VM.find 2176 left = VM.find 2176 right ->
 VM.find 2178 left = VM.find 2178 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2179 next_left = VM.find 2179 next_right.
Proof.
 intros H2176 H2178 E2145 E2176 E2178 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2179 reference_control_expr_2179 reference_control_0_positions reference_control_0_safety reference_control_member_2179) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2179 reference_control_expr_2179 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2179 left H2176 H2178)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2179 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2145.
 rewrite E2176.
 rewrite E2178.
 reflexivity.
Qed.
Lemma reference_control_ready_2180 old :
 (exists value ground, VM.find 2175 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2179 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2180.
Proof.
 intros H2175 H2179.
 destruct H2175 as [v2175 [G2175 [V2175 T2175]]].
 destruct H2179 as [v2179 [G2179 [V2179 T2179]]].
 unfold reference_control_expr_2180.
apply rc_mux.
{ eapply rc_ref; [exact V2175|exists G2175; exact T2175].
}
{ eapply rc_ref; [exact V2179|exists G2179; exact T2179].
}
Qed.
Lemma reference_control_member_2180 : List.In (2180,reference_control_expr_2180) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 297%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2180_ground inputs path old current result :
 (exists value ground, VM.find 2175 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2179 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2180 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2175 H2179 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2180 reference_control_expr_2180 reference_control_0_positions reference_control_0_safety reference_control_member_2180) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2180 reference_control_expr_2180 inputs path old current result Position Safe Nonreg (reference_control_ready_2180 old H2175 H2179) Step).
Qed.
Theorem reference_control_node_2180_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2175 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2179 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2145 left = VM.find 2145 right ->
 VM.find 2175 left = VM.find 2175 right ->
 VM.find 2179 left = VM.find 2179 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2180 next_left = VM.find 2180 next_right.
Proof.
 intros H2175 H2179 E2145 E2175 E2179 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2180 reference_control_expr_2180 reference_control_0_positions reference_control_0_safety reference_control_member_2180) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2180 reference_control_expr_2180 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2180 left H2175 H2179)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2180 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2145.
 rewrite E2175.
 rewrite E2179.
 reflexivity.
Qed.
Lemma reference_control_ready_2181 old :
 (exists value ground, VM.find 2174 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2180 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2181.
Proof.
 intros H2174 H2180.
 destruct H2174 as [v2174 [G2174 [V2174 T2174]]].
 destruct H2180 as [v2180 [G2180 [V2180 T2180]]].
 unfold reference_control_expr_2181.
apply rc_mux.
{ eapply rc_ref; [exact V2174|exists G2174; exact T2174].
}
{ eapply rc_ref; [exact V2180|exists G2180; exact T2180].
}
Qed.
Lemma reference_control_member_2181 : List.In (2181,reference_control_expr_2181) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 298%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2181_ground inputs path old current result :
 (exists value ground, VM.find 2174 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2180 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2181 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2174 H2180 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2181 reference_control_expr_2181 reference_control_0_positions reference_control_0_safety reference_control_member_2181) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2181 reference_control_expr_2181 inputs path old current result Position Safe Nonreg (reference_control_ready_2181 old H2174 H2180) Step).
Qed.
Theorem reference_control_node_2181_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2174 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2180 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2145 left = VM.find 2145 right ->
 VM.find 2174 left = VM.find 2174 right ->
 VM.find 2180 left = VM.find 2180 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2181 next_left = VM.find 2181 next_right.
Proof.
 intros H2174 H2180 E2145 E2174 E2180 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2181 reference_control_expr_2181 reference_control_0_positions reference_control_0_safety reference_control_member_2181) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2181 reference_control_expr_2181 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2181 left H2174 H2180)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2181 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2145.
 rewrite E2174.
 rewrite E2180.
 reflexivity.
Qed.
Lemma reference_control_ready_2182 old :
 (exists value ground, VM.find 2173 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2181 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2182.
Proof.
 intros H2173 H2181.
 destruct H2173 as [v2173 [G2173 [V2173 T2173]]].
 destruct H2181 as [v2181 [G2181 [V2181 T2181]]].
 unfold reference_control_expr_2182.
apply rc_mux.
{ eapply rc_ref; [exact V2173|exists G2173; exact T2173].
}
{ eapply rc_ref; [exact V2181|exists G2181; exact T2181].
}
Qed.
Lemma reference_control_member_2182 : List.In (2182,reference_control_expr_2182) reference_control_0_nodes.
Proof. apply (List.nth_error_In reference_control_0_nodes 299%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2182_ground inputs path old current result :
 (exists value ground, VM.find 2173 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2181 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2182 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2173 H2181 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2182 reference_control_expr_2182 reference_control_0_positions reference_control_0_safety reference_control_member_2182) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2182 reference_control_expr_2182 inputs path old current result Position Safe Nonreg (reference_control_ready_2182 old H2173 H2181) Step).
Qed.
Theorem reference_control_node_2182_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2173 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2181 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2145 left = VM.find 2145 right ->
 VM.find 2173 left = VM.find 2173 right ->
 VM.find 2181 left = VM.find 2181 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2182 next_left = VM.find 2182 next_right.
Proof.
 intros H2173 H2181 E2145 E2173 E2181 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements
 reference_control_0_nodes 2182 reference_control_expr_2182 reference_control_0_positions reference_control_0_safety reference_control_member_2182) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2182 reference_control_expr_2182 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2182 left H2173 H2181)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2182 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2145.
 rewrite E2173.
 rewrite E2181.
 reflexivity.
Qed.
Print Assumptions reference_control_node_2182_congruent.
