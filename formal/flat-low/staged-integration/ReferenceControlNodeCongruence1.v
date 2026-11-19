Require Import CoreSocModel ComparisonNodes ReferenceControlExpressions ReferenceControlGroundOperations ReferenceControlGroundExpressions ReferenceControlNodeGeneric SelectedNodeSafety.
From Coq Require Import ZArith List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Require Import ReferenceControlNodeCertificates1.
Lemma reference_control_ready_2183 old :
 (exists value ground, VM.find 2172 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2182 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2183.
Proof.
 intros H2172 H2182.
 destruct H2172 as [v2172 [G2172 [V2172 T2172]]].
 destruct H2182 as [v2182 [G2182 [V2182 T2182]]].
 unfold reference_control_expr_2183.
apply rc_mux.
{ eapply rc_ref; [exact V2172|exists G2172; exact T2172].
}
{ eapply rc_ref; [exact V2182|exists G2182; exact T2182].
}
Qed.
Lemma reference_control_member_2183 : List.In (2183,reference_control_expr_2183) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 0%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2183_ground inputs path old current result :
 (exists value ground, VM.find 2172 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2182 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2183 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2172 H2182 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2183 reference_control_expr_2183 reference_control_1_positions reference_control_1_safety reference_control_member_2183) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2183 reference_control_expr_2183 inputs path old current result Position Safe Nonreg (reference_control_ready_2183 old H2172 H2182) Step).
Qed.
Theorem reference_control_node_2183_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2172 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2182 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2145 left = VM.find 2145 right ->
 VM.find 2172 left = VM.find 2172 right ->
 VM.find 2182 left = VM.find 2182 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2183 next_left = VM.find 2183 next_right.
Proof.
 intros H2172 H2182 E2145 E2172 E2182 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2183 reference_control_expr_2183 reference_control_1_positions reference_control_1_safety reference_control_member_2183) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2183 reference_control_expr_2183 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2183 left H2172 H2182)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2183 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2145.
 rewrite E2172.
 rewrite E2182.
 reflexivity.
Qed.
Lemma reference_control_ready_2184 old :
 (exists value ground, VM.find 2171 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2183 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2184.
Proof.
 intros H2171 H2183.
 destruct H2171 as [v2171 [G2171 [V2171 T2171]]].
 destruct H2183 as [v2183 [G2183 [V2183 T2183]]].
 unfold reference_control_expr_2184.
apply rc_mux.
{ eapply rc_ref; [exact V2171|exists G2171; exact T2171].
}
{ eapply rc_ref; [exact V2183|exists G2183; exact T2183].
}
Qed.
Lemma reference_control_member_2184 : List.In (2184,reference_control_expr_2184) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 1%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2184_ground inputs path old current result :
 (exists value ground, VM.find 2171 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2183 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2184 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2171 H2183 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2184 reference_control_expr_2184 reference_control_1_positions reference_control_1_safety reference_control_member_2184) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2184 reference_control_expr_2184 inputs path old current result Position Safe Nonreg (reference_control_ready_2184 old H2171 H2183) Step).
Qed.
Theorem reference_control_node_2184_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2171 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2183 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2145 left = VM.find 2145 right ->
 VM.find 2171 left = VM.find 2171 right ->
 VM.find 2183 left = VM.find 2183 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2184 next_left = VM.find 2184 next_right.
Proof.
 intros H2171 H2183 E2145 E2171 E2183 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2184 reference_control_expr_2184 reference_control_1_positions reference_control_1_safety reference_control_member_2184) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2184 reference_control_expr_2184 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2184 left H2171 H2183)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2184 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2145.
 rewrite E2171.
 rewrite E2183.
 reflexivity.
Qed.
Lemma reference_control_ready_2185 old :
 (exists value ground, VM.find 2170 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2184 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2185.
Proof.
 intros H2170 H2184.
 destruct H2170 as [v2170 [G2170 [V2170 T2170]]].
 destruct H2184 as [v2184 [G2184 [V2184 T2184]]].
 unfold reference_control_expr_2185.
apply rc_mux.
{ eapply rc_ref; [exact V2170|exists G2170; exact T2170].
}
{ eapply rc_ref; [exact V2184|exists G2184; exact T2184].
}
Qed.
Lemma reference_control_member_2185 : List.In (2185,reference_control_expr_2185) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 2%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2185_ground inputs path old current result :
 (exists value ground, VM.find 2170 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2184 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2185 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2170 H2184 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2185 reference_control_expr_2185 reference_control_1_positions reference_control_1_safety reference_control_member_2185) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2185 reference_control_expr_2185 inputs path old current result Position Safe Nonreg (reference_control_ready_2185 old H2170 H2184) Step).
Qed.
Theorem reference_control_node_2185_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2170 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2184 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2145 left = VM.find 2145 right ->
 VM.find 2170 left = VM.find 2170 right ->
 VM.find 2184 left = VM.find 2184 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2185 next_left = VM.find 2185 next_right.
Proof.
 intros H2170 H2184 E2145 E2170 E2184 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2185 reference_control_expr_2185 reference_control_1_positions reference_control_1_safety reference_control_member_2185) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2185 reference_control_expr_2185 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2185 left H2170 H2184)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2185 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2145.
 rewrite E2170.
 rewrite E2184.
 reflexivity.
Qed.
Lemma reference_control_ready_2186 old :
 (exists value ground, VM.find 2169 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2185 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2186.
Proof.
 intros H2169 H2185.
 destruct H2169 as [v2169 [G2169 [V2169 T2169]]].
 destruct H2185 as [v2185 [G2185 [V2185 T2185]]].
 unfold reference_control_expr_2186.
apply rc_mux.
{ eapply rc_ref; [exact V2169|exists G2169; exact T2169].
}
{ eapply rc_ref; [exact V2185|exists G2185; exact T2185].
}
Qed.
Lemma reference_control_member_2186 : List.In (2186,reference_control_expr_2186) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 3%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2186_ground inputs path old current result :
 (exists value ground, VM.find 2169 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2185 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2186 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2169 H2185 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2186 reference_control_expr_2186 reference_control_1_positions reference_control_1_safety reference_control_member_2186) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2186 reference_control_expr_2186 inputs path old current result Position Safe Nonreg (reference_control_ready_2186 old H2169 H2185) Step).
Qed.
Theorem reference_control_node_2186_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2169 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2185 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2145 left = VM.find 2145 right ->
 VM.find 2169 left = VM.find 2169 right ->
 VM.find 2185 left = VM.find 2185 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2186 next_left = VM.find 2186 next_right.
Proof.
 intros H2169 H2185 E2145 E2169 E2185 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2186 reference_control_expr_2186 reference_control_1_positions reference_control_1_safety reference_control_member_2186) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2186 reference_control_expr_2186 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2186 left H2169 H2185)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2186 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2145.
 rewrite E2169.
 rewrite E2185.
 reflexivity.
Qed.
Lemma reference_control_ready_2187 old :
 (exists value ground, VM.find 2168 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2186 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2187.
Proof.
 intros H2168 H2186.
 destruct H2168 as [v2168 [G2168 [V2168 T2168]]].
 destruct H2186 as [v2186 [G2186 [V2186 T2186]]].
 unfold reference_control_expr_2187.
apply rc_mux.
{ eapply rc_ref; [exact V2168|exists G2168; exact T2168].
}
{ eapply rc_ref; [exact V2186|exists G2186; exact T2186].
}
Qed.
Lemma reference_control_member_2187 : List.In (2187,reference_control_expr_2187) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 4%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2187_ground inputs path old current result :
 (exists value ground, VM.find 2168 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2186 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2187 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2168 H2186 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2187 reference_control_expr_2187 reference_control_1_positions reference_control_1_safety reference_control_member_2187) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2187 reference_control_expr_2187 inputs path old current result Position Safe Nonreg (reference_control_ready_2187 old H2168 H2186) Step).
Qed.
Theorem reference_control_node_2187_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2168 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2186 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2145 left = VM.find 2145 right ->
 VM.find 2168 left = VM.find 2168 right ->
 VM.find 2186 left = VM.find 2186 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2187 next_left = VM.find 2187 next_right.
Proof.
 intros H2168 H2186 E2145 E2168 E2186 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2187 reference_control_expr_2187 reference_control_1_positions reference_control_1_safety reference_control_member_2187) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2187 reference_control_expr_2187 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2187 left H2168 H2186)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2187 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2145.
 rewrite E2168.
 rewrite E2186.
 reflexivity.
Qed.
Lemma reference_control_ready_2188 old :
 (exists value ground, VM.find 2167 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2187 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2188.
Proof.
 intros H2167 H2187.
 destruct H2167 as [v2167 [G2167 [V2167 T2167]]].
 destruct H2187 as [v2187 [G2187 [V2187 T2187]]].
 unfold reference_control_expr_2188.
apply rc_mux.
{ eapply rc_ref; [exact V2167|exists G2167; exact T2167].
}
{ eapply rc_ref; [exact V2187|exists G2187; exact T2187].
}
Qed.
Lemma reference_control_member_2188 : List.In (2188,reference_control_expr_2188) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 5%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2188_ground inputs path old current result :
 (exists value ground, VM.find 2167 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2187 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2188 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2167 H2187 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2188 reference_control_expr_2188 reference_control_1_positions reference_control_1_safety reference_control_member_2188) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2188 reference_control_expr_2188 inputs path old current result Position Safe Nonreg (reference_control_ready_2188 old H2167 H2187) Step).
Qed.
Theorem reference_control_node_2188_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2167 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2187 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2145 left = VM.find 2145 right ->
 VM.find 2167 left = VM.find 2167 right ->
 VM.find 2187 left = VM.find 2187 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2188 next_left = VM.find 2188 next_right.
Proof.
 intros H2167 H2187 E2145 E2167 E2187 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2188 reference_control_expr_2188 reference_control_1_positions reference_control_1_safety reference_control_member_2188) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2188 reference_control_expr_2188 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2188 left H2167 H2187)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2188 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2145.
 rewrite E2167.
 rewrite E2187.
 reflexivity.
Qed.
Lemma reference_control_ready_2189 old :
 (exists value ground, VM.find 2166 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2188 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2189.
Proof.
 intros H2166 H2188.
 destruct H2166 as [v2166 [G2166 [V2166 T2166]]].
 destruct H2188 as [v2188 [G2188 [V2188 T2188]]].
 unfold reference_control_expr_2189.
apply rc_mux.
{ eapply rc_ref; [exact V2166|exists G2166; exact T2166].
}
{ eapply rc_ref; [exact V2188|exists G2188; exact T2188].
}
Qed.
Lemma reference_control_member_2189 : List.In (2189,reference_control_expr_2189) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 6%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2189_ground inputs path old current result :
 (exists value ground, VM.find 2166 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2188 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2189 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2166 H2188 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2189 reference_control_expr_2189 reference_control_1_positions reference_control_1_safety reference_control_member_2189) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2189 reference_control_expr_2189 inputs path old current result Position Safe Nonreg (reference_control_ready_2189 old H2166 H2188) Step).
Qed.
Theorem reference_control_node_2189_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2166 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2188 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2145 left = VM.find 2145 right ->
 VM.find 2166 left = VM.find 2166 right ->
 VM.find 2188 left = VM.find 2188 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2189 next_left = VM.find 2189 next_right.
Proof.
 intros H2166 H2188 E2145 E2166 E2188 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2189 reference_control_expr_2189 reference_control_1_positions reference_control_1_safety reference_control_member_2189) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2189 reference_control_expr_2189 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2189 left H2166 H2188)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2189 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2145.
 rewrite E2166.
 rewrite E2188.
 reflexivity.
Qed.
Lemma reference_control_ready_2190 old :
 (exists value ground, VM.find 2165 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2189 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2190.
Proof.
 intros H2165 H2189.
 destruct H2165 as [v2165 [G2165 [V2165 T2165]]].
 destruct H2189 as [v2189 [G2189 [V2189 T2189]]].
 unfold reference_control_expr_2190.
apply rc_mux.
{ eapply rc_ref; [exact V2165|exists G2165; exact T2165].
}
{ eapply rc_ref; [exact V2189|exists G2189; exact T2189].
}
Qed.
Lemma reference_control_member_2190 : List.In (2190,reference_control_expr_2190) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 7%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2190_ground inputs path old current result :
 (exists value ground, VM.find 2165 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2189 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2190 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2165 H2189 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2190 reference_control_expr_2190 reference_control_1_positions reference_control_1_safety reference_control_member_2190) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2190 reference_control_expr_2190 inputs path old current result Position Safe Nonreg (reference_control_ready_2190 old H2165 H2189) Step).
Qed.
Theorem reference_control_node_2190_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2165 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2189 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2145 left = VM.find 2145 right ->
 VM.find 2165 left = VM.find 2165 right ->
 VM.find 2189 left = VM.find 2189 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2190 next_left = VM.find 2190 next_right.
Proof.
 intros H2165 H2189 E2145 E2165 E2189 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2190 reference_control_expr_2190 reference_control_1_positions reference_control_1_safety reference_control_member_2190) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2190 reference_control_expr_2190 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2190 left H2165 H2189)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2190 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2145.
 rewrite E2165.
 rewrite E2189.
 reflexivity.
Qed.
Lemma reference_control_ready_2191 old :
 (exists value ground, VM.find 2164 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2190 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2191.
Proof.
 intros H2164 H2190.
 destruct H2164 as [v2164 [G2164 [V2164 T2164]]].
 destruct H2190 as [v2190 [G2190 [V2190 T2190]]].
 unfold reference_control_expr_2191.
apply rc_mux.
{ eapply rc_ref; [exact V2164|exists G2164; exact T2164].
}
{ eapply rc_ref; [exact V2190|exists G2190; exact T2190].
}
Qed.
Lemma reference_control_member_2191 : List.In (2191,reference_control_expr_2191) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 8%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2191_ground inputs path old current result :
 (exists value ground, VM.find 2164 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2190 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2191 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2164 H2190 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2191 reference_control_expr_2191 reference_control_1_positions reference_control_1_safety reference_control_member_2191) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2191 reference_control_expr_2191 inputs path old current result Position Safe Nonreg (reference_control_ready_2191 old H2164 H2190) Step).
Qed.
Theorem reference_control_node_2191_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2164 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2190 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2145 left = VM.find 2145 right ->
 VM.find 2164 left = VM.find 2164 right ->
 VM.find 2190 left = VM.find 2190 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2191 next_left = VM.find 2191 next_right.
Proof.
 intros H2164 H2190 E2145 E2164 E2190 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2191 reference_control_expr_2191 reference_control_1_positions reference_control_1_safety reference_control_member_2191) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2191 reference_control_expr_2191 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2191 left H2164 H2190)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2191 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2145.
 rewrite E2164.
 rewrite E2190.
 reflexivity.
Qed.
Lemma reference_control_ready_2192 old :
 (exists value ground, VM.find 2163 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2191 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2192.
Proof.
 intros H2163 H2191.
 destruct H2163 as [v2163 [G2163 [V2163 T2163]]].
 destruct H2191 as [v2191 [G2191 [V2191 T2191]]].
 unfold reference_control_expr_2192.
apply rc_mux.
{ eapply rc_ref; [exact V2163|exists G2163; exact T2163].
}
{ eapply rc_ref; [exact V2191|exists G2191; exact T2191].
}
Qed.
Lemma reference_control_member_2192 : List.In (2192,reference_control_expr_2192) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 9%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2192_ground inputs path old current result :
 (exists value ground, VM.find 2163 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2191 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2192 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2163 H2191 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2192 reference_control_expr_2192 reference_control_1_positions reference_control_1_safety reference_control_member_2192) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2192 reference_control_expr_2192 inputs path old current result Position Safe Nonreg (reference_control_ready_2192 old H2163 H2191) Step).
Qed.
Theorem reference_control_node_2192_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2163 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2191 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2145 left = VM.find 2145 right ->
 VM.find 2163 left = VM.find 2163 right ->
 VM.find 2191 left = VM.find 2191 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2192 next_left = VM.find 2192 next_right.
Proof.
 intros H2163 H2191 E2145 E2163 E2191 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2192 reference_control_expr_2192 reference_control_1_positions reference_control_1_safety reference_control_member_2192) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2192 reference_control_expr_2192 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2192 left H2163 H2191)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2192 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2145.
 rewrite E2163.
 rewrite E2191.
 reflexivity.
Qed.
Lemma reference_control_ready_2193 old :
 (exists value ground, VM.find 2162 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2192 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2193.
Proof.
 intros H2162 H2192.
 destruct H2162 as [v2162 [G2162 [V2162 T2162]]].
 destruct H2192 as [v2192 [G2192 [V2192 T2192]]].
 unfold reference_control_expr_2193.
apply rc_mux.
{ eapply rc_ref; [exact V2162|exists G2162; exact T2162].
}
{ eapply rc_ref; [exact V2192|exists G2192; exact T2192].
}
Qed.
Lemma reference_control_member_2193 : List.In (2193,reference_control_expr_2193) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 10%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2193_ground inputs path old current result :
 (exists value ground, VM.find 2162 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2192 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2193 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2162 H2192 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2193 reference_control_expr_2193 reference_control_1_positions reference_control_1_safety reference_control_member_2193) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2193 reference_control_expr_2193 inputs path old current result Position Safe Nonreg (reference_control_ready_2193 old H2162 H2192) Step).
Qed.
Theorem reference_control_node_2193_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2162 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2192 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2145 left = VM.find 2145 right ->
 VM.find 2162 left = VM.find 2162 right ->
 VM.find 2192 left = VM.find 2192 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2193 next_left = VM.find 2193 next_right.
Proof.
 intros H2162 H2192 E2145 E2162 E2192 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2193 reference_control_expr_2193 reference_control_1_positions reference_control_1_safety reference_control_member_2193) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2193 reference_control_expr_2193 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2193 left H2162 H2192)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2193 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2145.
 rewrite E2162.
 rewrite E2192.
 reflexivity.
Qed.
Lemma reference_control_ready_2194 old :
 (exists value ground, VM.find 2161 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2193 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2194.
Proof.
 intros H2161 H2193.
 destruct H2161 as [v2161 [G2161 [V2161 T2161]]].
 destruct H2193 as [v2193 [G2193 [V2193 T2193]]].
 unfold reference_control_expr_2194.
apply rc_mux.
{ eapply rc_ref; [exact V2161|exists G2161; exact T2161].
}
{ eapply rc_ref; [exact V2193|exists G2193; exact T2193].
}
Qed.
Lemma reference_control_member_2194 : List.In (2194,reference_control_expr_2194) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 11%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2194_ground inputs path old current result :
 (exists value ground, VM.find 2161 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2193 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2194 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2161 H2193 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2194 reference_control_expr_2194 reference_control_1_positions reference_control_1_safety reference_control_member_2194) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2194 reference_control_expr_2194 inputs path old current result Position Safe Nonreg (reference_control_ready_2194 old H2161 H2193) Step).
Qed.
Theorem reference_control_node_2194_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2161 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2193 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2145 left = VM.find 2145 right ->
 VM.find 2161 left = VM.find 2161 right ->
 VM.find 2193 left = VM.find 2193 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2194 next_left = VM.find 2194 next_right.
Proof.
 intros H2161 H2193 E2145 E2161 E2193 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2194 reference_control_expr_2194 reference_control_1_positions reference_control_1_safety reference_control_member_2194) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2194 reference_control_expr_2194 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2194 left H2161 H2193)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2194 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2145.
 rewrite E2161.
 rewrite E2193.
 reflexivity.
Qed.
Lemma reference_control_ready_2195 old :
 (exists value ground, VM.find 2160 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2194 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2195.
Proof.
 intros H2160 H2194.
 destruct H2160 as [v2160 [G2160 [V2160 T2160]]].
 destruct H2194 as [v2194 [G2194 [V2194 T2194]]].
 unfold reference_control_expr_2195.
apply rc_mux.
{ eapply rc_ref; [exact V2160|exists G2160; exact T2160].
}
{ eapply rc_ref; [exact V2194|exists G2194; exact T2194].
}
Qed.
Lemma reference_control_member_2195 : List.In (2195,reference_control_expr_2195) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 12%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2195_ground inputs path old current result :
 (exists value ground, VM.find 2160 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2194 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2195 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2160 H2194 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2195 reference_control_expr_2195 reference_control_1_positions reference_control_1_safety reference_control_member_2195) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2195 reference_control_expr_2195 inputs path old current result Position Safe Nonreg (reference_control_ready_2195 old H2160 H2194) Step).
Qed.
Theorem reference_control_node_2195_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2160 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2194 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2145 left = VM.find 2145 right ->
 VM.find 2160 left = VM.find 2160 right ->
 VM.find 2194 left = VM.find 2194 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2195 next_left = VM.find 2195 next_right.
Proof.
 intros H2160 H2194 E2145 E2160 E2194 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2195 reference_control_expr_2195 reference_control_1_positions reference_control_1_safety reference_control_member_2195) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2195 reference_control_expr_2195 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2195 left H2160 H2194)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2195 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2145.
 rewrite E2160.
 rewrite E2194.
 reflexivity.
Qed.
Lemma reference_control_ready_2196 old :
 (exists value ground, VM.find 2159 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2195 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2196.
Proof.
 intros H2159 H2195.
 destruct H2159 as [v2159 [G2159 [V2159 T2159]]].
 destruct H2195 as [v2195 [G2195 [V2195 T2195]]].
 unfold reference_control_expr_2196.
apply rc_mux.
{ eapply rc_ref; [exact V2159|exists G2159; exact T2159].
}
{ eapply rc_ref; [exact V2195|exists G2195; exact T2195].
}
Qed.
Lemma reference_control_member_2196 : List.In (2196,reference_control_expr_2196) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 13%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2196_ground inputs path old current result :
 (exists value ground, VM.find 2159 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2195 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2196 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2159 H2195 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2196 reference_control_expr_2196 reference_control_1_positions reference_control_1_safety reference_control_member_2196) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2196 reference_control_expr_2196 inputs path old current result Position Safe Nonreg (reference_control_ready_2196 old H2159 H2195) Step).
Qed.
Theorem reference_control_node_2196_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2159 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2195 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2145 left = VM.find 2145 right ->
 VM.find 2159 left = VM.find 2159 right ->
 VM.find 2195 left = VM.find 2195 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2196 next_left = VM.find 2196 next_right.
Proof.
 intros H2159 H2195 E2145 E2159 E2195 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2196 reference_control_expr_2196 reference_control_1_positions reference_control_1_safety reference_control_member_2196) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2196 reference_control_expr_2196 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2196 left H2159 H2195)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2196 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2145.
 rewrite E2159.
 rewrite E2195.
 reflexivity.
Qed.
Lemma reference_control_ready_2197 old :
 (exists value ground, VM.find 2158 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2196 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2197.
Proof.
 intros H2158 H2196.
 destruct H2158 as [v2158 [G2158 [V2158 T2158]]].
 destruct H2196 as [v2196 [G2196 [V2196 T2196]]].
 unfold reference_control_expr_2197.
apply rc_mux.
{ eapply rc_ref; [exact V2158|exists G2158; exact T2158].
}
{ eapply rc_ref; [exact V2196|exists G2196; exact T2196].
}
Qed.
Lemma reference_control_member_2197 : List.In (2197,reference_control_expr_2197) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 14%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2197_ground inputs path old current result :
 (exists value ground, VM.find 2158 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2196 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2197 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2158 H2196 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2197 reference_control_expr_2197 reference_control_1_positions reference_control_1_safety reference_control_member_2197) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2197 reference_control_expr_2197 inputs path old current result Position Safe Nonreg (reference_control_ready_2197 old H2158 H2196) Step).
Qed.
Theorem reference_control_node_2197_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2158 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2196 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2145 left = VM.find 2145 right ->
 VM.find 2158 left = VM.find 2158 right ->
 VM.find 2196 left = VM.find 2196 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2197 next_left = VM.find 2197 next_right.
Proof.
 intros H2158 H2196 E2145 E2158 E2196 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2197 reference_control_expr_2197 reference_control_1_positions reference_control_1_safety reference_control_member_2197) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2197 reference_control_expr_2197 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2197 left H2158 H2196)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2197 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2145.
 rewrite E2158.
 rewrite E2196.
 reflexivity.
Qed.
Lemma reference_control_ready_2198 old :
 (exists value ground, VM.find 2157 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2197 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2198.
Proof.
 intros H2157 H2197.
 destruct H2157 as [v2157 [G2157 [V2157 T2157]]].
 destruct H2197 as [v2197 [G2197 [V2197 T2197]]].
 unfold reference_control_expr_2198.
apply rc_mux.
{ eapply rc_ref; [exact V2157|exists G2157; exact T2157].
}
{ eapply rc_ref; [exact V2197|exists G2197; exact T2197].
}
Qed.
Lemma reference_control_member_2198 : List.In (2198,reference_control_expr_2198) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 15%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2198_ground inputs path old current result :
 (exists value ground, VM.find 2157 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2197 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2198 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2157 H2197 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2198 reference_control_expr_2198 reference_control_1_positions reference_control_1_safety reference_control_member_2198) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2198 reference_control_expr_2198 inputs path old current result Position Safe Nonreg (reference_control_ready_2198 old H2157 H2197) Step).
Qed.
Theorem reference_control_node_2198_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2157 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2197 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2145 left = VM.find 2145 right ->
 VM.find 2157 left = VM.find 2157 right ->
 VM.find 2197 left = VM.find 2197 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2198 next_left = VM.find 2198 next_right.
Proof.
 intros H2157 H2197 E2145 E2157 E2197 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2198 reference_control_expr_2198 reference_control_1_positions reference_control_1_safety reference_control_member_2198) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2198 reference_control_expr_2198 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2198 left H2157 H2197)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2198 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2145.
 rewrite E2157.
 rewrite E2197.
 reflexivity.
Qed.
Lemma reference_control_ready_2199 old :
 (exists value ground, VM.find 2156 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2198 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2199.
Proof.
 intros H2156 H2198.
 destruct H2156 as [v2156 [G2156 [V2156 T2156]]].
 destruct H2198 as [v2198 [G2198 [V2198 T2198]]].
 unfold reference_control_expr_2199.
apply rc_mux.
{ eapply rc_ref; [exact V2156|exists G2156; exact T2156].
}
{ eapply rc_ref; [exact V2198|exists G2198; exact T2198].
}
Qed.
Lemma reference_control_member_2199 : List.In (2199,reference_control_expr_2199) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 16%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2199_ground inputs path old current result :
 (exists value ground, VM.find 2156 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2198 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2199 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2156 H2198 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2199 reference_control_expr_2199 reference_control_1_positions reference_control_1_safety reference_control_member_2199) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2199 reference_control_expr_2199 inputs path old current result Position Safe Nonreg (reference_control_ready_2199 old H2156 H2198) Step).
Qed.
Theorem reference_control_node_2199_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2156 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2198 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2145 left = VM.find 2145 right ->
 VM.find 2156 left = VM.find 2156 right ->
 VM.find 2198 left = VM.find 2198 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2199 next_left = VM.find 2199 next_right.
Proof.
 intros H2156 H2198 E2145 E2156 E2198 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2199 reference_control_expr_2199 reference_control_1_positions reference_control_1_safety reference_control_member_2199) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2199 reference_control_expr_2199 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2199 left H2156 H2198)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2199 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2145.
 rewrite E2156.
 rewrite E2198.
 reflexivity.
Qed.
Lemma reference_control_ready_2200 old :
 (exists value ground, VM.find 2155 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2199 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2200.
Proof.
 intros H2155 H2199.
 destruct H2155 as [v2155 [G2155 [V2155 T2155]]].
 destruct H2199 as [v2199 [G2199 [V2199 T2199]]].
 unfold reference_control_expr_2200.
apply rc_mux.
{ eapply rc_ref; [exact V2155|exists G2155; exact T2155].
}
{ eapply rc_ref; [exact V2199|exists G2199; exact T2199].
}
Qed.
Lemma reference_control_member_2200 : List.In (2200,reference_control_expr_2200) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 17%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2200_ground inputs path old current result :
 (exists value ground, VM.find 2155 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2199 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2200 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2155 H2199 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2200 reference_control_expr_2200 reference_control_1_positions reference_control_1_safety reference_control_member_2200) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2200 reference_control_expr_2200 inputs path old current result Position Safe Nonreg (reference_control_ready_2200 old H2155 H2199) Step).
Qed.
Theorem reference_control_node_2200_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2155 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2199 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2145 left = VM.find 2145 right ->
 VM.find 2155 left = VM.find 2155 right ->
 VM.find 2199 left = VM.find 2199 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2200 next_left = VM.find 2200 next_right.
Proof.
 intros H2155 H2199 E2145 E2155 E2199 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2200 reference_control_expr_2200 reference_control_1_positions reference_control_1_safety reference_control_member_2200) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2200 reference_control_expr_2200 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2200 left H2155 H2199)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2200 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2145.
 rewrite E2155.
 rewrite E2199.
 reflexivity.
Qed.
Lemma reference_control_ready_2201 old :
 (exists value ground, VM.find 2154 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2200 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2201.
Proof.
 intros H2154 H2200.
 destruct H2154 as [v2154 [G2154 [V2154 T2154]]].
 destruct H2200 as [v2200 [G2200 [V2200 T2200]]].
 unfold reference_control_expr_2201.
apply rc_mux.
{ eapply rc_ref; [exact V2154|exists G2154; exact T2154].
}
{ eapply rc_ref; [exact V2200|exists G2200; exact T2200].
}
Qed.
Lemma reference_control_member_2201 : List.In (2201,reference_control_expr_2201) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 18%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2201_ground inputs path old current result :
 (exists value ground, VM.find 2154 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2200 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2201 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2154 H2200 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2201 reference_control_expr_2201 reference_control_1_positions reference_control_1_safety reference_control_member_2201) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2201 reference_control_expr_2201 inputs path old current result Position Safe Nonreg (reference_control_ready_2201 old H2154 H2200) Step).
Qed.
Theorem reference_control_node_2201_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2154 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2200 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2145 left = VM.find 2145 right ->
 VM.find 2154 left = VM.find 2154 right ->
 VM.find 2200 left = VM.find 2200 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2201 next_left = VM.find 2201 next_right.
Proof.
 intros H2154 H2200 E2145 E2154 E2200 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2201 reference_control_expr_2201 reference_control_1_positions reference_control_1_safety reference_control_member_2201) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2201 reference_control_expr_2201 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2201 left H2154 H2200)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2201 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2145.
 rewrite E2154.
 rewrite E2200.
 reflexivity.
Qed.
Lemma reference_control_ready_2202 old :
 (exists value ground, VM.find 2153 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2201 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2202.
Proof.
 intros H2153 H2201.
 destruct H2153 as [v2153 [G2153 [V2153 T2153]]].
 destruct H2201 as [v2201 [G2201 [V2201 T2201]]].
 unfold reference_control_expr_2202.
apply rc_mux.
{ eapply rc_ref; [exact V2153|exists G2153; exact T2153].
}
{ eapply rc_ref; [exact V2201|exists G2201; exact T2201].
}
Qed.
Lemma reference_control_member_2202 : List.In (2202,reference_control_expr_2202) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 19%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2202_ground inputs path old current result :
 (exists value ground, VM.find 2153 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2201 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2202 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2153 H2201 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2202 reference_control_expr_2202 reference_control_1_positions reference_control_1_safety reference_control_member_2202) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2202 reference_control_expr_2202 inputs path old current result Position Safe Nonreg (reference_control_ready_2202 old H2153 H2201) Step).
Qed.
Theorem reference_control_node_2202_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2153 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2201 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2145 left = VM.find 2145 right ->
 VM.find 2153 left = VM.find 2153 right ->
 VM.find 2201 left = VM.find 2201 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2202 next_left = VM.find 2202 next_right.
Proof.
 intros H2153 H2201 E2145 E2153 E2201 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2202 reference_control_expr_2202 reference_control_1_positions reference_control_1_safety reference_control_member_2202) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2202 reference_control_expr_2202 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2202 left H2153 H2201)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2202 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2145.
 rewrite E2153.
 rewrite E2201.
 reflexivity.
Qed.
Lemma reference_control_ready_2203 old :
 (exists value ground, VM.find 2152 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2202 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2203.
Proof.
 intros H2152 H2202.
 destruct H2152 as [v2152 [G2152 [V2152 T2152]]].
 destruct H2202 as [v2202 [G2202 [V2202 T2202]]].
 unfold reference_control_expr_2203.
apply rc_mux.
{ eapply rc_ref; [exact V2152|exists G2152; exact T2152].
}
{ eapply rc_ref; [exact V2202|exists G2202; exact T2202].
}
Qed.
Lemma reference_control_member_2203 : List.In (2203,reference_control_expr_2203) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 20%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2203_ground inputs path old current result :
 (exists value ground, VM.find 2152 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2202 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2203 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2152 H2202 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2203 reference_control_expr_2203 reference_control_1_positions reference_control_1_safety reference_control_member_2203) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2203 reference_control_expr_2203 inputs path old current result Position Safe Nonreg (reference_control_ready_2203 old H2152 H2202) Step).
Qed.
Theorem reference_control_node_2203_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2152 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2202 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2145 left = VM.find 2145 right ->
 VM.find 2152 left = VM.find 2152 right ->
 VM.find 2202 left = VM.find 2202 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2203 next_left = VM.find 2203 next_right.
Proof.
 intros H2152 H2202 E2145 E2152 E2202 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2203 reference_control_expr_2203 reference_control_1_positions reference_control_1_safety reference_control_member_2203) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2203 reference_control_expr_2203 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2203 left H2152 H2202)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2203 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2145.
 rewrite E2152.
 rewrite E2202.
 reflexivity.
Qed.
Lemma reference_control_ready_2204 old :
 (exists value ground, VM.find 2151 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2203 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2204.
Proof.
 intros H2151 H2203.
 destruct H2151 as [v2151 [G2151 [V2151 T2151]]].
 destruct H2203 as [v2203 [G2203 [V2203 T2203]]].
 unfold reference_control_expr_2204.
apply rc_mux.
{ eapply rc_ref; [exact V2151|exists G2151; exact T2151].
}
{ eapply rc_ref; [exact V2203|exists G2203; exact T2203].
}
Qed.
Lemma reference_control_member_2204 : List.In (2204,reference_control_expr_2204) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 21%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2204_ground inputs path old current result :
 (exists value ground, VM.find 2151 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2203 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2204 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2151 H2203 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2204 reference_control_expr_2204 reference_control_1_positions reference_control_1_safety reference_control_member_2204) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2204 reference_control_expr_2204 inputs path old current result Position Safe Nonreg (reference_control_ready_2204 old H2151 H2203) Step).
Qed.
Theorem reference_control_node_2204_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2151 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2203 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2145 left = VM.find 2145 right ->
 VM.find 2151 left = VM.find 2151 right ->
 VM.find 2203 left = VM.find 2203 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2204 next_left = VM.find 2204 next_right.
Proof.
 intros H2151 H2203 E2145 E2151 E2203 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2204 reference_control_expr_2204 reference_control_1_positions reference_control_1_safety reference_control_member_2204) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2204 reference_control_expr_2204 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2204 left H2151 H2203)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2204 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2145.
 rewrite E2151.
 rewrite E2203.
 reflexivity.
Qed.
Lemma reference_control_ready_2205 old :
 (exists value ground, VM.find 2150 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2204 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2205.
Proof.
 intros H2150 H2204.
 destruct H2150 as [v2150 [G2150 [V2150 T2150]]].
 destruct H2204 as [v2204 [G2204 [V2204 T2204]]].
 unfold reference_control_expr_2205.
apply rc_mux.
{ eapply rc_ref; [exact V2150|exists G2150; exact T2150].
}
{ eapply rc_ref; [exact V2204|exists G2204; exact T2204].
}
Qed.
Lemma reference_control_member_2205 : List.In (2205,reference_control_expr_2205) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 22%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2205_ground inputs path old current result :
 (exists value ground, VM.find 2150 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2204 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2205 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2150 H2204 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2205 reference_control_expr_2205 reference_control_1_positions reference_control_1_safety reference_control_member_2205) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2205 reference_control_expr_2205 inputs path old current result Position Safe Nonreg (reference_control_ready_2205 old H2150 H2204) Step).
Qed.
Theorem reference_control_node_2205_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2150 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2204 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2145 left = VM.find 2145 right ->
 VM.find 2150 left = VM.find 2150 right ->
 VM.find 2204 left = VM.find 2204 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2205 next_left = VM.find 2205 next_right.
Proof.
 intros H2150 H2204 E2145 E2150 E2204 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2205 reference_control_expr_2205 reference_control_1_positions reference_control_1_safety reference_control_member_2205) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2205 reference_control_expr_2205 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2205 left H2150 H2204)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2205 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2145.
 rewrite E2150.
 rewrite E2204.
 reflexivity.
Qed.
Lemma reference_control_ready_2206 old :
 (exists value ground, VM.find 2149 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2205 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2206.
Proof.
 intros H2149 H2205.
 destruct H2149 as [v2149 [G2149 [V2149 T2149]]].
 destruct H2205 as [v2205 [G2205 [V2205 T2205]]].
 unfold reference_control_expr_2206.
apply rc_mux.
{ eapply rc_ref; [exact V2149|exists G2149; exact T2149].
}
{ eapply rc_ref; [exact V2205|exists G2205; exact T2205].
}
Qed.
Lemma reference_control_member_2206 : List.In (2206,reference_control_expr_2206) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 23%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2206_ground inputs path old current result :
 (exists value ground, VM.find 2149 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2205 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2206 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2149 H2205 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2206 reference_control_expr_2206 reference_control_1_positions reference_control_1_safety reference_control_member_2206) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2206 reference_control_expr_2206 inputs path old current result Position Safe Nonreg (reference_control_ready_2206 old H2149 H2205) Step).
Qed.
Theorem reference_control_node_2206_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2149 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2205 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2145 left = VM.find 2145 right ->
 VM.find 2149 left = VM.find 2149 right ->
 VM.find 2205 left = VM.find 2205 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2206 next_left = VM.find 2206 next_right.
Proof.
 intros H2149 H2205 E2145 E2149 E2205 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2206 reference_control_expr_2206 reference_control_1_positions reference_control_1_safety reference_control_member_2206) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2206 reference_control_expr_2206 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2206 left H2149 H2205)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2206 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2145.
 rewrite E2149.
 rewrite E2205.
 reflexivity.
Qed.
Lemma reference_control_ready_2207 old :
 (exists value ground, VM.find 2148 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2206 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2207.
Proof.
 intros H2148 H2206.
 destruct H2148 as [v2148 [G2148 [V2148 T2148]]].
 destruct H2206 as [v2206 [G2206 [V2206 T2206]]].
 unfold reference_control_expr_2207.
apply rc_mux.
{ eapply rc_ref; [exact V2148|exists G2148; exact T2148].
}
{ eapply rc_ref; [exact V2206|exists G2206; exact T2206].
}
Qed.
Lemma reference_control_member_2207 : List.In (2207,reference_control_expr_2207) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 24%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2207_ground inputs path old current result :
 (exists value ground, VM.find 2148 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2206 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2207 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2148 H2206 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2207 reference_control_expr_2207 reference_control_1_positions reference_control_1_safety reference_control_member_2207) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2207 reference_control_expr_2207 inputs path old current result Position Safe Nonreg (reference_control_ready_2207 old H2148 H2206) Step).
Qed.
Theorem reference_control_node_2207_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2148 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2206 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2145 left = VM.find 2145 right ->
 VM.find 2148 left = VM.find 2148 right ->
 VM.find 2206 left = VM.find 2206 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2207 next_left = VM.find 2207 next_right.
Proof.
 intros H2148 H2206 E2145 E2148 E2206 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2207 reference_control_expr_2207 reference_control_1_positions reference_control_1_safety reference_control_member_2207) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2207 reference_control_expr_2207 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2207 left H2148 H2206)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2207 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2145.
 rewrite E2148.
 rewrite E2206.
 reflexivity.
Qed.
Lemma reference_control_ready_2208 old :
 (exists value ground, VM.find 2147 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2207 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2208.
Proof.
 intros H2147 H2207.
 destruct H2147 as [v2147 [G2147 [V2147 T2147]]].
 destruct H2207 as [v2207 [G2207 [V2207 T2207]]].
 unfold reference_control_expr_2208.
apply rc_mux.
{ eapply rc_ref; [exact V2147|exists G2147; exact T2147].
}
{ eapply rc_ref; [exact V2207|exists G2207; exact T2207].
}
Qed.
Lemma reference_control_member_2208 : List.In (2208,reference_control_expr_2208) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 25%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2208_ground inputs path old current result :
 (exists value ground, VM.find 2147 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2207 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2208 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2147 H2207 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2208 reference_control_expr_2208 reference_control_1_positions reference_control_1_safety reference_control_member_2208) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2208 reference_control_expr_2208 inputs path old current result Position Safe Nonreg (reference_control_ready_2208 old H2147 H2207) Step).
Qed.
Theorem reference_control_node_2208_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2147 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2207 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2145 left = VM.find 2145 right ->
 VM.find 2147 left = VM.find 2147 right ->
 VM.find 2207 left = VM.find 2207 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2208 next_left = VM.find 2208 next_right.
Proof.
 intros H2147 H2207 E2145 E2147 E2207 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2208 reference_control_expr_2208 reference_control_1_positions reference_control_1_safety reference_control_member_2208) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2208 reference_control_expr_2208 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2208 left H2147 H2207)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2208 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2145.
 rewrite E2147.
 rewrite E2207.
 reflexivity.
Qed.
Lemma reference_control_ready_2209 old :
 (exists value ground, VM.find 2146 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2208 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2209.
Proof.
 intros H2146 H2208.
 destruct H2146 as [v2146 [G2146 [V2146 T2146]]].
 destruct H2208 as [v2208 [G2208 [V2208 T2208]]].
 unfold reference_control_expr_2209.
apply rc_mux.
{ eapply rc_ref; [exact V2146|exists G2146; exact T2146].
}
{ eapply rc_ref; [exact V2208|exists G2208; exact T2208].
}
Qed.
Lemma reference_control_member_2209 : List.In (2209,reference_control_expr_2209) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 26%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2209_ground inputs path old current result :
 (exists value ground, VM.find 2146 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2208 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2209 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2146 H2208 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2209 reference_control_expr_2209 reference_control_1_positions reference_control_1_safety reference_control_member_2209) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2209 reference_control_expr_2209 inputs path old current result Position Safe Nonreg (reference_control_ready_2209 old H2146 H2208) Step).
Qed.
Theorem reference_control_node_2209_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2146 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2208 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2145 left = VM.find 2145 right ->
 VM.find 2146 left = VM.find 2146 right ->
 VM.find 2208 left = VM.find 2208 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2209 next_left = VM.find 2209 next_right.
Proof.
 intros H2146 H2208 E2145 E2146 E2208 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2209 reference_control_expr_2209 reference_control_1_positions reference_control_1_safety reference_control_member_2209) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2209 reference_control_expr_2209 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2209 left H2146 H2208)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2209 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2145.
 rewrite E2146.
 rewrite E2208.
 reflexivity.
Qed.
Lemma reference_control_ready_2210 old :
 (exists value ground, VM.find 2209 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2210.
Proof.
 intros H2209.
 destruct H2209 as [v2209 [G2209 [V2209 T2209]]].
 unfold reference_control_expr_2210.
eapply rc_ref; [exact V2209|exists G2209; exact T2209].
Qed.
Lemma reference_control_member_2210 : List.In (2210,reference_control_expr_2210) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 27%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2210_ground inputs path old current result :
 (exists value ground, VM.find 2209 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2210 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2209 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2210 reference_control_expr_2210 reference_control_1_positions reference_control_1_safety reference_control_member_2210) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2210 reference_control_expr_2210 inputs path old current result Position Safe Nonreg (reference_control_ready_2210 old H2209) Step).
Qed.
Theorem reference_control_node_2210_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2209 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2209 left = VM.find 2209 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2210 next_left = VM.find 2210 next_right.
Proof.
 intros H2209 E2209 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2210 reference_control_expr_2210 reference_control_1_positions reference_control_1_safety reference_control_member_2210) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2210 reference_control_expr_2210 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2210 left H2209)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2210 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2209.
 reflexivity.
Qed.
Lemma reference_control_ready_2211 old :
 reference_control_ready old reference_control_expr_2211.
Proof.
 unfold reference_control_expr_2211.
apply rc_unary.
Qed.
Lemma reference_control_member_2211 : List.In (2211,reference_control_expr_2211) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 28%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2211_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2211 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2211 reference_control_expr_2211 reference_control_1_positions reference_control_1_safety reference_control_member_2211) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2211 reference_control_expr_2211 inputs path old current result Position Safe Nonreg (reference_control_ready_2211 old ) Step).
Qed.
Theorem reference_control_node_2211_congruent inputs path left right next_left next_right :
 VM.find 1884 left = VM.find 1884 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2211 next_left = VM.find 2211 next_right.
Proof.
 intros  E1884 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2211 reference_control_expr_2211 reference_control_1_positions reference_control_1_safety reference_control_member_2211) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2211 reference_control_expr_2211 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2211 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2211 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1884.
 reflexivity.
Qed.
Lemma reference_control_ready_2212 old :
 reference_control_ready old reference_control_expr_2212.
Proof.
 unfold reference_control_expr_2212.
apply rc_unary.
Qed.
Lemma reference_control_member_2212 : List.In (2212,reference_control_expr_2212) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 29%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2212_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2212 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2212 reference_control_expr_2212 reference_control_1_positions reference_control_1_safety reference_control_member_2212) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2212 reference_control_expr_2212 inputs path old current result Position Safe Nonreg (reference_control_ready_2212 old ) Step).
Qed.
Theorem reference_control_node_2212_congruent inputs path left right next_left next_right :
 VM.find 1884 left = VM.find 1884 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2212 next_left = VM.find 2212 next_right.
Proof.
 intros  E1884 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2212 reference_control_expr_2212 reference_control_1_positions reference_control_1_safety reference_control_member_2212) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2212 reference_control_expr_2212 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2212 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2212 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1884.
 reflexivity.
Qed.
Lemma reference_control_ready_2213 old :
 reference_control_ready old reference_control_expr_2213.
Proof.
 unfold reference_control_expr_2213.
apply rc_unary.
Qed.
Lemma reference_control_member_2213 : List.In (2213,reference_control_expr_2213) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 30%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2213_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2213 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2213 reference_control_expr_2213 reference_control_1_positions reference_control_1_safety reference_control_member_2213) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2213 reference_control_expr_2213 inputs path old current result Position Safe Nonreg (reference_control_ready_2213 old ) Step).
Qed.
Theorem reference_control_node_2213_congruent inputs path left right next_left next_right :
 VM.find 1884 left = VM.find 1884 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2213 next_left = VM.find 2213 next_right.
Proof.
 intros  E1884 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2213 reference_control_expr_2213 reference_control_1_positions reference_control_1_safety reference_control_member_2213) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2213 reference_control_expr_2213 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2213 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2213 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1884.
 reflexivity.
Qed.
Lemma reference_control_ready_2214 old :
 reference_control_ready old reference_control_expr_2214.
Proof.
 unfold reference_control_expr_2214.
apply rc_unary.
Qed.
Lemma reference_control_member_2214 : List.In (2214,reference_control_expr_2214) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 31%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2214_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2214 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2214 reference_control_expr_2214 reference_control_1_positions reference_control_1_safety reference_control_member_2214) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2214 reference_control_expr_2214 inputs path old current result Position Safe Nonreg (reference_control_ready_2214 old ) Step).
Qed.
Theorem reference_control_node_2214_congruent inputs path left right next_left next_right :
 VM.find 1884 left = VM.find 1884 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2214 next_left = VM.find 2214 next_right.
Proof.
 intros  E1884 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2214 reference_control_expr_2214 reference_control_1_positions reference_control_1_safety reference_control_member_2214) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2214 reference_control_expr_2214 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2214 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2214 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1884.
 reflexivity.
Qed.
Lemma reference_control_ready_2215 old :
 reference_control_ready old reference_control_expr_2215.
Proof.
 unfold reference_control_expr_2215.
apply rc_unary.
Qed.
Lemma reference_control_member_2215 : List.In (2215,reference_control_expr_2215) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 32%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2215_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2215 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2215 reference_control_expr_2215 reference_control_1_positions reference_control_1_safety reference_control_member_2215) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2215 reference_control_expr_2215 inputs path old current result Position Safe Nonreg (reference_control_ready_2215 old ) Step).
Qed.
Theorem reference_control_node_2215_congruent inputs path left right next_left next_right :
 VM.find 1884 left = VM.find 1884 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2215 next_left = VM.find 2215 next_right.
Proof.
 intros  E1884 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2215 reference_control_expr_2215 reference_control_1_positions reference_control_1_safety reference_control_member_2215) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2215 reference_control_expr_2215 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2215 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2215 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1884.
 reflexivity.
Qed.
Lemma reference_control_ready_2216 old :
 reference_control_ready old reference_control_expr_2216.
Proof.
 unfold reference_control_expr_2216.
apply rc_unary.
Qed.
Lemma reference_control_member_2216 : List.In (2216,reference_control_expr_2216) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 33%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2216_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2216 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2216 reference_control_expr_2216 reference_control_1_positions reference_control_1_safety reference_control_member_2216) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2216 reference_control_expr_2216 inputs path old current result Position Safe Nonreg (reference_control_ready_2216 old ) Step).
Qed.
Theorem reference_control_node_2216_congruent inputs path left right next_left next_right :
 VM.find 1884 left = VM.find 1884 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2216 next_left = VM.find 2216 next_right.
Proof.
 intros  E1884 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2216 reference_control_expr_2216 reference_control_1_positions reference_control_1_safety reference_control_member_2216) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2216 reference_control_expr_2216 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2216 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2216 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1884.
 reflexivity.
Qed.
Lemma reference_control_ready_2217 old :
 reference_control_ready old reference_control_expr_2217.
Proof.
 unfold reference_control_expr_2217.
apply rc_unary.
Qed.
Lemma reference_control_member_2217 : List.In (2217,reference_control_expr_2217) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 34%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2217_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2217 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2217 reference_control_expr_2217 reference_control_1_positions reference_control_1_safety reference_control_member_2217) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2217 reference_control_expr_2217 inputs path old current result Position Safe Nonreg (reference_control_ready_2217 old ) Step).
Qed.
Theorem reference_control_node_2217_congruent inputs path left right next_left next_right :
 VM.find 1884 left = VM.find 1884 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2217 next_left = VM.find 2217 next_right.
Proof.
 intros  E1884 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2217 reference_control_expr_2217 reference_control_1_positions reference_control_1_safety reference_control_member_2217) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2217 reference_control_expr_2217 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2217 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2217 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1884.
 reflexivity.
Qed.
Lemma reference_control_ready_2218 old :
 reference_control_ready old reference_control_expr_2218.
Proof.
 unfold reference_control_expr_2218.
apply rc_unary.
Qed.
Lemma reference_control_member_2218 : List.In (2218,reference_control_expr_2218) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 35%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2218_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2218 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2218 reference_control_expr_2218 reference_control_1_positions reference_control_1_safety reference_control_member_2218) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2218 reference_control_expr_2218 inputs path old current result Position Safe Nonreg (reference_control_ready_2218 old ) Step).
Qed.
Theorem reference_control_node_2218_congruent inputs path left right next_left next_right :
 VM.find 1884 left = VM.find 1884 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2218 next_left = VM.find 2218 next_right.
Proof.
 intros  E1884 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2218 reference_control_expr_2218 reference_control_1_positions reference_control_1_safety reference_control_member_2218) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2218 reference_control_expr_2218 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2218 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2218 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1884.
 reflexivity.
Qed.
Lemma reference_control_ready_2219 old :
 reference_control_ready old reference_control_expr_2219.
Proof.
 unfold reference_control_expr_2219.
apply rc_unary.
Qed.
Lemma reference_control_member_2219 : List.In (2219,reference_control_expr_2219) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 36%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2219_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2219 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2219 reference_control_expr_2219 reference_control_1_positions reference_control_1_safety reference_control_member_2219) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2219 reference_control_expr_2219 inputs path old current result Position Safe Nonreg (reference_control_ready_2219 old ) Step).
Qed.
Theorem reference_control_node_2219_congruent inputs path left right next_left next_right :
 VM.find 1884 left = VM.find 1884 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2219 next_left = VM.find 2219 next_right.
Proof.
 intros  E1884 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2219 reference_control_expr_2219 reference_control_1_positions reference_control_1_safety reference_control_member_2219) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2219 reference_control_expr_2219 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2219 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2219 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1884.
 reflexivity.
Qed.
Lemma reference_control_ready_2220 old :
 reference_control_ready old reference_control_expr_2220.
Proof.
 unfold reference_control_expr_2220.
apply rc_unary.
Qed.
Lemma reference_control_member_2220 : List.In (2220,reference_control_expr_2220) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 37%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2220_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2220 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2220 reference_control_expr_2220 reference_control_1_positions reference_control_1_safety reference_control_member_2220) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2220 reference_control_expr_2220 inputs path old current result Position Safe Nonreg (reference_control_ready_2220 old ) Step).
Qed.
Theorem reference_control_node_2220_congruent inputs path left right next_left next_right :
 VM.find 1884 left = VM.find 1884 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2220 next_left = VM.find 2220 next_right.
Proof.
 intros  E1884 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2220 reference_control_expr_2220 reference_control_1_positions reference_control_1_safety reference_control_member_2220) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2220 reference_control_expr_2220 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2220 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2220 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1884.
 reflexivity.
Qed.
Lemma reference_control_ready_2221 old :
 reference_control_ready old reference_control_expr_2221.
Proof.
 unfold reference_control_expr_2221.
apply rc_unary.
Qed.
Lemma reference_control_member_2221 : List.In (2221,reference_control_expr_2221) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 38%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2221_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2221 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2221 reference_control_expr_2221 reference_control_1_positions reference_control_1_safety reference_control_member_2221) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2221 reference_control_expr_2221 inputs path old current result Position Safe Nonreg (reference_control_ready_2221 old ) Step).
Qed.
Theorem reference_control_node_2221_congruent inputs path left right next_left next_right :
 VM.find 1884 left = VM.find 1884 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2221 next_left = VM.find 2221 next_right.
Proof.
 intros  E1884 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2221 reference_control_expr_2221 reference_control_1_positions reference_control_1_safety reference_control_member_2221) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2221 reference_control_expr_2221 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2221 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2221 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1884.
 reflexivity.
Qed.
Lemma reference_control_ready_2222 old :
 reference_control_ready old reference_control_expr_2222.
Proof.
 unfold reference_control_expr_2222.
apply rc_unary.
Qed.
Lemma reference_control_member_2222 : List.In (2222,reference_control_expr_2222) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 39%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2222_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2222 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2222 reference_control_expr_2222 reference_control_1_positions reference_control_1_safety reference_control_member_2222) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2222 reference_control_expr_2222 inputs path old current result Position Safe Nonreg (reference_control_ready_2222 old ) Step).
Qed.
Theorem reference_control_node_2222_congruent inputs path left right next_left next_right :
 VM.find 1884 left = VM.find 1884 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2222 next_left = VM.find 2222 next_right.
Proof.
 intros  E1884 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2222 reference_control_expr_2222 reference_control_1_positions reference_control_1_safety reference_control_member_2222) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2222 reference_control_expr_2222 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2222 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2222 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1884.
 reflexivity.
Qed.
Lemma reference_control_ready_2223 old :
 reference_control_ready old reference_control_expr_2223.
Proof.
 unfold reference_control_expr_2223.
apply rc_unary.
Qed.
Lemma reference_control_member_2223 : List.In (2223,reference_control_expr_2223) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 40%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2223_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2223 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2223 reference_control_expr_2223 reference_control_1_positions reference_control_1_safety reference_control_member_2223) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2223 reference_control_expr_2223 inputs path old current result Position Safe Nonreg (reference_control_ready_2223 old ) Step).
Qed.
Theorem reference_control_node_2223_congruent inputs path left right next_left next_right :
 VM.find 1884 left = VM.find 1884 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2223 next_left = VM.find 2223 next_right.
Proof.
 intros  E1884 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2223 reference_control_expr_2223 reference_control_1_positions reference_control_1_safety reference_control_member_2223) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2223 reference_control_expr_2223 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2223 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2223 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1884.
 reflexivity.
Qed.
Lemma reference_control_ready_2224 old :
 reference_control_ready old reference_control_expr_2224.
Proof.
 unfold reference_control_expr_2224.
apply rc_unary.
Qed.
Lemma reference_control_member_2224 : List.In (2224,reference_control_expr_2224) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 41%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2224_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2224 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2224 reference_control_expr_2224 reference_control_1_positions reference_control_1_safety reference_control_member_2224) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2224 reference_control_expr_2224 inputs path old current result Position Safe Nonreg (reference_control_ready_2224 old ) Step).
Qed.
Theorem reference_control_node_2224_congruent inputs path left right next_left next_right :
 VM.find 1884 left = VM.find 1884 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2224 next_left = VM.find 2224 next_right.
Proof.
 intros  E1884 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2224 reference_control_expr_2224 reference_control_1_positions reference_control_1_safety reference_control_member_2224) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2224 reference_control_expr_2224 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2224 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2224 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1884.
 reflexivity.
Qed.
Lemma reference_control_ready_2225 old :
 reference_control_ready old reference_control_expr_2225.
Proof.
 unfold reference_control_expr_2225.
apply rc_unary.
Qed.
Lemma reference_control_member_2225 : List.In (2225,reference_control_expr_2225) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 42%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2225_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2225 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2225 reference_control_expr_2225 reference_control_1_positions reference_control_1_safety reference_control_member_2225) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2225 reference_control_expr_2225 inputs path old current result Position Safe Nonreg (reference_control_ready_2225 old ) Step).
Qed.
Theorem reference_control_node_2225_congruent inputs path left right next_left next_right :
 VM.find 1884 left = VM.find 1884 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2225 next_left = VM.find 2225 next_right.
Proof.
 intros  E1884 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2225 reference_control_expr_2225 reference_control_1_positions reference_control_1_safety reference_control_member_2225) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2225 reference_control_expr_2225 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2225 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2225 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1884.
 reflexivity.
Qed.
Lemma reference_control_ready_2226 old :
 reference_control_ready old reference_control_expr_2226.
Proof.
 unfold reference_control_expr_2226.
apply rc_unary.
Qed.
Lemma reference_control_member_2226 : List.In (2226,reference_control_expr_2226) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 43%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2226_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2226 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2226 reference_control_expr_2226 reference_control_1_positions reference_control_1_safety reference_control_member_2226) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2226 reference_control_expr_2226 inputs path old current result Position Safe Nonreg (reference_control_ready_2226 old ) Step).
Qed.
Theorem reference_control_node_2226_congruent inputs path left right next_left next_right :
 VM.find 1884 left = VM.find 1884 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2226 next_left = VM.find 2226 next_right.
Proof.
 intros  E1884 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2226 reference_control_expr_2226 reference_control_1_positions reference_control_1_safety reference_control_member_2226) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2226 reference_control_expr_2226 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2226 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2226 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1884.
 reflexivity.
Qed.
Lemma reference_control_ready_2227 old :
 reference_control_ready old reference_control_expr_2227.
Proof.
 unfold reference_control_expr_2227.
apply rc_unary.
Qed.
Lemma reference_control_member_2227 : List.In (2227,reference_control_expr_2227) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 44%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2227_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2227 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2227 reference_control_expr_2227 reference_control_1_positions reference_control_1_safety reference_control_member_2227) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2227 reference_control_expr_2227 inputs path old current result Position Safe Nonreg (reference_control_ready_2227 old ) Step).
Qed.
Theorem reference_control_node_2227_congruent inputs path left right next_left next_right :
 VM.find 1884 left = VM.find 1884 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2227 next_left = VM.find 2227 next_right.
Proof.
 intros  E1884 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2227 reference_control_expr_2227 reference_control_1_positions reference_control_1_safety reference_control_member_2227) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2227 reference_control_expr_2227 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2227 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2227 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1884.
 reflexivity.
Qed.
Lemma reference_control_ready_2228 old :
 reference_control_ready old reference_control_expr_2228.
Proof.
 unfold reference_control_expr_2228.
apply rc_unary.
Qed.
Lemma reference_control_member_2228 : List.In (2228,reference_control_expr_2228) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 45%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2228_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2228 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2228 reference_control_expr_2228 reference_control_1_positions reference_control_1_safety reference_control_member_2228) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2228 reference_control_expr_2228 inputs path old current result Position Safe Nonreg (reference_control_ready_2228 old ) Step).
Qed.
Theorem reference_control_node_2228_congruent inputs path left right next_left next_right :
 VM.find 1884 left = VM.find 1884 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2228 next_left = VM.find 2228 next_right.
Proof.
 intros  E1884 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2228 reference_control_expr_2228 reference_control_1_positions reference_control_1_safety reference_control_member_2228) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2228 reference_control_expr_2228 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2228 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2228 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1884.
 reflexivity.
Qed.
Lemma reference_control_ready_2229 old :
 (exists value ground, VM.find 2228 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2229.
Proof.
 intros H2228.
 destruct H2228 as [v2228 [G2228 [V2228 T2228]]].
 unfold reference_control_expr_2229.
apply rc_mux.
{ eapply rc_ref; [exact V2228|exists G2228; exact T2228].
}
{ apply rc_const.
}
Qed.
Lemma reference_control_member_2229 : List.In (2229,reference_control_expr_2229) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 46%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2229_ground inputs path old current result :
 (exists value ground, VM.find 2228 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2229 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2228 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2229 reference_control_expr_2229 reference_control_1_positions reference_control_1_safety reference_control_member_2229) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2229 reference_control_expr_2229 inputs path old current result Position Safe Nonreg (reference_control_ready_2229 old H2228) Step).
Qed.
Theorem reference_control_node_2229_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2228 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2096 left = VM.find 2096 right ->
 VM.find 2228 left = VM.find 2228 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2229 next_left = VM.find 2229 next_right.
Proof.
 intros H2228 E2096 E2228 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2229 reference_control_expr_2229 reference_control_1_positions reference_control_1_safety reference_control_member_2229) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2229 reference_control_expr_2229 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2229 left H2228)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2229 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2096.
 rewrite E2228.
 reflexivity.
Qed.
Lemma reference_control_ready_2230 old :
 (exists value ground, VM.find 2227 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2229 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2230.
Proof.
 intros H2227 H2229.
 destruct H2227 as [v2227 [G2227 [V2227 T2227]]].
 destruct H2229 as [v2229 [G2229 [V2229 T2229]]].
 unfold reference_control_expr_2230.
apply rc_mux.
{ eapply rc_ref; [exact V2227|exists G2227; exact T2227].
}
{ eapply rc_ref; [exact V2229|exists G2229; exact T2229].
}
Qed.
Lemma reference_control_member_2230 : List.In (2230,reference_control_expr_2230) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 47%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2230_ground inputs path old current result :
 (exists value ground, VM.find 2227 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2229 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2230 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2227 H2229 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2230 reference_control_expr_2230 reference_control_1_positions reference_control_1_safety reference_control_member_2230) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2230 reference_control_expr_2230 inputs path old current result Position Safe Nonreg (reference_control_ready_2230 old H2227 H2229) Step).
Qed.
Theorem reference_control_node_2230_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2227 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2229 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2092 left = VM.find 2092 right ->
 VM.find 2227 left = VM.find 2227 right ->
 VM.find 2229 left = VM.find 2229 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2230 next_left = VM.find 2230 next_right.
Proof.
 intros H2227 H2229 E2092 E2227 E2229 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2230 reference_control_expr_2230 reference_control_1_positions reference_control_1_safety reference_control_member_2230) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2230 reference_control_expr_2230 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2230 left H2227 H2229)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2230 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2092.
 rewrite E2227.
 rewrite E2229.
 reflexivity.
Qed.
Lemma reference_control_ready_2231 old :
 (exists value ground, VM.find 2226 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2230 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2231.
Proof.
 intros H2226 H2230.
 destruct H2226 as [v2226 [G2226 [V2226 T2226]]].
 destruct H2230 as [v2230 [G2230 [V2230 T2230]]].
 unfold reference_control_expr_2231.
apply rc_mux.
{ eapply rc_ref; [exact V2226|exists G2226; exact T2226].
}
{ eapply rc_ref; [exact V2230|exists G2230; exact T2230].
}
Qed.
Lemma reference_control_member_2231 : List.In (2231,reference_control_expr_2231) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 48%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2231_ground inputs path old current result :
 (exists value ground, VM.find 2226 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2230 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2231 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2226 H2230 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2231 reference_control_expr_2231 reference_control_1_positions reference_control_1_safety reference_control_member_2231) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2231 reference_control_expr_2231 inputs path old current result Position Safe Nonreg (reference_control_ready_2231 old H2226 H2230) Step).
Qed.
Theorem reference_control_node_2231_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2226 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2230 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2088 left = VM.find 2088 right ->
 VM.find 2226 left = VM.find 2226 right ->
 VM.find 2230 left = VM.find 2230 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2231 next_left = VM.find 2231 next_right.
Proof.
 intros H2226 H2230 E2088 E2226 E2230 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2231 reference_control_expr_2231 reference_control_1_positions reference_control_1_safety reference_control_member_2231) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2231 reference_control_expr_2231 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2231 left H2226 H2230)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2231 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2088.
 rewrite E2226.
 rewrite E2230.
 reflexivity.
Qed.
Lemma reference_control_ready_2232 old :
 (exists value ground, VM.find 2225 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2231 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2232.
Proof.
 intros H2225 H2231.
 destruct H2225 as [v2225 [G2225 [V2225 T2225]]].
 destruct H2231 as [v2231 [G2231 [V2231 T2231]]].
 unfold reference_control_expr_2232.
apply rc_mux.
{ eapply rc_ref; [exact V2225|exists G2225; exact T2225].
}
{ eapply rc_ref; [exact V2231|exists G2231; exact T2231].
}
Qed.
Lemma reference_control_member_2232 : List.In (2232,reference_control_expr_2232) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 49%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2232_ground inputs path old current result :
 (exists value ground, VM.find 2225 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2231 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2232 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2225 H2231 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2232 reference_control_expr_2232 reference_control_1_positions reference_control_1_safety reference_control_member_2232) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2232 reference_control_expr_2232 inputs path old current result Position Safe Nonreg (reference_control_ready_2232 old H2225 H2231) Step).
Qed.
Theorem reference_control_node_2232_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2225 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2231 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2084 left = VM.find 2084 right ->
 VM.find 2225 left = VM.find 2225 right ->
 VM.find 2231 left = VM.find 2231 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2232 next_left = VM.find 2232 next_right.
Proof.
 intros H2225 H2231 E2084 E2225 E2231 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2232 reference_control_expr_2232 reference_control_1_positions reference_control_1_safety reference_control_member_2232) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2232 reference_control_expr_2232 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2232 left H2225 H2231)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2232 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2084.
 rewrite E2225.
 rewrite E2231.
 reflexivity.
Qed.
Lemma reference_control_ready_2233 old :
 (exists value ground, VM.find 2224 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2232 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2233.
Proof.
 intros H2224 H2232.
 destruct H2224 as [v2224 [G2224 [V2224 T2224]]].
 destruct H2232 as [v2232 [G2232 [V2232 T2232]]].
 unfold reference_control_expr_2233.
apply rc_mux.
{ eapply rc_ref; [exact V2224|exists G2224; exact T2224].
}
{ eapply rc_ref; [exact V2232|exists G2232; exact T2232].
}
Qed.
Lemma reference_control_member_2233 : List.In (2233,reference_control_expr_2233) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 50%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2233_ground inputs path old current result :
 (exists value ground, VM.find 2224 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2232 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2233 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2224 H2232 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2233 reference_control_expr_2233 reference_control_1_positions reference_control_1_safety reference_control_member_2233) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2233 reference_control_expr_2233 inputs path old current result Position Safe Nonreg (reference_control_ready_2233 old H2224 H2232) Step).
Qed.
Theorem reference_control_node_2233_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2224 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2232 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2080 left = VM.find 2080 right ->
 VM.find 2224 left = VM.find 2224 right ->
 VM.find 2232 left = VM.find 2232 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2233 next_left = VM.find 2233 next_right.
Proof.
 intros H2224 H2232 E2080 E2224 E2232 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2233 reference_control_expr_2233 reference_control_1_positions reference_control_1_safety reference_control_member_2233) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2233 reference_control_expr_2233 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2233 left H2224 H2232)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2233 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2080.
 rewrite E2224.
 rewrite E2232.
 reflexivity.
Qed.
Lemma reference_control_ready_2234 old :
 (exists value ground, VM.find 2223 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2233 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2234.
Proof.
 intros H2223 H2233.
 destruct H2223 as [v2223 [G2223 [V2223 T2223]]].
 destruct H2233 as [v2233 [G2233 [V2233 T2233]]].
 unfold reference_control_expr_2234.
apply rc_mux.
{ eapply rc_ref; [exact V2223|exists G2223; exact T2223].
}
{ eapply rc_ref; [exact V2233|exists G2233; exact T2233].
}
Qed.
Lemma reference_control_member_2234 : List.In (2234,reference_control_expr_2234) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 51%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2234_ground inputs path old current result :
 (exists value ground, VM.find 2223 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2233 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2234 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2223 H2233 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2234 reference_control_expr_2234 reference_control_1_positions reference_control_1_safety reference_control_member_2234) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2234 reference_control_expr_2234 inputs path old current result Position Safe Nonreg (reference_control_ready_2234 old H2223 H2233) Step).
Qed.
Theorem reference_control_node_2234_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2223 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2233 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2076 left = VM.find 2076 right ->
 VM.find 2223 left = VM.find 2223 right ->
 VM.find 2233 left = VM.find 2233 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2234 next_left = VM.find 2234 next_right.
Proof.
 intros H2223 H2233 E2076 E2223 E2233 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2234 reference_control_expr_2234 reference_control_1_positions reference_control_1_safety reference_control_member_2234) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2234 reference_control_expr_2234 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2234 left H2223 H2233)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2234 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2076.
 rewrite E2223.
 rewrite E2233.
 reflexivity.
Qed.
Lemma reference_control_ready_2235 old :
 (exists value ground, VM.find 2222 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2234 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2235.
Proof.
 intros H2222 H2234.
 destruct H2222 as [v2222 [G2222 [V2222 T2222]]].
 destruct H2234 as [v2234 [G2234 [V2234 T2234]]].
 unfold reference_control_expr_2235.
apply rc_mux.
{ eapply rc_ref; [exact V2222|exists G2222; exact T2222].
}
{ eapply rc_ref; [exact V2234|exists G2234; exact T2234].
}
Qed.
Lemma reference_control_member_2235 : List.In (2235,reference_control_expr_2235) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 52%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2235_ground inputs path old current result :
 (exists value ground, VM.find 2222 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2234 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2235 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2222 H2234 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2235 reference_control_expr_2235 reference_control_1_positions reference_control_1_safety reference_control_member_2235) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2235 reference_control_expr_2235 inputs path old current result Position Safe Nonreg (reference_control_ready_2235 old H2222 H2234) Step).
Qed.
Theorem reference_control_node_2235_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2222 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2234 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2072 left = VM.find 2072 right ->
 VM.find 2222 left = VM.find 2222 right ->
 VM.find 2234 left = VM.find 2234 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2235 next_left = VM.find 2235 next_right.
Proof.
 intros H2222 H2234 E2072 E2222 E2234 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2235 reference_control_expr_2235 reference_control_1_positions reference_control_1_safety reference_control_member_2235) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2235 reference_control_expr_2235 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2235 left H2222 H2234)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2235 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2072.
 rewrite E2222.
 rewrite E2234.
 reflexivity.
Qed.
Lemma reference_control_ready_2236 old :
 (exists value ground, VM.find 2221 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2235 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2236.
Proof.
 intros H2221 H2235.
 destruct H2221 as [v2221 [G2221 [V2221 T2221]]].
 destruct H2235 as [v2235 [G2235 [V2235 T2235]]].
 unfold reference_control_expr_2236.
apply rc_mux.
{ eapply rc_ref; [exact V2221|exists G2221; exact T2221].
}
{ eapply rc_ref; [exact V2235|exists G2235; exact T2235].
}
Qed.
Lemma reference_control_member_2236 : List.In (2236,reference_control_expr_2236) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 53%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2236_ground inputs path old current result :
 (exists value ground, VM.find 2221 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2235 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2236 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2221 H2235 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2236 reference_control_expr_2236 reference_control_1_positions reference_control_1_safety reference_control_member_2236) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2236 reference_control_expr_2236 inputs path old current result Position Safe Nonreg (reference_control_ready_2236 old H2221 H2235) Step).
Qed.
Theorem reference_control_node_2236_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2221 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2235 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2068 left = VM.find 2068 right ->
 VM.find 2221 left = VM.find 2221 right ->
 VM.find 2235 left = VM.find 2235 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2236 next_left = VM.find 2236 next_right.
Proof.
 intros H2221 H2235 E2068 E2221 E2235 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2236 reference_control_expr_2236 reference_control_1_positions reference_control_1_safety reference_control_member_2236) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2236 reference_control_expr_2236 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2236 left H2221 H2235)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2236 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2068.
 rewrite E2221.
 rewrite E2235.
 reflexivity.
Qed.
Lemma reference_control_ready_2237 old :
 (exists value ground, VM.find 2220 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2236 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2237.
Proof.
 intros H2220 H2236.
 destruct H2220 as [v2220 [G2220 [V2220 T2220]]].
 destruct H2236 as [v2236 [G2236 [V2236 T2236]]].
 unfold reference_control_expr_2237.
apply rc_mux.
{ eapply rc_ref; [exact V2220|exists G2220; exact T2220].
}
{ eapply rc_ref; [exact V2236|exists G2236; exact T2236].
}
Qed.
Lemma reference_control_member_2237 : List.In (2237,reference_control_expr_2237) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 54%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2237_ground inputs path old current result :
 (exists value ground, VM.find 2220 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2236 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2237 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2220 H2236 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2237 reference_control_expr_2237 reference_control_1_positions reference_control_1_safety reference_control_member_2237) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2237 reference_control_expr_2237 inputs path old current result Position Safe Nonreg (reference_control_ready_2237 old H2220 H2236) Step).
Qed.
Theorem reference_control_node_2237_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2220 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2236 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2064 left = VM.find 2064 right ->
 VM.find 2220 left = VM.find 2220 right ->
 VM.find 2236 left = VM.find 2236 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2237 next_left = VM.find 2237 next_right.
Proof.
 intros H2220 H2236 E2064 E2220 E2236 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2237 reference_control_expr_2237 reference_control_1_positions reference_control_1_safety reference_control_member_2237) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2237 reference_control_expr_2237 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2237 left H2220 H2236)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2237 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2064.
 rewrite E2220.
 rewrite E2236.
 reflexivity.
Qed.
Lemma reference_control_ready_2238 old :
 (exists value ground, VM.find 2219 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2237 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2238.
Proof.
 intros H2219 H2237.
 destruct H2219 as [v2219 [G2219 [V2219 T2219]]].
 destruct H2237 as [v2237 [G2237 [V2237 T2237]]].
 unfold reference_control_expr_2238.
apply rc_mux.
{ eapply rc_ref; [exact V2219|exists G2219; exact T2219].
}
{ eapply rc_ref; [exact V2237|exists G2237; exact T2237].
}
Qed.
Lemma reference_control_member_2238 : List.In (2238,reference_control_expr_2238) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 55%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2238_ground inputs path old current result :
 (exists value ground, VM.find 2219 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2237 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2238 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2219 H2237 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2238 reference_control_expr_2238 reference_control_1_positions reference_control_1_safety reference_control_member_2238) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2238 reference_control_expr_2238 inputs path old current result Position Safe Nonreg (reference_control_ready_2238 old H2219 H2237) Step).
Qed.
Theorem reference_control_node_2238_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2219 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2237 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2010 left = VM.find 2010 right ->
 VM.find 2219 left = VM.find 2219 right ->
 VM.find 2237 left = VM.find 2237 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2238 next_left = VM.find 2238 next_right.
Proof.
 intros H2219 H2237 E2010 E2219 E2237 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2238 reference_control_expr_2238 reference_control_1_positions reference_control_1_safety reference_control_member_2238) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2238 reference_control_expr_2238 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2238 left H2219 H2237)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2238 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2010.
 rewrite E2219.
 rewrite E2237.
 reflexivity.
Qed.
Lemma reference_control_ready_2239 old :
 (exists value ground, VM.find 2218 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2238 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2239.
Proof.
 intros H2218 H2238.
 destruct H2218 as [v2218 [G2218 [V2218 T2218]]].
 destruct H2238 as [v2238 [G2238 [V2238 T2238]]].
 unfold reference_control_expr_2239.
apply rc_mux.
{ eapply rc_ref; [exact V2218|exists G2218; exact T2218].
}
{ eapply rc_ref; [exact V2238|exists G2238; exact T2238].
}
Qed.
Lemma reference_control_member_2239 : List.In (2239,reference_control_expr_2239) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 56%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2239_ground inputs path old current result :
 (exists value ground, VM.find 2218 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2238 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2239 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2218 H2238 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2239 reference_control_expr_2239 reference_control_1_positions reference_control_1_safety reference_control_member_2239) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2239 reference_control_expr_2239 inputs path old current result Position Safe Nonreg (reference_control_ready_2239 old H2218 H2238) Step).
Qed.
Theorem reference_control_node_2239_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2218 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2238 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1970 left = VM.find 1970 right ->
 VM.find 2218 left = VM.find 2218 right ->
 VM.find 2238 left = VM.find 2238 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2239 next_left = VM.find 2239 next_right.
Proof.
 intros H2218 H2238 E1970 E2218 E2238 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2239 reference_control_expr_2239 reference_control_1_positions reference_control_1_safety reference_control_member_2239) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2239 reference_control_expr_2239 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2239 left H2218 H2238)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2239 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1970.
 rewrite E2218.
 rewrite E2238.
 reflexivity.
Qed.
Lemma reference_control_ready_2240 old :
 (exists value ground, VM.find 2217 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2239 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2240.
Proof.
 intros H2217 H2239.
 destruct H2217 as [v2217 [G2217 [V2217 T2217]]].
 destruct H2239 as [v2239 [G2239 [V2239 T2239]]].
 unfold reference_control_expr_2240.
apply rc_mux.
{ eapply rc_ref; [exact V2217|exists G2217; exact T2217].
}
{ eapply rc_ref; [exact V2239|exists G2239; exact T2239].
}
Qed.
Lemma reference_control_member_2240 : List.In (2240,reference_control_expr_2240) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 57%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2240_ground inputs path old current result :
 (exists value ground, VM.find 2217 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2239 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2240 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2217 H2239 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2240 reference_control_expr_2240 reference_control_1_positions reference_control_1_safety reference_control_member_2240) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2240 reference_control_expr_2240 inputs path old current result Position Safe Nonreg (reference_control_ready_2240 old H2217 H2239) Step).
Qed.
Theorem reference_control_node_2240_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2217 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2239 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1966 left = VM.find 1966 right ->
 VM.find 2217 left = VM.find 2217 right ->
 VM.find 2239 left = VM.find 2239 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2240 next_left = VM.find 2240 next_right.
Proof.
 intros H2217 H2239 E1966 E2217 E2239 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2240 reference_control_expr_2240 reference_control_1_positions reference_control_1_safety reference_control_member_2240) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2240 reference_control_expr_2240 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2240 left H2217 H2239)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2240 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1966.
 rewrite E2217.
 rewrite E2239.
 reflexivity.
Qed.
Lemma reference_control_ready_2241 old :
 (exists value ground, VM.find 2216 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2240 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2241.
Proof.
 intros H2216 H2240.
 destruct H2216 as [v2216 [G2216 [V2216 T2216]]].
 destruct H2240 as [v2240 [G2240 [V2240 T2240]]].
 unfold reference_control_expr_2241.
apply rc_mux.
{ eapply rc_ref; [exact V2216|exists G2216; exact T2216].
}
{ eapply rc_ref; [exact V2240|exists G2240; exact T2240].
}
Qed.
Lemma reference_control_member_2241 : List.In (2241,reference_control_expr_2241) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 58%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2241_ground inputs path old current result :
 (exists value ground, VM.find 2216 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2240 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2241 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2216 H2240 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2241 reference_control_expr_2241 reference_control_1_positions reference_control_1_safety reference_control_member_2241) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2241 reference_control_expr_2241 inputs path old current result Position Safe Nonreg (reference_control_ready_2241 old H2216 H2240) Step).
Qed.
Theorem reference_control_node_2241_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2216 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2240 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1962 left = VM.find 1962 right ->
 VM.find 2216 left = VM.find 2216 right ->
 VM.find 2240 left = VM.find 2240 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2241 next_left = VM.find 2241 next_right.
Proof.
 intros H2216 H2240 E1962 E2216 E2240 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2241 reference_control_expr_2241 reference_control_1_positions reference_control_1_safety reference_control_member_2241) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2241 reference_control_expr_2241 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2241 left H2216 H2240)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2241 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1962.
 rewrite E2216.
 rewrite E2240.
 reflexivity.
Qed.
Lemma reference_control_ready_2242 old :
 (exists value ground, VM.find 2215 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2241 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2242.
Proof.
 intros H2215 H2241.
 destruct H2215 as [v2215 [G2215 [V2215 T2215]]].
 destruct H2241 as [v2241 [G2241 [V2241 T2241]]].
 unfold reference_control_expr_2242.
apply rc_mux.
{ eapply rc_ref; [exact V2215|exists G2215; exact T2215].
}
{ eapply rc_ref; [exact V2241|exists G2241; exact T2241].
}
Qed.
Lemma reference_control_member_2242 : List.In (2242,reference_control_expr_2242) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 59%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2242_ground inputs path old current result :
 (exists value ground, VM.find 2215 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2241 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2242 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2215 H2241 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2242 reference_control_expr_2242 reference_control_1_positions reference_control_1_safety reference_control_member_2242) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2242 reference_control_expr_2242 inputs path old current result Position Safe Nonreg (reference_control_ready_2242 old H2215 H2241) Step).
Qed.
Theorem reference_control_node_2242_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2215 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2241 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1958 left = VM.find 1958 right ->
 VM.find 2215 left = VM.find 2215 right ->
 VM.find 2241 left = VM.find 2241 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2242 next_left = VM.find 2242 next_right.
Proof.
 intros H2215 H2241 E1958 E2215 E2241 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2242 reference_control_expr_2242 reference_control_1_positions reference_control_1_safety reference_control_member_2242) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2242 reference_control_expr_2242 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2242 left H2215 H2241)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2242 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1958.
 rewrite E2215.
 rewrite E2241.
 reflexivity.
Qed.
Lemma reference_control_ready_2243 old :
 (exists value ground, VM.find 2214 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2242 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2243.
Proof.
 intros H2214 H2242.
 destruct H2214 as [v2214 [G2214 [V2214 T2214]]].
 destruct H2242 as [v2242 [G2242 [V2242 T2242]]].
 unfold reference_control_expr_2243.
apply rc_mux.
{ eapply rc_ref; [exact V2214|exists G2214; exact T2214].
}
{ eapply rc_ref; [exact V2242|exists G2242; exact T2242].
}
Qed.
Lemma reference_control_member_2243 : List.In (2243,reference_control_expr_2243) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 60%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2243_ground inputs path old current result :
 (exists value ground, VM.find 2214 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2242 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2243 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2214 H2242 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2243 reference_control_expr_2243 reference_control_1_positions reference_control_1_safety reference_control_member_2243) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2243 reference_control_expr_2243 inputs path old current result Position Safe Nonreg (reference_control_ready_2243 old H2214 H2242) Step).
Qed.
Theorem reference_control_node_2243_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2214 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2242 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1886 left = VM.find 1886 right ->
 VM.find 2214 left = VM.find 2214 right ->
 VM.find 2242 left = VM.find 2242 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2243 next_left = VM.find 2243 next_right.
Proof.
 intros H2214 H2242 E1886 E2214 E2242 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2243 reference_control_expr_2243 reference_control_1_positions reference_control_1_safety reference_control_member_2243) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2243 reference_control_expr_2243 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2243 left H2214 H2242)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2243 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1886.
 rewrite E2214.
 rewrite E2242.
 reflexivity.
Qed.
Lemma reference_control_ready_2244 old :
 (exists value ground, VM.find 2213 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2243 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2244.
Proof.
 intros H2213 H2243.
 destruct H2213 as [v2213 [G2213 [V2213 T2213]]].
 destruct H2243 as [v2243 [G2243 [V2243 T2243]]].
 unfold reference_control_expr_2244.
apply rc_mux.
{ eapply rc_ref; [exact V2213|exists G2213; exact T2213].
}
{ eapply rc_ref; [exact V2243|exists G2243; exact T2243].
}
Qed.
Lemma reference_control_member_2244 : List.In (2244,reference_control_expr_2244) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 61%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2244_ground inputs path old current result :
 (exists value ground, VM.find 2213 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2243 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2244 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2213 H2243 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2244 reference_control_expr_2244 reference_control_1_positions reference_control_1_safety reference_control_member_2244) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2244 reference_control_expr_2244 inputs path old current result Position Safe Nonreg (reference_control_ready_2244 old H2213 H2243) Step).
Qed.
Theorem reference_control_node_2244_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2213 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2243 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1937 left = VM.find 1937 right ->
 VM.find 2213 left = VM.find 2213 right ->
 VM.find 2243 left = VM.find 2243 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2244 next_left = VM.find 2244 next_right.
Proof.
 intros H2213 H2243 E1937 E2213 E2243 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2244 reference_control_expr_2244 reference_control_1_positions reference_control_1_safety reference_control_member_2244) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2244 reference_control_expr_2244 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2244 left H2213 H2243)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2244 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1937.
 rewrite E2213.
 rewrite E2243.
 reflexivity.
Qed.
Lemma reference_control_ready_2245 old :
 (exists value ground, VM.find 2212 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2244 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2245.
Proof.
 intros H2212 H2244.
 destruct H2212 as [v2212 [G2212 [V2212 T2212]]].
 destruct H2244 as [v2244 [G2244 [V2244 T2244]]].
 unfold reference_control_expr_2245.
apply rc_mux.
{ eapply rc_ref; [exact V2212|exists G2212; exact T2212].
}
{ eapply rc_ref; [exact V2244|exists G2244; exact T2244].
}
Qed.
Lemma reference_control_member_2245 : List.In (2245,reference_control_expr_2245) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 62%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2245_ground inputs path old current result :
 (exists value ground, VM.find 2212 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2244 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2245 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2212 H2244 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2245 reference_control_expr_2245 reference_control_1_positions reference_control_1_safety reference_control_member_2245) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2245 reference_control_expr_2245 inputs path old current result Position Safe Nonreg (reference_control_ready_2245 old H2212 H2244) Step).
Qed.
Theorem reference_control_node_2245_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2212 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2244 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1933 left = VM.find 1933 right ->
 VM.find 2212 left = VM.find 2212 right ->
 VM.find 2244 left = VM.find 2244 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2245 next_left = VM.find 2245 next_right.
Proof.
 intros H2212 H2244 E1933 E2212 E2244 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2245 reference_control_expr_2245 reference_control_1_positions reference_control_1_safety reference_control_member_2245) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2245 reference_control_expr_2245 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2245 left H2212 H2244)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2245 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1933.
 rewrite E2212.
 rewrite E2244.
 reflexivity.
Qed.
Lemma reference_control_ready_2246 old :
 (exists value ground, VM.find 2211 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2245 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2246.
Proof.
 intros H2211 H2245.
 destruct H2211 as [v2211 [G2211 [V2211 T2211]]].
 destruct H2245 as [v2245 [G2245 [V2245 T2245]]].
 unfold reference_control_expr_2246.
apply rc_mux.
{ eapply rc_ref; [exact V2211|exists G2211; exact T2211].
}
{ eapply rc_ref; [exact V2245|exists G2245; exact T2245].
}
Qed.
Lemma reference_control_member_2246 : List.In (2246,reference_control_expr_2246) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 63%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2246_ground inputs path old current result :
 (exists value ground, VM.find 2211 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2245 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2246 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2211 H2245 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2246 reference_control_expr_2246 reference_control_1_positions reference_control_1_safety reference_control_member_2246) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2246 reference_control_expr_2246 inputs path old current result Position Safe Nonreg (reference_control_ready_2246 old H2211 H2245) Step).
Qed.
Theorem reference_control_node_2246_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2211 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2245 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1929 left = VM.find 1929 right ->
 VM.find 2211 left = VM.find 2211 right ->
 VM.find 2245 left = VM.find 2245 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2246 next_left = VM.find 2246 next_right.
Proof.
 intros H2211 H2245 E1929 E2211 E2245 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2246 reference_control_expr_2246 reference_control_1_positions reference_control_1_safety reference_control_member_2246) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2246 reference_control_expr_2246 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2246 left H2211 H2245)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2246 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1929.
 rewrite E2211.
 rewrite E2245.
 reflexivity.
Qed.
Lemma reference_control_ready_2247 old :
 (exists value ground, VM.find 2246 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2247.
Proof.
 intros H2246.
 destruct H2246 as [v2246 [G2246 [V2246 T2246]]].
 unfold reference_control_expr_2247.
apply rc_mux.
{ eapply rc_ref; [exact V2246|exists G2246; exact T2246].
}
{ apply rc_const.
}
Qed.
Lemma reference_control_member_2247 : List.In (2247,reference_control_expr_2247) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 64%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2247_ground inputs path old current result :
 (exists value ground, VM.find 2246 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2247 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2246 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2247 reference_control_expr_2247 reference_control_1_positions reference_control_1_safety reference_control_member_2247) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2247 reference_control_expr_2247 inputs path old current result Position Safe Nonreg (reference_control_ready_2247 old H2246) Step).
Qed.
Theorem reference_control_node_2247_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2246 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1707 left = VM.find 1707 right ->
 VM.find 2246 left = VM.find 2246 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2247 next_left = VM.find 2247 next_right.
Proof.
 intros H2246 E1707 E2246 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2247 reference_control_expr_2247 reference_control_1_positions reference_control_1_safety reference_control_member_2247) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2247 reference_control_expr_2247 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2247 left H2246)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2247 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1707.
 rewrite E2246.
 reflexivity.
Qed.
Lemma reference_control_ready_2248 old :
 (exists value ground, VM.find 2247 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2248.
Proof.
 intros H2247.
 destruct H2247 as [v2247 [G2247 [V2247 T2247]]].
 unfold reference_control_expr_2248.
eapply rc_ref; [exact V2247|exists G2247; exact T2247].
Qed.
Lemma reference_control_member_2248 : List.In (2248,reference_control_expr_2248) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 65%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2248_ground inputs path old current result :
 (exists value ground, VM.find 2247 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2248 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2247 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2248 reference_control_expr_2248 reference_control_1_positions reference_control_1_safety reference_control_member_2248) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2248 reference_control_expr_2248 inputs path old current result Position Safe Nonreg (reference_control_ready_2248 old H2247) Step).
Qed.
Theorem reference_control_node_2248_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2247 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2247 left = VM.find 2247 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2248 next_left = VM.find 2248 next_right.
Proof.
 intros H2247 E2247 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2248 reference_control_expr_2248 reference_control_1_positions reference_control_1_safety reference_control_member_2248) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2248 reference_control_expr_2248 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2248 left H2247)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2248 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2247.
 reflexivity.
Qed.
Lemma reference_control_ready_2249 old :
 reference_control_ready old reference_control_expr_2249.
Proof.
 unfold reference_control_expr_2249.
apply rc_unary.
Qed.
Lemma reference_control_member_2249 : List.In (2249,reference_control_expr_2249) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 66%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2249_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2249 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2249 reference_control_expr_2249 reference_control_1_positions reference_control_1_safety reference_control_member_2249) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2249 reference_control_expr_2249 inputs path old current result Position Safe Nonreg (reference_control_ready_2249 old ) Step).
Qed.
Theorem reference_control_node_2249_congruent inputs path left right next_left next_right :
 VM.find 2248 left = VM.find 2248 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2249 next_left = VM.find 2249 next_right.
Proof.
 intros  E2248 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2249 reference_control_expr_2249 reference_control_1_positions reference_control_1_safety reference_control_member_2249) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2249 reference_control_expr_2249 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2249 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2249 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2248.
 reflexivity.
Qed.
Lemma reference_control_ready_2250 old :
 reference_control_ready old reference_control_expr_2250.
Proof.
 unfold reference_control_expr_2250.
apply rc_unary.
Qed.
Lemma reference_control_member_2250 : List.In (2250,reference_control_expr_2250) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 67%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2250_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2250 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2250 reference_control_expr_2250 reference_control_1_positions reference_control_1_safety reference_control_member_2250) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2250 reference_control_expr_2250 inputs path old current result Position Safe Nonreg (reference_control_ready_2250 old ) Step).
Qed.
Theorem reference_control_node_2250_congruent inputs path left right next_left next_right :
 VM.find 2249 left = VM.find 2249 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2250 next_left = VM.find 2250 next_right.
Proof.
 intros  E2249 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2250 reference_control_expr_2250 reference_control_1_positions reference_control_1_safety reference_control_member_2250) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2250 reference_control_expr_2250 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2250 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2250 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2249.
 reflexivity.
Qed.
Lemma reference_control_ready_2251 old :
 reference_control_ready old reference_control_expr_2251.
Proof.
 unfold reference_control_expr_2251.
apply rc_mux.
{ apply rc_const.
}
{ apply rc_const.
}
Qed.
Lemma reference_control_member_2251 : List.In (2251,reference_control_expr_2251) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 68%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2251_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2251 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2251 reference_control_expr_2251 reference_control_1_positions reference_control_1_safety reference_control_member_2251) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2251 reference_control_expr_2251 inputs path old current result Position Safe Nonreg (reference_control_ready_2251 old ) Step).
Qed.
Theorem reference_control_node_2251_congruent inputs path left right next_left next_right :
 VM.find 2250 left = VM.find 2250 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2251 next_left = VM.find 2251 next_right.
Proof.
 intros  E2250 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2251 reference_control_expr_2251 reference_control_1_positions reference_control_1_safety reference_control_member_2251) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2251 reference_control_expr_2251 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2251 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2251 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2250.
 reflexivity.
Qed.
Lemma reference_control_ready_2252 old :
 reference_control_ready old reference_control_expr_2252.
Proof.
 unfold reference_control_expr_2252.
apply rc_binary.
Qed.
Lemma reference_control_member_2252 : List.In (2252,reference_control_expr_2252) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 69%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2252_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2252 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2252 reference_control_expr_2252 reference_control_1_positions reference_control_1_safety reference_control_member_2252) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2252 reference_control_expr_2252 inputs path old current result Position Safe Nonreg (reference_control_ready_2252 old ) Step).
Qed.
Theorem reference_control_node_2252_congruent inputs path left right next_left next_right :
 VM.find 2248 left = VM.find 2248 right ->
 VM.find 2251 left = VM.find 2251 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2252 next_left = VM.find 2252 next_right.
Proof.
 intros  E2248 E2251 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2252 reference_control_expr_2252 reference_control_1_positions reference_control_1_safety reference_control_member_2252) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2252 reference_control_expr_2252 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2252 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2252 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2248.
 rewrite E2251.
 reflexivity.
Qed.
Lemma reference_control_ready_2253 old :
 reference_control_ready old reference_control_expr_2253.
Proof.
 unfold reference_control_expr_2253.
apply rc_unary.
Qed.
Lemma reference_control_member_2253 : List.In (2253,reference_control_expr_2253) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 70%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2253_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2253 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2253 reference_control_expr_2253 reference_control_1_positions reference_control_1_safety reference_control_member_2253) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2253 reference_control_expr_2253 inputs path old current result Position Safe Nonreg (reference_control_ready_2253 old ) Step).
Qed.
Theorem reference_control_node_2253_congruent inputs path left right next_left next_right :
 VM.find 2248 left = VM.find 2248 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2253 next_left = VM.find 2253 next_right.
Proof.
 intros  E2248 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2253 reference_control_expr_2253 reference_control_1_positions reference_control_1_safety reference_control_member_2253) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2253 reference_control_expr_2253 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2253 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2253 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2248.
 reflexivity.
Qed.
Lemma reference_control_ready_2254 old :
 reference_control_ready old reference_control_expr_2254.
Proof.
 unfold reference_control_expr_2254.
apply rc_unary.
Qed.
Lemma reference_control_member_2254 : List.In (2254,reference_control_expr_2254) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 71%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2254_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2254 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2254 reference_control_expr_2254 reference_control_1_positions reference_control_1_safety reference_control_member_2254) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2254 reference_control_expr_2254 inputs path old current result Position Safe Nonreg (reference_control_ready_2254 old ) Step).
Qed.
Theorem reference_control_node_2254_congruent inputs path left right next_left next_right :
 VM.find 2253 left = VM.find 2253 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2254 next_left = VM.find 2254 next_right.
Proof.
 intros  E2253 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2254 reference_control_expr_2254 reference_control_1_positions reference_control_1_safety reference_control_member_2254) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2254 reference_control_expr_2254 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2254 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2254 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2253.
 reflexivity.
Qed.
Lemma reference_control_ready_2255 old :
 reference_control_ready old reference_control_expr_2255.
Proof.
 unfold reference_control_expr_2255.
apply rc_mux.
{ apply rc_const.
}
{ apply rc_const.
}
Qed.
Lemma reference_control_member_2255 : List.In (2255,reference_control_expr_2255) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 72%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2255_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2255 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2255 reference_control_expr_2255 reference_control_1_positions reference_control_1_safety reference_control_member_2255) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2255 reference_control_expr_2255 inputs path old current result Position Safe Nonreg (reference_control_ready_2255 old ) Step).
Qed.
Theorem reference_control_node_2255_congruent inputs path left right next_left next_right :
 VM.find 2254 left = VM.find 2254 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2255 next_left = VM.find 2255 next_right.
Proof.
 intros  E2254 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2255 reference_control_expr_2255 reference_control_1_positions reference_control_1_safety reference_control_member_2255) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2255 reference_control_expr_2255 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2255 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2255 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2254.
 reflexivity.
Qed.
Lemma reference_control_ready_2256 old :
 reference_control_ready old reference_control_expr_2256.
Proof.
 unfold reference_control_expr_2256.
apply rc_binary.
Qed.
Lemma reference_control_member_2256 : List.In (2256,reference_control_expr_2256) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 73%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2256_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2256 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2256 reference_control_expr_2256 reference_control_1_positions reference_control_1_safety reference_control_member_2256) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2256 reference_control_expr_2256 inputs path old current result Position Safe Nonreg (reference_control_ready_2256 old ) Step).
Qed.
Theorem reference_control_node_2256_congruent inputs path left right next_left next_right :
 VM.find 2248 left = VM.find 2248 right ->
 VM.find 2255 left = VM.find 2255 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2256 next_left = VM.find 2256 next_right.
Proof.
 intros  E2248 E2255 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2256 reference_control_expr_2256 reference_control_1_positions reference_control_1_safety reference_control_member_2256) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2256 reference_control_expr_2256 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2256 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2256 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2248.
 rewrite E2255.
 reflexivity.
Qed.
Lemma reference_control_ready_2257 old :
 reference_control_ready old reference_control_expr_2257.
Proof.
 unfold reference_control_expr_2257.
apply rc_unary.
Qed.
Lemma reference_control_member_2257 : List.In (2257,reference_control_expr_2257) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 74%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2257_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2257 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2257 reference_control_expr_2257 reference_control_1_positions reference_control_1_safety reference_control_member_2257) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2257 reference_control_expr_2257 inputs path old current result Position Safe Nonreg (reference_control_ready_2257 old ) Step).
Qed.
Theorem reference_control_node_2257_congruent inputs path left right next_left next_right :
 VM.find 2248 left = VM.find 2248 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2257 next_left = VM.find 2257 next_right.
Proof.
 intros  E2248 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2257 reference_control_expr_2257 reference_control_1_positions reference_control_1_safety reference_control_member_2257) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2257 reference_control_expr_2257 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2257 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2257 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2248.
 reflexivity.
Qed.
Lemma reference_control_ready_2258 old :
 reference_control_ready old reference_control_expr_2258.
Proof.
 unfold reference_control_expr_2258.
apply rc_unary.
Qed.
Lemma reference_control_member_2258 : List.In (2258,reference_control_expr_2258) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 75%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2258_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2258 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2258 reference_control_expr_2258 reference_control_1_positions reference_control_1_safety reference_control_member_2258) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2258 reference_control_expr_2258 inputs path old current result Position Safe Nonreg (reference_control_ready_2258 old ) Step).
Qed.
Theorem reference_control_node_2258_congruent inputs path left right next_left next_right :
 VM.find 2257 left = VM.find 2257 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2258 next_left = VM.find 2258 next_right.
Proof.
 intros  E2257 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2258 reference_control_expr_2258 reference_control_1_positions reference_control_1_safety reference_control_member_2258) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2258 reference_control_expr_2258 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2258 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2258 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2257.
 reflexivity.
Qed.
Lemma reference_control_ready_2259 old :
 reference_control_ready old reference_control_expr_2259.
Proof.
 unfold reference_control_expr_2259.
apply rc_mux.
{ apply rc_const.
}
{ apply rc_const.
}
Qed.
Lemma reference_control_member_2259 : List.In (2259,reference_control_expr_2259) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 76%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2259_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2259 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2259 reference_control_expr_2259 reference_control_1_positions reference_control_1_safety reference_control_member_2259) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2259 reference_control_expr_2259 inputs path old current result Position Safe Nonreg (reference_control_ready_2259 old ) Step).
Qed.
Theorem reference_control_node_2259_congruent inputs path left right next_left next_right :
 VM.find 2258 left = VM.find 2258 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2259 next_left = VM.find 2259 next_right.
Proof.
 intros  E2258 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2259 reference_control_expr_2259 reference_control_1_positions reference_control_1_safety reference_control_member_2259) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2259 reference_control_expr_2259 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2259 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2259 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2258.
 reflexivity.
Qed.
Lemma reference_control_ready_2260 old :
 reference_control_ready old reference_control_expr_2260.
Proof.
 unfold reference_control_expr_2260.
apply rc_binary.
Qed.
Lemma reference_control_member_2260 : List.In (2260,reference_control_expr_2260) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 77%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2260_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2260 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2260 reference_control_expr_2260 reference_control_1_positions reference_control_1_safety reference_control_member_2260) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2260 reference_control_expr_2260 inputs path old current result Position Safe Nonreg (reference_control_ready_2260 old ) Step).
Qed.
Theorem reference_control_node_2260_congruent inputs path left right next_left next_right :
 VM.find 2248 left = VM.find 2248 right ->
 VM.find 2259 left = VM.find 2259 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2260 next_left = VM.find 2260 next_right.
Proof.
 intros  E2248 E2259 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2260 reference_control_expr_2260 reference_control_1_positions reference_control_1_safety reference_control_member_2260) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2260 reference_control_expr_2260 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2260 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2260 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2248.
 rewrite E2259.
 reflexivity.
Qed.
Lemma reference_control_ready_2261 old :
 reference_control_ready old reference_control_expr_2261.
Proof.
 unfold reference_control_expr_2261.
apply rc_unary.
Qed.
Lemma reference_control_member_2261 : List.In (2261,reference_control_expr_2261) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 78%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2261_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2261 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2261 reference_control_expr_2261 reference_control_1_positions reference_control_1_safety reference_control_member_2261) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2261 reference_control_expr_2261 inputs path old current result Position Safe Nonreg (reference_control_ready_2261 old ) Step).
Qed.
Theorem reference_control_node_2261_congruent inputs path left right next_left next_right :
 VM.find 1884 left = VM.find 1884 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2261 next_left = VM.find 2261 next_right.
Proof.
 intros  E1884 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2261 reference_control_expr_2261 reference_control_1_positions reference_control_1_safety reference_control_member_2261) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2261 reference_control_expr_2261 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2261 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2261 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1884.
 reflexivity.
Qed.
Lemma reference_control_ready_2262 old :
 reference_control_ready old reference_control_expr_2262.
Proof.
 unfold reference_control_expr_2262.
apply rc_unary.
Qed.
Lemma reference_control_member_2262 : List.In (2262,reference_control_expr_2262) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 79%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2262_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2262 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2262 reference_control_expr_2262 reference_control_1_positions reference_control_1_safety reference_control_member_2262) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2262 reference_control_expr_2262 inputs path old current result Position Safe Nonreg (reference_control_ready_2262 old ) Step).
Qed.
Theorem reference_control_node_2262_congruent inputs path left right next_left next_right :
 VM.find 1884 left = VM.find 1884 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2262 next_left = VM.find 2262 next_right.
Proof.
 intros  E1884 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2262 reference_control_expr_2262 reference_control_1_positions reference_control_1_safety reference_control_member_2262) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2262 reference_control_expr_2262 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2262 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2262 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1884.
 reflexivity.
Qed.
Lemma reference_control_ready_2263 old :
 reference_control_ready old reference_control_expr_2263.
Proof.
 unfold reference_control_expr_2263.
apply rc_unary.
Qed.
Lemma reference_control_member_2263 : List.In (2263,reference_control_expr_2263) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 80%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2263_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2263 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2263 reference_control_expr_2263 reference_control_1_positions reference_control_1_safety reference_control_member_2263) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2263 reference_control_expr_2263 inputs path old current result Position Safe Nonreg (reference_control_ready_2263 old ) Step).
Qed.
Theorem reference_control_node_2263_congruent inputs path left right next_left next_right :
 VM.find 1884 left = VM.find 1884 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2263 next_left = VM.find 2263 next_right.
Proof.
 intros  E1884 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2263 reference_control_expr_2263 reference_control_1_positions reference_control_1_safety reference_control_member_2263) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2263 reference_control_expr_2263 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2263 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2263 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1884.
 reflexivity.
Qed.
Lemma reference_control_ready_2264 old :
 (exists value ground, VM.find 2263 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2264.
Proof.
 intros H2263.
 destruct H2263 as [v2263 [G2263 [V2263 T2263]]].
 unfold reference_control_expr_2264.
apply rc_mux.
{ eapply rc_ref; [exact V2263|exists G2263; exact T2263].
}
{ apply rc_const.
}
Qed.
Lemma reference_control_member_2264 : List.In (2264,reference_control_expr_2264) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 81%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2264_ground inputs path old current result :
 (exists value ground, VM.find 2263 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2264 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2263 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2264 reference_control_expr_2264 reference_control_1_positions reference_control_1_safety reference_control_member_2264) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2264 reference_control_expr_2264 inputs path old current result Position Safe Nonreg (reference_control_ready_2264 old H2263) Step).
Qed.
Theorem reference_control_node_2264_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2263 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1951 left = VM.find 1951 right ->
 VM.find 2263 left = VM.find 2263 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2264 next_left = VM.find 2264 next_right.
Proof.
 intros H2263 E1951 E2263 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2264 reference_control_expr_2264 reference_control_1_positions reference_control_1_safety reference_control_member_2264) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2264 reference_control_expr_2264 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2264 left H2263)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2264 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1951.
 rewrite E2263.
 reflexivity.
Qed.
Lemma reference_control_ready_2265 old :
 (exists value ground, VM.find 2262 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2264 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2265.
Proof.
 intros H2262 H2264.
 destruct H2262 as [v2262 [G2262 [V2262 T2262]]].
 destruct H2264 as [v2264 [G2264 [V2264 T2264]]].
 unfold reference_control_expr_2265.
apply rc_mux.
{ eapply rc_ref; [exact V2262|exists G2262; exact T2262].
}
{ eapply rc_ref; [exact V2264|exists G2264; exact T2264].
}
Qed.
Lemma reference_control_member_2265 : List.In (2265,reference_control_expr_2265) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 82%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2265_ground inputs path old current result :
 (exists value ground, VM.find 2262 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2264 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2265 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2262 H2264 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2265 reference_control_expr_2265 reference_control_1_positions reference_control_1_safety reference_control_member_2265) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2265 reference_control_expr_2265 inputs path old current result Position Safe Nonreg (reference_control_ready_2265 old H2262 H2264) Step).
Qed.
Theorem reference_control_node_2265_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2262 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2264 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1946 left = VM.find 1946 right ->
 VM.find 2262 left = VM.find 2262 right ->
 VM.find 2264 left = VM.find 2264 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2265 next_left = VM.find 2265 next_right.
Proof.
 intros H2262 H2264 E1946 E2262 E2264 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2265 reference_control_expr_2265 reference_control_1_positions reference_control_1_safety reference_control_member_2265) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2265 reference_control_expr_2265 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2265 left H2262 H2264)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2265 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1946.
 rewrite E2262.
 rewrite E2264.
 reflexivity.
Qed.
Lemma reference_control_ready_2266 old :
 (exists value ground, VM.find 2261 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2265 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2266.
Proof.
 intros H2261 H2265.
 destruct H2261 as [v2261 [G2261 [V2261 T2261]]].
 destruct H2265 as [v2265 [G2265 [V2265 T2265]]].
 unfold reference_control_expr_2266.
apply rc_mux.
{ eapply rc_ref; [exact V2261|exists G2261; exact T2261].
}
{ eapply rc_ref; [exact V2265|exists G2265; exact T2265].
}
Qed.
Lemma reference_control_member_2266 : List.In (2266,reference_control_expr_2266) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 83%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2266_ground inputs path old current result :
 (exists value ground, VM.find 2261 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2265 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2266 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2261 H2265 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2266 reference_control_expr_2266 reference_control_1_positions reference_control_1_safety reference_control_member_2266) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2266 reference_control_expr_2266 inputs path old current result Position Safe Nonreg (reference_control_ready_2266 old H2261 H2265) Step).
Qed.
Theorem reference_control_node_2266_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2261 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2265 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1941 left = VM.find 1941 right ->
 VM.find 2261 left = VM.find 2261 right ->
 VM.find 2265 left = VM.find 2265 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2266 next_left = VM.find 2266 next_right.
Proof.
 intros H2261 H2265 E1941 E2261 E2265 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2266 reference_control_expr_2266 reference_control_1_positions reference_control_1_safety reference_control_member_2266) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2266 reference_control_expr_2266 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2266 left H2261 H2265)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2266 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1941.
 rewrite E2261.
 rewrite E2265.
 reflexivity.
Qed.
Lemma reference_control_ready_2267 old :
 (exists value ground, VM.find 2266 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2267.
Proof.
 intros H2266.
 destruct H2266 as [v2266 [G2266 [V2266 T2266]]].
 unfold reference_control_expr_2267.
apply rc_mux.
{ eapply rc_ref; [exact V2266|exists G2266; exact T2266].
}
{ apply rc_const.
}
Qed.
Lemma reference_control_member_2267 : List.In (2267,reference_control_expr_2267) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 84%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2267_ground inputs path old current result :
 (exists value ground, VM.find 2266 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2267 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2266 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2267 reference_control_expr_2267 reference_control_1_positions reference_control_1_safety reference_control_member_2267) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2267 reference_control_expr_2267 inputs path old current result Position Safe Nonreg (reference_control_ready_2267 old H2266) Step).
Qed.
Theorem reference_control_node_2267_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2266 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1707 left = VM.find 1707 right ->
 VM.find 2266 left = VM.find 2266 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2267 next_left = VM.find 2267 next_right.
Proof.
 intros H2266 E1707 E2266 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2267 reference_control_expr_2267 reference_control_1_positions reference_control_1_safety reference_control_member_2267) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2267 reference_control_expr_2267 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2267 left H2266)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2267 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1707.
 rewrite E2266.
 reflexivity.
Qed.
Lemma reference_control_ready_2268 old :
 (exists value ground, VM.find 2267 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2268.
Proof.
 intros H2267.
 destruct H2267 as [v2267 [G2267 [V2267 T2267]]].
 unfold reference_control_expr_2268.
eapply rc_ref; [exact V2267|exists G2267; exact T2267].
Qed.
Lemma reference_control_member_2268 : List.In (2268,reference_control_expr_2268) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 85%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2268_ground inputs path old current result :
 (exists value ground, VM.find 2267 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2268 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2267 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2268 reference_control_expr_2268 reference_control_1_positions reference_control_1_safety reference_control_member_2268) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2268 reference_control_expr_2268 inputs path old current result Position Safe Nonreg (reference_control_ready_2268 old H2267) Step).
Qed.
Theorem reference_control_node_2268_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2267 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2267 left = VM.find 2267 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2268 next_left = VM.find 2268 next_right.
Proof.
 intros H2267 E2267 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2268 reference_control_expr_2268 reference_control_1_positions reference_control_1_safety reference_control_member_2268) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2268 reference_control_expr_2268 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2268 left H2267)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2268 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2267.
 reflexivity.
Qed.
Lemma reference_control_ready_2269 old :
 reference_control_ready old reference_control_expr_2269.
Proof.
 unfold reference_control_expr_2269.
apply rc_unary.
Qed.
Lemma reference_control_member_2269 : List.In (2269,reference_control_expr_2269) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 86%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2269_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2269 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2269 reference_control_expr_2269 reference_control_1_positions reference_control_1_safety reference_control_member_2269) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2269 reference_control_expr_2269 inputs path old current result Position Safe Nonreg (reference_control_ready_2269 old ) Step).
Qed.
Theorem reference_control_node_2269_congruent inputs path left right next_left next_right :
 VM.find 1943 left = VM.find 1943 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2269 next_left = VM.find 2269 next_right.
Proof.
 intros  E1943 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2269 reference_control_expr_2269 reference_control_1_positions reference_control_1_safety reference_control_member_2269) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2269 reference_control_expr_2269 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2269 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2269 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1943.
 reflexivity.
Qed.
Lemma reference_control_ready_2270 old :
 reference_control_ready old reference_control_expr_2270.
Proof.
 unfold reference_control_expr_2270.
apply rc_unary.
Qed.
Lemma reference_control_member_2270 : List.In (2270,reference_control_expr_2270) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 87%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2270_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2270 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2270 reference_control_expr_2270 reference_control_1_positions reference_control_1_safety reference_control_member_2270) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2270 reference_control_expr_2270 inputs path old current result Position Safe Nonreg (reference_control_ready_2270 old ) Step).
Qed.
Theorem reference_control_node_2270_congruent inputs path left right next_left next_right :
 VM.find 2269 left = VM.find 2269 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2270 next_left = VM.find 2270 next_right.
Proof.
 intros  E2269 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2270 reference_control_expr_2270 reference_control_1_positions reference_control_1_safety reference_control_member_2270) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2270 reference_control_expr_2270 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2270 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2270 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2269.
 reflexivity.
Qed.
Lemma reference_control_ready_2271 old :
 reference_control_ready old reference_control_expr_2271.
Proof.
 unfold reference_control_expr_2271.
apply rc_unary.
Qed.
Lemma reference_control_member_2271 : List.In (2271,reference_control_expr_2271) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 88%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2271_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2271 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2271 reference_control_expr_2271 reference_control_1_positions reference_control_1_safety reference_control_member_2271) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2271 reference_control_expr_2271 inputs path old current result Position Safe Nonreg (reference_control_ready_2271 old ) Step).
Qed.
Theorem reference_control_node_2271_congruent inputs path left right next_left next_right :
 VM.find 2270 left = VM.find 2270 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2271 next_left = VM.find 2271 next_right.
Proof.
 intros  E2270 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2271 reference_control_expr_2271 reference_control_1_positions reference_control_1_safety reference_control_member_2271) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2271 reference_control_expr_2271 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2271 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2271 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2270.
 reflexivity.
Qed.
Lemma reference_control_ready_2272 old :
 reference_control_ready old reference_control_expr_2272.
Proof.
 unfold reference_control_expr_2272.
apply rc_unary.
Qed.
Lemma reference_control_member_2272 : List.In (2272,reference_control_expr_2272) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 89%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2272_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2272 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2272 reference_control_expr_2272 reference_control_1_positions reference_control_1_safety reference_control_member_2272) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2272 reference_control_expr_2272 inputs path old current result Position Safe Nonreg (reference_control_ready_2272 old ) Step).
Qed.
Theorem reference_control_node_2272_congruent inputs path left right next_left next_right :
 VM.find 1948 left = VM.find 1948 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2272 next_left = VM.find 2272 next_right.
Proof.
 intros  E1948 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2272 reference_control_expr_2272 reference_control_1_positions reference_control_1_safety reference_control_member_2272) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2272 reference_control_expr_2272 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2272 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2272 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1948.
 reflexivity.
Qed.
Lemma reference_control_ready_2273 old :
 reference_control_ready old reference_control_expr_2273.
Proof.
 unfold reference_control_expr_2273.
apply rc_unary.
Qed.
Lemma reference_control_member_2273 : List.In (2273,reference_control_expr_2273) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 90%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2273_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2273 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2273 reference_control_expr_2273 reference_control_1_positions reference_control_1_safety reference_control_member_2273) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2273 reference_control_expr_2273 inputs path old current result Position Safe Nonreg (reference_control_ready_2273 old ) Step).
Qed.
Theorem reference_control_node_2273_congruent inputs path left right next_left next_right :
 VM.find 2272 left = VM.find 2272 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2273 next_left = VM.find 2273 next_right.
Proof.
 intros  E2272 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2273 reference_control_expr_2273 reference_control_1_positions reference_control_1_safety reference_control_member_2273) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2273 reference_control_expr_2273 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2273 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2273 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2272.
 reflexivity.
Qed.
Lemma reference_control_ready_2274 old :
 reference_control_ready old reference_control_expr_2274.
Proof.
 unfold reference_control_expr_2274.
apply rc_unary.
Qed.
Lemma reference_control_member_2274 : List.In (2274,reference_control_expr_2274) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 91%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2274_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2274 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2274 reference_control_expr_2274 reference_control_1_positions reference_control_1_safety reference_control_member_2274) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2274 reference_control_expr_2274 inputs path old current result Position Safe Nonreg (reference_control_ready_2274 old ) Step).
Qed.
Theorem reference_control_node_2274_congruent inputs path left right next_left next_right :
 VM.find 2273 left = VM.find 2273 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2274 next_left = VM.find 2274 next_right.
Proof.
 intros  E2273 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2274 reference_control_expr_2274 reference_control_1_positions reference_control_1_safety reference_control_member_2274) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2274 reference_control_expr_2274 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2274 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2274 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2273.
 reflexivity.
Qed.
Lemma reference_control_ready_2275 old :
 reference_control_ready old reference_control_expr_2275.
Proof.
 unfold reference_control_expr_2275.
apply rc_unary.
Qed.
Lemma reference_control_member_2275 : List.In (2275,reference_control_expr_2275) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 92%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2275_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2275 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2275 reference_control_expr_2275 reference_control_1_positions reference_control_1_safety reference_control_member_2275) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2275 reference_control_expr_2275 inputs path old current result Position Safe Nonreg (reference_control_ready_2275 old ) Step).
Qed.
Theorem reference_control_node_2275_congruent inputs path left right next_left next_right :
 VM.find 1953 left = VM.find 1953 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2275 next_left = VM.find 2275 next_right.
Proof.
 intros  E1953 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2275 reference_control_expr_2275 reference_control_1_positions reference_control_1_safety reference_control_member_2275) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2275 reference_control_expr_2275 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2275 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2275 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1953.
 reflexivity.
Qed.
Lemma reference_control_ready_2276 old :
 reference_control_ready old reference_control_expr_2276.
Proof.
 unfold reference_control_expr_2276.
apply rc_unary.
Qed.
Lemma reference_control_member_2276 : List.In (2276,reference_control_expr_2276) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 93%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2276_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2276 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2276 reference_control_expr_2276 reference_control_1_positions reference_control_1_safety reference_control_member_2276) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2276 reference_control_expr_2276 inputs path old current result Position Safe Nonreg (reference_control_ready_2276 old ) Step).
Qed.
Theorem reference_control_node_2276_congruent inputs path left right next_left next_right :
 VM.find 2275 left = VM.find 2275 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2276 next_left = VM.find 2276 next_right.
Proof.
 intros  E2275 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2276 reference_control_expr_2276 reference_control_1_positions reference_control_1_safety reference_control_member_2276) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2276 reference_control_expr_2276 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2276 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2276 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2275.
 reflexivity.
Qed.
Lemma reference_control_ready_2277 old :
 reference_control_ready old reference_control_expr_2277.
Proof.
 unfold reference_control_expr_2277.
apply rc_unary.
Qed.
Lemma reference_control_member_2277 : List.In (2277,reference_control_expr_2277) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 94%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2277_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2277 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2277 reference_control_expr_2277 reference_control_1_positions reference_control_1_safety reference_control_member_2277) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2277 reference_control_expr_2277 inputs path old current result Position Safe Nonreg (reference_control_ready_2277 old ) Step).
Qed.
Theorem reference_control_node_2277_congruent inputs path left right next_left next_right :
 VM.find 2276 left = VM.find 2276 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2277 next_left = VM.find 2277 next_right.
Proof.
 intros  E2276 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2277 reference_control_expr_2277 reference_control_1_positions reference_control_1_safety reference_control_member_2277) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2277 reference_control_expr_2277 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2277 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2277 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2276.
 reflexivity.
Qed.
Lemma reference_control_ready_2278 old :
 (exists value ground, VM.find 2277 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2278.
Proof.
 intros H2277.
 destruct H2277 as [v2277 [G2277 [V2277 T2277]]].
 unfold reference_control_expr_2278.
apply rc_mux.
{ eapply rc_ref; [exact V2277|exists G2277; exact T2277].
}
{ apply rc_const.
}
Qed.
Lemma reference_control_member_2278 : List.In (2278,reference_control_expr_2278) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 95%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2278_ground inputs path old current result :
 (exists value ground, VM.find 2277 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2278 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2277 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2278 reference_control_expr_2278 reference_control_1_positions reference_control_1_safety reference_control_member_2278) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2278 reference_control_expr_2278 inputs path old current result Position Safe Nonreg (reference_control_ready_2278 old H2277) Step).
Qed.
Theorem reference_control_node_2278_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2277 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1951 left = VM.find 1951 right ->
 VM.find 2277 left = VM.find 2277 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2278 next_left = VM.find 2278 next_right.
Proof.
 intros H2277 E1951 E2277 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2278 reference_control_expr_2278 reference_control_1_positions reference_control_1_safety reference_control_member_2278) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2278 reference_control_expr_2278 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2278 left H2277)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2278 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1951.
 rewrite E2277.
 reflexivity.
Qed.
Lemma reference_control_ready_2279 old :
 (exists value ground, VM.find 2274 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2278 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2279.
Proof.
 intros H2274 H2278.
 destruct H2274 as [v2274 [G2274 [V2274 T2274]]].
 destruct H2278 as [v2278 [G2278 [V2278 T2278]]].
 unfold reference_control_expr_2279.
apply rc_mux.
{ eapply rc_ref; [exact V2274|exists G2274; exact T2274].
}
{ eapply rc_ref; [exact V2278|exists G2278; exact T2278].
}
Qed.
Lemma reference_control_member_2279 : List.In (2279,reference_control_expr_2279) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 96%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2279_ground inputs path old current result :
 (exists value ground, VM.find 2274 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2278 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2279 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2274 H2278 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2279 reference_control_expr_2279 reference_control_1_positions reference_control_1_safety reference_control_member_2279) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2279 reference_control_expr_2279 inputs path old current result Position Safe Nonreg (reference_control_ready_2279 old H2274 H2278) Step).
Qed.
Theorem reference_control_node_2279_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2274 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2278 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1946 left = VM.find 1946 right ->
 VM.find 2274 left = VM.find 2274 right ->
 VM.find 2278 left = VM.find 2278 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2279 next_left = VM.find 2279 next_right.
Proof.
 intros H2274 H2278 E1946 E2274 E2278 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2279 reference_control_expr_2279 reference_control_1_positions reference_control_1_safety reference_control_member_2279) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2279 reference_control_expr_2279 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2279 left H2274 H2278)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2279 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1946.
 rewrite E2274.
 rewrite E2278.
 reflexivity.
Qed.
Lemma reference_control_ready_2280 old :
 (exists value ground, VM.find 2271 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2279 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2280.
Proof.
 intros H2271 H2279.
 destruct H2271 as [v2271 [G2271 [V2271 T2271]]].
 destruct H2279 as [v2279 [G2279 [V2279 T2279]]].
 unfold reference_control_expr_2280.
apply rc_mux.
{ eapply rc_ref; [exact V2271|exists G2271; exact T2271].
}
{ eapply rc_ref; [exact V2279|exists G2279; exact T2279].
}
Qed.
Lemma reference_control_member_2280 : List.In (2280,reference_control_expr_2280) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 97%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2280_ground inputs path old current result :
 (exists value ground, VM.find 2271 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2279 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2280 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2271 H2279 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2280 reference_control_expr_2280 reference_control_1_positions reference_control_1_safety reference_control_member_2280) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2280 reference_control_expr_2280 inputs path old current result Position Safe Nonreg (reference_control_ready_2280 old H2271 H2279) Step).
Qed.
Theorem reference_control_node_2280_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2271 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2279 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1941 left = VM.find 1941 right ->
 VM.find 2271 left = VM.find 2271 right ->
 VM.find 2279 left = VM.find 2279 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2280 next_left = VM.find 2280 next_right.
Proof.
 intros H2271 H2279 E1941 E2271 E2279 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2280 reference_control_expr_2280 reference_control_1_positions reference_control_1_safety reference_control_member_2280) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2280 reference_control_expr_2280 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2280 left H2271 H2279)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2280 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1941.
 rewrite E2271.
 rewrite E2279.
 reflexivity.
Qed.
Lemma reference_control_ready_2281 old :
 (exists value ground, VM.find 2280 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2281.
Proof.
 intros H2280.
 destruct H2280 as [v2280 [G2280 [V2280 T2280]]].
 unfold reference_control_expr_2281.
apply rc_mux.
{ eapply rc_ref; [exact V2280|exists G2280; exact T2280].
}
{ apply rc_const.
}
Qed.
Lemma reference_control_member_2281 : List.In (2281,reference_control_expr_2281) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 98%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2281_ground inputs path old current result :
 (exists value ground, VM.find 2280 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2281 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2280 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2281 reference_control_expr_2281 reference_control_1_positions reference_control_1_safety reference_control_member_2281) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2281 reference_control_expr_2281 inputs path old current result Position Safe Nonreg (reference_control_ready_2281 old H2280) Step).
Qed.
Theorem reference_control_node_2281_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2280 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1707 left = VM.find 1707 right ->
 VM.find 2280 left = VM.find 2280 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2281 next_left = VM.find 2281 next_right.
Proof.
 intros H2280 E1707 E2280 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2281 reference_control_expr_2281 reference_control_1_positions reference_control_1_safety reference_control_member_2281) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2281 reference_control_expr_2281 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2281 left H2280)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2281 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1707.
 rewrite E2280.
 reflexivity.
Qed.
Lemma reference_control_ready_2282 old :
 (exists value ground, VM.find 2281 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2282.
Proof.
 intros H2281.
 destruct H2281 as [v2281 [G2281 [V2281 T2281]]].
 unfold reference_control_expr_2282.
eapply rc_ref; [exact V2281|exists G2281; exact T2281].
Qed.
Lemma reference_control_member_2282 : List.In (2282,reference_control_expr_2282) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 99%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2282_ground inputs path old current result :
 (exists value ground, VM.find 2281 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2282 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2281 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2282 reference_control_expr_2282 reference_control_1_positions reference_control_1_safety reference_control_member_2282) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2282 reference_control_expr_2282 inputs path old current result Position Safe Nonreg (reference_control_ready_2282 old H2281) Step).
Qed.
Theorem reference_control_node_2282_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2281 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2281 left = VM.find 2281 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2282 next_left = VM.find 2282 next_right.
Proof.
 intros H2281 E2281 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2282 reference_control_expr_2282 reference_control_1_positions reference_control_1_safety reference_control_member_2282) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2282 reference_control_expr_2282 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2282 left H2281)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2282 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2281.
 reflexivity.
Qed.
Lemma reference_control_ready_2283 old :
 reference_control_ready old reference_control_expr_2283.
Proof.
 unfold reference_control_expr_2283.
apply rc_binary.
Qed.
Lemma reference_control_member_2283 : List.In (2283,reference_control_expr_2283) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 100%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2283_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2283 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2283 reference_control_expr_2283 reference_control_1_positions reference_control_1_safety reference_control_member_2283) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2283 reference_control_expr_2283 inputs path old current result Position Safe Nonreg (reference_control_ready_2283 old ) Step).
Qed.
Theorem reference_control_node_2283_congruent inputs path left right next_left next_right :
 VM.find 2268 left = VM.find 2268 right ->
 VM.find 2282 left = VM.find 2282 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2283 next_left = VM.find 2283 next_right.
Proof.
 intros  E2268 E2282 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2283 reference_control_expr_2283 reference_control_1_positions reference_control_1_safety reference_control_member_2283) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2283 reference_control_expr_2283 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2283 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2283 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2268.
 rewrite E2282.
 reflexivity.
Qed.
Lemma reference_control_ready_2284 old :
 reference_control_ready old reference_control_expr_2284.
Proof.
 unfold reference_control_expr_2284.
apply rc_unary.
Qed.
Lemma reference_control_member_2284 : List.In (2284,reference_control_expr_2284) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 101%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2284_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2284 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2284 reference_control_expr_2284 reference_control_1_positions reference_control_1_safety reference_control_member_2284) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2284 reference_control_expr_2284 inputs path old current result Position Safe Nonreg (reference_control_ready_2284 old ) Step).
Qed.
Theorem reference_control_node_2284_congruent inputs path left right next_left next_right :
 VM.find 2283 left = VM.find 2283 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2284 next_left = VM.find 2284 next_right.
Proof.
 intros  E2283 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2284 reference_control_expr_2284 reference_control_1_positions reference_control_1_safety reference_control_member_2284) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2284 reference_control_expr_2284 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2284 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2284 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2283.
 reflexivity.
Qed.
Lemma reference_control_ready_2285 old :
 reference_control_ready old reference_control_expr_2285.
Proof.
 unfold reference_control_expr_2285.
apply rc_unary.
Qed.
Lemma reference_control_member_2285 : List.In (2285,reference_control_expr_2285) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 102%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2285_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2285 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2285 reference_control_expr_2285 reference_control_1_positions reference_control_1_safety reference_control_member_2285) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2285 reference_control_expr_2285 inputs path old current result Position Safe Nonreg (reference_control_ready_2285 old ) Step).
Qed.
Theorem reference_control_node_2285_congruent inputs path left right next_left next_right :
 VM.find 2284 left = VM.find 2284 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2285 next_left = VM.find 2285 next_right.
Proof.
 intros  E2284 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2285 reference_control_expr_2285 reference_control_1_positions reference_control_1_safety reference_control_member_2285) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2285 reference_control_expr_2285 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2285 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2285 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2284.
 reflexivity.
Qed.
Lemma reference_control_ready_2286 old :
 reference_control_ready old reference_control_expr_2286.
Proof.
 unfold reference_control_expr_2286.
apply rc_mux.
{ apply rc_const.
}
{ apply rc_const.
}
Qed.
Lemma reference_control_member_2286 : List.In (2286,reference_control_expr_2286) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 103%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2286_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2286 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2286 reference_control_expr_2286 reference_control_1_positions reference_control_1_safety reference_control_member_2286) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2286 reference_control_expr_2286 inputs path old current result Position Safe Nonreg (reference_control_ready_2286 old ) Step).
Qed.
Theorem reference_control_node_2286_congruent inputs path left right next_left next_right :
 VM.find 2285 left = VM.find 2285 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2286 next_left = VM.find 2286 next_right.
Proof.
 intros  E2285 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2286 reference_control_expr_2286 reference_control_1_positions reference_control_1_safety reference_control_member_2286) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2286 reference_control_expr_2286 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2286 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2286 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2285.
 reflexivity.
Qed.
Lemma reference_control_ready_2287 old :
 reference_control_ready old reference_control_expr_2287.
Proof.
 unfold reference_control_expr_2287.
apply rc_binary.
Qed.
Lemma reference_control_member_2287 : List.In (2287,reference_control_expr_2287) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 104%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2287_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2287 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2287 reference_control_expr_2287 reference_control_1_positions reference_control_1_safety reference_control_member_2287) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2287 reference_control_expr_2287 inputs path old current result Position Safe Nonreg (reference_control_ready_2287 old ) Step).
Qed.
Theorem reference_control_node_2287_congruent inputs path left right next_left next_right :
 VM.find 2283 left = VM.find 2283 right ->
 VM.find 2286 left = VM.find 2286 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2287 next_left = VM.find 2287 next_right.
Proof.
 intros  E2283 E2286 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2287 reference_control_expr_2287 reference_control_1_positions reference_control_1_safety reference_control_member_2287) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2287 reference_control_expr_2287 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2287 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2287 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2283.
 rewrite E2286.
 reflexivity.
Qed.
Lemma reference_control_ready_2288 old :
 reference_control_ready old reference_control_expr_2288.
Proof.
 unfold reference_control_expr_2288.
apply rc_binary.
Qed.
Lemma reference_control_member_2288 : List.In (2288,reference_control_expr_2288) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 105%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2288_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2288 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2288 reference_control_expr_2288 reference_control_1_positions reference_control_1_safety reference_control_member_2288) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2288 reference_control_expr_2288 inputs path old current result Position Safe Nonreg (reference_control_ready_2288 old ) Step).
Qed.
Theorem reference_control_node_2288_congruent inputs path left right next_left next_right :
 VM.find 2268 left = VM.find 2268 right ->
 VM.find 2282 left = VM.find 2282 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2288 next_left = VM.find 2288 next_right.
Proof.
 intros  E2268 E2282 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2288 reference_control_expr_2288 reference_control_1_positions reference_control_1_safety reference_control_member_2288) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2288 reference_control_expr_2288 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2288 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2288 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2268.
 rewrite E2282.
 reflexivity.
Qed.
Lemma reference_control_ready_2289 old :
 reference_control_ready old reference_control_expr_2289.
Proof.
 unfold reference_control_expr_2289.
apply rc_unary.
Qed.
Lemma reference_control_member_2289 : List.In (2289,reference_control_expr_2289) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 106%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2289_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2289 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2289 reference_control_expr_2289 reference_control_1_positions reference_control_1_safety reference_control_member_2289) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2289 reference_control_expr_2289 inputs path old current result Position Safe Nonreg (reference_control_ready_2289 old ) Step).
Qed.
Theorem reference_control_node_2289_congruent inputs path left right next_left next_right :
 VM.find 2288 left = VM.find 2288 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2289 next_left = VM.find 2289 next_right.
Proof.
 intros  E2288 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2289 reference_control_expr_2289 reference_control_1_positions reference_control_1_safety reference_control_member_2289) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2289 reference_control_expr_2289 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2289 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2289 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2288.
 reflexivity.
Qed.
Lemma reference_control_ready_2290 old :
 reference_control_ready old reference_control_expr_2290.
Proof.
 unfold reference_control_expr_2290.
apply rc_unary.
Qed.
Lemma reference_control_member_2290 : List.In (2290,reference_control_expr_2290) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 107%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2290_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2290 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2290 reference_control_expr_2290 reference_control_1_positions reference_control_1_safety reference_control_member_2290) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2290 reference_control_expr_2290 inputs path old current result Position Safe Nonreg (reference_control_ready_2290 old ) Step).
Qed.
Theorem reference_control_node_2290_congruent inputs path left right next_left next_right :
 VM.find 2289 left = VM.find 2289 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2290 next_left = VM.find 2290 next_right.
Proof.
 intros  E2289 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2290 reference_control_expr_2290 reference_control_1_positions reference_control_1_safety reference_control_member_2290) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2290 reference_control_expr_2290 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2290 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2290 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2289.
 reflexivity.
Qed.
Lemma reference_control_ready_2291 old :
 reference_control_ready old reference_control_expr_2291.
Proof.
 unfold reference_control_expr_2291.
apply rc_mux.
{ apply rc_const.
}
{ apply rc_const.
}
Qed.
Lemma reference_control_member_2291 : List.In (2291,reference_control_expr_2291) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 108%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2291_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2291 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2291 reference_control_expr_2291 reference_control_1_positions reference_control_1_safety reference_control_member_2291) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2291 reference_control_expr_2291 inputs path old current result Position Safe Nonreg (reference_control_ready_2291 old ) Step).
Qed.
Theorem reference_control_node_2291_congruent inputs path left right next_left next_right :
 VM.find 2290 left = VM.find 2290 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2291 next_left = VM.find 2291 next_right.
Proof.
 intros  E2290 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2291 reference_control_expr_2291 reference_control_1_positions reference_control_1_safety reference_control_member_2291) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2291 reference_control_expr_2291 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2291 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2291 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2290.
 reflexivity.
Qed.
Lemma reference_control_ready_2292 old :
 reference_control_ready old reference_control_expr_2292.
Proof.
 unfold reference_control_expr_2292.
apply rc_binary.
Qed.
Lemma reference_control_member_2292 : List.In (2292,reference_control_expr_2292) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 109%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2292_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2292 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2292 reference_control_expr_2292 reference_control_1_positions reference_control_1_safety reference_control_member_2292) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2292 reference_control_expr_2292 inputs path old current result Position Safe Nonreg (reference_control_ready_2292 old ) Step).
Qed.
Theorem reference_control_node_2292_congruent inputs path left right next_left next_right :
 VM.find 2288 left = VM.find 2288 right ->
 VM.find 2291 left = VM.find 2291 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2292 next_left = VM.find 2292 next_right.
Proof.
 intros  E2288 E2291 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2292 reference_control_expr_2292 reference_control_1_positions reference_control_1_safety reference_control_member_2292) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2292 reference_control_expr_2292 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2292 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2292 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2288.
 rewrite E2291.
 reflexivity.
Qed.
Lemma reference_control_ready_2293 old :
 reference_control_ready old reference_control_expr_2293.
Proof.
 unfold reference_control_expr_2293.
apply rc_binary.
Qed.
Lemma reference_control_member_2293 : List.In (2293,reference_control_expr_2293) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 110%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2293_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2293 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2293 reference_control_expr_2293 reference_control_1_positions reference_control_1_safety reference_control_member_2293) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2293 reference_control_expr_2293 inputs path old current result Position Safe Nonreg (reference_control_ready_2293 old ) Step).
Qed.
Theorem reference_control_node_2293_congruent inputs path left right next_left next_right :
 VM.find 2268 left = VM.find 2268 right ->
 VM.find 2282 left = VM.find 2282 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2293 next_left = VM.find 2293 next_right.
Proof.
 intros  E2268 E2282 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2293 reference_control_expr_2293 reference_control_1_positions reference_control_1_safety reference_control_member_2293) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2293 reference_control_expr_2293 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2293 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2293 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2268.
 rewrite E2282.
 reflexivity.
Qed.
Lemma reference_control_ready_2294 old :
 reference_control_ready old reference_control_expr_2294.
Proof.
 unfold reference_control_expr_2294.
apply rc_unary.
Qed.
Lemma reference_control_member_2294 : List.In (2294,reference_control_expr_2294) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 111%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2294_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2294 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2294 reference_control_expr_2294 reference_control_1_positions reference_control_1_safety reference_control_member_2294) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2294 reference_control_expr_2294 inputs path old current result Position Safe Nonreg (reference_control_ready_2294 old ) Step).
Qed.
Theorem reference_control_node_2294_congruent inputs path left right next_left next_right :
 VM.find 2293 left = VM.find 2293 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2294 next_left = VM.find 2294 next_right.
Proof.
 intros  E2293 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2294 reference_control_expr_2294 reference_control_1_positions reference_control_1_safety reference_control_member_2294) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2294 reference_control_expr_2294 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2294 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2294 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2293.
 reflexivity.
Qed.
Lemma reference_control_ready_2295 old :
 reference_control_ready old reference_control_expr_2295.
Proof.
 unfold reference_control_expr_2295.
apply rc_unary.
Qed.
Lemma reference_control_member_2295 : List.In (2295,reference_control_expr_2295) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 112%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2295_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2295 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2295 reference_control_expr_2295 reference_control_1_positions reference_control_1_safety reference_control_member_2295) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2295 reference_control_expr_2295 inputs path old current result Position Safe Nonreg (reference_control_ready_2295 old ) Step).
Qed.
Theorem reference_control_node_2295_congruent inputs path left right next_left next_right :
 VM.find 2294 left = VM.find 2294 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2295 next_left = VM.find 2295 next_right.
Proof.
 intros  E2294 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2295 reference_control_expr_2295 reference_control_1_positions reference_control_1_safety reference_control_member_2295) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2295 reference_control_expr_2295 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2295 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2295 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2294.
 reflexivity.
Qed.
Lemma reference_control_ready_2296 old :
 reference_control_ready old reference_control_expr_2296.
Proof.
 unfold reference_control_expr_2296.
apply rc_mux.
{ apply rc_const.
}
{ apply rc_const.
}
Qed.
Lemma reference_control_member_2296 : List.In (2296,reference_control_expr_2296) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 113%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2296_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2296 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2296 reference_control_expr_2296 reference_control_1_positions reference_control_1_safety reference_control_member_2296) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2296 reference_control_expr_2296 inputs path old current result Position Safe Nonreg (reference_control_ready_2296 old ) Step).
Qed.
Theorem reference_control_node_2296_congruent inputs path left right next_left next_right :
 VM.find 2295 left = VM.find 2295 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2296 next_left = VM.find 2296 next_right.
Proof.
 intros  E2295 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2296 reference_control_expr_2296 reference_control_1_positions reference_control_1_safety reference_control_member_2296) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2296 reference_control_expr_2296 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2296 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2296 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2295.
 reflexivity.
Qed.
Lemma reference_control_ready_2297 old :
 reference_control_ready old reference_control_expr_2297.
Proof.
 unfold reference_control_expr_2297.
apply rc_binary.
Qed.
Lemma reference_control_member_2297 : List.In (2297,reference_control_expr_2297) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 114%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2297_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2297 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2297 reference_control_expr_2297 reference_control_1_positions reference_control_1_safety reference_control_member_2297) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2297 reference_control_expr_2297 inputs path old current result Position Safe Nonreg (reference_control_ready_2297 old ) Step).
Qed.
Theorem reference_control_node_2297_congruent inputs path left right next_left next_right :
 VM.find 2293 left = VM.find 2293 right ->
 VM.find 2296 left = VM.find 2296 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2297 next_left = VM.find 2297 next_right.
Proof.
 intros  E2293 E2296 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2297 reference_control_expr_2297 reference_control_1_positions reference_control_1_safety reference_control_member_2297) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2297 reference_control_expr_2297 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2297 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2297 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2293.
 rewrite E2296.
 reflexivity.
Qed.
Lemma reference_control_ready_2298 old :
 reference_control_ready old reference_control_expr_2298.
Proof.
 unfold reference_control_expr_2298.
apply rc_unary.
Qed.
Lemma reference_control_member_2298 : List.In (2298,reference_control_expr_2298) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 115%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2298_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2298 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2298 reference_control_expr_2298 reference_control_1_positions reference_control_1_safety reference_control_member_2298) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2298 reference_control_expr_2298 inputs path old current result Position Safe Nonreg (reference_control_ready_2298 old ) Step).
Qed.
Theorem reference_control_node_2298_congruent inputs path left right next_left next_right :
 VM.find 2248 left = VM.find 2248 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2298 next_left = VM.find 2298 next_right.
Proof.
 intros  E2248 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2298 reference_control_expr_2298 reference_control_1_positions reference_control_1_safety reference_control_member_2298) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2298 reference_control_expr_2298 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2298 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2298 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2248.
 reflexivity.
Qed.
Lemma reference_control_ready_2299 old :
 reference_control_ready old reference_control_expr_2299.
Proof.
 unfold reference_control_expr_2299.
apply rc_unary.
Qed.
Lemma reference_control_member_2299 : List.In (2299,reference_control_expr_2299) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 116%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2299_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2299 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2299 reference_control_expr_2299 reference_control_1_positions reference_control_1_safety reference_control_member_2299) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2299 reference_control_expr_2299 inputs path old current result Position Safe Nonreg (reference_control_ready_2299 old ) Step).
Qed.
Theorem reference_control_node_2299_congruent inputs path left right next_left next_right :
 VM.find 2298 left = VM.find 2298 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2299 next_left = VM.find 2299 next_right.
Proof.
 intros  E2298 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2299 reference_control_expr_2299 reference_control_1_positions reference_control_1_safety reference_control_member_2299) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2299 reference_control_expr_2299 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2299 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2299 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2298.
 reflexivity.
Qed.
Lemma reference_control_ready_2300 old :
 reference_control_ready old reference_control_expr_2300.
Proof.
 unfold reference_control_expr_2300.
apply rc_mux.
{ apply rc_const.
}
{ apply rc_const.
}
Qed.
Lemma reference_control_member_2300 : List.In (2300,reference_control_expr_2300) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 117%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2300_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2300 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2300 reference_control_expr_2300 reference_control_1_positions reference_control_1_safety reference_control_member_2300) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2300 reference_control_expr_2300 inputs path old current result Position Safe Nonreg (reference_control_ready_2300 old ) Step).
Qed.
Theorem reference_control_node_2300_congruent inputs path left right next_left next_right :
 VM.find 2299 left = VM.find 2299 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2300 next_left = VM.find 2300 next_right.
Proof.
 intros  E2299 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2300 reference_control_expr_2300 reference_control_1_positions reference_control_1_safety reference_control_member_2300) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2300 reference_control_expr_2300 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2300 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2300 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2299.
 reflexivity.
Qed.
Lemma reference_control_ready_2301 old :
 reference_control_ready old reference_control_expr_2301.
Proof.
 unfold reference_control_expr_2301.
apply rc_binary.
Qed.
Lemma reference_control_member_2301 : List.In (2301,reference_control_expr_2301) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 118%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2301_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2301 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2301 reference_control_expr_2301 reference_control_1_positions reference_control_1_safety reference_control_member_2301) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2301 reference_control_expr_2301 inputs path old current result Position Safe Nonreg (reference_control_ready_2301 old ) Step).
Qed.
Theorem reference_control_node_2301_congruent inputs path left right next_left next_right :
 VM.find 2248 left = VM.find 2248 right ->
 VM.find 2300 left = VM.find 2300 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2301 next_left = VM.find 2301 next_right.
Proof.
 intros  E2248 E2300 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2301 reference_control_expr_2301 reference_control_1_positions reference_control_1_safety reference_control_member_2301) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2301 reference_control_expr_2301 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2301 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2301 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2248.
 rewrite E2300.
 reflexivity.
Qed.
Lemma reference_control_ready_2302 old :
 reference_control_ready old reference_control_expr_2302.
Proof.
 unfold reference_control_expr_2302.
apply rc_unary.
Qed.
Lemma reference_control_member_2302 : List.In (2302,reference_control_expr_2302) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 119%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2302_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2302 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2302 reference_control_expr_2302 reference_control_1_positions reference_control_1_safety reference_control_member_2302) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2302 reference_control_expr_2302 inputs path old current result Position Safe Nonreg (reference_control_ready_2302 old ) Step).
Qed.
Theorem reference_control_node_2302_congruent inputs path left right next_left next_right :
 VM.find 2248 left = VM.find 2248 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2302 next_left = VM.find 2302 next_right.
Proof.
 intros  E2248 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2302 reference_control_expr_2302 reference_control_1_positions reference_control_1_safety reference_control_member_2302) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2302 reference_control_expr_2302 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2302 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2302 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2248.
 reflexivity.
Qed.
Lemma reference_control_ready_2303 old :
 reference_control_ready old reference_control_expr_2303.
Proof.
 unfold reference_control_expr_2303.
apply rc_unary.
Qed.
Lemma reference_control_member_2303 : List.In (2303,reference_control_expr_2303) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 120%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2303_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2303 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2303 reference_control_expr_2303 reference_control_1_positions reference_control_1_safety reference_control_member_2303) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2303 reference_control_expr_2303 inputs path old current result Position Safe Nonreg (reference_control_ready_2303 old ) Step).
Qed.
Theorem reference_control_node_2303_congruent inputs path left right next_left next_right :
 VM.find 2302 left = VM.find 2302 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2303 next_left = VM.find 2303 next_right.
Proof.
 intros  E2302 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2303 reference_control_expr_2303 reference_control_1_positions reference_control_1_safety reference_control_member_2303) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2303 reference_control_expr_2303 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2303 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2303 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2302.
 reflexivity.
Qed.
Lemma reference_control_ready_2304 old :
 reference_control_ready old reference_control_expr_2304.
Proof.
 unfold reference_control_expr_2304.
apply rc_mux.
{ apply rc_const.
}
{ apply rc_const.
}
Qed.
Lemma reference_control_member_2304 : List.In (2304,reference_control_expr_2304) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 121%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2304_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2304 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2304 reference_control_expr_2304 reference_control_1_positions reference_control_1_safety reference_control_member_2304) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2304 reference_control_expr_2304 inputs path old current result Position Safe Nonreg (reference_control_ready_2304 old ) Step).
Qed.
Theorem reference_control_node_2304_congruent inputs path left right next_left next_right :
 VM.find 2303 left = VM.find 2303 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2304 next_left = VM.find 2304 next_right.
Proof.
 intros  E2303 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2304 reference_control_expr_2304 reference_control_1_positions reference_control_1_safety reference_control_member_2304) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2304 reference_control_expr_2304 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2304 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2304 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2303.
 reflexivity.
Qed.
Lemma reference_control_ready_2305 old :
 reference_control_ready old reference_control_expr_2305.
Proof.
 unfold reference_control_expr_2305.
apply rc_binary.
Qed.
Lemma reference_control_member_2305 : List.In (2305,reference_control_expr_2305) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 122%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2305_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2305 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2305 reference_control_expr_2305 reference_control_1_positions reference_control_1_safety reference_control_member_2305) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2305 reference_control_expr_2305 inputs path old current result Position Safe Nonreg (reference_control_ready_2305 old ) Step).
Qed.
Theorem reference_control_node_2305_congruent inputs path left right next_left next_right :
 VM.find 2248 left = VM.find 2248 right ->
 VM.find 2304 left = VM.find 2304 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2305 next_left = VM.find 2305 next_right.
Proof.
 intros  E2248 E2304 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2305 reference_control_expr_2305 reference_control_1_positions reference_control_1_safety reference_control_member_2305) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2305 reference_control_expr_2305 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2305 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2305 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2248.
 rewrite E2304.
 reflexivity.
Qed.
Lemma reference_control_ready_2306 old :
 reference_control_ready old reference_control_expr_2306.
Proof.
 unfold reference_control_expr_2306.
apply rc_unary.
Qed.
Lemma reference_control_member_2306 : List.In (2306,reference_control_expr_2306) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 123%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2306_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2306 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2306 reference_control_expr_2306 reference_control_1_positions reference_control_1_safety reference_control_member_2306) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2306 reference_control_expr_2306 inputs path old current result Position Safe Nonreg (reference_control_ready_2306 old ) Step).
Qed.
Theorem reference_control_node_2306_congruent inputs path left right next_left next_right :
 VM.find 2248 left = VM.find 2248 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2306 next_left = VM.find 2306 next_right.
Proof.
 intros  E2248 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2306 reference_control_expr_2306 reference_control_1_positions reference_control_1_safety reference_control_member_2306) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2306 reference_control_expr_2306 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2306 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2306 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2248.
 reflexivity.
Qed.
Lemma reference_control_ready_2307 old :
 reference_control_ready old reference_control_expr_2307.
Proof.
 unfold reference_control_expr_2307.
apply rc_unary.
Qed.
Lemma reference_control_member_2307 : List.In (2307,reference_control_expr_2307) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 124%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2307_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2307 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2307 reference_control_expr_2307 reference_control_1_positions reference_control_1_safety reference_control_member_2307) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2307 reference_control_expr_2307 inputs path old current result Position Safe Nonreg (reference_control_ready_2307 old ) Step).
Qed.
Theorem reference_control_node_2307_congruent inputs path left right next_left next_right :
 VM.find 2306 left = VM.find 2306 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2307 next_left = VM.find 2307 next_right.
Proof.
 intros  E2306 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2307 reference_control_expr_2307 reference_control_1_positions reference_control_1_safety reference_control_member_2307) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2307 reference_control_expr_2307 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2307 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2307 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2306.
 reflexivity.
Qed.
Lemma reference_control_ready_2308 old :
 reference_control_ready old reference_control_expr_2308.
Proof.
 unfold reference_control_expr_2308.
apply rc_mux.
{ apply rc_const.
}
{ apply rc_const.
}
Qed.
Lemma reference_control_member_2308 : List.In (2308,reference_control_expr_2308) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 125%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2308_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2308 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2308 reference_control_expr_2308 reference_control_1_positions reference_control_1_safety reference_control_member_2308) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2308 reference_control_expr_2308 inputs path old current result Position Safe Nonreg (reference_control_ready_2308 old ) Step).
Qed.
Theorem reference_control_node_2308_congruent inputs path left right next_left next_right :
 VM.find 2307 left = VM.find 2307 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2308 next_left = VM.find 2308 next_right.
Proof.
 intros  E2307 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2308 reference_control_expr_2308 reference_control_1_positions reference_control_1_safety reference_control_member_2308) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2308 reference_control_expr_2308 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2308 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2308 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2307.
 reflexivity.
Qed.
Lemma reference_control_ready_2309 old :
 reference_control_ready old reference_control_expr_2309.
Proof.
 unfold reference_control_expr_2309.
apply rc_binary.
Qed.
Lemma reference_control_member_2309 : List.In (2309,reference_control_expr_2309) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 126%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2309_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2309 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2309 reference_control_expr_2309 reference_control_1_positions reference_control_1_safety reference_control_member_2309) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2309 reference_control_expr_2309 inputs path old current result Position Safe Nonreg (reference_control_ready_2309 old ) Step).
Qed.
Theorem reference_control_node_2309_congruent inputs path left right next_left next_right :
 VM.find 2248 left = VM.find 2248 right ->
 VM.find 2308 left = VM.find 2308 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2309 next_left = VM.find 2309 next_right.
Proof.
 intros  E2248 E2308 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2309 reference_control_expr_2309 reference_control_1_positions reference_control_1_safety reference_control_member_2309) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2309 reference_control_expr_2309 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2309 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2309 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2248.
 rewrite E2308.
 reflexivity.
Qed.
Lemma reference_control_ready_2310 old :
 reference_control_ready old reference_control_expr_2310.
Proof.
 unfold reference_control_expr_2310.
apply rc_unary.
Qed.
Lemma reference_control_member_2310 : List.In (2310,reference_control_expr_2310) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 127%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2310_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2310 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2310 reference_control_expr_2310 reference_control_1_positions reference_control_1_safety reference_control_member_2310) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2310 reference_control_expr_2310 inputs path old current result Position Safe Nonreg (reference_control_ready_2310 old ) Step).
Qed.
Theorem reference_control_node_2310_congruent inputs path left right next_left next_right :
 VM.find 2248 left = VM.find 2248 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2310 next_left = VM.find 2310 next_right.
Proof.
 intros  E2248 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2310 reference_control_expr_2310 reference_control_1_positions reference_control_1_safety reference_control_member_2310) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2310 reference_control_expr_2310 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2310 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2310 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2248.
 reflexivity.
Qed.
Lemma reference_control_ready_2311 old :
 reference_control_ready old reference_control_expr_2311.
Proof.
 unfold reference_control_expr_2311.
apply rc_unary.
Qed.
Lemma reference_control_member_2311 : List.In (2311,reference_control_expr_2311) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 128%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2311_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2311 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2311 reference_control_expr_2311 reference_control_1_positions reference_control_1_safety reference_control_member_2311) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2311 reference_control_expr_2311 inputs path old current result Position Safe Nonreg (reference_control_ready_2311 old ) Step).
Qed.
Theorem reference_control_node_2311_congruent inputs path left right next_left next_right :
 VM.find 2310 left = VM.find 2310 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2311 next_left = VM.find 2311 next_right.
Proof.
 intros  E2310 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2311 reference_control_expr_2311 reference_control_1_positions reference_control_1_safety reference_control_member_2311) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2311 reference_control_expr_2311 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2311 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2311 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2310.
 reflexivity.
Qed.
Lemma reference_control_ready_2312 old :
 reference_control_ready old reference_control_expr_2312.
Proof.
 unfold reference_control_expr_2312.
apply rc_mux.
{ apply rc_const.
}
{ apply rc_const.
}
Qed.
Lemma reference_control_member_2312 : List.In (2312,reference_control_expr_2312) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 129%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2312_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2312 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2312 reference_control_expr_2312 reference_control_1_positions reference_control_1_safety reference_control_member_2312) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2312 reference_control_expr_2312 inputs path old current result Position Safe Nonreg (reference_control_ready_2312 old ) Step).
Qed.
Theorem reference_control_node_2312_congruent inputs path left right next_left next_right :
 VM.find 2311 left = VM.find 2311 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2312 next_left = VM.find 2312 next_right.
Proof.
 intros  E2311 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2312 reference_control_expr_2312 reference_control_1_positions reference_control_1_safety reference_control_member_2312) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2312 reference_control_expr_2312 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2312 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2312 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2311.
 reflexivity.
Qed.
Lemma reference_control_ready_2313 old :
 reference_control_ready old reference_control_expr_2313.
Proof.
 unfold reference_control_expr_2313.
apply rc_binary.
Qed.
Lemma reference_control_member_2313 : List.In (2313,reference_control_expr_2313) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 130%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2313_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2313 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2313 reference_control_expr_2313 reference_control_1_positions reference_control_1_safety reference_control_member_2313) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2313 reference_control_expr_2313 inputs path old current result Position Safe Nonreg (reference_control_ready_2313 old ) Step).
Qed.
Theorem reference_control_node_2313_congruent inputs path left right next_left next_right :
 VM.find 2248 left = VM.find 2248 right ->
 VM.find 2312 left = VM.find 2312 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2313 next_left = VM.find 2313 next_right.
Proof.
 intros  E2248 E2312 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2313 reference_control_expr_2313 reference_control_1_positions reference_control_1_safety reference_control_member_2313) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2313 reference_control_expr_2313 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2313 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2313 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2248.
 rewrite E2312.
 reflexivity.
Qed.
Lemma reference_control_ready_2314 old :
 reference_control_ready old reference_control_expr_2314.
Proof.
 unfold reference_control_expr_2314.
apply rc_unary.
Qed.
Lemma reference_control_member_2314 : List.In (2314,reference_control_expr_2314) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 131%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2314_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2314 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2314 reference_control_expr_2314 reference_control_1_positions reference_control_1_safety reference_control_member_2314) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2314 reference_control_expr_2314 inputs path old current result Position Safe Nonreg (reference_control_ready_2314 old ) Step).
Qed.
Theorem reference_control_node_2314_congruent inputs path left right next_left next_right :
 VM.find 2248 left = VM.find 2248 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2314 next_left = VM.find 2314 next_right.
Proof.
 intros  E2248 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2314 reference_control_expr_2314 reference_control_1_positions reference_control_1_safety reference_control_member_2314) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2314 reference_control_expr_2314 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2314 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2314 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2248.
 reflexivity.
Qed.
Lemma reference_control_ready_2315 old :
 reference_control_ready old reference_control_expr_2315.
Proof.
 unfold reference_control_expr_2315.
apply rc_unary.
Qed.
Lemma reference_control_member_2315 : List.In (2315,reference_control_expr_2315) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 132%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2315_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2315 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2315 reference_control_expr_2315 reference_control_1_positions reference_control_1_safety reference_control_member_2315) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2315 reference_control_expr_2315 inputs path old current result Position Safe Nonreg (reference_control_ready_2315 old ) Step).
Qed.
Theorem reference_control_node_2315_congruent inputs path left right next_left next_right :
 VM.find 2314 left = VM.find 2314 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2315 next_left = VM.find 2315 next_right.
Proof.
 intros  E2314 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2315 reference_control_expr_2315 reference_control_1_positions reference_control_1_safety reference_control_member_2315) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2315 reference_control_expr_2315 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2315 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2315 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2314.
 reflexivity.
Qed.
Lemma reference_control_ready_2316 old :
 reference_control_ready old reference_control_expr_2316.
Proof.
 unfold reference_control_expr_2316.
apply rc_mux.
{ apply rc_const.
}
{ apply rc_const.
}
Qed.
Lemma reference_control_member_2316 : List.In (2316,reference_control_expr_2316) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 133%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2316_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2316 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2316 reference_control_expr_2316 reference_control_1_positions reference_control_1_safety reference_control_member_2316) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2316 reference_control_expr_2316 inputs path old current result Position Safe Nonreg (reference_control_ready_2316 old ) Step).
Qed.
Theorem reference_control_node_2316_congruent inputs path left right next_left next_right :
 VM.find 2315 left = VM.find 2315 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2316 next_left = VM.find 2316 next_right.
Proof.
 intros  E2315 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2316 reference_control_expr_2316 reference_control_1_positions reference_control_1_safety reference_control_member_2316) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2316 reference_control_expr_2316 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2316 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2316 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2315.
 reflexivity.
Qed.
Lemma reference_control_ready_2317 old :
 reference_control_ready old reference_control_expr_2317.
Proof.
 unfold reference_control_expr_2317.
apply rc_binary.
Qed.
Lemma reference_control_member_2317 : List.In (2317,reference_control_expr_2317) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 134%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2317_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2317 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2317 reference_control_expr_2317 reference_control_1_positions reference_control_1_safety reference_control_member_2317) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2317 reference_control_expr_2317 inputs path old current result Position Safe Nonreg (reference_control_ready_2317 old ) Step).
Qed.
Theorem reference_control_node_2317_congruent inputs path left right next_left next_right :
 VM.find 2248 left = VM.find 2248 right ->
 VM.find 2316 left = VM.find 2316 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2317 next_left = VM.find 2317 next_right.
Proof.
 intros  E2248 E2316 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2317 reference_control_expr_2317 reference_control_1_positions reference_control_1_safety reference_control_member_2317) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2317 reference_control_expr_2317 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2317 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2317 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2248.
 rewrite E2316.
 reflexivity.
Qed.
Lemma reference_control_ready_2318 old :
 reference_control_ready old reference_control_expr_2318.
Proof.
 unfold reference_control_expr_2318.
apply rc_unary.
Qed.
Lemma reference_control_member_2318 : List.In (2318,reference_control_expr_2318) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 135%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2318_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2318 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2318 reference_control_expr_2318 reference_control_1_positions reference_control_1_safety reference_control_member_2318) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2318 reference_control_expr_2318 inputs path old current result Position Safe Nonreg (reference_control_ready_2318 old ) Step).
Qed.
Theorem reference_control_node_2318_congruent inputs path left right next_left next_right :
 VM.find 1884 left = VM.find 1884 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2318 next_left = VM.find 2318 next_right.
Proof.
 intros  E1884 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2318 reference_control_expr_2318 reference_control_1_positions reference_control_1_safety reference_control_member_2318) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2318 reference_control_expr_2318 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2318 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2318 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1884.
 reflexivity.
Qed.
Lemma reference_control_ready_2319 old :
 reference_control_ready old reference_control_expr_2319.
Proof.
 unfold reference_control_expr_2319.
apply rc_unary.
Qed.
Lemma reference_control_member_2319 : List.In (2319,reference_control_expr_2319) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 136%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2319_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2319 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2319 reference_control_expr_2319 reference_control_1_positions reference_control_1_safety reference_control_member_2319) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2319 reference_control_expr_2319 inputs path old current result Position Safe Nonreg (reference_control_ready_2319 old ) Step).
Qed.
Theorem reference_control_node_2319_congruent inputs path left right next_left next_right :
 VM.find 1884 left = VM.find 1884 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2319 next_left = VM.find 2319 next_right.
Proof.
 intros  E1884 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2319 reference_control_expr_2319 reference_control_1_positions reference_control_1_safety reference_control_member_2319) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2319 reference_control_expr_2319 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2319 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2319 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1884.
 reflexivity.
Qed.
Lemma reference_control_ready_2320 old :
 reference_control_ready old reference_control_expr_2320.
Proof.
 unfold reference_control_expr_2320.
apply rc_unary.
Qed.
Lemma reference_control_member_2320 : List.In (2320,reference_control_expr_2320) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 137%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2320_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2320 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2320 reference_control_expr_2320 reference_control_1_positions reference_control_1_safety reference_control_member_2320) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2320 reference_control_expr_2320 inputs path old current result Position Safe Nonreg (reference_control_ready_2320 old ) Step).
Qed.
Theorem reference_control_node_2320_congruent inputs path left right next_left next_right :
 VM.find 1884 left = VM.find 1884 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2320 next_left = VM.find 2320 next_right.
Proof.
 intros  E1884 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2320 reference_control_expr_2320 reference_control_1_positions reference_control_1_safety reference_control_member_2320) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2320 reference_control_expr_2320 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2320 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2320 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1884.
 reflexivity.
Qed.
Lemma reference_control_ready_2321 old :
 reference_control_ready old reference_control_expr_2321.
Proof.
 unfold reference_control_expr_2321.
apply rc_unary.
Qed.
Lemma reference_control_member_2321 : List.In (2321,reference_control_expr_2321) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 138%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2321_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2321 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2321 reference_control_expr_2321 reference_control_1_positions reference_control_1_safety reference_control_member_2321) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2321 reference_control_expr_2321 inputs path old current result Position Safe Nonreg (reference_control_ready_2321 old ) Step).
Qed.
Theorem reference_control_node_2321_congruent inputs path left right next_left next_right :
 VM.find 1884 left = VM.find 1884 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2321 next_left = VM.find 2321 next_right.
Proof.
 intros  E1884 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2321 reference_control_expr_2321 reference_control_1_positions reference_control_1_safety reference_control_member_2321) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2321 reference_control_expr_2321 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2321 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2321 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1884.
 reflexivity.
Qed.
Lemma reference_control_ready_2322 old :
 reference_control_ready old reference_control_expr_2322.
Proof.
 unfold reference_control_expr_2322.
apply rc_unary.
Qed.
Lemma reference_control_member_2322 : List.In (2322,reference_control_expr_2322) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 139%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2322_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2322 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2322 reference_control_expr_2322 reference_control_1_positions reference_control_1_safety reference_control_member_2322) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2322 reference_control_expr_2322 inputs path old current result Position Safe Nonreg (reference_control_ready_2322 old ) Step).
Qed.
Theorem reference_control_node_2322_congruent inputs path left right next_left next_right :
 VM.find 1884 left = VM.find 1884 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2322 next_left = VM.find 2322 next_right.
Proof.
 intros  E1884 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2322 reference_control_expr_2322 reference_control_1_positions reference_control_1_safety reference_control_member_2322) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2322 reference_control_expr_2322 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2322 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2322 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1884.
 reflexivity.
Qed.
Lemma reference_control_ready_2323 old :
 reference_control_ready old reference_control_expr_2323.
Proof.
 unfold reference_control_expr_2323.
apply rc_unary.
Qed.
Lemma reference_control_member_2323 : List.In (2323,reference_control_expr_2323) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 140%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2323_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2323 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2323 reference_control_expr_2323 reference_control_1_positions reference_control_1_safety reference_control_member_2323) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2323 reference_control_expr_2323 inputs path old current result Position Safe Nonreg (reference_control_ready_2323 old ) Step).
Qed.
Theorem reference_control_node_2323_congruent inputs path left right next_left next_right :
 VM.find 1884 left = VM.find 1884 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2323 next_left = VM.find 2323 next_right.
Proof.
 intros  E1884 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2323 reference_control_expr_2323 reference_control_1_positions reference_control_1_safety reference_control_member_2323) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2323 reference_control_expr_2323 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2323 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2323 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1884.
 reflexivity.
Qed.
Lemma reference_control_ready_2324 old :
 (exists value ground, VM.find 2323 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2324.
Proof.
 intros H2323.
 destruct H2323 as [v2323 [G2323 [V2323 T2323]]].
 unfold reference_control_expr_2324.
apply rc_mux.
{ eapply rc_ref; [exact V2323|exists G2323; exact T2323].
}
{ apply rc_const.
}
Qed.
Lemma reference_control_member_2324 : List.In (2324,reference_control_expr_2324) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 141%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2324_ground inputs path old current result :
 (exists value ground, VM.find 2323 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2324 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2323 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2324 reference_control_expr_2324 reference_control_1_positions reference_control_1_safety reference_control_member_2324) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2324 reference_control_expr_2324 inputs path old current result Position Safe Nonreg (reference_control_ready_2324 old H2323) Step).
Qed.
Theorem reference_control_node_2324_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2323 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2004 left = VM.find 2004 right ->
 VM.find 2323 left = VM.find 2323 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2324 next_left = VM.find 2324 next_right.
Proof.
 intros H2323 E2004 E2323 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2324 reference_control_expr_2324 reference_control_1_positions reference_control_1_safety reference_control_member_2324) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2324 reference_control_expr_2324 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2324 left H2323)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2324 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2004.
 rewrite E2323.
 reflexivity.
Qed.
Lemma reference_control_ready_2325 old :
 (exists value ground, VM.find 2322 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2324 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2325.
Proof.
 intros H2322 H2324.
 destruct H2322 as [v2322 [G2322 [V2322 T2322]]].
 destruct H2324 as [v2324 [G2324 [V2324 T2324]]].
 unfold reference_control_expr_2325.
apply rc_mux.
{ eapply rc_ref; [exact V2322|exists G2322; exact T2322].
}
{ eapply rc_ref; [exact V2324|exists G2324; exact T2324].
}
Qed.
Lemma reference_control_member_2325 : List.In (2325,reference_control_expr_2325) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 142%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2325_ground inputs path old current result :
 (exists value ground, VM.find 2322 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2324 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2325 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2322 H2324 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2325 reference_control_expr_2325 reference_control_1_positions reference_control_1_safety reference_control_member_2325) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2325 reference_control_expr_2325 inputs path old current result Position Safe Nonreg (reference_control_ready_2325 old H2322 H2324) Step).
Qed.
Theorem reference_control_node_2325_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2322 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2324 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1998 left = VM.find 1998 right ->
 VM.find 2322 left = VM.find 2322 right ->
 VM.find 2324 left = VM.find 2324 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2325 next_left = VM.find 2325 next_right.
Proof.
 intros H2322 H2324 E1998 E2322 E2324 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2325 reference_control_expr_2325 reference_control_1_positions reference_control_1_safety reference_control_member_2325) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2325 reference_control_expr_2325 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2325 left H2322 H2324)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2325 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1998.
 rewrite E2322.
 rewrite E2324.
 reflexivity.
Qed.
Lemma reference_control_ready_2326 old :
 (exists value ground, VM.find 2321 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2325 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2326.
Proof.
 intros H2321 H2325.
 destruct H2321 as [v2321 [G2321 [V2321 T2321]]].
 destruct H2325 as [v2325 [G2325 [V2325 T2325]]].
 unfold reference_control_expr_2326.
apply rc_mux.
{ eapply rc_ref; [exact V2321|exists G2321; exact T2321].
}
{ eapply rc_ref; [exact V2325|exists G2325; exact T2325].
}
Qed.
Lemma reference_control_member_2326 : List.In (2326,reference_control_expr_2326) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 143%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2326_ground inputs path old current result :
 (exists value ground, VM.find 2321 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2325 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2326 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2321 H2325 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2326 reference_control_expr_2326 reference_control_1_positions reference_control_1_safety reference_control_member_2326) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2326 reference_control_expr_2326 inputs path old current result Position Safe Nonreg (reference_control_ready_2326 old H2321 H2325) Step).
Qed.
Theorem reference_control_node_2326_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2321 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2325 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1992 left = VM.find 1992 right ->
 VM.find 2321 left = VM.find 2321 right ->
 VM.find 2325 left = VM.find 2325 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2326 next_left = VM.find 2326 next_right.
Proof.
 intros H2321 H2325 E1992 E2321 E2325 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2326 reference_control_expr_2326 reference_control_1_positions reference_control_1_safety reference_control_member_2326) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2326 reference_control_expr_2326 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2326 left H2321 H2325)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2326 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1992.
 rewrite E2321.
 rewrite E2325.
 reflexivity.
Qed.
Lemma reference_control_ready_2327 old :
 (exists value ground, VM.find 2320 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2326 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2327.
Proof.
 intros H2320 H2326.
 destruct H2320 as [v2320 [G2320 [V2320 T2320]]].
 destruct H2326 as [v2326 [G2326 [V2326 T2326]]].
 unfold reference_control_expr_2327.
apply rc_mux.
{ eapply rc_ref; [exact V2320|exists G2320; exact T2320].
}
{ eapply rc_ref; [exact V2326|exists G2326; exact T2326].
}
Qed.
Lemma reference_control_member_2327 : List.In (2327,reference_control_expr_2327) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 144%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2327_ground inputs path old current result :
 (exists value ground, VM.find 2320 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2326 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2327 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2320 H2326 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2327 reference_control_expr_2327 reference_control_1_positions reference_control_1_safety reference_control_member_2327) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2327 reference_control_expr_2327 inputs path old current result Position Safe Nonreg (reference_control_ready_2327 old H2320 H2326) Step).
Qed.
Theorem reference_control_node_2327_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2320 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2326 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1986 left = VM.find 1986 right ->
 VM.find 2320 left = VM.find 2320 right ->
 VM.find 2326 left = VM.find 2326 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2327 next_left = VM.find 2327 next_right.
Proof.
 intros H2320 H2326 E1986 E2320 E2326 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2327 reference_control_expr_2327 reference_control_1_positions reference_control_1_safety reference_control_member_2327) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2327 reference_control_expr_2327 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2327 left H2320 H2326)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2327 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1986.
 rewrite E2320.
 rewrite E2326.
 reflexivity.
Qed.
Lemma reference_control_ready_2328 old :
 (exists value ground, VM.find 2319 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2327 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2328.
Proof.
 intros H2319 H2327.
 destruct H2319 as [v2319 [G2319 [V2319 T2319]]].
 destruct H2327 as [v2327 [G2327 [V2327 T2327]]].
 unfold reference_control_expr_2328.
apply rc_mux.
{ eapply rc_ref; [exact V2319|exists G2319; exact T2319].
}
{ eapply rc_ref; [exact V2327|exists G2327; exact T2327].
}
Qed.
Lemma reference_control_member_2328 : List.In (2328,reference_control_expr_2328) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 145%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2328_ground inputs path old current result :
 (exists value ground, VM.find 2319 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2327 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2328 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2319 H2327 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2328 reference_control_expr_2328 reference_control_1_positions reference_control_1_safety reference_control_member_2328) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2328 reference_control_expr_2328 inputs path old current result Position Safe Nonreg (reference_control_ready_2328 old H2319 H2327) Step).
Qed.
Theorem reference_control_node_2328_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2319 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2327 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1980 left = VM.find 1980 right ->
 VM.find 2319 left = VM.find 2319 right ->
 VM.find 2327 left = VM.find 2327 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2328 next_left = VM.find 2328 next_right.
Proof.
 intros H2319 H2327 E1980 E2319 E2327 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2328 reference_control_expr_2328 reference_control_1_positions reference_control_1_safety reference_control_member_2328) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2328 reference_control_expr_2328 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2328 left H2319 H2327)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2328 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1980.
 rewrite E2319.
 rewrite E2327.
 reflexivity.
Qed.
Lemma reference_control_ready_2329 old :
 (exists value ground, VM.find 2318 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2328 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2329.
Proof.
 intros H2318 H2328.
 destruct H2318 as [v2318 [G2318 [V2318 T2318]]].
 destruct H2328 as [v2328 [G2328 [V2328 T2328]]].
 unfold reference_control_expr_2329.
apply rc_mux.
{ eapply rc_ref; [exact V2318|exists G2318; exact T2318].
}
{ eapply rc_ref; [exact V2328|exists G2328; exact T2328].
}
Qed.
Lemma reference_control_member_2329 : List.In (2329,reference_control_expr_2329) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 146%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2329_ground inputs path old current result :
 (exists value ground, VM.find 2318 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2328 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2329 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2318 H2328 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2329 reference_control_expr_2329 reference_control_1_positions reference_control_1_safety reference_control_member_2329) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2329 reference_control_expr_2329 inputs path old current result Position Safe Nonreg (reference_control_ready_2329 old H2318 H2328) Step).
Qed.
Theorem reference_control_node_2329_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2318 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2328 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1974 left = VM.find 1974 right ->
 VM.find 2318 left = VM.find 2318 right ->
 VM.find 2328 left = VM.find 2328 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2329 next_left = VM.find 2329 next_right.
Proof.
 intros H2318 H2328 E1974 E2318 E2328 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2329 reference_control_expr_2329 reference_control_1_positions reference_control_1_safety reference_control_member_2329) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2329 reference_control_expr_2329 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2329 left H2318 H2328)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2329 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1974.
 rewrite E2318.
 rewrite E2328.
 reflexivity.
Qed.
Lemma reference_control_ready_2330 old :
 (exists value ground, VM.find 2329 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2330.
Proof.
 intros H2329.
 destruct H2329 as [v2329 [G2329 [V2329 T2329]]].
 unfold reference_control_expr_2330.
apply rc_mux.
{ eapply rc_ref; [exact V2329|exists G2329; exact T2329].
}
{ apply rc_const.
}
Qed.
Lemma reference_control_member_2330 : List.In (2330,reference_control_expr_2330) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 147%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2330_ground inputs path old current result :
 (exists value ground, VM.find 2329 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2330 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2329 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2330 reference_control_expr_2330 reference_control_1_positions reference_control_1_safety reference_control_member_2330) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2330 reference_control_expr_2330 inputs path old current result Position Safe Nonreg (reference_control_ready_2330 old H2329) Step).
Qed.
Theorem reference_control_node_2330_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2329 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1707 left = VM.find 1707 right ->
 VM.find 2329 left = VM.find 2329 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2330 next_left = VM.find 2330 next_right.
Proof.
 intros H2329 E1707 E2329 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2330 reference_control_expr_2330 reference_control_1_positions reference_control_1_safety reference_control_member_2330) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2330 reference_control_expr_2330 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2330 left H2329)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2330 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1707.
 rewrite E2329.
 reflexivity.
Qed.
Lemma reference_control_ready_2331 old :
 (exists value ground, VM.find 2330 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2331.
Proof.
 intros H2330.
 destruct H2330 as [v2330 [G2330 [V2330 T2330]]].
 unfold reference_control_expr_2331.
eapply rc_ref; [exact V2330|exists G2330; exact T2330].
Qed.
Lemma reference_control_member_2331 : List.In (2331,reference_control_expr_2331) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 148%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2331_ground inputs path old current result :
 (exists value ground, VM.find 2330 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2331 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2330 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2331 reference_control_expr_2331 reference_control_1_positions reference_control_1_safety reference_control_member_2331) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2331 reference_control_expr_2331 inputs path old current result Position Safe Nonreg (reference_control_ready_2331 old H2330) Step).
Qed.
Theorem reference_control_node_2331_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2330 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2330 left = VM.find 2330 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2331 next_left = VM.find 2331 next_right.
Proof.
 intros H2330 E2330 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2331 reference_control_expr_2331 reference_control_1_positions reference_control_1_safety reference_control_member_2331) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2331 reference_control_expr_2331 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2331 left H2330)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2331 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2330.
 reflexivity.
Qed.
Lemma reference_control_ready_2332 old :
 reference_control_ready old reference_control_expr_2332.
Proof.
 unfold reference_control_expr_2332.
apply rc_unary.
Qed.
Lemma reference_control_member_2332 : List.In (2332,reference_control_expr_2332) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 149%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2332_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2332 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2332 reference_control_expr_2332 reference_control_1_positions reference_control_1_safety reference_control_member_2332) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2332 reference_control_expr_2332 inputs path old current result Position Safe Nonreg (reference_control_ready_2332 old ) Step).
Qed.
Theorem reference_control_node_2332_congruent inputs path left right next_left next_right :
 VM.find 1977 left = VM.find 1977 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2332 next_left = VM.find 2332 next_right.
Proof.
 intros  E1977 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2332 reference_control_expr_2332 reference_control_1_positions reference_control_1_safety reference_control_member_2332) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2332 reference_control_expr_2332 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2332 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2332 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1977.
 reflexivity.
Qed.
Lemma reference_control_ready_2333 old :
 reference_control_ready old reference_control_expr_2333.
Proof.
 unfold reference_control_expr_2333.
apply rc_unary.
Qed.
Lemma reference_control_member_2333 : List.In (2333,reference_control_expr_2333) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 150%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2333_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2333 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2333 reference_control_expr_2333 reference_control_1_positions reference_control_1_safety reference_control_member_2333) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2333 reference_control_expr_2333 inputs path old current result Position Safe Nonreg (reference_control_ready_2333 old ) Step).
Qed.
Theorem reference_control_node_2333_congruent inputs path left right next_left next_right :
 VM.find 2332 left = VM.find 2332 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2333 next_left = VM.find 2333 next_right.
Proof.
 intros  E2332 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2333 reference_control_expr_2333 reference_control_1_positions reference_control_1_safety reference_control_member_2333) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2333 reference_control_expr_2333 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2333 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2333 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2332.
 reflexivity.
Qed.
Lemma reference_control_ready_2334 old :
 reference_control_ready old reference_control_expr_2334.
Proof.
 unfold reference_control_expr_2334.
apply rc_unary.
Qed.
Lemma reference_control_member_2334 : List.In (2334,reference_control_expr_2334) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 151%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2334_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2334 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2334 reference_control_expr_2334 reference_control_1_positions reference_control_1_safety reference_control_member_2334) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2334 reference_control_expr_2334 inputs path old current result Position Safe Nonreg (reference_control_ready_2334 old ) Step).
Qed.
Theorem reference_control_node_2334_congruent inputs path left right next_left next_right :
 VM.find 2333 left = VM.find 2333 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2334 next_left = VM.find 2334 next_right.
Proof.
 intros  E2333 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2334 reference_control_expr_2334 reference_control_1_positions reference_control_1_safety reference_control_member_2334) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2334 reference_control_expr_2334 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2334 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2334 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2333.
 reflexivity.
Qed.
Lemma reference_control_ready_2335 old :
 reference_control_ready old reference_control_expr_2335.
Proof.
 unfold reference_control_expr_2335.
apply rc_unary.
Qed.
Lemma reference_control_member_2335 : List.In (2335,reference_control_expr_2335) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 152%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2335_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2335 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2335 reference_control_expr_2335 reference_control_1_positions reference_control_1_safety reference_control_member_2335) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2335 reference_control_expr_2335 inputs path old current result Position Safe Nonreg (reference_control_ready_2335 old ) Step).
Qed.
Theorem reference_control_node_2335_congruent inputs path left right next_left next_right :
 VM.find 2334 left = VM.find 2334 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2335 next_left = VM.find 2335 next_right.
Proof.
 intros  E2334 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2335 reference_control_expr_2335 reference_control_1_positions reference_control_1_safety reference_control_member_2335) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2335 reference_control_expr_2335 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2335 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2335 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2334.
 reflexivity.
Qed.
Lemma reference_control_ready_2336 old :
 reference_control_ready old reference_control_expr_2336.
Proof.
 unfold reference_control_expr_2336.
apply rc_unary.
Qed.
Lemma reference_control_member_2336 : List.In (2336,reference_control_expr_2336) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 153%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2336_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2336 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2336 reference_control_expr_2336 reference_control_1_positions reference_control_1_safety reference_control_member_2336) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2336 reference_control_expr_2336 inputs path old current result Position Safe Nonreg (reference_control_ready_2336 old ) Step).
Qed.
Theorem reference_control_node_2336_congruent inputs path left right next_left next_right :
 VM.find 1983 left = VM.find 1983 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2336 next_left = VM.find 2336 next_right.
Proof.
 intros  E1983 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2336 reference_control_expr_2336 reference_control_1_positions reference_control_1_safety reference_control_member_2336) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2336 reference_control_expr_2336 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2336 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2336 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1983.
 reflexivity.
Qed.
Lemma reference_control_ready_2337 old :
 reference_control_ready old reference_control_expr_2337.
Proof.
 unfold reference_control_expr_2337.
apply rc_unary.
Qed.
Lemma reference_control_member_2337 : List.In (2337,reference_control_expr_2337) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 154%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2337_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2337 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2337 reference_control_expr_2337 reference_control_1_positions reference_control_1_safety reference_control_member_2337) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2337 reference_control_expr_2337 inputs path old current result Position Safe Nonreg (reference_control_ready_2337 old ) Step).
Qed.
Theorem reference_control_node_2337_congruent inputs path left right next_left next_right :
 VM.find 2336 left = VM.find 2336 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2337 next_left = VM.find 2337 next_right.
Proof.
 intros  E2336 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2337 reference_control_expr_2337 reference_control_1_positions reference_control_1_safety reference_control_member_2337) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2337 reference_control_expr_2337 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2337 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2337 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2336.
 reflexivity.
Qed.
Lemma reference_control_ready_2338 old :
 reference_control_ready old reference_control_expr_2338.
Proof.
 unfold reference_control_expr_2338.
apply rc_unary.
Qed.
Lemma reference_control_member_2338 : List.In (2338,reference_control_expr_2338) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 155%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2338_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2338 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2338 reference_control_expr_2338 reference_control_1_positions reference_control_1_safety reference_control_member_2338) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2338 reference_control_expr_2338 inputs path old current result Position Safe Nonreg (reference_control_ready_2338 old ) Step).
Qed.
Theorem reference_control_node_2338_congruent inputs path left right next_left next_right :
 VM.find 2337 left = VM.find 2337 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2338 next_left = VM.find 2338 next_right.
Proof.
 intros  E2337 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2338 reference_control_expr_2338 reference_control_1_positions reference_control_1_safety reference_control_member_2338) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2338 reference_control_expr_2338 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2338 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2338 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2337.
 reflexivity.
Qed.
Lemma reference_control_ready_2339 old :
 reference_control_ready old reference_control_expr_2339.
Proof.
 unfold reference_control_expr_2339.
apply rc_unary.
Qed.
Lemma reference_control_member_2339 : List.In (2339,reference_control_expr_2339) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 156%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2339_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2339 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2339 reference_control_expr_2339 reference_control_1_positions reference_control_1_safety reference_control_member_2339) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2339 reference_control_expr_2339 inputs path old current result Position Safe Nonreg (reference_control_ready_2339 old ) Step).
Qed.
Theorem reference_control_node_2339_congruent inputs path left right next_left next_right :
 VM.find 2338 left = VM.find 2338 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2339 next_left = VM.find 2339 next_right.
Proof.
 intros  E2338 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2339 reference_control_expr_2339 reference_control_1_positions reference_control_1_safety reference_control_member_2339) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2339 reference_control_expr_2339 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2339 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2339 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2338.
 reflexivity.
Qed.
Lemma reference_control_ready_2340 old :
 reference_control_ready old reference_control_expr_2340.
Proof.
 unfold reference_control_expr_2340.
apply rc_unary.
Qed.
Lemma reference_control_member_2340 : List.In (2340,reference_control_expr_2340) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 157%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2340_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2340 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2340 reference_control_expr_2340 reference_control_1_positions reference_control_1_safety reference_control_member_2340) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2340 reference_control_expr_2340 inputs path old current result Position Safe Nonreg (reference_control_ready_2340 old ) Step).
Qed.
Theorem reference_control_node_2340_congruent inputs path left right next_left next_right :
 VM.find 1989 left = VM.find 1989 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2340 next_left = VM.find 2340 next_right.
Proof.
 intros  E1989 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2340 reference_control_expr_2340 reference_control_1_positions reference_control_1_safety reference_control_member_2340) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2340 reference_control_expr_2340 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2340 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2340 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1989.
 reflexivity.
Qed.
Lemma reference_control_ready_2341 old :
 reference_control_ready old reference_control_expr_2341.
Proof.
 unfold reference_control_expr_2341.
apply rc_unary.
Qed.
Lemma reference_control_member_2341 : List.In (2341,reference_control_expr_2341) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 158%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2341_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2341 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2341 reference_control_expr_2341 reference_control_1_positions reference_control_1_safety reference_control_member_2341) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2341 reference_control_expr_2341 inputs path old current result Position Safe Nonreg (reference_control_ready_2341 old ) Step).
Qed.
Theorem reference_control_node_2341_congruent inputs path left right next_left next_right :
 VM.find 2340 left = VM.find 2340 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2341 next_left = VM.find 2341 next_right.
Proof.
 intros  E2340 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2341 reference_control_expr_2341 reference_control_1_positions reference_control_1_safety reference_control_member_2341) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2341 reference_control_expr_2341 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2341 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2341 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2340.
 reflexivity.
Qed.
Lemma reference_control_ready_2342 old :
 reference_control_ready old reference_control_expr_2342.
Proof.
 unfold reference_control_expr_2342.
apply rc_unary.
Qed.
Lemma reference_control_member_2342 : List.In (2342,reference_control_expr_2342) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 159%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2342_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2342 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2342 reference_control_expr_2342 reference_control_1_positions reference_control_1_safety reference_control_member_2342) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2342 reference_control_expr_2342 inputs path old current result Position Safe Nonreg (reference_control_ready_2342 old ) Step).
Qed.
Theorem reference_control_node_2342_congruent inputs path left right next_left next_right :
 VM.find 2341 left = VM.find 2341 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2342 next_left = VM.find 2342 next_right.
Proof.
 intros  E2341 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2342 reference_control_expr_2342 reference_control_1_positions reference_control_1_safety reference_control_member_2342) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2342 reference_control_expr_2342 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2342 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2342 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2341.
 reflexivity.
Qed.
Lemma reference_control_ready_2343 old :
 reference_control_ready old reference_control_expr_2343.
Proof.
 unfold reference_control_expr_2343.
apply rc_unary.
Qed.
Lemma reference_control_member_2343 : List.In (2343,reference_control_expr_2343) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 160%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2343_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2343 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2343 reference_control_expr_2343 reference_control_1_positions reference_control_1_safety reference_control_member_2343) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2343 reference_control_expr_2343 inputs path old current result Position Safe Nonreg (reference_control_ready_2343 old ) Step).
Qed.
Theorem reference_control_node_2343_congruent inputs path left right next_left next_right :
 VM.find 2342 left = VM.find 2342 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2343 next_left = VM.find 2343 next_right.
Proof.
 intros  E2342 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2343 reference_control_expr_2343 reference_control_1_positions reference_control_1_safety reference_control_member_2343) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2343 reference_control_expr_2343 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2343 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2343 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2342.
 reflexivity.
Qed.
Lemma reference_control_ready_2344 old :
 reference_control_ready old reference_control_expr_2344.
Proof.
 unfold reference_control_expr_2344.
apply rc_unary.
Qed.
Lemma reference_control_member_2344 : List.In (2344,reference_control_expr_2344) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 161%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2344_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2344 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2344 reference_control_expr_2344 reference_control_1_positions reference_control_1_safety reference_control_member_2344) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2344 reference_control_expr_2344 inputs path old current result Position Safe Nonreg (reference_control_ready_2344 old ) Step).
Qed.
Theorem reference_control_node_2344_congruent inputs path left right next_left next_right :
 VM.find 1995 left = VM.find 1995 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2344 next_left = VM.find 2344 next_right.
Proof.
 intros  E1995 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2344 reference_control_expr_2344 reference_control_1_positions reference_control_1_safety reference_control_member_2344) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2344 reference_control_expr_2344 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2344 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2344 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1995.
 reflexivity.
Qed.
Lemma reference_control_ready_2345 old :
 reference_control_ready old reference_control_expr_2345.
Proof.
 unfold reference_control_expr_2345.
apply rc_unary.
Qed.
Lemma reference_control_member_2345 : List.In (2345,reference_control_expr_2345) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 162%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2345_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2345 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2345 reference_control_expr_2345 reference_control_1_positions reference_control_1_safety reference_control_member_2345) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2345 reference_control_expr_2345 inputs path old current result Position Safe Nonreg (reference_control_ready_2345 old ) Step).
Qed.
Theorem reference_control_node_2345_congruent inputs path left right next_left next_right :
 VM.find 2344 left = VM.find 2344 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2345 next_left = VM.find 2345 next_right.
Proof.
 intros  E2344 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2345 reference_control_expr_2345 reference_control_1_positions reference_control_1_safety reference_control_member_2345) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2345 reference_control_expr_2345 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2345 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2345 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2344.
 reflexivity.
Qed.
Lemma reference_control_ready_2346 old :
 reference_control_ready old reference_control_expr_2346.
Proof.
 unfold reference_control_expr_2346.
apply rc_unary.
Qed.
Lemma reference_control_member_2346 : List.In (2346,reference_control_expr_2346) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 163%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2346_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2346 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2346 reference_control_expr_2346 reference_control_1_positions reference_control_1_safety reference_control_member_2346) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2346 reference_control_expr_2346 inputs path old current result Position Safe Nonreg (reference_control_ready_2346 old ) Step).
Qed.
Theorem reference_control_node_2346_congruent inputs path left right next_left next_right :
 VM.find 2345 left = VM.find 2345 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2346 next_left = VM.find 2346 next_right.
Proof.
 intros  E2345 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2346 reference_control_expr_2346 reference_control_1_positions reference_control_1_safety reference_control_member_2346) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2346 reference_control_expr_2346 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2346 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2346 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2345.
 reflexivity.
Qed.
Lemma reference_control_ready_2347 old :
 reference_control_ready old reference_control_expr_2347.
Proof.
 unfold reference_control_expr_2347.
apply rc_unary.
Qed.
Lemma reference_control_member_2347 : List.In (2347,reference_control_expr_2347) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 164%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2347_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2347 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2347 reference_control_expr_2347 reference_control_1_positions reference_control_1_safety reference_control_member_2347) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2347 reference_control_expr_2347 inputs path old current result Position Safe Nonreg (reference_control_ready_2347 old ) Step).
Qed.
Theorem reference_control_node_2347_congruent inputs path left right next_left next_right :
 VM.find 2346 left = VM.find 2346 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2347 next_left = VM.find 2347 next_right.
Proof.
 intros  E2346 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2347 reference_control_expr_2347 reference_control_1_positions reference_control_1_safety reference_control_member_2347) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2347 reference_control_expr_2347 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2347 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2347 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2346.
 reflexivity.
Qed.
Lemma reference_control_ready_2348 old :
 reference_control_ready old reference_control_expr_2348.
Proof.
 unfold reference_control_expr_2348.
apply rc_unary.
Qed.
Lemma reference_control_member_2348 : List.In (2348,reference_control_expr_2348) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 165%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2348_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2348 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2348 reference_control_expr_2348 reference_control_1_positions reference_control_1_safety reference_control_member_2348) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2348 reference_control_expr_2348 inputs path old current result Position Safe Nonreg (reference_control_ready_2348 old ) Step).
Qed.
Theorem reference_control_node_2348_congruent inputs path left right next_left next_right :
 VM.find 2001 left = VM.find 2001 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2348 next_left = VM.find 2348 next_right.
Proof.
 intros  E2001 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2348 reference_control_expr_2348 reference_control_1_positions reference_control_1_safety reference_control_member_2348) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2348 reference_control_expr_2348 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2348 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2348 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2001.
 reflexivity.
Qed.
Lemma reference_control_ready_2349 old :
 reference_control_ready old reference_control_expr_2349.
Proof.
 unfold reference_control_expr_2349.
apply rc_unary.
Qed.
Lemma reference_control_member_2349 : List.In (2349,reference_control_expr_2349) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 166%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2349_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2349 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2349 reference_control_expr_2349 reference_control_1_positions reference_control_1_safety reference_control_member_2349) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2349 reference_control_expr_2349 inputs path old current result Position Safe Nonreg (reference_control_ready_2349 old ) Step).
Qed.
Theorem reference_control_node_2349_congruent inputs path left right next_left next_right :
 VM.find 2348 left = VM.find 2348 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2349 next_left = VM.find 2349 next_right.
Proof.
 intros  E2348 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2349 reference_control_expr_2349 reference_control_1_positions reference_control_1_safety reference_control_member_2349) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2349 reference_control_expr_2349 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2349 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2349 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2348.
 reflexivity.
Qed.
Lemma reference_control_ready_2350 old :
 reference_control_ready old reference_control_expr_2350.
Proof.
 unfold reference_control_expr_2350.
apply rc_unary.
Qed.
Lemma reference_control_member_2350 : List.In (2350,reference_control_expr_2350) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 167%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2350_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2350 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2350 reference_control_expr_2350 reference_control_1_positions reference_control_1_safety reference_control_member_2350) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2350 reference_control_expr_2350 inputs path old current result Position Safe Nonreg (reference_control_ready_2350 old ) Step).
Qed.
Theorem reference_control_node_2350_congruent inputs path left right next_left next_right :
 VM.find 2349 left = VM.find 2349 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2350 next_left = VM.find 2350 next_right.
Proof.
 intros  E2349 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2350 reference_control_expr_2350 reference_control_1_positions reference_control_1_safety reference_control_member_2350) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2350 reference_control_expr_2350 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2350 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2350 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2349.
 reflexivity.
Qed.
Lemma reference_control_ready_2351 old :
 reference_control_ready old reference_control_expr_2351.
Proof.
 unfold reference_control_expr_2351.
apply rc_unary.
Qed.
Lemma reference_control_member_2351 : List.In (2351,reference_control_expr_2351) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 168%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2351_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2351 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2351 reference_control_expr_2351 reference_control_1_positions reference_control_1_safety reference_control_member_2351) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2351 reference_control_expr_2351 inputs path old current result Position Safe Nonreg (reference_control_ready_2351 old ) Step).
Qed.
Theorem reference_control_node_2351_congruent inputs path left right next_left next_right :
 VM.find 2350 left = VM.find 2350 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2351 next_left = VM.find 2351 next_right.
Proof.
 intros  E2350 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2351 reference_control_expr_2351 reference_control_1_positions reference_control_1_safety reference_control_member_2351) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2351 reference_control_expr_2351 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2351 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2351 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2350.
 reflexivity.
Qed.
Lemma reference_control_ready_2352 old :
 reference_control_ready old reference_control_expr_2352.
Proof.
 unfold reference_control_expr_2352.
apply rc_unary.
Qed.
Lemma reference_control_member_2352 : List.In (2352,reference_control_expr_2352) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 169%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2352_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2352 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2352 reference_control_expr_2352 reference_control_1_positions reference_control_1_safety reference_control_member_2352) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2352 reference_control_expr_2352 inputs path old current result Position Safe Nonreg (reference_control_ready_2352 old ) Step).
Qed.
Theorem reference_control_node_2352_congruent inputs path left right next_left next_right :
 VM.find 2007 left = VM.find 2007 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2352 next_left = VM.find 2352 next_right.
Proof.
 intros  E2007 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2352 reference_control_expr_2352 reference_control_1_positions reference_control_1_safety reference_control_member_2352) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2352 reference_control_expr_2352 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2352 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2352 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2007.
 reflexivity.
Qed.
Lemma reference_control_ready_2353 old :
 reference_control_ready old reference_control_expr_2353.
Proof.
 unfold reference_control_expr_2353.
apply rc_unary.
Qed.
Lemma reference_control_member_2353 : List.In (2353,reference_control_expr_2353) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 170%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2353_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2353 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2353 reference_control_expr_2353 reference_control_1_positions reference_control_1_safety reference_control_member_2353) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2353 reference_control_expr_2353 inputs path old current result Position Safe Nonreg (reference_control_ready_2353 old ) Step).
Qed.
Theorem reference_control_node_2353_congruent inputs path left right next_left next_right :
 VM.find 2352 left = VM.find 2352 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2353 next_left = VM.find 2353 next_right.
Proof.
 intros  E2352 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2353 reference_control_expr_2353 reference_control_1_positions reference_control_1_safety reference_control_member_2353) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2353 reference_control_expr_2353 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2353 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2353 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2352.
 reflexivity.
Qed.
Lemma reference_control_ready_2354 old :
 reference_control_ready old reference_control_expr_2354.
Proof.
 unfold reference_control_expr_2354.
apply rc_unary.
Qed.
Lemma reference_control_member_2354 : List.In (2354,reference_control_expr_2354) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 171%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2354_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2354 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2354 reference_control_expr_2354 reference_control_1_positions reference_control_1_safety reference_control_member_2354) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2354 reference_control_expr_2354 inputs path old current result Position Safe Nonreg (reference_control_ready_2354 old ) Step).
Qed.
Theorem reference_control_node_2354_congruent inputs path left right next_left next_right :
 VM.find 2353 left = VM.find 2353 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2354 next_left = VM.find 2354 next_right.
Proof.
 intros  E2353 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2354 reference_control_expr_2354 reference_control_1_positions reference_control_1_safety reference_control_member_2354) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2354 reference_control_expr_2354 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2354 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2354 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2353.
 reflexivity.
Qed.
Lemma reference_control_ready_2355 old :
 reference_control_ready old reference_control_expr_2355.
Proof.
 unfold reference_control_expr_2355.
apply rc_unary.
Qed.
Lemma reference_control_member_2355 : List.In (2355,reference_control_expr_2355) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 172%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2355_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2355 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2355 reference_control_expr_2355 reference_control_1_positions reference_control_1_safety reference_control_member_2355) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2355 reference_control_expr_2355 inputs path old current result Position Safe Nonreg (reference_control_ready_2355 old ) Step).
Qed.
Theorem reference_control_node_2355_congruent inputs path left right next_left next_right :
 VM.find 2354 left = VM.find 2354 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2355 next_left = VM.find 2355 next_right.
Proof.
 intros  E2354 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2355 reference_control_expr_2355 reference_control_1_positions reference_control_1_safety reference_control_member_2355) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2355 reference_control_expr_2355 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2355 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2355 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2354.
 reflexivity.
Qed.
Lemma reference_control_ready_2356 old :
 reference_control_ready old reference_control_expr_2356.
Proof.
 unfold reference_control_expr_2356.
apply rc_binary.
Qed.
Lemma reference_control_member_2356 : List.In (2356,reference_control_expr_2356) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 173%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2356_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2356 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2356 reference_control_expr_2356 reference_control_1_positions reference_control_1_safety reference_control_member_2356) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2356 reference_control_expr_2356 inputs path old current result Position Safe Nonreg (reference_control_ready_2356 old ) Step).
Qed.
Theorem reference_control_node_2356_congruent inputs path left right next_left next_right :
 VM.find 1884 left = VM.find 1884 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2356 next_left = VM.find 2356 next_right.
Proof.
 intros  E1884 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2356 reference_control_expr_2356 reference_control_1_positions reference_control_1_safety reference_control_member_2356) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2356 reference_control_expr_2356 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2356 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2356 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1884.
 reflexivity.
Qed.
Lemma reference_control_ready_2357 old :
 reference_control_ready old reference_control_expr_2357.
Proof.
 unfold reference_control_expr_2357.
apply rc_binary.
Qed.
Lemma reference_control_member_2357 : List.In (2357,reference_control_expr_2357) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 174%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2357_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2357 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2357 reference_control_expr_2357 reference_control_1_positions reference_control_1_safety reference_control_member_2357) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2357 reference_control_expr_2357 inputs path old current result Position Safe Nonreg (reference_control_ready_2357 old ) Step).
Qed.
Theorem reference_control_node_2357_congruent inputs path left right next_left next_right :
 VM.find 2356 left = VM.find 2356 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2357 next_left = VM.find 2357 next_right.
Proof.
 intros  E2356 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2357 reference_control_expr_2357 reference_control_1_positions reference_control_1_safety reference_control_member_2357) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2357 reference_control_expr_2357 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2357 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2357 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2356.
 reflexivity.
Qed.
Lemma reference_control_ready_2358 old :
 reference_control_ready old reference_control_expr_2358.
Proof.
 unfold reference_control_expr_2358.
apply rc_unary.
Qed.
Lemma reference_control_member_2358 : List.In (2358,reference_control_expr_2358) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 175%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2358_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2358 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2358 reference_control_expr_2358 reference_control_1_positions reference_control_1_safety reference_control_member_2358) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2358 reference_control_expr_2358 inputs path old current result Position Safe Nonreg (reference_control_ready_2358 old ) Step).
Qed.
Theorem reference_control_node_2358_congruent inputs path left right next_left next_right :
 VM.find 1884 left = VM.find 1884 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2358 next_left = VM.find 2358 next_right.
Proof.
 intros  E1884 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2358 reference_control_expr_2358 reference_control_1_positions reference_control_1_safety reference_control_member_2358) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2358 reference_control_expr_2358 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2358 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2358 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1884.
 reflexivity.
Qed.
Lemma reference_control_ready_2359 old :
 reference_control_ready old reference_control_expr_2359.
Proof.
 unfold reference_control_expr_2359.
apply rc_unary.
Qed.
Lemma reference_control_member_2359 : List.In (2359,reference_control_expr_2359) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 176%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2359_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2359 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2359 reference_control_expr_2359 reference_control_1_positions reference_control_1_safety reference_control_member_2359) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2359 reference_control_expr_2359 inputs path old current result Position Safe Nonreg (reference_control_ready_2359 old ) Step).
Qed.
Theorem reference_control_node_2359_congruent inputs path left right next_left next_right :
 VM.find 2358 left = VM.find 2358 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2359 next_left = VM.find 2359 next_right.
Proof.
 intros  E2358 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2359 reference_control_expr_2359 reference_control_1_positions reference_control_1_safety reference_control_member_2359) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2359 reference_control_expr_2359 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2359 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2359 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2358.
 reflexivity.
Qed.
Lemma reference_control_ready_2360 old :
 reference_control_ready old reference_control_expr_2360.
Proof.
 unfold reference_control_expr_2360.
apply rc_unary.
Qed.
Lemma reference_control_member_2360 : List.In (2360,reference_control_expr_2360) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 177%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2360_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2360 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2360 reference_control_expr_2360 reference_control_1_positions reference_control_1_safety reference_control_member_2360) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2360 reference_control_expr_2360 inputs path old current result Position Safe Nonreg (reference_control_ready_2360 old ) Step).
Qed.
Theorem reference_control_node_2360_congruent inputs path left right next_left next_right :
 VM.find 2359 left = VM.find 2359 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2360 next_left = VM.find 2360 next_right.
Proof.
 intros  E2359 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2360 reference_control_expr_2360 reference_control_1_positions reference_control_1_safety reference_control_member_2360) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2360 reference_control_expr_2360 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2360 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2360 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2359.
 reflexivity.
Qed.
Lemma reference_control_ready_2361 old :
 (exists value ground, VM.find 2360 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2361.
Proof.
 intros H2360.
 destruct H2360 as [v2360 [G2360 [V2360 T2360]]].
 unfold reference_control_expr_2361.
apply rc_mux.
{ eapply rc_ref; [exact V2360|exists G2360; exact T2360].
}
{ apply rc_const.
}
Qed.
Lemma reference_control_member_2361 : List.In (2361,reference_control_expr_2361) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 178%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2361_ground inputs path old current result :
 (exists value ground, VM.find 2360 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2361 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2360 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2361 reference_control_expr_2361 reference_control_1_positions reference_control_1_safety reference_control_member_2361) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2361 reference_control_expr_2361 inputs path old current result Position Safe Nonreg (reference_control_ready_2361 old H2360) Step).
Qed.
Theorem reference_control_node_2361_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2360 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2357 left = VM.find 2357 right ->
 VM.find 2360 left = VM.find 2360 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2361 next_left = VM.find 2361 next_right.
Proof.
 intros H2360 E2357 E2360 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2361 reference_control_expr_2361 reference_control_1_positions reference_control_1_safety reference_control_member_2361) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2361 reference_control_expr_2361 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2361 left H2360)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2361 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2357.
 rewrite E2360.
 reflexivity.
Qed.
Lemma reference_control_ready_2362 old :
 (exists value ground, VM.find 2355 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2361 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2362.
Proof.
 intros H2355 H2361.
 destruct H2355 as [v2355 [G2355 [V2355 T2355]]].
 destruct H2361 as [v2361 [G2361 [V2361 T2361]]].
 unfold reference_control_expr_2362.
apply rc_mux.
{ eapply rc_ref; [exact V2355|exists G2355; exact T2355].
}
{ eapply rc_ref; [exact V2361|exists G2361; exact T2361].
}
Qed.
Lemma reference_control_member_2362 : List.In (2362,reference_control_expr_2362) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 179%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2362_ground inputs path old current result :
 (exists value ground, VM.find 2355 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2361 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2362 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2355 H2361 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2362 reference_control_expr_2362 reference_control_1_positions reference_control_1_safety reference_control_member_2362) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2362 reference_control_expr_2362 inputs path old current result Position Safe Nonreg (reference_control_ready_2362 old H2355 H2361) Step).
Qed.
Theorem reference_control_node_2362_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2355 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2361 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2004 left = VM.find 2004 right ->
 VM.find 2355 left = VM.find 2355 right ->
 VM.find 2361 left = VM.find 2361 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2362 next_left = VM.find 2362 next_right.
Proof.
 intros H2355 H2361 E2004 E2355 E2361 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2362 reference_control_expr_2362 reference_control_1_positions reference_control_1_safety reference_control_member_2362) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2362 reference_control_expr_2362 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2362 left H2355 H2361)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2362 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2004.
 rewrite E2355.
 rewrite E2361.
 reflexivity.
Qed.
Lemma reference_control_ready_2363 old :
 (exists value ground, VM.find 2351 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2362 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2363.
Proof.
 intros H2351 H2362.
 destruct H2351 as [v2351 [G2351 [V2351 T2351]]].
 destruct H2362 as [v2362 [G2362 [V2362 T2362]]].
 unfold reference_control_expr_2363.
apply rc_mux.
{ eapply rc_ref; [exact V2351|exists G2351; exact T2351].
}
{ eapply rc_ref; [exact V2362|exists G2362; exact T2362].
}
Qed.
Lemma reference_control_member_2363 : List.In (2363,reference_control_expr_2363) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 180%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2363_ground inputs path old current result :
 (exists value ground, VM.find 2351 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2362 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2363 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2351 H2362 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2363 reference_control_expr_2363 reference_control_1_positions reference_control_1_safety reference_control_member_2363) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2363 reference_control_expr_2363 inputs path old current result Position Safe Nonreg (reference_control_ready_2363 old H2351 H2362) Step).
Qed.
Theorem reference_control_node_2363_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2351 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2362 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1998 left = VM.find 1998 right ->
 VM.find 2351 left = VM.find 2351 right ->
 VM.find 2362 left = VM.find 2362 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2363 next_left = VM.find 2363 next_right.
Proof.
 intros H2351 H2362 E1998 E2351 E2362 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2363 reference_control_expr_2363 reference_control_1_positions reference_control_1_safety reference_control_member_2363) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2363 reference_control_expr_2363 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2363 left H2351 H2362)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2363 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1998.
 rewrite E2351.
 rewrite E2362.
 reflexivity.
Qed.
Lemma reference_control_ready_2364 old :
 (exists value ground, VM.find 2347 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2363 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2364.
Proof.
 intros H2347 H2363.
 destruct H2347 as [v2347 [G2347 [V2347 T2347]]].
 destruct H2363 as [v2363 [G2363 [V2363 T2363]]].
 unfold reference_control_expr_2364.
apply rc_mux.
{ eapply rc_ref; [exact V2347|exists G2347; exact T2347].
}
{ eapply rc_ref; [exact V2363|exists G2363; exact T2363].
}
Qed.
Lemma reference_control_member_2364 : List.In (2364,reference_control_expr_2364) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 181%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2364_ground inputs path old current result :
 (exists value ground, VM.find 2347 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2363 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2364 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2347 H2363 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2364 reference_control_expr_2364 reference_control_1_positions reference_control_1_safety reference_control_member_2364) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2364 reference_control_expr_2364 inputs path old current result Position Safe Nonreg (reference_control_ready_2364 old H2347 H2363) Step).
Qed.
Theorem reference_control_node_2364_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2347 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2363 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1992 left = VM.find 1992 right ->
 VM.find 2347 left = VM.find 2347 right ->
 VM.find 2363 left = VM.find 2363 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2364 next_left = VM.find 2364 next_right.
Proof.
 intros H2347 H2363 E1992 E2347 E2363 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2364 reference_control_expr_2364 reference_control_1_positions reference_control_1_safety reference_control_member_2364) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2364 reference_control_expr_2364 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2364 left H2347 H2363)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2364 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1992.
 rewrite E2347.
 rewrite E2363.
 reflexivity.
Qed.
Lemma reference_control_ready_2365 old :
 (exists value ground, VM.find 2343 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2364 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2365.
Proof.
 intros H2343 H2364.
 destruct H2343 as [v2343 [G2343 [V2343 T2343]]].
 destruct H2364 as [v2364 [G2364 [V2364 T2364]]].
 unfold reference_control_expr_2365.
apply rc_mux.
{ eapply rc_ref; [exact V2343|exists G2343; exact T2343].
}
{ eapply rc_ref; [exact V2364|exists G2364; exact T2364].
}
Qed.
Lemma reference_control_member_2365 : List.In (2365,reference_control_expr_2365) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 182%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2365_ground inputs path old current result :
 (exists value ground, VM.find 2343 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2364 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2365 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2343 H2364 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2365 reference_control_expr_2365 reference_control_1_positions reference_control_1_safety reference_control_member_2365) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2365 reference_control_expr_2365 inputs path old current result Position Safe Nonreg (reference_control_ready_2365 old H2343 H2364) Step).
Qed.
Theorem reference_control_node_2365_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2343 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2364 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1986 left = VM.find 1986 right ->
 VM.find 2343 left = VM.find 2343 right ->
 VM.find 2364 left = VM.find 2364 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2365 next_left = VM.find 2365 next_right.
Proof.
 intros H2343 H2364 E1986 E2343 E2364 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2365 reference_control_expr_2365 reference_control_1_positions reference_control_1_safety reference_control_member_2365) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2365 reference_control_expr_2365 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2365 left H2343 H2364)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2365 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1986.
 rewrite E2343.
 rewrite E2364.
 reflexivity.
Qed.
Lemma reference_control_ready_2366 old :
 (exists value ground, VM.find 2339 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2365 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2366.
Proof.
 intros H2339 H2365.
 destruct H2339 as [v2339 [G2339 [V2339 T2339]]].
 destruct H2365 as [v2365 [G2365 [V2365 T2365]]].
 unfold reference_control_expr_2366.
apply rc_mux.
{ eapply rc_ref; [exact V2339|exists G2339; exact T2339].
}
{ eapply rc_ref; [exact V2365|exists G2365; exact T2365].
}
Qed.
Lemma reference_control_member_2366 : List.In (2366,reference_control_expr_2366) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 183%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2366_ground inputs path old current result :
 (exists value ground, VM.find 2339 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2365 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2366 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2339 H2365 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2366 reference_control_expr_2366 reference_control_1_positions reference_control_1_safety reference_control_member_2366) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2366 reference_control_expr_2366 inputs path old current result Position Safe Nonreg (reference_control_ready_2366 old H2339 H2365) Step).
Qed.
Theorem reference_control_node_2366_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2339 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2365 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1980 left = VM.find 1980 right ->
 VM.find 2339 left = VM.find 2339 right ->
 VM.find 2365 left = VM.find 2365 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2366 next_left = VM.find 2366 next_right.
Proof.
 intros H2339 H2365 E1980 E2339 E2365 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2366 reference_control_expr_2366 reference_control_1_positions reference_control_1_safety reference_control_member_2366) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2366 reference_control_expr_2366 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2366 left H2339 H2365)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2366 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1980.
 rewrite E2339.
 rewrite E2365.
 reflexivity.
Qed.
Lemma reference_control_ready_2367 old :
 (exists value ground, VM.find 2335 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2366 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2367.
Proof.
 intros H2335 H2366.
 destruct H2335 as [v2335 [G2335 [V2335 T2335]]].
 destruct H2366 as [v2366 [G2366 [V2366 T2366]]].
 unfold reference_control_expr_2367.
apply rc_mux.
{ eapply rc_ref; [exact V2335|exists G2335; exact T2335].
}
{ eapply rc_ref; [exact V2366|exists G2366; exact T2366].
}
Qed.
Lemma reference_control_member_2367 : List.In (2367,reference_control_expr_2367) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 184%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2367_ground inputs path old current result :
 (exists value ground, VM.find 2335 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2366 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2367 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2335 H2366 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2367 reference_control_expr_2367 reference_control_1_positions reference_control_1_safety reference_control_member_2367) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2367 reference_control_expr_2367 inputs path old current result Position Safe Nonreg (reference_control_ready_2367 old H2335 H2366) Step).
Qed.
Theorem reference_control_node_2367_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2335 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2366 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1974 left = VM.find 1974 right ->
 VM.find 2335 left = VM.find 2335 right ->
 VM.find 2366 left = VM.find 2366 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2367 next_left = VM.find 2367 next_right.
Proof.
 intros H2335 H2366 E1974 E2335 E2366 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2367 reference_control_expr_2367 reference_control_1_positions reference_control_1_safety reference_control_member_2367) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2367 reference_control_expr_2367 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2367 left H2335 H2366)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2367 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1974.
 rewrite E2335.
 rewrite E2366.
 reflexivity.
Qed.
Lemma reference_control_ready_2368 old :
 (exists value ground, VM.find 2367 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2368.
Proof.
 intros H2367.
 destruct H2367 as [v2367 [G2367 [V2367 T2367]]].
 unfold reference_control_expr_2368.
apply rc_mux.
{ eapply rc_ref; [exact V2367|exists G2367; exact T2367].
}
{ apply rc_const.
}
Qed.
Lemma reference_control_member_2368 : List.In (2368,reference_control_expr_2368) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 185%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2368_ground inputs path old current result :
 (exists value ground, VM.find 2367 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2368 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2367 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2368 reference_control_expr_2368 reference_control_1_positions reference_control_1_safety reference_control_member_2368) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2368 reference_control_expr_2368 inputs path old current result Position Safe Nonreg (reference_control_ready_2368 old H2367) Step).
Qed.
Theorem reference_control_node_2368_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2367 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1707 left = VM.find 1707 right ->
 VM.find 2367 left = VM.find 2367 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2368 next_left = VM.find 2368 next_right.
Proof.
 intros H2367 E1707 E2367 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2368 reference_control_expr_2368 reference_control_1_positions reference_control_1_safety reference_control_member_2368) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2368 reference_control_expr_2368 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2368 left H2367)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2368 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1707.
 rewrite E2367.
 reflexivity.
Qed.
Lemma reference_control_ready_2369 old :
 (exists value ground, VM.find 2368 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2369.
Proof.
 intros H2368.
 destruct H2368 as [v2368 [G2368 [V2368 T2368]]].
 unfold reference_control_expr_2369.
eapply rc_ref; [exact V2368|exists G2368; exact T2368].
Qed.
Lemma reference_control_member_2369 : List.In (2369,reference_control_expr_2369) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 186%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2369_ground inputs path old current result :
 (exists value ground, VM.find 2368 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2369 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2368 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2369 reference_control_expr_2369 reference_control_1_positions reference_control_1_safety reference_control_member_2369) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2369 reference_control_expr_2369 inputs path old current result Position Safe Nonreg (reference_control_ready_2369 old H2368) Step).
Qed.
Theorem reference_control_node_2369_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2368 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2368 left = VM.find 2368 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2369 next_left = VM.find 2369 next_right.
Proof.
 intros H2368 E2368 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2369 reference_control_expr_2369 reference_control_1_positions reference_control_1_safety reference_control_member_2369) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2369 reference_control_expr_2369 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2369 left H2368)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2369 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2368.
 reflexivity.
Qed.
Lemma reference_control_ready_2370 old :
 reference_control_ready old reference_control_expr_2370.
Proof.
 unfold reference_control_expr_2370.
apply rc_binary.
Qed.
Lemma reference_control_member_2370 : List.In (2370,reference_control_expr_2370) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 187%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2370_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2370 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2370 reference_control_expr_2370 reference_control_1_positions reference_control_1_safety reference_control_member_2370) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2370 reference_control_expr_2370 inputs path old current result Position Safe Nonreg (reference_control_ready_2370 old ) Step).
Qed.
Theorem reference_control_node_2370_congruent inputs path left right next_left next_right :
 VM.find 2331 left = VM.find 2331 right ->
 VM.find 2369 left = VM.find 2369 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2370 next_left = VM.find 2370 next_right.
Proof.
 intros  E2331 E2369 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2370 reference_control_expr_2370 reference_control_1_positions reference_control_1_safety reference_control_member_2370) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2370 reference_control_expr_2370 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2370 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2370 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2331.
 rewrite E2369.
 reflexivity.
Qed.
Lemma reference_control_ready_2371 old :
 reference_control_ready old reference_control_expr_2371.
Proof.
 unfold reference_control_expr_2371.
apply rc_unary.
Qed.
Lemma reference_control_member_2371 : List.In (2371,reference_control_expr_2371) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 188%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2371_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2371 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2371 reference_control_expr_2371 reference_control_1_positions reference_control_1_safety reference_control_member_2371) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2371 reference_control_expr_2371 inputs path old current result Position Safe Nonreg (reference_control_ready_2371 old ) Step).
Qed.
Theorem reference_control_node_2371_congruent inputs path left right next_left next_right :
 VM.find 1975 left = VM.find 1975 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2371 next_left = VM.find 2371 next_right.
Proof.
 intros  E1975 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2371 reference_control_expr_2371 reference_control_1_positions reference_control_1_safety reference_control_member_2371) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2371 reference_control_expr_2371 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2371 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2371 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1975.
 reflexivity.
Qed.
Lemma reference_control_ready_2372 old :
 reference_control_ready old reference_control_expr_2372.
Proof.
 unfold reference_control_expr_2372.
apply rc_unary.
Qed.
Lemma reference_control_member_2372 : List.In (2372,reference_control_expr_2372) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 189%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2372_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2372 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2372 reference_control_expr_2372 reference_control_1_positions reference_control_1_safety reference_control_member_2372) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2372 reference_control_expr_2372 inputs path old current result Position Safe Nonreg (reference_control_ready_2372 old ) Step).
Qed.
Theorem reference_control_node_2372_congruent inputs path left right next_left next_right :
 VM.find 1981 left = VM.find 1981 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2372 next_left = VM.find 2372 next_right.
Proof.
 intros  E1981 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2372 reference_control_expr_2372 reference_control_1_positions reference_control_1_safety reference_control_member_2372) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2372 reference_control_expr_2372 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2372 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2372 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1981.
 reflexivity.
Qed.
Lemma reference_control_ready_2373 old :
 reference_control_ready old reference_control_expr_2373.
Proof.
 unfold reference_control_expr_2373.
apply rc_unary.
Qed.
Lemma reference_control_member_2373 : List.In (2373,reference_control_expr_2373) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 190%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2373_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2373 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2373 reference_control_expr_2373 reference_control_1_positions reference_control_1_safety reference_control_member_2373) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2373 reference_control_expr_2373 inputs path old current result Position Safe Nonreg (reference_control_ready_2373 old ) Step).
Qed.
Theorem reference_control_node_2373_congruent inputs path left right next_left next_right :
 VM.find 1987 left = VM.find 1987 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2373 next_left = VM.find 2373 next_right.
Proof.
 intros  E1987 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2373 reference_control_expr_2373 reference_control_1_positions reference_control_1_safety reference_control_member_2373) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2373 reference_control_expr_2373 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2373 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2373 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1987.
 reflexivity.
Qed.
Lemma reference_control_ready_2374 old :
 reference_control_ready old reference_control_expr_2374.
Proof.
 unfold reference_control_expr_2374.
apply rc_unary.
Qed.
Lemma reference_control_member_2374 : List.In (2374,reference_control_expr_2374) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 191%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2374_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2374 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2374 reference_control_expr_2374 reference_control_1_positions reference_control_1_safety reference_control_member_2374) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2374 reference_control_expr_2374 inputs path old current result Position Safe Nonreg (reference_control_ready_2374 old ) Step).
Qed.
Theorem reference_control_node_2374_congruent inputs path left right next_left next_right :
 VM.find 1993 left = VM.find 1993 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2374 next_left = VM.find 2374 next_right.
Proof.
 intros  E1993 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2374 reference_control_expr_2374 reference_control_1_positions reference_control_1_safety reference_control_member_2374) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2374 reference_control_expr_2374 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2374 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2374 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1993.
 reflexivity.
Qed.
Lemma reference_control_ready_2375 old :
 reference_control_ready old reference_control_expr_2375.
Proof.
 unfold reference_control_expr_2375.
apply rc_unary.
Qed.
Lemma reference_control_member_2375 : List.In (2375,reference_control_expr_2375) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 192%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2375_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2375 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2375 reference_control_expr_2375 reference_control_1_positions reference_control_1_safety reference_control_member_2375) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2375 reference_control_expr_2375 inputs path old current result Position Safe Nonreg (reference_control_ready_2375 old ) Step).
Qed.
Theorem reference_control_node_2375_congruent inputs path left right next_left next_right :
 VM.find 1999 left = VM.find 1999 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2375 next_left = VM.find 2375 next_right.
Proof.
 intros  E1999 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2375 reference_control_expr_2375 reference_control_1_positions reference_control_1_safety reference_control_member_2375) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2375 reference_control_expr_2375 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2375 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2375 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1999.
 reflexivity.
Qed.
Lemma reference_control_ready_2376 old :
 reference_control_ready old reference_control_expr_2376.
Proof.
 unfold reference_control_expr_2376.
apply rc_unary.
Qed.
Lemma reference_control_member_2376 : List.In (2376,reference_control_expr_2376) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 193%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2376_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2376 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2376 reference_control_expr_2376 reference_control_1_positions reference_control_1_safety reference_control_member_2376) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2376 reference_control_expr_2376 inputs path old current result Position Safe Nonreg (reference_control_ready_2376 old ) Step).
Qed.
Theorem reference_control_node_2376_congruent inputs path left right next_left next_right :
 VM.find 2005 left = VM.find 2005 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2376 next_left = VM.find 2376 next_right.
Proof.
 intros  E2005 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2376 reference_control_expr_2376 reference_control_1_positions reference_control_1_safety reference_control_member_2376) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2376 reference_control_expr_2376 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2376 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2376 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2005.
 reflexivity.
Qed.
Lemma reference_control_ready_2377 old :
 (exists value ground, VM.find 2376 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2377.
Proof.
 intros H2376.
 destruct H2376 as [v2376 [G2376 [V2376 T2376]]].
 unfold reference_control_expr_2377.
apply rc_mux.
{ eapply rc_ref; [exact V2376|exists G2376; exact T2376].
}
{ apply rc_const.
}
Qed.
Lemma reference_control_member_2377 : List.In (2377,reference_control_expr_2377) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 194%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2377_ground inputs path old current result :
 (exists value ground, VM.find 2376 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2377 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2376 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2377 reference_control_expr_2377 reference_control_1_positions reference_control_1_safety reference_control_member_2377) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2377 reference_control_expr_2377 inputs path old current result Position Safe Nonreg (reference_control_ready_2377 old H2376) Step).
Qed.
Theorem reference_control_node_2377_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2376 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2004 left = VM.find 2004 right ->
 VM.find 2376 left = VM.find 2376 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2377 next_left = VM.find 2377 next_right.
Proof.
 intros H2376 E2004 E2376 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2377 reference_control_expr_2377 reference_control_1_positions reference_control_1_safety reference_control_member_2377) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2377 reference_control_expr_2377 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2377 left H2376)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2377 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2004.
 rewrite E2376.
 reflexivity.
Qed.
Lemma reference_control_ready_2378 old :
 (exists value ground, VM.find 2375 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2377 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2378.
Proof.
 intros H2375 H2377.
 destruct H2375 as [v2375 [G2375 [V2375 T2375]]].
 destruct H2377 as [v2377 [G2377 [V2377 T2377]]].
 unfold reference_control_expr_2378.
apply rc_mux.
{ eapply rc_ref; [exact V2375|exists G2375; exact T2375].
}
{ eapply rc_ref; [exact V2377|exists G2377; exact T2377].
}
Qed.
Lemma reference_control_member_2378 : List.In (2378,reference_control_expr_2378) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 195%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2378_ground inputs path old current result :
 (exists value ground, VM.find 2375 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2377 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2378 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2375 H2377 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2378 reference_control_expr_2378 reference_control_1_positions reference_control_1_safety reference_control_member_2378) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2378 reference_control_expr_2378 inputs path old current result Position Safe Nonreg (reference_control_ready_2378 old H2375 H2377) Step).
Qed.
Theorem reference_control_node_2378_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2375 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2377 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1998 left = VM.find 1998 right ->
 VM.find 2375 left = VM.find 2375 right ->
 VM.find 2377 left = VM.find 2377 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2378 next_left = VM.find 2378 next_right.
Proof.
 intros H2375 H2377 E1998 E2375 E2377 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2378 reference_control_expr_2378 reference_control_1_positions reference_control_1_safety reference_control_member_2378) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2378 reference_control_expr_2378 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2378 left H2375 H2377)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2378 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1998.
 rewrite E2375.
 rewrite E2377.
 reflexivity.
Qed.
Lemma reference_control_ready_2379 old :
 (exists value ground, VM.find 2374 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2378 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2379.
Proof.
 intros H2374 H2378.
 destruct H2374 as [v2374 [G2374 [V2374 T2374]]].
 destruct H2378 as [v2378 [G2378 [V2378 T2378]]].
 unfold reference_control_expr_2379.
apply rc_mux.
{ eapply rc_ref; [exact V2374|exists G2374; exact T2374].
}
{ eapply rc_ref; [exact V2378|exists G2378; exact T2378].
}
Qed.
Lemma reference_control_member_2379 : List.In (2379,reference_control_expr_2379) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 196%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2379_ground inputs path old current result :
 (exists value ground, VM.find 2374 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2378 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2379 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2374 H2378 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2379 reference_control_expr_2379 reference_control_1_positions reference_control_1_safety reference_control_member_2379) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2379 reference_control_expr_2379 inputs path old current result Position Safe Nonreg (reference_control_ready_2379 old H2374 H2378) Step).
Qed.
Theorem reference_control_node_2379_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2374 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2378 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1992 left = VM.find 1992 right ->
 VM.find 2374 left = VM.find 2374 right ->
 VM.find 2378 left = VM.find 2378 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2379 next_left = VM.find 2379 next_right.
Proof.
 intros H2374 H2378 E1992 E2374 E2378 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2379 reference_control_expr_2379 reference_control_1_positions reference_control_1_safety reference_control_member_2379) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2379 reference_control_expr_2379 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2379 left H2374 H2378)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2379 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1992.
 rewrite E2374.
 rewrite E2378.
 reflexivity.
Qed.
Lemma reference_control_ready_2380 old :
 (exists value ground, VM.find 2373 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2379 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2380.
Proof.
 intros H2373 H2379.
 destruct H2373 as [v2373 [G2373 [V2373 T2373]]].
 destruct H2379 as [v2379 [G2379 [V2379 T2379]]].
 unfold reference_control_expr_2380.
apply rc_mux.
{ eapply rc_ref; [exact V2373|exists G2373; exact T2373].
}
{ eapply rc_ref; [exact V2379|exists G2379; exact T2379].
}
Qed.
Lemma reference_control_member_2380 : List.In (2380,reference_control_expr_2380) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 197%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2380_ground inputs path old current result :
 (exists value ground, VM.find 2373 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2379 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2380 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2373 H2379 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2380 reference_control_expr_2380 reference_control_1_positions reference_control_1_safety reference_control_member_2380) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2380 reference_control_expr_2380 inputs path old current result Position Safe Nonreg (reference_control_ready_2380 old H2373 H2379) Step).
Qed.
Theorem reference_control_node_2380_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2373 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2379 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1986 left = VM.find 1986 right ->
 VM.find 2373 left = VM.find 2373 right ->
 VM.find 2379 left = VM.find 2379 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2380 next_left = VM.find 2380 next_right.
Proof.
 intros H2373 H2379 E1986 E2373 E2379 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2380 reference_control_expr_2380 reference_control_1_positions reference_control_1_safety reference_control_member_2380) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2380 reference_control_expr_2380 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2380 left H2373 H2379)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2380 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1986.
 rewrite E2373.
 rewrite E2379.
 reflexivity.
Qed.
Lemma reference_control_ready_2381 old :
 (exists value ground, VM.find 2372 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2380 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2381.
Proof.
 intros H2372 H2380.
 destruct H2372 as [v2372 [G2372 [V2372 T2372]]].
 destruct H2380 as [v2380 [G2380 [V2380 T2380]]].
 unfold reference_control_expr_2381.
apply rc_mux.
{ eapply rc_ref; [exact V2372|exists G2372; exact T2372].
}
{ eapply rc_ref; [exact V2380|exists G2380; exact T2380].
}
Qed.
Lemma reference_control_member_2381 : List.In (2381,reference_control_expr_2381) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 198%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2381_ground inputs path old current result :
 (exists value ground, VM.find 2372 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2380 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2381 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2372 H2380 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2381 reference_control_expr_2381 reference_control_1_positions reference_control_1_safety reference_control_member_2381) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2381 reference_control_expr_2381 inputs path old current result Position Safe Nonreg (reference_control_ready_2381 old H2372 H2380) Step).
Qed.
Theorem reference_control_node_2381_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2372 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2380 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1980 left = VM.find 1980 right ->
 VM.find 2372 left = VM.find 2372 right ->
 VM.find 2380 left = VM.find 2380 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2381 next_left = VM.find 2381 next_right.
Proof.
 intros H2372 H2380 E1980 E2372 E2380 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2381 reference_control_expr_2381 reference_control_1_positions reference_control_1_safety reference_control_member_2381) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2381 reference_control_expr_2381 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2381 left H2372 H2380)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2381 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1980.
 rewrite E2372.
 rewrite E2380.
 reflexivity.
Qed.
Lemma reference_control_ready_2382 old :
 (exists value ground, VM.find 2371 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2381 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2382.
Proof.
 intros H2371 H2381.
 destruct H2371 as [v2371 [G2371 [V2371 T2371]]].
 destruct H2381 as [v2381 [G2381 [V2381 T2381]]].
 unfold reference_control_expr_2382.
apply rc_mux.
{ eapply rc_ref; [exact V2371|exists G2371; exact T2371].
}
{ eapply rc_ref; [exact V2381|exists G2381; exact T2381].
}
Qed.
Lemma reference_control_member_2382 : List.In (2382,reference_control_expr_2382) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 199%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2382_ground inputs path old current result :
 (exists value ground, VM.find 2371 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2381 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2382 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2371 H2381 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2382 reference_control_expr_2382 reference_control_1_positions reference_control_1_safety reference_control_member_2382) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2382 reference_control_expr_2382 inputs path old current result Position Safe Nonreg (reference_control_ready_2382 old H2371 H2381) Step).
Qed.
Theorem reference_control_node_2382_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2371 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2381 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1974 left = VM.find 1974 right ->
 VM.find 2371 left = VM.find 2371 right ->
 VM.find 2381 left = VM.find 2381 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2382 next_left = VM.find 2382 next_right.
Proof.
 intros H2371 H2381 E1974 E2371 E2381 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2382 reference_control_expr_2382 reference_control_1_positions reference_control_1_safety reference_control_member_2382) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2382 reference_control_expr_2382 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2382 left H2371 H2381)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2382 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1974.
 rewrite E2371.
 rewrite E2381.
 reflexivity.
Qed.
Lemma reference_control_ready_2383 old :
 (exists value ground, VM.find 2382 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2383.
Proof.
 intros H2382.
 destruct H2382 as [v2382 [G2382 [V2382 T2382]]].
 unfold reference_control_expr_2383.
apply rc_mux.
{ eapply rc_ref; [exact V2382|exists G2382; exact T2382].
}
{ apply rc_const.
}
Qed.
Lemma reference_control_member_2383 : List.In (2383,reference_control_expr_2383) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 200%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2383_ground inputs path old current result :
 (exists value ground, VM.find 2382 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2383 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2382 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2383 reference_control_expr_2383 reference_control_1_positions reference_control_1_safety reference_control_member_2383) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2383 reference_control_expr_2383 inputs path old current result Position Safe Nonreg (reference_control_ready_2383 old H2382) Step).
Qed.
Theorem reference_control_node_2383_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2382 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1707 left = VM.find 1707 right ->
 VM.find 2382 left = VM.find 2382 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2383 next_left = VM.find 2383 next_right.
Proof.
 intros H2382 E1707 E2382 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2383 reference_control_expr_2383 reference_control_1_positions reference_control_1_safety reference_control_member_2383) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2383 reference_control_expr_2383 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2383 left H2382)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2383 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1707.
 rewrite E2382.
 reflexivity.
Qed.
Lemma reference_control_ready_2384 old :
 (exists value ground, VM.find 2383 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2384.
Proof.
 intros H2383.
 destruct H2383 as [v2383 [G2383 [V2383 T2383]]].
 unfold reference_control_expr_2384.
eapply rc_ref; [exact V2383|exists G2383; exact T2383].
Qed.
Lemma reference_control_member_2384 : List.In (2384,reference_control_expr_2384) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 201%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2384_ground inputs path old current result :
 (exists value ground, VM.find 2383 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2384 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2383 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2384 reference_control_expr_2384 reference_control_1_positions reference_control_1_safety reference_control_member_2384) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2384 reference_control_expr_2384 inputs path old current result Position Safe Nonreg (reference_control_ready_2384 old H2383) Step).
Qed.
Theorem reference_control_node_2384_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2383 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2383 left = VM.find 2383 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2384 next_left = VM.find 2384 next_right.
Proof.
 intros H2383 E2383 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2384 reference_control_expr_2384 reference_control_1_positions reference_control_1_safety reference_control_member_2384) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2384 reference_control_expr_2384 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2384 left H2383)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2384 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2383.
 reflexivity.
Qed.
Lemma reference_control_ready_2385 old :
 reference_control_ready old reference_control_expr_2385.
Proof.
 unfold reference_control_expr_2385.
apply rc_binary.
Qed.
Lemma reference_control_member_2385 : List.In (2385,reference_control_expr_2385) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 202%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2385_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2385 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2385 reference_control_expr_2385 reference_control_1_positions reference_control_1_safety reference_control_member_2385) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2385 reference_control_expr_2385 inputs path old current result Position Safe Nonreg (reference_control_ready_2385 old ) Step).
Qed.
Theorem reference_control_node_2385_congruent inputs path left right next_left next_right :
 VM.find 2370 left = VM.find 2370 right ->
 VM.find 2384 left = VM.find 2384 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2385 next_left = VM.find 2385 next_right.
Proof.
 intros  E2370 E2384 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2385 reference_control_expr_2385 reference_control_1_positions reference_control_1_safety reference_control_member_2385) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2385 reference_control_expr_2385 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2385 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2385 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2370.
 rewrite E2384.
 reflexivity.
Qed.
Lemma reference_control_ready_2386 old :
 reference_control_ready old reference_control_expr_2386.
Proof.
 unfold reference_control_expr_2386.
apply rc_unary.
Qed.
Lemma reference_control_member_2386 : List.In (2386,reference_control_expr_2386) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 203%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2386_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2386 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2386 reference_control_expr_2386 reference_control_1_positions reference_control_1_safety reference_control_member_2386) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2386 reference_control_expr_2386 inputs path old current result Position Safe Nonreg (reference_control_ready_2386 old ) Step).
Qed.
Theorem reference_control_node_2386_congruent inputs path left right next_left next_right :
 VM.find 2333 left = VM.find 2333 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2386 next_left = VM.find 2386 next_right.
Proof.
 intros  E2333 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2386 reference_control_expr_2386 reference_control_1_positions reference_control_1_safety reference_control_member_2386) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2386 reference_control_expr_2386 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2386 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2386 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2333.
 reflexivity.
Qed.
Lemma reference_control_ready_2387 old :
 reference_control_ready old reference_control_expr_2387.
Proof.
 unfold reference_control_expr_2387.
apply rc_unary.
Qed.
Lemma reference_control_member_2387 : List.In (2387,reference_control_expr_2387) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 204%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2387_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2387 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2387 reference_control_expr_2387 reference_control_1_positions reference_control_1_safety reference_control_member_2387) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2387 reference_control_expr_2387 inputs path old current result Position Safe Nonreg (reference_control_ready_2387 old ) Step).
Qed.
Theorem reference_control_node_2387_congruent inputs path left right next_left next_right :
 VM.find 2337 left = VM.find 2337 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2387 next_left = VM.find 2387 next_right.
Proof.
 intros  E2337 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2387 reference_control_expr_2387 reference_control_1_positions reference_control_1_safety reference_control_member_2387) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2387 reference_control_expr_2387 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2387 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2387 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2337.
 reflexivity.
Qed.
Lemma reference_control_ready_2388 old :
 reference_control_ready old reference_control_expr_2388.
Proof.
 unfold reference_control_expr_2388.
apply rc_unary.
Qed.
Lemma reference_control_member_2388 : List.In (2388,reference_control_expr_2388) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 205%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2388_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2388 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2388 reference_control_expr_2388 reference_control_1_positions reference_control_1_safety reference_control_member_2388) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2388 reference_control_expr_2388 inputs path old current result Position Safe Nonreg (reference_control_ready_2388 old ) Step).
Qed.
Theorem reference_control_node_2388_congruent inputs path left right next_left next_right :
 VM.find 2341 left = VM.find 2341 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2388 next_left = VM.find 2388 next_right.
Proof.
 intros  E2341 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2388 reference_control_expr_2388 reference_control_1_positions reference_control_1_safety reference_control_member_2388) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2388 reference_control_expr_2388 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2388 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2388 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2341.
 reflexivity.
Qed.
Lemma reference_control_ready_2389 old :
 reference_control_ready old reference_control_expr_2389.
Proof.
 unfold reference_control_expr_2389.
apply rc_unary.
Qed.
Lemma reference_control_member_2389 : List.In (2389,reference_control_expr_2389) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 206%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2389_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2389 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2389 reference_control_expr_2389 reference_control_1_positions reference_control_1_safety reference_control_member_2389) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2389 reference_control_expr_2389 inputs path old current result Position Safe Nonreg (reference_control_ready_2389 old ) Step).
Qed.
Theorem reference_control_node_2389_congruent inputs path left right next_left next_right :
 VM.find 2345 left = VM.find 2345 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2389 next_left = VM.find 2389 next_right.
Proof.
 intros  E2345 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2389 reference_control_expr_2389 reference_control_1_positions reference_control_1_safety reference_control_member_2389) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2389 reference_control_expr_2389 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2389 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2389 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2345.
 reflexivity.
Qed.
Lemma reference_control_ready_2390 old :
 reference_control_ready old reference_control_expr_2390.
Proof.
 unfold reference_control_expr_2390.
apply rc_unary.
Qed.
Lemma reference_control_member_2390 : List.In (2390,reference_control_expr_2390) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 207%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2390_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2390 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2390 reference_control_expr_2390 reference_control_1_positions reference_control_1_safety reference_control_member_2390) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2390 reference_control_expr_2390 inputs path old current result Position Safe Nonreg (reference_control_ready_2390 old ) Step).
Qed.
Theorem reference_control_node_2390_congruent inputs path left right next_left next_right :
 VM.find 2349 left = VM.find 2349 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2390 next_left = VM.find 2390 next_right.
Proof.
 intros  E2349 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2390 reference_control_expr_2390 reference_control_1_positions reference_control_1_safety reference_control_member_2390) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2390 reference_control_expr_2390 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2390 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2390 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2349.
 reflexivity.
Qed.
Lemma reference_control_ready_2391 old :
 reference_control_ready old reference_control_expr_2391.
Proof.
 unfold reference_control_expr_2391.
apply rc_unary.
Qed.
Lemma reference_control_member_2391 : List.In (2391,reference_control_expr_2391) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 208%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2391_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2391 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2391 reference_control_expr_2391 reference_control_1_positions reference_control_1_safety reference_control_member_2391) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2391 reference_control_expr_2391 inputs path old current result Position Safe Nonreg (reference_control_ready_2391 old ) Step).
Qed.
Theorem reference_control_node_2391_congruent inputs path left right next_left next_right :
 VM.find 2353 left = VM.find 2353 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2391 next_left = VM.find 2391 next_right.
Proof.
 intros  E2353 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2391 reference_control_expr_2391 reference_control_1_positions reference_control_1_safety reference_control_member_2391) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2391 reference_control_expr_2391 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2391 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2391 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2353.
 reflexivity.
Qed.
Lemma reference_control_ready_2392 old :
 (exists value ground, VM.find 2391 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2392.
Proof.
 intros H2391.
 destruct H2391 as [v2391 [G2391 [V2391 T2391]]].
 unfold reference_control_expr_2392.
apply rc_mux.
{ eapply rc_ref; [exact V2391|exists G2391; exact T2391].
}
{ apply rc_const.
}
Qed.
Lemma reference_control_member_2392 : List.In (2392,reference_control_expr_2392) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 209%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2392_ground inputs path old current result :
 (exists value ground, VM.find 2391 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2392 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2391 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2392 reference_control_expr_2392 reference_control_1_positions reference_control_1_safety reference_control_member_2392) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2392 reference_control_expr_2392 inputs path old current result Position Safe Nonreg (reference_control_ready_2392 old H2391) Step).
Qed.
Theorem reference_control_node_2392_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2391 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2004 left = VM.find 2004 right ->
 VM.find 2391 left = VM.find 2391 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2392 next_left = VM.find 2392 next_right.
Proof.
 intros H2391 E2004 E2391 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2392 reference_control_expr_2392 reference_control_1_positions reference_control_1_safety reference_control_member_2392) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2392 reference_control_expr_2392 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2392 left H2391)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2392 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2004.
 rewrite E2391.
 reflexivity.
Qed.
Lemma reference_control_ready_2393 old :
 (exists value ground, VM.find 2390 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2392 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2393.
Proof.
 intros H2390 H2392.
 destruct H2390 as [v2390 [G2390 [V2390 T2390]]].
 destruct H2392 as [v2392 [G2392 [V2392 T2392]]].
 unfold reference_control_expr_2393.
apply rc_mux.
{ eapply rc_ref; [exact V2390|exists G2390; exact T2390].
}
{ eapply rc_ref; [exact V2392|exists G2392; exact T2392].
}
Qed.
Lemma reference_control_member_2393 : List.In (2393,reference_control_expr_2393) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 210%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2393_ground inputs path old current result :
 (exists value ground, VM.find 2390 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2392 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2393 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2390 H2392 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2393 reference_control_expr_2393 reference_control_1_positions reference_control_1_safety reference_control_member_2393) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2393 reference_control_expr_2393 inputs path old current result Position Safe Nonreg (reference_control_ready_2393 old H2390 H2392) Step).
Qed.
Theorem reference_control_node_2393_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2390 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2392 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1998 left = VM.find 1998 right ->
 VM.find 2390 left = VM.find 2390 right ->
 VM.find 2392 left = VM.find 2392 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2393 next_left = VM.find 2393 next_right.
Proof.
 intros H2390 H2392 E1998 E2390 E2392 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2393 reference_control_expr_2393 reference_control_1_positions reference_control_1_safety reference_control_member_2393) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2393 reference_control_expr_2393 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2393 left H2390 H2392)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2393 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1998.
 rewrite E2390.
 rewrite E2392.
 reflexivity.
Qed.
Lemma reference_control_ready_2394 old :
 (exists value ground, VM.find 2389 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2393 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2394.
Proof.
 intros H2389 H2393.
 destruct H2389 as [v2389 [G2389 [V2389 T2389]]].
 destruct H2393 as [v2393 [G2393 [V2393 T2393]]].
 unfold reference_control_expr_2394.
apply rc_mux.
{ eapply rc_ref; [exact V2389|exists G2389; exact T2389].
}
{ eapply rc_ref; [exact V2393|exists G2393; exact T2393].
}
Qed.
Lemma reference_control_member_2394 : List.In (2394,reference_control_expr_2394) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 211%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2394_ground inputs path old current result :
 (exists value ground, VM.find 2389 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2393 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2394 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2389 H2393 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2394 reference_control_expr_2394 reference_control_1_positions reference_control_1_safety reference_control_member_2394) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2394 reference_control_expr_2394 inputs path old current result Position Safe Nonreg (reference_control_ready_2394 old H2389 H2393) Step).
Qed.
Theorem reference_control_node_2394_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2389 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2393 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1992 left = VM.find 1992 right ->
 VM.find 2389 left = VM.find 2389 right ->
 VM.find 2393 left = VM.find 2393 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2394 next_left = VM.find 2394 next_right.
Proof.
 intros H2389 H2393 E1992 E2389 E2393 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2394 reference_control_expr_2394 reference_control_1_positions reference_control_1_safety reference_control_member_2394) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2394 reference_control_expr_2394 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2394 left H2389 H2393)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2394 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1992.
 rewrite E2389.
 rewrite E2393.
 reflexivity.
Qed.
Lemma reference_control_ready_2395 old :
 (exists value ground, VM.find 2388 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2394 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2395.
Proof.
 intros H2388 H2394.
 destruct H2388 as [v2388 [G2388 [V2388 T2388]]].
 destruct H2394 as [v2394 [G2394 [V2394 T2394]]].
 unfold reference_control_expr_2395.
apply rc_mux.
{ eapply rc_ref; [exact V2388|exists G2388; exact T2388].
}
{ eapply rc_ref; [exact V2394|exists G2394; exact T2394].
}
Qed.
Lemma reference_control_member_2395 : List.In (2395,reference_control_expr_2395) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 212%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2395_ground inputs path old current result :
 (exists value ground, VM.find 2388 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2394 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2395 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2388 H2394 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2395 reference_control_expr_2395 reference_control_1_positions reference_control_1_safety reference_control_member_2395) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2395 reference_control_expr_2395 inputs path old current result Position Safe Nonreg (reference_control_ready_2395 old H2388 H2394) Step).
Qed.
Theorem reference_control_node_2395_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2388 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2394 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1986 left = VM.find 1986 right ->
 VM.find 2388 left = VM.find 2388 right ->
 VM.find 2394 left = VM.find 2394 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2395 next_left = VM.find 2395 next_right.
Proof.
 intros H2388 H2394 E1986 E2388 E2394 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2395 reference_control_expr_2395 reference_control_1_positions reference_control_1_safety reference_control_member_2395) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2395 reference_control_expr_2395 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2395 left H2388 H2394)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2395 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1986.
 rewrite E2388.
 rewrite E2394.
 reflexivity.
Qed.
Lemma reference_control_ready_2396 old :
 (exists value ground, VM.find 2387 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2395 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2396.
Proof.
 intros H2387 H2395.
 destruct H2387 as [v2387 [G2387 [V2387 T2387]]].
 destruct H2395 as [v2395 [G2395 [V2395 T2395]]].
 unfold reference_control_expr_2396.
apply rc_mux.
{ eapply rc_ref; [exact V2387|exists G2387; exact T2387].
}
{ eapply rc_ref; [exact V2395|exists G2395; exact T2395].
}
Qed.
Lemma reference_control_member_2396 : List.In (2396,reference_control_expr_2396) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 213%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2396_ground inputs path old current result :
 (exists value ground, VM.find 2387 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2395 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2396 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2387 H2395 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2396 reference_control_expr_2396 reference_control_1_positions reference_control_1_safety reference_control_member_2396) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2396 reference_control_expr_2396 inputs path old current result Position Safe Nonreg (reference_control_ready_2396 old H2387 H2395) Step).
Qed.
Theorem reference_control_node_2396_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2387 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2395 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1980 left = VM.find 1980 right ->
 VM.find 2387 left = VM.find 2387 right ->
 VM.find 2395 left = VM.find 2395 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2396 next_left = VM.find 2396 next_right.
Proof.
 intros H2387 H2395 E1980 E2387 E2395 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2396 reference_control_expr_2396 reference_control_1_positions reference_control_1_safety reference_control_member_2396) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2396 reference_control_expr_2396 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2396 left H2387 H2395)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2396 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1980.
 rewrite E2387.
 rewrite E2395.
 reflexivity.
Qed.
Lemma reference_control_ready_2397 old :
 (exists value ground, VM.find 2386 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2396 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2397.
Proof.
 intros H2386 H2396.
 destruct H2386 as [v2386 [G2386 [V2386 T2386]]].
 destruct H2396 as [v2396 [G2396 [V2396 T2396]]].
 unfold reference_control_expr_2397.
apply rc_mux.
{ eapply rc_ref; [exact V2386|exists G2386; exact T2386].
}
{ eapply rc_ref; [exact V2396|exists G2396; exact T2396].
}
Qed.
Lemma reference_control_member_2397 : List.In (2397,reference_control_expr_2397) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 214%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2397_ground inputs path old current result :
 (exists value ground, VM.find 2386 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2396 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2397 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2386 H2396 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2397 reference_control_expr_2397 reference_control_1_positions reference_control_1_safety reference_control_member_2397) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2397 reference_control_expr_2397 inputs path old current result Position Safe Nonreg (reference_control_ready_2397 old H2386 H2396) Step).
Qed.
Theorem reference_control_node_2397_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2386 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2396 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1974 left = VM.find 1974 right ->
 VM.find 2386 left = VM.find 2386 right ->
 VM.find 2396 left = VM.find 2396 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2397 next_left = VM.find 2397 next_right.
Proof.
 intros H2386 H2396 E1974 E2386 E2396 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2397 reference_control_expr_2397 reference_control_1_positions reference_control_1_safety reference_control_member_2397) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2397 reference_control_expr_2397 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2397 left H2386 H2396)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2397 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1974.
 rewrite E2386.
 rewrite E2396.
 reflexivity.
Qed.
Lemma reference_control_ready_2398 old :
 (exists value ground, VM.find 2397 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2398.
Proof.
 intros H2397.
 destruct H2397 as [v2397 [G2397 [V2397 T2397]]].
 unfold reference_control_expr_2398.
apply rc_mux.
{ eapply rc_ref; [exact V2397|exists G2397; exact T2397].
}
{ apply rc_const.
}
Qed.
Lemma reference_control_member_2398 : List.In (2398,reference_control_expr_2398) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 215%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2398_ground inputs path old current result :
 (exists value ground, VM.find 2397 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2398 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2397 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2398 reference_control_expr_2398 reference_control_1_positions reference_control_1_safety reference_control_member_2398) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2398 reference_control_expr_2398 inputs path old current result Position Safe Nonreg (reference_control_ready_2398 old H2397) Step).
Qed.
Theorem reference_control_node_2398_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2397 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1707 left = VM.find 1707 right ->
 VM.find 2397 left = VM.find 2397 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2398 next_left = VM.find 2398 next_right.
Proof.
 intros H2397 E1707 E2397 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2398 reference_control_expr_2398 reference_control_1_positions reference_control_1_safety reference_control_member_2398) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2398 reference_control_expr_2398 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2398 left H2397)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2398 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1707.
 rewrite E2397.
 reflexivity.
Qed.
Lemma reference_control_ready_2399 old :
 (exists value ground, VM.find 2398 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2399.
Proof.
 intros H2398.
 destruct H2398 as [v2398 [G2398 [V2398 T2398]]].
 unfold reference_control_expr_2399.
eapply rc_ref; [exact V2398|exists G2398; exact T2398].
Qed.
Lemma reference_control_member_2399 : List.In (2399,reference_control_expr_2399) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 216%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2399_ground inputs path old current result :
 (exists value ground, VM.find 2398 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2399 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2398 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2399 reference_control_expr_2399 reference_control_1_positions reference_control_1_safety reference_control_member_2399) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2399 reference_control_expr_2399 inputs path old current result Position Safe Nonreg (reference_control_ready_2399 old H2398) Step).
Qed.
Theorem reference_control_node_2399_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2398 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2398 left = VM.find 2398 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2399 next_left = VM.find 2399 next_right.
Proof.
 intros H2398 E2398 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2399 reference_control_expr_2399 reference_control_1_positions reference_control_1_safety reference_control_member_2399) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2399 reference_control_expr_2399 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2399 left H2398)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2399 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2398.
 reflexivity.
Qed.
Lemma reference_control_ready_2400 old :
 reference_control_ready old reference_control_expr_2400.
Proof.
 unfold reference_control_expr_2400.
apply rc_binary.
Qed.
Lemma reference_control_member_2400 : List.In (2400,reference_control_expr_2400) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 217%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2400_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2400 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2400 reference_control_expr_2400 reference_control_1_positions reference_control_1_safety reference_control_member_2400) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2400 reference_control_expr_2400 inputs path old current result Position Safe Nonreg (reference_control_ready_2400 old ) Step).
Qed.
Theorem reference_control_node_2400_congruent inputs path left right next_left next_right :
 VM.find 2399 left = VM.find 2399 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2400 next_left = VM.find 2400 next_right.
Proof.
 intros  E2399 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2400 reference_control_expr_2400 reference_control_1_positions reference_control_1_safety reference_control_member_2400) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2400 reference_control_expr_2400 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2400 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2400 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2399.
 reflexivity.
Qed.
Lemma reference_control_ready_2401 old :
 reference_control_ready old reference_control_expr_2401.
Proof.
 unfold reference_control_expr_2401.
apply rc_binary.
Qed.
Lemma reference_control_member_2401 : List.In (2401,reference_control_expr_2401) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 218%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2401_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2401 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2401 reference_control_expr_2401 reference_control_1_positions reference_control_1_safety reference_control_member_2401) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2401 reference_control_expr_2401 inputs path old current result Position Safe Nonreg (reference_control_ready_2401 old ) Step).
Qed.
Theorem reference_control_node_2401_congruent inputs path left right next_left next_right :
 VM.find 2385 left = VM.find 2385 right ->
 VM.find 2400 left = VM.find 2400 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2401 next_left = VM.find 2401 next_right.
Proof.
 intros  E2385 E2400 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2401 reference_control_expr_2401 reference_control_1_positions reference_control_1_safety reference_control_member_2401) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2401 reference_control_expr_2401 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2401 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2401 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2385.
 rewrite E2400.
 reflexivity.
Qed.
Lemma reference_control_ready_2402 old :
 reference_control_ready old reference_control_expr_2402.
Proof.
 unfold reference_control_expr_2402.
apply rc_unary.
Qed.
Lemma reference_control_member_2402 : List.In (2402,reference_control_expr_2402) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 219%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2402_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2402 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2402 reference_control_expr_2402 reference_control_1_positions reference_control_1_safety reference_control_member_2402) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2402 reference_control_expr_2402 inputs path old current result Position Safe Nonreg (reference_control_ready_2402 old ) Step).
Qed.
Theorem reference_control_node_2402_congruent inputs path left right next_left next_right :
 VM.find 2401 left = VM.find 2401 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2402 next_left = VM.find 2402 next_right.
Proof.
 intros  E2401 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2402 reference_control_expr_2402 reference_control_1_positions reference_control_1_safety reference_control_member_2402) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2402 reference_control_expr_2402 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2402 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2402 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2401.
 reflexivity.
Qed.
Lemma reference_control_ready_2403 old :
 reference_control_ready old reference_control_expr_2403.
Proof.
 unfold reference_control_expr_2403.
apply rc_unary.
Qed.
Lemma reference_control_member_2403 : List.In (2403,reference_control_expr_2403) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 220%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2403_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2403 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2403 reference_control_expr_2403 reference_control_1_positions reference_control_1_safety reference_control_member_2403) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2403 reference_control_expr_2403 inputs path old current result Position Safe Nonreg (reference_control_ready_2403 old ) Step).
Qed.
Theorem reference_control_node_2403_congruent inputs path left right next_left next_right :
 VM.find 2402 left = VM.find 2402 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2403 next_left = VM.find 2403 next_right.
Proof.
 intros  E2402 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2403 reference_control_expr_2403 reference_control_1_positions reference_control_1_safety reference_control_member_2403) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2403 reference_control_expr_2403 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2403 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2403 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2402.
 reflexivity.
Qed.
Lemma reference_control_ready_2404 old :
 reference_control_ready old reference_control_expr_2404.
Proof.
 unfold reference_control_expr_2404.
apply rc_mux.
{ apply rc_const.
}
{ apply rc_const.
}
Qed.
Lemma reference_control_member_2404 : List.In (2404,reference_control_expr_2404) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 221%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2404_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2404 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2404 reference_control_expr_2404 reference_control_1_positions reference_control_1_safety reference_control_member_2404) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2404 reference_control_expr_2404 inputs path old current result Position Safe Nonreg (reference_control_ready_2404 old ) Step).
Qed.
Theorem reference_control_node_2404_congruent inputs path left right next_left next_right :
 VM.find 2403 left = VM.find 2403 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2404 next_left = VM.find 2404 next_right.
Proof.
 intros  E2403 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2404 reference_control_expr_2404 reference_control_1_positions reference_control_1_safety reference_control_member_2404) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2404 reference_control_expr_2404 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2404 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2404 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2403.
 reflexivity.
Qed.
Lemma reference_control_ready_2405 old :
 reference_control_ready old reference_control_expr_2405.
Proof.
 unfold reference_control_expr_2405.
apply rc_binary.
Qed.
Lemma reference_control_member_2405 : List.In (2405,reference_control_expr_2405) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 222%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2405_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2405 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2405 reference_control_expr_2405 reference_control_1_positions reference_control_1_safety reference_control_member_2405) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2405 reference_control_expr_2405 inputs path old current result Position Safe Nonreg (reference_control_ready_2405 old ) Step).
Qed.
Theorem reference_control_node_2405_congruent inputs path left right next_left next_right :
 VM.find 2401 left = VM.find 2401 right ->
 VM.find 2404 left = VM.find 2404 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2405 next_left = VM.find 2405 next_right.
Proof.
 intros  E2401 E2404 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2405 reference_control_expr_2405 reference_control_1_positions reference_control_1_safety reference_control_member_2405) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2405 reference_control_expr_2405 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2405 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2405 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2401.
 rewrite E2404.
 reflexivity.
Qed.
Lemma reference_control_ready_2406 old :
 reference_control_ready old reference_control_expr_2406.
Proof.
 unfold reference_control_expr_2406.
apply rc_binary.
Qed.
Lemma reference_control_member_2406 : List.In (2406,reference_control_expr_2406) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 223%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2406_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2406 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2406 reference_control_expr_2406 reference_control_1_positions reference_control_1_safety reference_control_member_2406) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2406 reference_control_expr_2406 inputs path old current result Position Safe Nonreg (reference_control_ready_2406 old ) Step).
Qed.
Theorem reference_control_node_2406_congruent inputs path left right next_left next_right :
 VM.find 2331 left = VM.find 2331 right ->
 VM.find 2369 left = VM.find 2369 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2406 next_left = VM.find 2406 next_right.
Proof.
 intros  E2331 E2369 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2406 reference_control_expr_2406 reference_control_1_positions reference_control_1_safety reference_control_member_2406) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2406 reference_control_expr_2406 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2406 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2406 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2331.
 rewrite E2369.
 reflexivity.
Qed.
Lemma reference_control_ready_2407 old :
 reference_control_ready old reference_control_expr_2407.
Proof.
 unfold reference_control_expr_2407.
apply rc_binary.
Qed.
Lemma reference_control_member_2407 : List.In (2407,reference_control_expr_2407) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 224%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2407_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2407 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2407 reference_control_expr_2407 reference_control_1_positions reference_control_1_safety reference_control_member_2407) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2407 reference_control_expr_2407 inputs path old current result Position Safe Nonreg (reference_control_ready_2407 old ) Step).
Qed.
Theorem reference_control_node_2407_congruent inputs path left right next_left next_right :
 VM.find 2384 left = VM.find 2384 right ->
 VM.find 2406 left = VM.find 2406 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2407 next_left = VM.find 2407 next_right.
Proof.
 intros  E2384 E2406 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2407 reference_control_expr_2407 reference_control_1_positions reference_control_1_safety reference_control_member_2407) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2407 reference_control_expr_2407 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2407 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2407 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2384.
 rewrite E2406.
 reflexivity.
Qed.
Lemma reference_control_ready_2408 old :
 reference_control_ready old reference_control_expr_2408.
Proof.
 unfold reference_control_expr_2408.
apply rc_binary.
Qed.
Lemma reference_control_member_2408 : List.In (2408,reference_control_expr_2408) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 225%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2408_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2408 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2408 reference_control_expr_2408 reference_control_1_positions reference_control_1_safety reference_control_member_2408) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2408 reference_control_expr_2408 inputs path old current result Position Safe Nonreg (reference_control_ready_2408 old ) Step).
Qed.
Theorem reference_control_node_2408_congruent inputs path left right next_left next_right :
 VM.find 2399 left = VM.find 2399 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2408 next_left = VM.find 2408 next_right.
Proof.
 intros  E2399 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2408 reference_control_expr_2408 reference_control_1_positions reference_control_1_safety reference_control_member_2408) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2408 reference_control_expr_2408 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2408 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2408 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2399.
 reflexivity.
Qed.
Lemma reference_control_ready_2409 old :
 reference_control_ready old reference_control_expr_2409.
Proof.
 unfold reference_control_expr_2409.
apply rc_binary.
Qed.
Lemma reference_control_member_2409 : List.In (2409,reference_control_expr_2409) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 226%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2409_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2409 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2409 reference_control_expr_2409 reference_control_1_positions reference_control_1_safety reference_control_member_2409) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2409 reference_control_expr_2409 inputs path old current result Position Safe Nonreg (reference_control_ready_2409 old ) Step).
Qed.
Theorem reference_control_node_2409_congruent inputs path left right next_left next_right :
 VM.find 2407 left = VM.find 2407 right ->
 VM.find 2408 left = VM.find 2408 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2409 next_left = VM.find 2409 next_right.
Proof.
 intros  E2407 E2408 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2409 reference_control_expr_2409 reference_control_1_positions reference_control_1_safety reference_control_member_2409) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2409 reference_control_expr_2409 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2409 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2409 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2407.
 rewrite E2408.
 reflexivity.
Qed.
Lemma reference_control_ready_2410 old :
 reference_control_ready old reference_control_expr_2410.
Proof.
 unfold reference_control_expr_2410.
apply rc_unary.
Qed.
Lemma reference_control_member_2410 : List.In (2410,reference_control_expr_2410) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 227%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2410_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2410 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2410 reference_control_expr_2410 reference_control_1_positions reference_control_1_safety reference_control_member_2410) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2410 reference_control_expr_2410 inputs path old current result Position Safe Nonreg (reference_control_ready_2410 old ) Step).
Qed.
Theorem reference_control_node_2410_congruent inputs path left right next_left next_right :
 VM.find 2409 left = VM.find 2409 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2410 next_left = VM.find 2410 next_right.
Proof.
 intros  E2409 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2410 reference_control_expr_2410 reference_control_1_positions reference_control_1_safety reference_control_member_2410) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2410 reference_control_expr_2410 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2410 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2410 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2409.
 reflexivity.
Qed.
Lemma reference_control_ready_2411 old :
 reference_control_ready old reference_control_expr_2411.
Proof.
 unfold reference_control_expr_2411.
apply rc_unary.
Qed.
Lemma reference_control_member_2411 : List.In (2411,reference_control_expr_2411) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 228%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2411_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2411 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2411 reference_control_expr_2411 reference_control_1_positions reference_control_1_safety reference_control_member_2411) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2411 reference_control_expr_2411 inputs path old current result Position Safe Nonreg (reference_control_ready_2411 old ) Step).
Qed.
Theorem reference_control_node_2411_congruent inputs path left right next_left next_right :
 VM.find 2410 left = VM.find 2410 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2411 next_left = VM.find 2411 next_right.
Proof.
 intros  E2410 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2411 reference_control_expr_2411 reference_control_1_positions reference_control_1_safety reference_control_member_2411) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2411 reference_control_expr_2411 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2411 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2411 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2410.
 reflexivity.
Qed.
Lemma reference_control_ready_2412 old :
 reference_control_ready old reference_control_expr_2412.
Proof.
 unfold reference_control_expr_2412.
apply rc_mux.
{ apply rc_const.
}
{ apply rc_const.
}
Qed.
Lemma reference_control_member_2412 : List.In (2412,reference_control_expr_2412) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 229%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2412_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2412 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2412 reference_control_expr_2412 reference_control_1_positions reference_control_1_safety reference_control_member_2412) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2412 reference_control_expr_2412 inputs path old current result Position Safe Nonreg (reference_control_ready_2412 old ) Step).
Qed.
Theorem reference_control_node_2412_congruent inputs path left right next_left next_right :
 VM.find 2411 left = VM.find 2411 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2412 next_left = VM.find 2412 next_right.
Proof.
 intros  E2411 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2412 reference_control_expr_2412 reference_control_1_positions reference_control_1_safety reference_control_member_2412) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2412 reference_control_expr_2412 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2412 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2412 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2411.
 reflexivity.
Qed.
Lemma reference_control_ready_2413 old :
 reference_control_ready old reference_control_expr_2413.
Proof.
 unfold reference_control_expr_2413.
apply rc_binary.
Qed.
Lemma reference_control_member_2413 : List.In (2413,reference_control_expr_2413) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 230%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2413_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2413 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2413 reference_control_expr_2413 reference_control_1_positions reference_control_1_safety reference_control_member_2413) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2413 reference_control_expr_2413 inputs path old current result Position Safe Nonreg (reference_control_ready_2413 old ) Step).
Qed.
Theorem reference_control_node_2413_congruent inputs path left right next_left next_right :
 VM.find 2409 left = VM.find 2409 right ->
 VM.find 2412 left = VM.find 2412 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2413 next_left = VM.find 2413 next_right.
Proof.
 intros  E2409 E2412 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2413 reference_control_expr_2413 reference_control_1_positions reference_control_1_safety reference_control_member_2413) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2413 reference_control_expr_2413 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2413 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2413 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2409.
 rewrite E2412.
 reflexivity.
Qed.
Lemma reference_control_ready_2414 old :
 reference_control_ready old reference_control_expr_2414.
Proof.
 unfold reference_control_expr_2414.
apply rc_binary.
Qed.
Lemma reference_control_member_2414 : List.In (2414,reference_control_expr_2414) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 231%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2414_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2414 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2414 reference_control_expr_2414 reference_control_1_positions reference_control_1_safety reference_control_member_2414) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2414 reference_control_expr_2414 inputs path old current result Position Safe Nonreg (reference_control_ready_2414 old ) Step).
Qed.
Theorem reference_control_node_2414_congruent inputs path left right next_left next_right :
 VM.find 2331 left = VM.find 2331 right ->
 VM.find 2369 left = VM.find 2369 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2414 next_left = VM.find 2414 next_right.
Proof.
 intros  E2331 E2369 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2414 reference_control_expr_2414 reference_control_1_positions reference_control_1_safety reference_control_member_2414) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2414 reference_control_expr_2414 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2414 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2414 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2331.
 rewrite E2369.
 reflexivity.
Qed.
Lemma reference_control_ready_2415 old :
 reference_control_ready old reference_control_expr_2415.
Proof.
 unfold reference_control_expr_2415.
apply rc_binary.
Qed.
Lemma reference_control_member_2415 : List.In (2415,reference_control_expr_2415) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 232%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2415_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2415 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2415 reference_control_expr_2415 reference_control_1_positions reference_control_1_safety reference_control_member_2415) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2415 reference_control_expr_2415 inputs path old current result Position Safe Nonreg (reference_control_ready_2415 old ) Step).
Qed.
Theorem reference_control_node_2415_congruent inputs path left right next_left next_right :
 VM.find 2384 left = VM.find 2384 right ->
 VM.find 2414 left = VM.find 2414 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2415 next_left = VM.find 2415 next_right.
Proof.
 intros  E2384 E2414 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2415 reference_control_expr_2415 reference_control_1_positions reference_control_1_safety reference_control_member_2415) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2415 reference_control_expr_2415 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2415 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2415 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2384.
 rewrite E2414.
 reflexivity.
Qed.
Lemma reference_control_ready_2416 old :
 reference_control_ready old reference_control_expr_2416.
Proof.
 unfold reference_control_expr_2416.
apply rc_binary.
Qed.
Lemma reference_control_member_2416 : List.In (2416,reference_control_expr_2416) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 233%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2416_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2416 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2416 reference_control_expr_2416 reference_control_1_positions reference_control_1_safety reference_control_member_2416) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2416 reference_control_expr_2416 inputs path old current result Position Safe Nonreg (reference_control_ready_2416 old ) Step).
Qed.
Theorem reference_control_node_2416_congruent inputs path left right next_left next_right :
 VM.find 2399 left = VM.find 2399 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2416 next_left = VM.find 2416 next_right.
Proof.
 intros  E2399 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2416 reference_control_expr_2416 reference_control_1_positions reference_control_1_safety reference_control_member_2416) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2416 reference_control_expr_2416 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2416 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2416 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2399.
 reflexivity.
Qed.
Lemma reference_control_ready_2417 old :
 reference_control_ready old reference_control_expr_2417.
Proof.
 unfold reference_control_expr_2417.
apply rc_binary.
Qed.
Lemma reference_control_member_2417 : List.In (2417,reference_control_expr_2417) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 234%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2417_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2417 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2417 reference_control_expr_2417 reference_control_1_positions reference_control_1_safety reference_control_member_2417) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2417 reference_control_expr_2417 inputs path old current result Position Safe Nonreg (reference_control_ready_2417 old ) Step).
Qed.
Theorem reference_control_node_2417_congruent inputs path left right next_left next_right :
 VM.find 2415 left = VM.find 2415 right ->
 VM.find 2416 left = VM.find 2416 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2417 next_left = VM.find 2417 next_right.
Proof.
 intros  E2415 E2416 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2417 reference_control_expr_2417 reference_control_1_positions reference_control_1_safety reference_control_member_2417) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2417 reference_control_expr_2417 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2417 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2417 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2415.
 rewrite E2416.
 reflexivity.
Qed.
Lemma reference_control_ready_2418 old :
 reference_control_ready old reference_control_expr_2418.
Proof.
 unfold reference_control_expr_2418.
apply rc_unary.
Qed.
Lemma reference_control_member_2418 : List.In (2418,reference_control_expr_2418) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 235%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2418_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2418 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2418 reference_control_expr_2418 reference_control_1_positions reference_control_1_safety reference_control_member_2418) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2418 reference_control_expr_2418 inputs path old current result Position Safe Nonreg (reference_control_ready_2418 old ) Step).
Qed.
Theorem reference_control_node_2418_congruent inputs path left right next_left next_right :
 VM.find 2417 left = VM.find 2417 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2418 next_left = VM.find 2418 next_right.
Proof.
 intros  E2417 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2418 reference_control_expr_2418 reference_control_1_positions reference_control_1_safety reference_control_member_2418) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2418 reference_control_expr_2418 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2418 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2418 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2417.
 reflexivity.
Qed.
Lemma reference_control_ready_2419 old :
 reference_control_ready old reference_control_expr_2419.
Proof.
 unfold reference_control_expr_2419.
apply rc_unary.
Qed.
Lemma reference_control_member_2419 : List.In (2419,reference_control_expr_2419) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 236%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2419_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2419 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2419 reference_control_expr_2419 reference_control_1_positions reference_control_1_safety reference_control_member_2419) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2419 reference_control_expr_2419 inputs path old current result Position Safe Nonreg (reference_control_ready_2419 old ) Step).
Qed.
Theorem reference_control_node_2419_congruent inputs path left right next_left next_right :
 VM.find 2418 left = VM.find 2418 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2419 next_left = VM.find 2419 next_right.
Proof.
 intros  E2418 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2419 reference_control_expr_2419 reference_control_1_positions reference_control_1_safety reference_control_member_2419) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2419 reference_control_expr_2419 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2419 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2419 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2418.
 reflexivity.
Qed.
Lemma reference_control_ready_2420 old :
 reference_control_ready old reference_control_expr_2420.
Proof.
 unfold reference_control_expr_2420.
apply rc_mux.
{ apply rc_const.
}
{ apply rc_const.
}
Qed.
Lemma reference_control_member_2420 : List.In (2420,reference_control_expr_2420) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 237%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2420_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2420 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2420 reference_control_expr_2420 reference_control_1_positions reference_control_1_safety reference_control_member_2420) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2420 reference_control_expr_2420 inputs path old current result Position Safe Nonreg (reference_control_ready_2420 old ) Step).
Qed.
Theorem reference_control_node_2420_congruent inputs path left right next_left next_right :
 VM.find 2419 left = VM.find 2419 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2420 next_left = VM.find 2420 next_right.
Proof.
 intros  E2419 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2420 reference_control_expr_2420 reference_control_1_positions reference_control_1_safety reference_control_member_2420) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2420 reference_control_expr_2420 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2420 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2420 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2419.
 reflexivity.
Qed.
Lemma reference_control_ready_2421 old :
 reference_control_ready old reference_control_expr_2421.
Proof.
 unfold reference_control_expr_2421.
apply rc_binary.
Qed.
Lemma reference_control_member_2421 : List.In (2421,reference_control_expr_2421) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 238%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2421_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2421 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2421 reference_control_expr_2421 reference_control_1_positions reference_control_1_safety reference_control_member_2421) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2421 reference_control_expr_2421 inputs path old current result Position Safe Nonreg (reference_control_ready_2421 old ) Step).
Qed.
Theorem reference_control_node_2421_congruent inputs path left right next_left next_right :
 VM.find 2417 left = VM.find 2417 right ->
 VM.find 2420 left = VM.find 2420 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2421 next_left = VM.find 2421 next_right.
Proof.
 intros  E2417 E2420 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2421 reference_control_expr_2421 reference_control_1_positions reference_control_1_safety reference_control_member_2421) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2421 reference_control_expr_2421 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2421 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2421 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2417.
 rewrite E2420.
 reflexivity.
Qed.
Lemma reference_control_ready_2422 old :
 reference_control_ready old reference_control_expr_2422.
Proof.
 unfold reference_control_expr_2422.
apply rc_binary.
Qed.
Lemma reference_control_member_2422 : List.In (2422,reference_control_expr_2422) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 239%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2422_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2422 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2422 reference_control_expr_2422 reference_control_1_positions reference_control_1_safety reference_control_member_2422) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2422 reference_control_expr_2422 inputs path old current result Position Safe Nonreg (reference_control_ready_2422 old ) Step).
Qed.
Theorem reference_control_node_2422_congruent inputs path left right next_left next_right :
 VM.find 2331 left = VM.find 2331 right ->
 VM.find 2369 left = VM.find 2369 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2422 next_left = VM.find 2422 next_right.
Proof.
 intros  E2331 E2369 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2422 reference_control_expr_2422 reference_control_1_positions reference_control_1_safety reference_control_member_2422) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2422 reference_control_expr_2422 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2422 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2422 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2331.
 rewrite E2369.
 reflexivity.
Qed.
Lemma reference_control_ready_2423 old :
 reference_control_ready old reference_control_expr_2423.
Proof.
 unfold reference_control_expr_2423.
apply rc_binary.
Qed.
Lemma reference_control_member_2423 : List.In (2423,reference_control_expr_2423) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 240%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2423_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2423 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2423 reference_control_expr_2423 reference_control_1_positions reference_control_1_safety reference_control_member_2423) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2423 reference_control_expr_2423 inputs path old current result Position Safe Nonreg (reference_control_ready_2423 old ) Step).
Qed.
Theorem reference_control_node_2423_congruent inputs path left right next_left next_right :
 VM.find 2384 left = VM.find 2384 right ->
 VM.find 2422 left = VM.find 2422 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2423 next_left = VM.find 2423 next_right.
Proof.
 intros  E2384 E2422 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2423 reference_control_expr_2423 reference_control_1_positions reference_control_1_safety reference_control_member_2423) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2423 reference_control_expr_2423 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2423 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2423 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2384.
 rewrite E2422.
 reflexivity.
Qed.
Lemma reference_control_ready_2424 old :
 reference_control_ready old reference_control_expr_2424.
Proof.
 unfold reference_control_expr_2424.
apply rc_binary.
Qed.
Lemma reference_control_member_2424 : List.In (2424,reference_control_expr_2424) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 241%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2424_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2424 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2424 reference_control_expr_2424 reference_control_1_positions reference_control_1_safety reference_control_member_2424) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2424 reference_control_expr_2424 inputs path old current result Position Safe Nonreg (reference_control_ready_2424 old ) Step).
Qed.
Theorem reference_control_node_2424_congruent inputs path left right next_left next_right :
 VM.find 2399 left = VM.find 2399 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2424 next_left = VM.find 2424 next_right.
Proof.
 intros  E2399 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2424 reference_control_expr_2424 reference_control_1_positions reference_control_1_safety reference_control_member_2424) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2424 reference_control_expr_2424 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2424 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2424 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2399.
 reflexivity.
Qed.
Lemma reference_control_ready_2425 old :
 reference_control_ready old reference_control_expr_2425.
Proof.
 unfold reference_control_expr_2425.
apply rc_binary.
Qed.
Lemma reference_control_member_2425 : List.In (2425,reference_control_expr_2425) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 242%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2425_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2425 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2425 reference_control_expr_2425 reference_control_1_positions reference_control_1_safety reference_control_member_2425) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2425 reference_control_expr_2425 inputs path old current result Position Safe Nonreg (reference_control_ready_2425 old ) Step).
Qed.
Theorem reference_control_node_2425_congruent inputs path left right next_left next_right :
 VM.find 2423 left = VM.find 2423 right ->
 VM.find 2424 left = VM.find 2424 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2425 next_left = VM.find 2425 next_right.
Proof.
 intros  E2423 E2424 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2425 reference_control_expr_2425 reference_control_1_positions reference_control_1_safety reference_control_member_2425) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2425 reference_control_expr_2425 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2425 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2425 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2423.
 rewrite E2424.
 reflexivity.
Qed.
Lemma reference_control_ready_2426 old :
 reference_control_ready old reference_control_expr_2426.
Proof.
 unfold reference_control_expr_2426.
apply rc_unary.
Qed.
Lemma reference_control_member_2426 : List.In (2426,reference_control_expr_2426) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 243%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2426_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2426 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2426 reference_control_expr_2426 reference_control_1_positions reference_control_1_safety reference_control_member_2426) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2426 reference_control_expr_2426 inputs path old current result Position Safe Nonreg (reference_control_ready_2426 old ) Step).
Qed.
Theorem reference_control_node_2426_congruent inputs path left right next_left next_right :
 VM.find 2425 left = VM.find 2425 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2426 next_left = VM.find 2426 next_right.
Proof.
 intros  E2425 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2426 reference_control_expr_2426 reference_control_1_positions reference_control_1_safety reference_control_member_2426) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2426 reference_control_expr_2426 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2426 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2426 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2425.
 reflexivity.
Qed.
Lemma reference_control_ready_2427 old :
 reference_control_ready old reference_control_expr_2427.
Proof.
 unfold reference_control_expr_2427.
apply rc_unary.
Qed.
Lemma reference_control_member_2427 : List.In (2427,reference_control_expr_2427) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 244%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2427_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2427 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2427 reference_control_expr_2427 reference_control_1_positions reference_control_1_safety reference_control_member_2427) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2427 reference_control_expr_2427 inputs path old current result Position Safe Nonreg (reference_control_ready_2427 old ) Step).
Qed.
Theorem reference_control_node_2427_congruent inputs path left right next_left next_right :
 VM.find 2426 left = VM.find 2426 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2427 next_left = VM.find 2427 next_right.
Proof.
 intros  E2426 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2427 reference_control_expr_2427 reference_control_1_positions reference_control_1_safety reference_control_member_2427) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2427 reference_control_expr_2427 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2427 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2427 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2426.
 reflexivity.
Qed.
Lemma reference_control_ready_2428 old :
 reference_control_ready old reference_control_expr_2428.
Proof.
 unfold reference_control_expr_2428.
apply rc_mux.
{ apply rc_const.
}
{ apply rc_const.
}
Qed.
Lemma reference_control_member_2428 : List.In (2428,reference_control_expr_2428) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 245%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2428_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2428 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2428 reference_control_expr_2428 reference_control_1_positions reference_control_1_safety reference_control_member_2428) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2428 reference_control_expr_2428 inputs path old current result Position Safe Nonreg (reference_control_ready_2428 old ) Step).
Qed.
Theorem reference_control_node_2428_congruent inputs path left right next_left next_right :
 VM.find 2427 left = VM.find 2427 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2428 next_left = VM.find 2428 next_right.
Proof.
 intros  E2427 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2428 reference_control_expr_2428 reference_control_1_positions reference_control_1_safety reference_control_member_2428) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2428 reference_control_expr_2428 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2428 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2428 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2427.
 reflexivity.
Qed.
Lemma reference_control_ready_2429 old :
 reference_control_ready old reference_control_expr_2429.
Proof.
 unfold reference_control_expr_2429.
apply rc_binary.
Qed.
Lemma reference_control_member_2429 : List.In (2429,reference_control_expr_2429) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 246%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2429_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2429 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2429 reference_control_expr_2429 reference_control_1_positions reference_control_1_safety reference_control_member_2429) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2429 reference_control_expr_2429 inputs path old current result Position Safe Nonreg (reference_control_ready_2429 old ) Step).
Qed.
Theorem reference_control_node_2429_congruent inputs path left right next_left next_right :
 VM.find 2425 left = VM.find 2425 right ->
 VM.find 2428 left = VM.find 2428 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2429 next_left = VM.find 2429 next_right.
Proof.
 intros  E2425 E2428 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2429 reference_control_expr_2429 reference_control_1_positions reference_control_1_safety reference_control_member_2429) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2429 reference_control_expr_2429 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2429 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2429 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2425.
 rewrite E2428.
 reflexivity.
Qed.
Lemma reference_control_ready_2430 old :
 reference_control_ready old reference_control_expr_2430.
Proof.
 unfold reference_control_expr_2430.
apply rc_binary.
Qed.
Lemma reference_control_member_2430 : List.In (2430,reference_control_expr_2430) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 247%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2430_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2430 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2430 reference_control_expr_2430 reference_control_1_positions reference_control_1_safety reference_control_member_2430) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2430 reference_control_expr_2430 inputs path old current result Position Safe Nonreg (reference_control_ready_2430 old ) Step).
Qed.
Theorem reference_control_node_2430_congruent inputs path left right next_left next_right :
 VM.find 2331 left = VM.find 2331 right ->
 VM.find 2369 left = VM.find 2369 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2430 next_left = VM.find 2430 next_right.
Proof.
 intros  E2331 E2369 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2430 reference_control_expr_2430 reference_control_1_positions reference_control_1_safety reference_control_member_2430) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2430 reference_control_expr_2430 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2430 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2430 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2331.
 rewrite E2369.
 reflexivity.
Qed.
Lemma reference_control_ready_2431 old :
 reference_control_ready old reference_control_expr_2431.
Proof.
 unfold reference_control_expr_2431.
apply rc_binary.
Qed.
Lemma reference_control_member_2431 : List.In (2431,reference_control_expr_2431) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 248%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2431_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2431 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2431 reference_control_expr_2431 reference_control_1_positions reference_control_1_safety reference_control_member_2431) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2431 reference_control_expr_2431 inputs path old current result Position Safe Nonreg (reference_control_ready_2431 old ) Step).
Qed.
Theorem reference_control_node_2431_congruent inputs path left right next_left next_right :
 VM.find 2384 left = VM.find 2384 right ->
 VM.find 2430 left = VM.find 2430 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2431 next_left = VM.find 2431 next_right.
Proof.
 intros  E2384 E2430 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2431 reference_control_expr_2431 reference_control_1_positions reference_control_1_safety reference_control_member_2431) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2431 reference_control_expr_2431 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2431 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2431 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2384.
 rewrite E2430.
 reflexivity.
Qed.
Lemma reference_control_ready_2432 old :
 reference_control_ready old reference_control_expr_2432.
Proof.
 unfold reference_control_expr_2432.
apply rc_binary.
Qed.
Lemma reference_control_member_2432 : List.In (2432,reference_control_expr_2432) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 249%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2432_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2432 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2432 reference_control_expr_2432 reference_control_1_positions reference_control_1_safety reference_control_member_2432) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2432 reference_control_expr_2432 inputs path old current result Position Safe Nonreg (reference_control_ready_2432 old ) Step).
Qed.
Theorem reference_control_node_2432_congruent inputs path left right next_left next_right :
 VM.find 2399 left = VM.find 2399 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2432 next_left = VM.find 2432 next_right.
Proof.
 intros  E2399 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2432 reference_control_expr_2432 reference_control_1_positions reference_control_1_safety reference_control_member_2432) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2432 reference_control_expr_2432 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2432 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2432 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2399.
 reflexivity.
Qed.
Lemma reference_control_ready_2433 old :
 reference_control_ready old reference_control_expr_2433.
Proof.
 unfold reference_control_expr_2433.
apply rc_binary.
Qed.
Lemma reference_control_member_2433 : List.In (2433,reference_control_expr_2433) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 250%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2433_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2433 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2433 reference_control_expr_2433 reference_control_1_positions reference_control_1_safety reference_control_member_2433) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2433 reference_control_expr_2433 inputs path old current result Position Safe Nonreg (reference_control_ready_2433 old ) Step).
Qed.
Theorem reference_control_node_2433_congruent inputs path left right next_left next_right :
 VM.find 2431 left = VM.find 2431 right ->
 VM.find 2432 left = VM.find 2432 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2433 next_left = VM.find 2433 next_right.
Proof.
 intros  E2431 E2432 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2433 reference_control_expr_2433 reference_control_1_positions reference_control_1_safety reference_control_member_2433) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2433 reference_control_expr_2433 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2433 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2433 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2431.
 rewrite E2432.
 reflexivity.
Qed.
Lemma reference_control_ready_2434 old :
 reference_control_ready old reference_control_expr_2434.
Proof.
 unfold reference_control_expr_2434.
apply rc_unary.
Qed.
Lemma reference_control_member_2434 : List.In (2434,reference_control_expr_2434) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 251%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2434_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2434 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2434 reference_control_expr_2434 reference_control_1_positions reference_control_1_safety reference_control_member_2434) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2434 reference_control_expr_2434 inputs path old current result Position Safe Nonreg (reference_control_ready_2434 old ) Step).
Qed.
Theorem reference_control_node_2434_congruent inputs path left right next_left next_right :
 VM.find 2433 left = VM.find 2433 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2434 next_left = VM.find 2434 next_right.
Proof.
 intros  E2433 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2434 reference_control_expr_2434 reference_control_1_positions reference_control_1_safety reference_control_member_2434) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2434 reference_control_expr_2434 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2434 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2434 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2433.
 reflexivity.
Qed.
Lemma reference_control_ready_2435 old :
 reference_control_ready old reference_control_expr_2435.
Proof.
 unfold reference_control_expr_2435.
apply rc_unary.
Qed.
Lemma reference_control_member_2435 : List.In (2435,reference_control_expr_2435) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 252%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2435_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2435 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2435 reference_control_expr_2435 reference_control_1_positions reference_control_1_safety reference_control_member_2435) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2435 reference_control_expr_2435 inputs path old current result Position Safe Nonreg (reference_control_ready_2435 old ) Step).
Qed.
Theorem reference_control_node_2435_congruent inputs path left right next_left next_right :
 VM.find 2434 left = VM.find 2434 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2435 next_left = VM.find 2435 next_right.
Proof.
 intros  E2434 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2435 reference_control_expr_2435 reference_control_1_positions reference_control_1_safety reference_control_member_2435) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2435 reference_control_expr_2435 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2435 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2435 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2434.
 reflexivity.
Qed.
Lemma reference_control_ready_2436 old :
 reference_control_ready old reference_control_expr_2436.
Proof.
 unfold reference_control_expr_2436.
apply rc_mux.
{ apply rc_const.
}
{ apply rc_const.
}
Qed.
Lemma reference_control_member_2436 : List.In (2436,reference_control_expr_2436) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 253%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2436_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2436 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2436 reference_control_expr_2436 reference_control_1_positions reference_control_1_safety reference_control_member_2436) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2436 reference_control_expr_2436 inputs path old current result Position Safe Nonreg (reference_control_ready_2436 old ) Step).
Qed.
Theorem reference_control_node_2436_congruent inputs path left right next_left next_right :
 VM.find 2435 left = VM.find 2435 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2436 next_left = VM.find 2436 next_right.
Proof.
 intros  E2435 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2436 reference_control_expr_2436 reference_control_1_positions reference_control_1_safety reference_control_member_2436) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2436 reference_control_expr_2436 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2436 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2436 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2435.
 reflexivity.
Qed.
Lemma reference_control_ready_2437 old :
 reference_control_ready old reference_control_expr_2437.
Proof.
 unfold reference_control_expr_2437.
apply rc_binary.
Qed.
Lemma reference_control_member_2437 : List.In (2437,reference_control_expr_2437) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 254%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2437_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2437 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2437 reference_control_expr_2437 reference_control_1_positions reference_control_1_safety reference_control_member_2437) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2437 reference_control_expr_2437 inputs path old current result Position Safe Nonreg (reference_control_ready_2437 old ) Step).
Qed.
Theorem reference_control_node_2437_congruent inputs path left right next_left next_right :
 VM.find 2433 left = VM.find 2433 right ->
 VM.find 2436 left = VM.find 2436 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2437 next_left = VM.find 2437 next_right.
Proof.
 intros  E2433 E2436 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2437 reference_control_expr_2437 reference_control_1_positions reference_control_1_safety reference_control_member_2437) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2437 reference_control_expr_2437 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2437 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2437 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2433.
 rewrite E2436.
 reflexivity.
Qed.
Lemma reference_control_ready_2438 old :
 reference_control_ready old reference_control_expr_2438.
Proof.
 unfold reference_control_expr_2438.
apply rc_binary.
Qed.
Lemma reference_control_member_2438 : List.In (2438,reference_control_expr_2438) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 255%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2438_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2438 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2438 reference_control_expr_2438 reference_control_1_positions reference_control_1_safety reference_control_member_2438) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2438 reference_control_expr_2438 inputs path old current result Position Safe Nonreg (reference_control_ready_2438 old ) Step).
Qed.
Theorem reference_control_node_2438_congruent inputs path left right next_left next_right :
 VM.find 2331 left = VM.find 2331 right ->
 VM.find 2369 left = VM.find 2369 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2438 next_left = VM.find 2438 next_right.
Proof.
 intros  E2331 E2369 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2438 reference_control_expr_2438 reference_control_1_positions reference_control_1_safety reference_control_member_2438) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2438 reference_control_expr_2438 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2438 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2438 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2331.
 rewrite E2369.
 reflexivity.
Qed.
Lemma reference_control_ready_2439 old :
 reference_control_ready old reference_control_expr_2439.
Proof.
 unfold reference_control_expr_2439.
apply rc_binary.
Qed.
Lemma reference_control_member_2439 : List.In (2439,reference_control_expr_2439) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 256%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2439_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2439 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2439 reference_control_expr_2439 reference_control_1_positions reference_control_1_safety reference_control_member_2439) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2439 reference_control_expr_2439 inputs path old current result Position Safe Nonreg (reference_control_ready_2439 old ) Step).
Qed.
Theorem reference_control_node_2439_congruent inputs path left right next_left next_right :
 VM.find 2384 left = VM.find 2384 right ->
 VM.find 2438 left = VM.find 2438 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2439 next_left = VM.find 2439 next_right.
Proof.
 intros  E2384 E2438 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2439 reference_control_expr_2439 reference_control_1_positions reference_control_1_safety reference_control_member_2439) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2439 reference_control_expr_2439 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2439 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2439 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2384.
 rewrite E2438.
 reflexivity.
Qed.
Lemma reference_control_ready_2440 old :
 reference_control_ready old reference_control_expr_2440.
Proof.
 unfold reference_control_expr_2440.
apply rc_binary.
Qed.
Lemma reference_control_member_2440 : List.In (2440,reference_control_expr_2440) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 257%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2440_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2440 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2440 reference_control_expr_2440 reference_control_1_positions reference_control_1_safety reference_control_member_2440) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2440 reference_control_expr_2440 inputs path old current result Position Safe Nonreg (reference_control_ready_2440 old ) Step).
Qed.
Theorem reference_control_node_2440_congruent inputs path left right next_left next_right :
 VM.find 2399 left = VM.find 2399 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2440 next_left = VM.find 2440 next_right.
Proof.
 intros  E2399 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2440 reference_control_expr_2440 reference_control_1_positions reference_control_1_safety reference_control_member_2440) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2440 reference_control_expr_2440 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2440 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2440 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2399.
 reflexivity.
Qed.
Lemma reference_control_ready_2441 old :
 reference_control_ready old reference_control_expr_2441.
Proof.
 unfold reference_control_expr_2441.
apply rc_binary.
Qed.
Lemma reference_control_member_2441 : List.In (2441,reference_control_expr_2441) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 258%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2441_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2441 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2441 reference_control_expr_2441 reference_control_1_positions reference_control_1_safety reference_control_member_2441) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2441 reference_control_expr_2441 inputs path old current result Position Safe Nonreg (reference_control_ready_2441 old ) Step).
Qed.
Theorem reference_control_node_2441_congruent inputs path left right next_left next_right :
 VM.find 2439 left = VM.find 2439 right ->
 VM.find 2440 left = VM.find 2440 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2441 next_left = VM.find 2441 next_right.
Proof.
 intros  E2439 E2440 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2441 reference_control_expr_2441 reference_control_1_positions reference_control_1_safety reference_control_member_2441) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2441 reference_control_expr_2441 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2441 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2441 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2439.
 rewrite E2440.
 reflexivity.
Qed.
Lemma reference_control_ready_2442 old :
 reference_control_ready old reference_control_expr_2442.
Proof.
 unfold reference_control_expr_2442.
apply rc_unary.
Qed.
Lemma reference_control_member_2442 : List.In (2442,reference_control_expr_2442) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 259%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2442_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2442 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2442 reference_control_expr_2442 reference_control_1_positions reference_control_1_safety reference_control_member_2442) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2442 reference_control_expr_2442 inputs path old current result Position Safe Nonreg (reference_control_ready_2442 old ) Step).
Qed.
Theorem reference_control_node_2442_congruent inputs path left right next_left next_right :
 VM.find 2441 left = VM.find 2441 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2442 next_left = VM.find 2442 next_right.
Proof.
 intros  E2441 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2442 reference_control_expr_2442 reference_control_1_positions reference_control_1_safety reference_control_member_2442) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2442 reference_control_expr_2442 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2442 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2442 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2441.
 reflexivity.
Qed.
Lemma reference_control_ready_2443 old :
 reference_control_ready old reference_control_expr_2443.
Proof.
 unfold reference_control_expr_2443.
apply rc_unary.
Qed.
Lemma reference_control_member_2443 : List.In (2443,reference_control_expr_2443) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 260%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2443_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2443 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2443 reference_control_expr_2443 reference_control_1_positions reference_control_1_safety reference_control_member_2443) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2443 reference_control_expr_2443 inputs path old current result Position Safe Nonreg (reference_control_ready_2443 old ) Step).
Qed.
Theorem reference_control_node_2443_congruent inputs path left right next_left next_right :
 VM.find 2442 left = VM.find 2442 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2443 next_left = VM.find 2443 next_right.
Proof.
 intros  E2442 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2443 reference_control_expr_2443 reference_control_1_positions reference_control_1_safety reference_control_member_2443) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2443 reference_control_expr_2443 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2443 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2443 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2442.
 reflexivity.
Qed.
Lemma reference_control_ready_2444 old :
 reference_control_ready old reference_control_expr_2444.
Proof.
 unfold reference_control_expr_2444.
apply rc_mux.
{ apply rc_const.
}
{ apply rc_const.
}
Qed.
Lemma reference_control_member_2444 : List.In (2444,reference_control_expr_2444) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 261%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2444_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2444 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2444 reference_control_expr_2444 reference_control_1_positions reference_control_1_safety reference_control_member_2444) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2444 reference_control_expr_2444 inputs path old current result Position Safe Nonreg (reference_control_ready_2444 old ) Step).
Qed.
Theorem reference_control_node_2444_congruent inputs path left right next_left next_right :
 VM.find 2443 left = VM.find 2443 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2444 next_left = VM.find 2444 next_right.
Proof.
 intros  E2443 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2444 reference_control_expr_2444 reference_control_1_positions reference_control_1_safety reference_control_member_2444) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2444 reference_control_expr_2444 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2444 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2444 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2443.
 reflexivity.
Qed.
Lemma reference_control_ready_2445 old :
 reference_control_ready old reference_control_expr_2445.
Proof.
 unfold reference_control_expr_2445.
apply rc_binary.
Qed.
Lemma reference_control_member_2445 : List.In (2445,reference_control_expr_2445) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 262%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2445_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2445 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2445 reference_control_expr_2445 reference_control_1_positions reference_control_1_safety reference_control_member_2445) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2445 reference_control_expr_2445 inputs path old current result Position Safe Nonreg (reference_control_ready_2445 old ) Step).
Qed.
Theorem reference_control_node_2445_congruent inputs path left right next_left next_right :
 VM.find 2441 left = VM.find 2441 right ->
 VM.find 2444 left = VM.find 2444 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2445 next_left = VM.find 2445 next_right.
Proof.
 intros  E2441 E2444 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2445 reference_control_expr_2445 reference_control_1_positions reference_control_1_safety reference_control_member_2445) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2445 reference_control_expr_2445 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2445 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2445 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2441.
 rewrite E2444.
 reflexivity.
Qed.
Lemma reference_control_ready_2446 old :
 reference_control_ready old reference_control_expr_2446.
Proof.
 unfold reference_control_expr_2446.
apply rc_unary.
Qed.
Lemma reference_control_member_2446 : List.In (2446,reference_control_expr_2446) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 263%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2446_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2446 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2446 reference_control_expr_2446 reference_control_1_positions reference_control_1_safety reference_control_member_2446) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2446 reference_control_expr_2446 inputs path old current result Position Safe Nonreg (reference_control_ready_2446 old ) Step).
Qed.
Theorem reference_control_node_2446_congruent inputs path left right next_left next_right :
 VM.find 2248 left = VM.find 2248 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2446 next_left = VM.find 2446 next_right.
Proof.
 intros  E2248 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2446 reference_control_expr_2446 reference_control_1_positions reference_control_1_safety reference_control_member_2446) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2446 reference_control_expr_2446 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2446 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2446 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2248.
 reflexivity.
Qed.
Lemma reference_control_ready_2447 old :
 reference_control_ready old reference_control_expr_2447.
Proof.
 unfold reference_control_expr_2447.
apply rc_unary.
Qed.
Lemma reference_control_member_2447 : List.In (2447,reference_control_expr_2447) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 264%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2447_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2447 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2447 reference_control_expr_2447 reference_control_1_positions reference_control_1_safety reference_control_member_2447) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2447 reference_control_expr_2447 inputs path old current result Position Safe Nonreg (reference_control_ready_2447 old ) Step).
Qed.
Theorem reference_control_node_2447_congruent inputs path left right next_left next_right :
 VM.find 2446 left = VM.find 2446 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2447 next_left = VM.find 2447 next_right.
Proof.
 intros  E2446 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2447 reference_control_expr_2447 reference_control_1_positions reference_control_1_safety reference_control_member_2447) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2447 reference_control_expr_2447 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2447 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2447 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2446.
 reflexivity.
Qed.
Lemma reference_control_ready_2448 old :
 reference_control_ready old reference_control_expr_2448.
Proof.
 unfold reference_control_expr_2448.
apply rc_mux.
{ apply rc_const.
}
{ apply rc_const.
}
Qed.
Lemma reference_control_member_2448 : List.In (2448,reference_control_expr_2448) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 265%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2448_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2448 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2448 reference_control_expr_2448 reference_control_1_positions reference_control_1_safety reference_control_member_2448) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2448 reference_control_expr_2448 inputs path old current result Position Safe Nonreg (reference_control_ready_2448 old ) Step).
Qed.
Theorem reference_control_node_2448_congruent inputs path left right next_left next_right :
 VM.find 2447 left = VM.find 2447 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2448 next_left = VM.find 2448 next_right.
Proof.
 intros  E2447 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2448 reference_control_expr_2448 reference_control_1_positions reference_control_1_safety reference_control_member_2448) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2448 reference_control_expr_2448 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2448 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2448 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2447.
 reflexivity.
Qed.
Lemma reference_control_ready_2449 old :
 reference_control_ready old reference_control_expr_2449.
Proof.
 unfold reference_control_expr_2449.
apply rc_binary.
Qed.
Lemma reference_control_member_2449 : List.In (2449,reference_control_expr_2449) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 266%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2449_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2449 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2449 reference_control_expr_2449 reference_control_1_positions reference_control_1_safety reference_control_member_2449) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2449 reference_control_expr_2449 inputs path old current result Position Safe Nonreg (reference_control_ready_2449 old ) Step).
Qed.
Theorem reference_control_node_2449_congruent inputs path left right next_left next_right :
 VM.find 2248 left = VM.find 2248 right ->
 VM.find 2448 left = VM.find 2448 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2449 next_left = VM.find 2449 next_right.
Proof.
 intros  E2248 E2448 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2449 reference_control_expr_2449 reference_control_1_positions reference_control_1_safety reference_control_member_2449) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2449 reference_control_expr_2449 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2449 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2449 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2248.
 rewrite E2448.
 reflexivity.
Qed.
Lemma reference_control_ready_2450 old :
 reference_control_ready old reference_control_expr_2450.
Proof.
 unfold reference_control_expr_2450.
apply rc_unary.
Qed.
Lemma reference_control_member_2450 : List.In (2450,reference_control_expr_2450) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 267%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2450_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2450 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2450 reference_control_expr_2450 reference_control_1_positions reference_control_1_safety reference_control_member_2450) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2450 reference_control_expr_2450 inputs path old current result Position Safe Nonreg (reference_control_ready_2450 old ) Step).
Qed.
Theorem reference_control_node_2450_congruent inputs path left right next_left next_right :
 VM.find 1884 left = VM.find 1884 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2450 next_left = VM.find 2450 next_right.
Proof.
 intros  E1884 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2450 reference_control_expr_2450 reference_control_1_positions reference_control_1_safety reference_control_member_2450) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2450 reference_control_expr_2450 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2450 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2450 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1884.
 reflexivity.
Qed.
Lemma reference_control_ready_2451 old :
 (exists value ground, VM.find 2450 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2451.
Proof.
 intros H2450.
 destruct H2450 as [v2450 [G2450 [V2450 T2450]]].
 unfold reference_control_expr_2451.
apply rc_mux.
{ eapply rc_ref; [exact V2450|exists G2450; exact T2450].
}
{ apply rc_const.
}
Qed.
Lemma reference_control_member_2451 : List.In (2451,reference_control_expr_2451) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 268%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2451_ground inputs path old current result :
 (exists value ground, VM.find 2450 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2451 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2450 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2451 reference_control_expr_2451 reference_control_1_positions reference_control_1_safety reference_control_member_2451) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2451 reference_control_expr_2451 inputs path old current result Position Safe Nonreg (reference_control_ready_2451 old H2450) Step).
Qed.
Theorem reference_control_node_2451_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2450 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2357 left = VM.find 2357 right ->
 VM.find 2450 left = VM.find 2450 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2451 next_left = VM.find 2451 next_right.
Proof.
 intros H2450 E2357 E2450 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2451 reference_control_expr_2451 reference_control_1_positions reference_control_1_safety reference_control_member_2451) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2451 reference_control_expr_2451 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2451 left H2450)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2451 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2357.
 rewrite E2450.
 reflexivity.
Qed.
Lemma reference_control_ready_2452 old :
 (exists value ground, VM.find 2451 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2452.
Proof.
 intros H2451.
 destruct H2451 as [v2451 [G2451 [V2451 T2451]]].
 unfold reference_control_expr_2452.
apply rc_mux.
{ eapply rc_ref; [exact V2451|exists G2451; exact T2451].
}
{ apply rc_const.
}
Qed.
Lemma reference_control_member_2452 : List.In (2452,reference_control_expr_2452) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 269%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2452_ground inputs path old current result :
 (exists value ground, VM.find 2451 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2452 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2451 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2452 reference_control_expr_2452 reference_control_1_positions reference_control_1_safety reference_control_member_2452) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2452 reference_control_expr_2452 inputs path old current result Position Safe Nonreg (reference_control_ready_2452 old H2451) Step).
Qed.
Theorem reference_control_node_2452_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2451 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1707 left = VM.find 1707 right ->
 VM.find 2451 left = VM.find 2451 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2452 next_left = VM.find 2452 next_right.
Proof.
 intros H2451 E1707 E2451 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2452 reference_control_expr_2452 reference_control_1_positions reference_control_1_safety reference_control_member_2452) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2452 reference_control_expr_2452 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2452 left H2451)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2452 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1707.
 rewrite E2451.
 reflexivity.
Qed.
Lemma reference_control_ready_2453 old :
 (exists value ground, VM.find 2452 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2453.
Proof.
 intros H2452.
 destruct H2452 as [v2452 [G2452 [V2452 T2452]]].
 unfold reference_control_expr_2453.
eapply rc_ref; [exact V2452|exists G2452; exact T2452].
Qed.
Lemma reference_control_member_2453 : List.In (2453,reference_control_expr_2453) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 270%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2453_ground inputs path old current result :
 (exists value ground, VM.find 2452 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2453 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2452 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2453 reference_control_expr_2453 reference_control_1_positions reference_control_1_safety reference_control_member_2453) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2453 reference_control_expr_2453 inputs path old current result Position Safe Nonreg (reference_control_ready_2453 old H2452) Step).
Qed.
Theorem reference_control_node_2453_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2452 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2452 left = VM.find 2452 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2453 next_left = VM.find 2453 next_right.
Proof.
 intros H2452 E2452 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2453 reference_control_expr_2453 reference_control_1_positions reference_control_1_safety reference_control_member_2453) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2453 reference_control_expr_2453 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2453 left H2452)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2453 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2452.
 reflexivity.
Qed.
Lemma reference_control_ready_2454 old :
 reference_control_ready old reference_control_expr_2454.
Proof.
 unfold reference_control_expr_2454.
apply rc_unary.
Qed.
Lemma reference_control_member_2454 : List.In (2454,reference_control_expr_2454) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 271%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2454_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2454 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2454 reference_control_expr_2454 reference_control_1_positions reference_control_1_safety reference_control_member_2454) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2454 reference_control_expr_2454 inputs path old current result Position Safe Nonreg (reference_control_ready_2454 old ) Step).
Qed.
Theorem reference_control_node_2454_congruent inputs path left right next_left next_right :
 VM.find 2359 left = VM.find 2359 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2454 next_left = VM.find 2454 next_right.
Proof.
 intros  E2359 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2454 reference_control_expr_2454 reference_control_1_positions reference_control_1_safety reference_control_member_2454) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2454 reference_control_expr_2454 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2454 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2454 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2359.
 reflexivity.
Qed.
Lemma reference_control_ready_2455 old :
 reference_control_ready old reference_control_expr_2455.
Proof.
 unfold reference_control_expr_2455.
apply rc_unary.
Qed.
Lemma reference_control_member_2455 : List.In (2455,reference_control_expr_2455) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 272%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2455_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2455 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2455 reference_control_expr_2455 reference_control_1_positions reference_control_1_safety reference_control_member_2455) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2455 reference_control_expr_2455 inputs path old current result Position Safe Nonreg (reference_control_ready_2455 old ) Step).
Qed.
Theorem reference_control_node_2455_congruent inputs path left right next_left next_right :
 VM.find 2454 left = VM.find 2454 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2455 next_left = VM.find 2455 next_right.
Proof.
 intros  E2454 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2455 reference_control_expr_2455 reference_control_1_positions reference_control_1_safety reference_control_member_2455) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2455 reference_control_expr_2455 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2455 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2455 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2454.
 reflexivity.
Qed.
Lemma reference_control_ready_2456 old :
 (exists value ground, VM.find 2455 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2456.
Proof.
 intros H2455.
 destruct H2455 as [v2455 [G2455 [V2455 T2455]]].
 unfold reference_control_expr_2456.
apply rc_mux.
{ eapply rc_ref; [exact V2455|exists G2455; exact T2455].
}
{ apply rc_const.
}
Qed.
Lemma reference_control_member_2456 : List.In (2456,reference_control_expr_2456) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 273%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2456_ground inputs path old current result :
 (exists value ground, VM.find 2455 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2456 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2455 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2456 reference_control_expr_2456 reference_control_1_positions reference_control_1_safety reference_control_member_2456) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2456 reference_control_expr_2456 inputs path old current result Position Safe Nonreg (reference_control_ready_2456 old H2455) Step).
Qed.
Theorem reference_control_node_2456_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2455 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2357 left = VM.find 2357 right ->
 VM.find 2455 left = VM.find 2455 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2456 next_left = VM.find 2456 next_right.
Proof.
 intros H2455 E2357 E2455 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2456 reference_control_expr_2456 reference_control_1_positions reference_control_1_safety reference_control_member_2456) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2456 reference_control_expr_2456 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2456 left H2455)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2456 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2357.
 rewrite E2455.
 reflexivity.
Qed.
Lemma reference_control_ready_2457 old :
 (exists value ground, VM.find 2456 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2457.
Proof.
 intros H2456.
 destruct H2456 as [v2456 [G2456 [V2456 T2456]]].
 unfold reference_control_expr_2457.
apply rc_mux.
{ eapply rc_ref; [exact V2456|exists G2456; exact T2456].
}
{ apply rc_const.
}
Qed.
Lemma reference_control_member_2457 : List.In (2457,reference_control_expr_2457) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 274%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2457_ground inputs path old current result :
 (exists value ground, VM.find 2456 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2457 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2456 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2457 reference_control_expr_2457 reference_control_1_positions reference_control_1_safety reference_control_member_2457) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2457 reference_control_expr_2457 inputs path old current result Position Safe Nonreg (reference_control_ready_2457 old H2456) Step).
Qed.
Theorem reference_control_node_2457_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2456 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1707 left = VM.find 1707 right ->
 VM.find 2456 left = VM.find 2456 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2457 next_left = VM.find 2457 next_right.
Proof.
 intros H2456 E1707 E2456 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2457 reference_control_expr_2457 reference_control_1_positions reference_control_1_safety reference_control_member_2457) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2457 reference_control_expr_2457 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2457 left H2456)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2457 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1707.
 rewrite E2456.
 reflexivity.
Qed.
Lemma reference_control_ready_2458 old :
 (exists value ground, VM.find 2457 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2458.
Proof.
 intros H2457.
 destruct H2457 as [v2457 [G2457 [V2457 T2457]]].
 unfold reference_control_expr_2458.
eapply rc_ref; [exact V2457|exists G2457; exact T2457].
Qed.
Lemma reference_control_member_2458 : List.In (2458,reference_control_expr_2458) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 275%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2458_ground inputs path old current result :
 (exists value ground, VM.find 2457 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2458 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2457 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2458 reference_control_expr_2458 reference_control_1_positions reference_control_1_safety reference_control_member_2458) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2458 reference_control_expr_2458 inputs path old current result Position Safe Nonreg (reference_control_ready_2458 old H2457) Step).
Qed.
Theorem reference_control_node_2458_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2457 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2457 left = VM.find 2457 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2458 next_left = VM.find 2458 next_right.
Proof.
 intros H2457 E2457 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2458 reference_control_expr_2458 reference_control_1_positions reference_control_1_safety reference_control_member_2458) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2458 reference_control_expr_2458 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2458 left H2457)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2458 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2457.
 reflexivity.
Qed.
Lemma reference_control_ready_2459 old :
 reference_control_ready old reference_control_expr_2459.
Proof.
 unfold reference_control_expr_2459.
apply rc_binary.
Qed.
Lemma reference_control_member_2459 : List.In (2459,reference_control_expr_2459) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 276%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2459_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2459 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2459 reference_control_expr_2459 reference_control_1_positions reference_control_1_safety reference_control_member_2459) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2459 reference_control_expr_2459 inputs path old current result Position Safe Nonreg (reference_control_ready_2459 old ) Step).
Qed.
Theorem reference_control_node_2459_congruent inputs path left right next_left next_right :
 VM.find 2453 left = VM.find 2453 right ->
 VM.find 2458 left = VM.find 2458 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2459 next_left = VM.find 2459 next_right.
Proof.
 intros  E2453 E2458 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2459 reference_control_expr_2459 reference_control_1_positions reference_control_1_safety reference_control_member_2459) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2459 reference_control_expr_2459 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2459 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2459 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2453.
 rewrite E2458.
 reflexivity.
Qed.
Lemma reference_control_ready_2460 old :
 reference_control_ready old reference_control_expr_2460.
Proof.
 unfold reference_control_expr_2460.
apply rc_binary.
Qed.
Lemma reference_control_member_2460 : List.In (2460,reference_control_expr_2460) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 277%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2460_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2460 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2460 reference_control_expr_2460 reference_control_1_positions reference_control_1_safety reference_control_member_2460) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2460 reference_control_expr_2460 inputs path old current result Position Safe Nonreg (reference_control_ready_2460 old ) Step).
Qed.
Theorem reference_control_node_2460_congruent inputs path left right next_left next_right :
 VM.find 2369 left = VM.find 2369 right ->
 VM.find 2459 left = VM.find 2459 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2460 next_left = VM.find 2460 next_right.
Proof.
 intros  E2369 E2459 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2460 reference_control_expr_2460 reference_control_1_positions reference_control_1_safety reference_control_member_2460) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2460 reference_control_expr_2460 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2460 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2460 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2369.
 rewrite E2459.
 reflexivity.
Qed.
Lemma reference_control_ready_2461 old :
 reference_control_ready old reference_control_expr_2461.
Proof.
 unfold reference_control_expr_2461.
apply rc_unary.
Qed.
Lemma reference_control_member_2461 : List.In (2461,reference_control_expr_2461) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 278%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2461_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2461 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2461 reference_control_expr_2461 reference_control_1_positions reference_control_1_safety reference_control_member_2461) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2461 reference_control_expr_2461 inputs path old current result Position Safe Nonreg (reference_control_ready_2461 old ) Step).
Qed.
Theorem reference_control_node_2461_congruent inputs path left right next_left next_right :
 VM.find 2358 left = VM.find 2358 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2461 next_left = VM.find 2461 next_right.
Proof.
 intros  E2358 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2461 reference_control_expr_2461 reference_control_1_positions reference_control_1_safety reference_control_member_2461) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2461 reference_control_expr_2461 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2461 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2461 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2358.
 reflexivity.
Qed.
Lemma reference_control_ready_2462 old :
 (exists value ground, VM.find 2461 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2462.
Proof.
 intros H2461.
 destruct H2461 as [v2461 [G2461 [V2461 T2461]]].
 unfold reference_control_expr_2462.
apply rc_mux.
{ eapply rc_ref; [exact V2461|exists G2461; exact T2461].
}
{ apply rc_const.
}
Qed.
Lemma reference_control_member_2462 : List.In (2462,reference_control_expr_2462) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 279%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2462_ground inputs path old current result :
 (exists value ground, VM.find 2461 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2462 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2461 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2462 reference_control_expr_2462 reference_control_1_positions reference_control_1_safety reference_control_member_2462) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2462 reference_control_expr_2462 inputs path old current result Position Safe Nonreg (reference_control_ready_2462 old H2461) Step).
Qed.
Theorem reference_control_node_2462_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2461 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2357 left = VM.find 2357 right ->
 VM.find 2461 left = VM.find 2461 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2462 next_left = VM.find 2462 next_right.
Proof.
 intros H2461 E2357 E2461 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2462 reference_control_expr_2462 reference_control_1_positions reference_control_1_safety reference_control_member_2462) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2462 reference_control_expr_2462 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2462 left H2461)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2462 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2357.
 rewrite E2461.
 reflexivity.
Qed.
Lemma reference_control_ready_2463 old :
 (exists value ground, VM.find 2462 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2463.
Proof.
 intros H2462.
 destruct H2462 as [v2462 [G2462 [V2462 T2462]]].
 unfold reference_control_expr_2463.
apply rc_mux.
{ eapply rc_ref; [exact V2462|exists G2462; exact T2462].
}
{ apply rc_const.
}
Qed.
Lemma reference_control_member_2463 : List.In (2463,reference_control_expr_2463) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 280%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2463_ground inputs path old current result :
 (exists value ground, VM.find 2462 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2463 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2462 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2463 reference_control_expr_2463 reference_control_1_positions reference_control_1_safety reference_control_member_2463) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2463 reference_control_expr_2463 inputs path old current result Position Safe Nonreg (reference_control_ready_2463 old H2462) Step).
Qed.
Theorem reference_control_node_2463_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2462 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1707 left = VM.find 1707 right ->
 VM.find 2462 left = VM.find 2462 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2463 next_left = VM.find 2463 next_right.
Proof.
 intros H2462 E1707 E2462 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2463 reference_control_expr_2463 reference_control_1_positions reference_control_1_safety reference_control_member_2463) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2463 reference_control_expr_2463 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2463 left H2462)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2463 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1707.
 rewrite E2462.
 reflexivity.
Qed.
Lemma reference_control_ready_2464 old :
 (exists value ground, VM.find 2463 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2464.
Proof.
 intros H2463.
 destruct H2463 as [v2463 [G2463 [V2463 T2463]]].
 unfold reference_control_expr_2464.
eapply rc_ref; [exact V2463|exists G2463; exact T2463].
Qed.
Lemma reference_control_member_2464 : List.In (2464,reference_control_expr_2464) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 281%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2464_ground inputs path old current result :
 (exists value ground, VM.find 2463 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2464 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2463 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2464 reference_control_expr_2464 reference_control_1_positions reference_control_1_safety reference_control_member_2464) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2464 reference_control_expr_2464 inputs path old current result Position Safe Nonreg (reference_control_ready_2464 old H2463) Step).
Qed.
Theorem reference_control_node_2464_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2463 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2463 left = VM.find 2463 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2464 next_left = VM.find 2464 next_right.
Proof.
 intros H2463 E2463 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2464 reference_control_expr_2464 reference_control_1_positions reference_control_1_safety reference_control_member_2464) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2464 reference_control_expr_2464 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2464 left H2463)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2464 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2463.
 reflexivity.
Qed.
Lemma reference_control_ready_2465 old :
 reference_control_ready old reference_control_expr_2465.
Proof.
 unfold reference_control_expr_2465.
apply rc_binary.
Qed.
Lemma reference_control_member_2465 : List.In (2465,reference_control_expr_2465) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 282%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2465_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2465 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2465 reference_control_expr_2465 reference_control_1_positions reference_control_1_safety reference_control_member_2465) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2465 reference_control_expr_2465 inputs path old current result Position Safe Nonreg (reference_control_ready_2465 old ) Step).
Qed.
Theorem reference_control_node_2465_congruent inputs path left right next_left next_right :
 VM.find 2464 left = VM.find 2464 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2465 next_left = VM.find 2465 next_right.
Proof.
 intros  E2464 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2465 reference_control_expr_2465 reference_control_1_positions reference_control_1_safety reference_control_member_2465) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2465 reference_control_expr_2465 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2465 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2465 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2464.
 reflexivity.
Qed.
Lemma reference_control_ready_2466 old :
 reference_control_ready old reference_control_expr_2466.
Proof.
 unfold reference_control_expr_2466.
apply rc_binary.
Qed.
Lemma reference_control_member_2466 : List.In (2466,reference_control_expr_2466) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 283%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2466_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2466 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2466 reference_control_expr_2466 reference_control_1_positions reference_control_1_safety reference_control_member_2466) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2466 reference_control_expr_2466 inputs path old current result Position Safe Nonreg (reference_control_ready_2466 old ) Step).
Qed.
Theorem reference_control_node_2466_congruent inputs path left right next_left next_right :
 VM.find 2460 left = VM.find 2460 right ->
 VM.find 2465 left = VM.find 2465 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2466 next_left = VM.find 2466 next_right.
Proof.
 intros  E2460 E2465 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2466 reference_control_expr_2466 reference_control_1_positions reference_control_1_safety reference_control_member_2466) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2466 reference_control_expr_2466 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2466 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2466 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2460.
 rewrite E2465.
 reflexivity.
Qed.
Lemma reference_control_ready_2467 old :
 reference_control_ready old reference_control_expr_2467.
Proof.
 unfold reference_control_expr_2467.
apply rc_unary.
Qed.
Lemma reference_control_member_2467 : List.In (2467,reference_control_expr_2467) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 284%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2467_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2467 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2467 reference_control_expr_2467 reference_control_1_positions reference_control_1_safety reference_control_member_2467) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2467 reference_control_expr_2467 inputs path old current result Position Safe Nonreg (reference_control_ready_2467 old ) Step).
Qed.
Theorem reference_control_node_2467_congruent inputs path left right next_left next_right :
 VM.find 2466 left = VM.find 2466 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2467 next_left = VM.find 2467 next_right.
Proof.
 intros  E2466 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2467 reference_control_expr_2467 reference_control_1_positions reference_control_1_safety reference_control_member_2467) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2467 reference_control_expr_2467 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2467 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2467 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2466.
 reflexivity.
Qed.
Lemma reference_control_ready_2468 old :
 reference_control_ready old reference_control_expr_2468.
Proof.
 unfold reference_control_expr_2468.
apply rc_unary.
Qed.
Lemma reference_control_member_2468 : List.In (2468,reference_control_expr_2468) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 285%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2468_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2468 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2468 reference_control_expr_2468 reference_control_1_positions reference_control_1_safety reference_control_member_2468) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2468 reference_control_expr_2468 inputs path old current result Position Safe Nonreg (reference_control_ready_2468 old ) Step).
Qed.
Theorem reference_control_node_2468_congruent inputs path left right next_left next_right :
 VM.find 2467 left = VM.find 2467 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2468 next_left = VM.find 2468 next_right.
Proof.
 intros  E2467 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2468 reference_control_expr_2468 reference_control_1_positions reference_control_1_safety reference_control_member_2468) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2468 reference_control_expr_2468 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2468 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2468 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2467.
 reflexivity.
Qed.
Lemma reference_control_ready_2469 old :
 reference_control_ready old reference_control_expr_2469.
Proof.
 unfold reference_control_expr_2469.
apply rc_mux.
{ apply rc_const.
}
{ apply rc_const.
}
Qed.
Lemma reference_control_member_2469 : List.In (2469,reference_control_expr_2469) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 286%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2469_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2469 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2469 reference_control_expr_2469 reference_control_1_positions reference_control_1_safety reference_control_member_2469) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2469 reference_control_expr_2469 inputs path old current result Position Safe Nonreg (reference_control_ready_2469 old ) Step).
Qed.
Theorem reference_control_node_2469_congruent inputs path left right next_left next_right :
 VM.find 2468 left = VM.find 2468 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2469 next_left = VM.find 2469 next_right.
Proof.
 intros  E2468 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2469 reference_control_expr_2469 reference_control_1_positions reference_control_1_safety reference_control_member_2469) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2469 reference_control_expr_2469 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2469 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2469 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2468.
 reflexivity.
Qed.
Lemma reference_control_ready_2470 old :
 reference_control_ready old reference_control_expr_2470.
Proof.
 unfold reference_control_expr_2470.
apply rc_binary.
Qed.
Lemma reference_control_member_2470 : List.In (2470,reference_control_expr_2470) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 287%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2470_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2470 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2470 reference_control_expr_2470 reference_control_1_positions reference_control_1_safety reference_control_member_2470) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2470 reference_control_expr_2470 inputs path old current result Position Safe Nonreg (reference_control_ready_2470 old ) Step).
Qed.
Theorem reference_control_node_2470_congruent inputs path left right next_left next_right :
 VM.find 2466 left = VM.find 2466 right ->
 VM.find 2469 left = VM.find 2469 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2470 next_left = VM.find 2470 next_right.
Proof.
 intros  E2466 E2469 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2470 reference_control_expr_2470 reference_control_1_positions reference_control_1_safety reference_control_member_2470) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2470 reference_control_expr_2470 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2470 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2470 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2466.
 rewrite E2469.
 reflexivity.
Qed.
Lemma reference_control_ready_2471 old :
 reference_control_ready old reference_control_expr_2471.
Proof.
 unfold reference_control_expr_2471.
apply rc_binary.
Qed.
Lemma reference_control_member_2471 : List.In (2471,reference_control_expr_2471) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 288%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2471_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2471 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2471 reference_control_expr_2471 reference_control_1_positions reference_control_1_safety reference_control_member_2471) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2471 reference_control_expr_2471 inputs path old current result Position Safe Nonreg (reference_control_ready_2471 old ) Step).
Qed.
Theorem reference_control_node_2471_congruent inputs path left right next_left next_right :
 VM.find 1884 left = VM.find 1884 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2471 next_left = VM.find 2471 next_right.
Proof.
 intros  E1884 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2471 reference_control_expr_2471 reference_control_1_positions reference_control_1_safety reference_control_member_2471) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2471 reference_control_expr_2471 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2471 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2471 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1884.
 reflexivity.
Qed.
Lemma reference_control_ready_2472 old :
 reference_control_ready old reference_control_expr_2472.
Proof.
 unfold reference_control_expr_2472.
apply rc_binary.
Qed.
Lemma reference_control_member_2472 : List.In (2472,reference_control_expr_2472) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 289%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2472_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2472 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2472 reference_control_expr_2472 reference_control_1_positions reference_control_1_safety reference_control_member_2472) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2472 reference_control_expr_2472 inputs path old current result Position Safe Nonreg (reference_control_ready_2472 old ) Step).
Qed.
Theorem reference_control_node_2472_congruent inputs path left right next_left next_right :
 VM.find 2471 left = VM.find 2471 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2472 next_left = VM.find 2472 next_right.
Proof.
 intros  E2471 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2472 reference_control_expr_2472 reference_control_1_positions reference_control_1_safety reference_control_member_2472) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2472 reference_control_expr_2472 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2472 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2472 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2471.
 reflexivity.
Qed.
Lemma reference_control_ready_2473 old :
 reference_control_ready old reference_control_expr_2473.
Proof.
 unfold reference_control_expr_2473.
apply rc_unary.
Qed.
Lemma reference_control_member_2473 : List.In (2473,reference_control_expr_2473) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 290%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2473_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2473 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2473 reference_control_expr_2473 reference_control_1_positions reference_control_1_safety reference_control_member_2473) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2473 reference_control_expr_2473 inputs path old current result Position Safe Nonreg (reference_control_ready_2473 old ) Step).
Qed.
Theorem reference_control_node_2473_congruent inputs path left right next_left next_right :
 VM.find 1884 left = VM.find 1884 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2473 next_left = VM.find 2473 next_right.
Proof.
 intros  E1884 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2473 reference_control_expr_2473 reference_control_1_positions reference_control_1_safety reference_control_member_2473) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2473 reference_control_expr_2473 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2473 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2473 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1884.
 reflexivity.
Qed.
Lemma reference_control_ready_2474 old :
 reference_control_ready old reference_control_expr_2474.
Proof.
 unfold reference_control_expr_2474.
apply rc_binary.
Qed.
Lemma reference_control_member_2474 : List.In (2474,reference_control_expr_2474) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 291%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2474_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2474 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2474 reference_control_expr_2474 reference_control_1_positions reference_control_1_safety reference_control_member_2474) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2474 reference_control_expr_2474 inputs path old current result Position Safe Nonreg (reference_control_ready_2474 old ) Step).
Qed.
Theorem reference_control_node_2474_congruent inputs path left right next_left next_right :
 VM.find 1884 left = VM.find 1884 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2474 next_left = VM.find 2474 next_right.
Proof.
 intros  E1884 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2474 reference_control_expr_2474 reference_control_1_positions reference_control_1_safety reference_control_member_2474) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2474 reference_control_expr_2474 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2474 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2474 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1884.
 reflexivity.
Qed.
Lemma reference_control_ready_2475 old :
 reference_control_ready old reference_control_expr_2475.
Proof.
 unfold reference_control_expr_2475.
apply rc_binary.
Qed.
Lemma reference_control_member_2475 : List.In (2475,reference_control_expr_2475) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 292%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2475_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2475 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2475 reference_control_expr_2475 reference_control_1_positions reference_control_1_safety reference_control_member_2475) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2475 reference_control_expr_2475 inputs path old current result Position Safe Nonreg (reference_control_ready_2475 old ) Step).
Qed.
Theorem reference_control_node_2475_congruent inputs path left right next_left next_right :
 VM.find 2474 left = VM.find 2474 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2475 next_left = VM.find 2475 next_right.
Proof.
 intros  E2474 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2475 reference_control_expr_2475 reference_control_1_positions reference_control_1_safety reference_control_member_2475) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2475 reference_control_expr_2475 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2475 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2475 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2474.
 reflexivity.
Qed.
Lemma reference_control_ready_2476 old :
 reference_control_ready old reference_control_expr_2476.
Proof.
 unfold reference_control_expr_2476.
apply rc_unary.
Qed.
Lemma reference_control_member_2476 : List.In (2476,reference_control_expr_2476) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 293%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2476_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2476 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2476 reference_control_expr_2476 reference_control_1_positions reference_control_1_safety reference_control_member_2476) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2476 reference_control_expr_2476 inputs path old current result Position Safe Nonreg (reference_control_ready_2476 old ) Step).
Qed.
Theorem reference_control_node_2476_congruent inputs path left right next_left next_right :
 VM.find 1884 left = VM.find 1884 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2476 next_left = VM.find 2476 next_right.
Proof.
 intros  E1884 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2476 reference_control_expr_2476 reference_control_1_positions reference_control_1_safety reference_control_member_2476) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2476 reference_control_expr_2476 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2476 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2476 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1884.
 reflexivity.
Qed.
Lemma reference_control_ready_2477 old :
 (exists value ground, VM.find 2476 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2477.
Proof.
 intros H2476.
 destruct H2476 as [v2476 [G2476 [V2476 T2476]]].
 unfold reference_control_expr_2477.
apply rc_mux.
{ eapply rc_ref; [exact V2476|exists G2476; exact T2476].
}
{ apply rc_const.
}
Qed.
Lemma reference_control_member_2477 : List.In (2477,reference_control_expr_2477) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 294%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2477_ground inputs path old current result :
 (exists value ground, VM.find 2476 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2477 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2476 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2477 reference_control_expr_2477 reference_control_1_positions reference_control_1_safety reference_control_member_2477) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2477 reference_control_expr_2477 inputs path old current result Position Safe Nonreg (reference_control_ready_2477 old H2476) Step).
Qed.
Theorem reference_control_node_2477_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2476 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2475 left = VM.find 2475 right ->
 VM.find 2476 left = VM.find 2476 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2477 next_left = VM.find 2477 next_right.
Proof.
 intros H2476 E2475 E2476 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2477 reference_control_expr_2477 reference_control_1_positions reference_control_1_safety reference_control_member_2477) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2477 reference_control_expr_2477 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2477 left H2476)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2477 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2475.
 rewrite E2476.
 reflexivity.
Qed.
Lemma reference_control_ready_2478 old :
 (exists value ground, VM.find 2473 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2477 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2478.
Proof.
 intros H2473 H2477.
 destruct H2473 as [v2473 [G2473 [V2473 T2473]]].
 destruct H2477 as [v2477 [G2477 [V2477 T2477]]].
 unfold reference_control_expr_2478.
apply rc_mux.
{ eapply rc_ref; [exact V2473|exists G2473; exact T2473].
}
{ eapply rc_ref; [exact V2477|exists G2477; exact T2477].
}
Qed.
Lemma reference_control_member_2478 : List.In (2478,reference_control_expr_2478) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 295%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2478_ground inputs path old current result :
 (exists value ground, VM.find 2473 old = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2477 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2478 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2473 H2477 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2478 reference_control_expr_2478 reference_control_1_positions reference_control_1_safety reference_control_member_2478) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2478 reference_control_expr_2478 inputs path old current result Position Safe Nonreg (reference_control_ready_2478 old H2473 H2477) Step).
Qed.
Theorem reference_control_node_2478_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2473 left = Some value /\ type_of_val value = Gtyp ground) ->
 (exists value ground, VM.find 2477 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2472 left = VM.find 2472 right ->
 VM.find 2473 left = VM.find 2473 right ->
 VM.find 2477 left = VM.find 2477 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2478 next_left = VM.find 2478 next_right.
Proof.
 intros H2473 H2477 E2472 E2473 E2477 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2478 reference_control_expr_2478 reference_control_1_positions reference_control_1_safety reference_control_member_2478) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2478 reference_control_expr_2478 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2478 left H2473 H2477)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2478 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2472.
 rewrite E2473.
 rewrite E2477.
 reflexivity.
Qed.
Lemma reference_control_ready_2479 old :
 (exists value ground, VM.find 2478 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2479.
Proof.
 intros H2478.
 destruct H2478 as [v2478 [G2478 [V2478 T2478]]].
 unfold reference_control_expr_2479.
apply rc_mux.
{ eapply rc_ref; [exact V2478|exists G2478; exact T2478].
}
{ apply rc_const.
}
Qed.
Lemma reference_control_member_2479 : List.In (2479,reference_control_expr_2479) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 296%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2479_ground inputs path old current result :
 (exists value ground, VM.find 2478 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2479 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2478 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2479 reference_control_expr_2479 reference_control_1_positions reference_control_1_safety reference_control_member_2479) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2479 reference_control_expr_2479 inputs path old current result Position Safe Nonreg (reference_control_ready_2479 old H2478) Step).
Qed.
Theorem reference_control_node_2479_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2478 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 1707 left = VM.find 1707 right ->
 VM.find 2478 left = VM.find 2478 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2479 next_left = VM.find 2479 next_right.
Proof.
 intros H2478 E1707 E2478 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2479 reference_control_expr_2479 reference_control_1_positions reference_control_1_safety reference_control_member_2479) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2479 reference_control_expr_2479 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2479 left H2478)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2479 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E1707.
 rewrite E2478.
 reflexivity.
Qed.
Lemma reference_control_ready_2480 old :
 (exists value ground, VM.find 2479 old = Some value /\ type_of_val value = Gtyp ground) ->
 reference_control_ready old reference_control_expr_2480.
Proof.
 intros H2479.
 destruct H2479 as [v2479 [G2479 [V2479 T2479]]].
 unfold reference_control_expr_2480.
eapply rc_ref; [exact V2479|exists G2479; exact T2479].
Qed.
Lemma reference_control_member_2480 : List.In (2480,reference_control_expr_2480) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 297%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2480_ground inputs path old current result :
 (exists value ground, VM.find 2479 old = Some value /\ type_of_val value = Gtyp ground) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2480 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros H2479 Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2480 reference_control_expr_2480 reference_control_1_positions reference_control_1_safety reference_control_member_2480) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2480 reference_control_expr_2480 inputs path old current result Position Safe Nonreg (reference_control_ready_2480 old H2479) Step).
Qed.
Theorem reference_control_node_2480_congruent inputs path left right next_left next_right :
 (exists value ground, VM.find 2479 left = Some value /\ type_of_val value = Gtyp ground) ->
 VM.find 2479 left = VM.find 2479 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2480 next_left = VM.find 2480 next_right.
Proof.
 intros H2479 E2479 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2480 reference_control_expr_2480 reference_control_1_positions reference_control_1_safety reference_control_member_2480) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2480 reference_control_expr_2480 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2480 left H2479)); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2480 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2479.
 reflexivity.
Qed.
Lemma reference_control_ready_2481 old :
 reference_control_ready old reference_control_expr_2481.
Proof.
 unfold reference_control_expr_2481.
apply rc_binary.
Qed.
Lemma reference_control_member_2481 : List.In (2481,reference_control_expr_2481) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 298%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2481_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2481 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2481 reference_control_expr_2481 reference_control_1_positions reference_control_1_safety reference_control_member_2481) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2481 reference_control_expr_2481 inputs path old current result Position Safe Nonreg (reference_control_ready_2481 old ) Step).
Qed.
Theorem reference_control_node_2481_congruent inputs path left right next_left next_right :
 VM.find 2480 left = VM.find 2480 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2481 next_left = VM.find 2481 next_right.
Proof.
 intros  E2480 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2481 reference_control_expr_2481 reference_control_1_positions reference_control_1_safety reference_control_member_2481) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2481 reference_control_expr_2481 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2481 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2481 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2480.
 reflexivity.
Qed.
Lemma reference_control_ready_2482 old :
 reference_control_ready old reference_control_expr_2482.
Proof.
 unfold reference_control_expr_2482.
apply rc_unary.
Qed.
Lemma reference_control_member_2482 : List.In (2482,reference_control_expr_2482) reference_control_1_nodes.
Proof. apply (List.nth_error_In reference_control_1_nodes 299%nat). vm_compute. reflexivity. Qed.
Theorem reference_control_node_2482_ground inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 2482 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intros  Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2482 reference_control_expr_2482 reference_control_1_positions reference_control_1_safety reference_control_member_2482) as [count [tail [Position [Safe Nonreg]]]].
 exact (reference_control_node_ground count tail 2482 reference_control_expr_2482 inputs path old current result Position Safe Nonreg (reference_control_ready_2482 old ) Step).
Qed.
Theorem reference_control_node_2482_congruent inputs path left right next_left next_right :
 VM.find 2481 left = VM.find 2481 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 2482 next_left = VM.find 2482 next_right.
Proof.
 intros  E2481 L R.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements
 reference_control_1_nodes 2482 reference_control_expr_2482 reference_control_1_positions reference_control_1_safety reference_control_member_2482) as [count [tail [Position [Safe Nonreg]]]].
 apply (reference_control_node_congruent count tail 2482 reference_control_expr_2482 inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_2482 left )); [|exact L|exact R].
 intro site. cbn [reference_control_expr_2482 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite E2481.
 reflexivity.
Qed.
Print Assumptions reference_control_node_2482_congruent.
