Require Import CoreSocModel ComparisonNodes FormalTypedNodeEquation SelectedNodeSafety FormalDeclaredConnection DataAddressPositionCertificate DataAddressSafetyCertificate DataAddressExpressionCertificates JointUpdateNodePositions JointUpdateExpressionCertificates DataAddressConnectionCertificates JointUpdateConnectionCertificates.
From Coq Require Import ZArith List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Definition nop_kill_value_7748 := Gval (Fuint 32) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false].
Definition nop_kill_value_83 := Gval (Fuint 32) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false].
Theorem nop_kill_step_83 invalid old current result :
 VM.find 7748 old = Some nop_kill_value_7748 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 83 result = Some nop_kill_value_83.
Proof.
 intros H7748 Step.
 apply (declared_connection_value 60 flat_statements data_address_connection_83_decl data_address_connection_83_mid data_address_connection_83_tail
 83 7748 32 nop_kill_value_7748 nop_kill_value_83 invalid flat_memories old current result
 data_address_connection_83_position data_address_connection_83_split data_address_connection_83_straight data_address_connection_83_mid_safe data_address_connection_83_tail_safe data_address_connection_83_nonregister (Logic.eq_refl _) H7748);
 [vm_compute;reflexivity|exact Step].
Qed.
Definition nop_kill_value_8249 := Gval (Fuint 32) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false].
Theorem nop_kill_step_8249 invalid old current result :
 VM.find 83 old = Some nop_kill_value_83 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8249 result = Some nop_kill_value_8249.
Proof.
 intros H83 Step.
 apply (declared_connection_value 9009 flat_statements data_address_connection_8249_decl data_address_connection_8249_mid data_address_connection_8249_tail
 8249 83 32 nop_kill_value_83 nop_kill_value_8249 invalid flat_memories old current result
 data_address_connection_8249_position data_address_connection_8249_split data_address_connection_8249_straight data_address_connection_8249_mid_safe data_address_connection_8249_tail_safe data_address_connection_8249_nonregister (Logic.eq_refl _) H83);
 [vm_compute;reflexivity|exact Step].
Qed.
Definition nop_kill_value_8263 := Gval (Fuint 32) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false].
Theorem nop_kill_step_8263 invalid old current result :
 VM.find 8249 old = Some nop_kill_value_8249 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8263 result = Some nop_kill_value_8263.
Proof.
 intros H8249 Step.
 assert (Member : List.In (8263,address_expr_8263) data_address_expected_nodes).
 { apply (List.nth_error_In data_address_expected_nodes 149%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8263 address_expr_8263 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [address_expr_8263 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8249.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8265 := Gval (Fuint 32) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false].
Theorem nop_kill_step_8265 invalid old current result :
 VM.find 8249 old = Some nop_kill_value_8249 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8265 result = Some nop_kill_value_8265.
Proof.
 intros H8249 Step.
 assert (Member : List.In (8265,address_expr_8265) data_address_expected_nodes).
 { apply (List.nth_error_In data_address_expected_nodes 151%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8265 address_expr_8265 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [address_expr_8265 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8249.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8267 := Gval (Fuint 32) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false].
Theorem nop_kill_step_8267 invalid old current result :
 VM.find 8249 old = Some nop_kill_value_8249 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8267 result = Some nop_kill_value_8267.
Proof.
 intros H8249 Step.
 assert (Member : List.In (8267,address_expr_8267) data_address_expected_nodes).
 { apply (List.nth_error_In data_address_expected_nodes 153%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8267 address_expr_8267 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [address_expr_8267 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8249.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8269 := Gval (Fuint 32) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false].
Theorem nop_kill_step_8269 invalid old current result :
 VM.find 8249 old = Some nop_kill_value_8249 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8269 result = Some nop_kill_value_8269.
Proof.
 intros H8249 Step.
 assert (Member : List.In (8269,address_expr_8269) data_address_expected_nodes).
 { apply (List.nth_error_In data_address_expected_nodes 155%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8269 address_expr_8269 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [address_expr_8269 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8249.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8271 := Gval (Fuint 32) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false].
Theorem nop_kill_step_8271 invalid old current result :
 VM.find 8249 old = Some nop_kill_value_8249 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8271 result = Some nop_kill_value_8271.
Proof.
 intros H8249 Step.
 assert (Member : List.In (8271,address_expr_8271) data_address_expected_nodes).
 { apply (List.nth_error_In data_address_expected_nodes 157%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8271 address_expr_8271 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [address_expr_8271 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8249.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8273 := Gval (Fuint 32) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false].
Theorem nop_kill_step_8273 invalid old current result :
 VM.find 8249 old = Some nop_kill_value_8249 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8273 result = Some nop_kill_value_8273.
Proof.
 intros H8249 Step.
 assert (Member : List.In (8273,address_expr_8273) data_address_expected_nodes).
 { apply (List.nth_error_In data_address_expected_nodes 159%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8273 address_expr_8273 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [address_expr_8273 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8249.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8275 := Gval (Fuint 32) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false].
Theorem nop_kill_step_8275 invalid old current result :
 VM.find 8249 old = Some nop_kill_value_8249 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8275 result = Some nop_kill_value_8275.
Proof.
 intros H8249 Step.
 assert (Member : List.In (8275,address_expr_8275) data_address_expected_nodes).
 { apply (List.nth_error_In data_address_expected_nodes 161%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8275 address_expr_8275 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [address_expr_8275 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8249.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8277 := Gval (Fuint 32) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false].
Theorem nop_kill_step_8277 invalid old current result :
 VM.find 8249 old = Some nop_kill_value_8249 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8277 result = Some nop_kill_value_8277.
Proof.
 intros H8249 Step.
 assert (Member : List.In (8277,address_expr_8277) data_address_expected_nodes).
 { apply (List.nth_error_In data_address_expected_nodes 163%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8277 address_expr_8277 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [address_expr_8277 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8249.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8279 := Gval (Fuint 32) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false].
Theorem nop_kill_step_8279 invalid old current result :
 VM.find 8249 old = Some nop_kill_value_8249 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8279 result = Some nop_kill_value_8279.
Proof.
 intros H8249 Step.
 assert (Member : List.In (8279,address_expr_8279) data_address_expected_nodes).
 { apply (List.nth_error_In data_address_expected_nodes 165%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8279 address_expr_8279 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [address_expr_8279 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8249.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8281 := Gval (Fuint 32) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false].
Theorem nop_kill_step_8281 invalid old current result :
 VM.find 8249 old = Some nop_kill_value_8249 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8281 result = Some nop_kill_value_8281.
Proof.
 intros H8249 Step.
 assert (Member : List.In (8281,address_expr_8281) data_address_expected_nodes).
 { apply (List.nth_error_In data_address_expected_nodes 167%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8281 address_expr_8281 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [address_expr_8281 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8249.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8283 := Gval (Fuint 32) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false].
Theorem nop_kill_step_8283 invalid old current result :
 VM.find 8249 old = Some nop_kill_value_8249 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8283 result = Some nop_kill_value_8283.
Proof.
 intros H8249 Step.
 assert (Member : List.In (8283,address_expr_8283) data_address_expected_nodes).
 { apply (List.nth_error_In data_address_expected_nodes 169%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8283 address_expr_8283 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [address_expr_8283 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8249.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8285 := Gval (Fuint 32) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false].
Theorem nop_kill_step_8285 invalid old current result :
 VM.find 8249 old = Some nop_kill_value_8249 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8285 result = Some nop_kill_value_8285.
Proof.
 intros H8249 Step.
 assert (Member : List.In (8285,address_expr_8285) data_address_expected_nodes).
 { apply (List.nth_error_In data_address_expected_nodes 171%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8285 address_expr_8285 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [address_expr_8285 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8249.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8287 := Gval (Fuint 32) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false].
Theorem nop_kill_step_8287 invalid old current result :
 VM.find 8249 old = Some nop_kill_value_8249 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8287 result = Some nop_kill_value_8287.
Proof.
 intros H8249 Step.
 assert (Member : List.In (8287,address_expr_8287) data_address_expected_nodes).
 { apply (List.nth_error_In data_address_expected_nodes 173%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8287 address_expr_8287 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [address_expr_8287 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8249.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8289 := Gval (Fuint 32) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false].
Theorem nop_kill_step_8289 invalid old current result :
 VM.find 8249 old = Some nop_kill_value_8249 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8289 result = Some nop_kill_value_8289.
Proof.
 intros H8249 Step.
 assert (Member : List.In (8289,address_expr_8289) data_address_expected_nodes).
 { apply (List.nth_error_In data_address_expected_nodes 175%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8289 address_expr_8289 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [address_expr_8289 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8249.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8291 := Gval (Fuint 32) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false].
Theorem nop_kill_step_8291 invalid old current result :
 VM.find 8249 old = Some nop_kill_value_8249 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8291 result = Some nop_kill_value_8291.
Proof.
 intros H8249 Step.
 assert (Member : List.In (8291,address_expr_8291) data_address_expected_nodes).
 { apply (List.nth_error_In data_address_expected_nodes 177%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8291 address_expr_8291 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [address_expr_8291 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8249.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8293 := Gval (Fuint 32) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false].
Theorem nop_kill_step_8293 invalid old current result :
 VM.find 8249 old = Some nop_kill_value_8249 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8293 result = Some nop_kill_value_8293.
Proof.
 intros H8249 Step.
 assert (Member : List.In (8293,address_expr_8293) data_address_expected_nodes).
 { apply (List.nth_error_In data_address_expected_nodes 179%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8293 address_expr_8293 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [address_expr_8293 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8249.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8295 := Gval (Fuint 32) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false].
Theorem nop_kill_step_8295 invalid old current result :
 VM.find 8249 old = Some nop_kill_value_8249 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8295 result = Some nop_kill_value_8295.
Proof.
 intros H8249 Step.
 assert (Member : List.In (8295,address_expr_8295) data_address_expected_nodes).
 { apply (List.nth_error_In data_address_expected_nodes 181%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8295 address_expr_8295 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [address_expr_8295 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8249.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8297 := Gval (Fuint 32) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false].
Theorem nop_kill_step_8297 invalid old current result :
 VM.find 8249 old = Some nop_kill_value_8249 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8297 result = Some nop_kill_value_8297.
Proof.
 intros H8249 Step.
 assert (Member : List.In (8297,address_expr_8297) data_address_expected_nodes).
 { apply (List.nth_error_In data_address_expected_nodes 183%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8297 address_expr_8297 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [address_expr_8297 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8249.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8299 := Gval (Fuint 32) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false].
Theorem nop_kill_step_8299 invalid old current result :
 VM.find 8249 old = Some nop_kill_value_8249 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8299 result = Some nop_kill_value_8299.
Proof.
 intros H8249 Step.
 assert (Member : List.In (8299,address_expr_8299) data_address_expected_nodes).
 { apply (List.nth_error_In data_address_expected_nodes 185%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8299 address_expr_8299 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [address_expr_8299 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8249.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8301 := Gval (Fuint 32) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false].
Theorem nop_kill_step_8301 invalid old current result :
 VM.find 8249 old = Some nop_kill_value_8249 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8301 result = Some nop_kill_value_8301.
Proof.
 intros H8249 Step.
 assert (Member : List.In (8301,address_expr_8301) data_address_expected_nodes).
 { apply (List.nth_error_In data_address_expected_nodes 187%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8301 address_expr_8301 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [address_expr_8301 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8249.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8303 := Gval (Fuint 32) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false].
Theorem nop_kill_step_8303 invalid old current result :
 VM.find 8249 old = Some nop_kill_value_8249 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8303 result = Some nop_kill_value_8303.
Proof.
 intros H8249 Step.
 assert (Member : List.In (8303,address_expr_8303) data_address_expected_nodes).
 { apply (List.nth_error_In data_address_expected_nodes 189%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8303 address_expr_8303 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [address_expr_8303 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8249.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8305 := Gval (Fuint 32) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false].
Theorem nop_kill_step_8305 invalid old current result :
 VM.find 8249 old = Some nop_kill_value_8249 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8305 result = Some nop_kill_value_8305.
Proof.
 intros H8249 Step.
 assert (Member : List.In (8305,address_expr_8305) data_address_expected_nodes).
 { apply (List.nth_error_In data_address_expected_nodes 191%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8305 address_expr_8305 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [address_expr_8305 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8249.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8307 := Gval (Fuint 32) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false].
Theorem nop_kill_step_8307 invalid old current result :
 VM.find 8249 old = Some nop_kill_value_8249 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8307 result = Some nop_kill_value_8307.
Proof.
 intros H8249 Step.
 assert (Member : List.In (8307,address_expr_8307) data_address_expected_nodes).
 { apply (List.nth_error_In data_address_expected_nodes 193%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8307 address_expr_8307 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [address_expr_8307 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8249.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8309 := Gval (Fuint 32) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false].
Theorem nop_kill_step_8309 invalid old current result :
 VM.find 8249 old = Some nop_kill_value_8249 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8309 result = Some nop_kill_value_8309.
Proof.
 intros H8249 Step.
 assert (Member : List.In (8309,address_expr_8309) data_address_expected_nodes).
 { apply (List.nth_error_In data_address_expected_nodes 195%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8309 address_expr_8309 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [address_expr_8309 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8249.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8311 := Gval (Fuint 32) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false].
Theorem nop_kill_step_8311 invalid old current result :
 VM.find 8249 old = Some nop_kill_value_8249 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8311 result = Some nop_kill_value_8311.
Proof.
 intros H8249 Step.
 assert (Member : List.In (8311,address_expr_8311) data_address_expected_nodes).
 { apply (List.nth_error_In data_address_expected_nodes 197%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8311 address_expr_8311 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [address_expr_8311 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8249.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8313 := Gval (Fuint 32) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false].
Theorem nop_kill_step_8313 invalid old current result :
 VM.find 8249 old = Some nop_kill_value_8249 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8313 result = Some nop_kill_value_8313.
Proof.
 intros H8249 Step.
 assert (Member : List.In (8313,address_expr_8313) data_address_expected_nodes).
 { apply (List.nth_error_In data_address_expected_nodes 199%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8313 address_expr_8313 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [address_expr_8313 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8249.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8315 := Gval (Fuint 32) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false].
Theorem nop_kill_step_8315 invalid old current result :
 VM.find 8249 old = Some nop_kill_value_8249 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8315 result = Some nop_kill_value_8315.
Proof.
 intros H8249 Step.
 assert (Member : List.In (8315,address_expr_8315) data_address_expected_nodes).
 { apply (List.nth_error_In data_address_expected_nodes 201%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8315 address_expr_8315 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [address_expr_8315 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8249.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8317 := Gval (Fuint 32) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false].
Theorem nop_kill_step_8317 invalid old current result :
 VM.find 8249 old = Some nop_kill_value_8249 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8317 result = Some nop_kill_value_8317.
Proof.
 intros H8249 Step.
 assert (Member : List.In (8317,address_expr_8317) data_address_expected_nodes).
 { apply (List.nth_error_In data_address_expected_nodes 203%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8317 address_expr_8317 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [address_expr_8317 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8249.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8319 := Gval (Fuint 32) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false].
Theorem nop_kill_step_8319 invalid old current result :
 VM.find 8249 old = Some nop_kill_value_8249 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8319 result = Some nop_kill_value_8319.
Proof.
 intros H8249 Step.
 assert (Member : List.In (8319,address_expr_8319) data_address_expected_nodes).
 { apply (List.nth_error_In data_address_expected_nodes 205%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8319 address_expr_8319 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [address_expr_8319 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8249.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8321 := Gval (Fuint 32) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false].
Theorem nop_kill_step_8321 invalid old current result :
 VM.find 8249 old = Some nop_kill_value_8249 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8321 result = Some nop_kill_value_8321.
Proof.
 intros H8249 Step.
 assert (Member : List.In (8321,address_expr_8321) data_address_expected_nodes).
 { apply (List.nth_error_In data_address_expected_nodes 207%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8321 address_expr_8321 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [address_expr_8321 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8249.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8323 := Gval (Fuint 32) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false].
Theorem nop_kill_step_8323 invalid old current result :
 VM.find 8249 old = Some nop_kill_value_8249 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8323 result = Some nop_kill_value_8323.
Proof.
 intros H8249 Step.
 assert (Member : List.In (8323,address_expr_8323) data_address_expected_nodes).
 { apply (List.nth_error_In data_address_expected_nodes 209%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8323 address_expr_8323 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [address_expr_8323 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8249.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8325 := Gval (Fuint 32) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false].
Theorem nop_kill_step_8325 invalid old current result :
 VM.find 8249 old = Some nop_kill_value_8249 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8325 result = Some nop_kill_value_8325.
Proof.
 intros H8249 Step.
 assert (Member : List.In (8325,address_expr_8325) data_address_expected_nodes).
 { apply (List.nth_error_In data_address_expected_nodes 211%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8325 address_expr_8325 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [address_expr_8325 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8249.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8327 := Gval (Fuint 32) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false].
Theorem nop_kill_step_8327 invalid old current result :
 VM.find 8249 old = Some nop_kill_value_8249 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8327 result = Some nop_kill_value_8327.
Proof.
 intros H8249 Step.
 assert (Member : List.In (8327,address_expr_8327) data_address_expected_nodes).
 { apply (List.nth_error_In data_address_expected_nodes 213%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8327 address_expr_8327 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [address_expr_8327 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8249.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8329 := Gval (Fuint 32) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false].
Theorem nop_kill_step_8329 invalid old current result :
 VM.find 8249 old = Some nop_kill_value_8249 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8329 result = Some nop_kill_value_8329.
Proof.
 intros H8249 Step.
 assert (Member : List.In (8329,address_expr_8329) data_address_expected_nodes).
 { apply (List.nth_error_In data_address_expected_nodes 215%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8329 address_expr_8329 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [address_expr_8329 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8249.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8331 := Gval (Fuint 32) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false].
Theorem nop_kill_step_8331 invalid old current result :
 VM.find 8249 old = Some nop_kill_value_8249 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8331 result = Some nop_kill_value_8331.
Proof.
 intros H8249 Step.
 assert (Member : List.In (8331,address_expr_8331) data_address_expected_nodes).
 { apply (List.nth_error_In data_address_expected_nodes 217%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8331 address_expr_8331 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [address_expr_8331 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8249.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8333 := Gval (Fuint 32) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false].
Theorem nop_kill_step_8333 invalid old current result :
 VM.find 8249 old = Some nop_kill_value_8249 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8333 result = Some nop_kill_value_8333.
Proof.
 intros H8249 Step.
 assert (Member : List.In (8333,address_expr_8333) data_address_expected_nodes).
 { apply (List.nth_error_In data_address_expected_nodes 219%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8333 address_expr_8333 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [address_expr_8333 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8249.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8335 := Gval (Fuint 32) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false].
Theorem nop_kill_step_8335 invalid old current result :
 VM.find 8249 old = Some nop_kill_value_8249 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8335 result = Some nop_kill_value_8335.
Proof.
 intros H8249 Step.
 assert (Member : List.In (8335,address_expr_8335) data_address_expected_nodes).
 { apply (List.nth_error_In data_address_expected_nodes 221%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8335 address_expr_8335 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [address_expr_8335 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8249.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8337 := Gval (Fuint 32) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false].
Theorem nop_kill_step_8337 invalid old current result :
 VM.find 8249 old = Some nop_kill_value_8249 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8337 result = Some nop_kill_value_8337.
Proof.
 intros H8249 Step.
 assert (Member : List.In (8337,address_expr_8337) data_address_expected_nodes).
 { apply (List.nth_error_In data_address_expected_nodes 223%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8337 address_expr_8337 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [address_expr_8337 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8249.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8339 := Gval (Fuint 32) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false].
Theorem nop_kill_step_8339 invalid old current result :
 VM.find 8249 old = Some nop_kill_value_8249 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8339 result = Some nop_kill_value_8339.
Proof.
 intros H8249 Step.
 assert (Member : List.In (8339,address_expr_8339) data_address_expected_nodes).
 { apply (List.nth_error_In data_address_expected_nodes 225%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8339 address_expr_8339 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [address_expr_8339 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8249.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8341 := Gval (Fuint 32) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false].
Theorem nop_kill_step_8341 invalid old current result :
 VM.find 8249 old = Some nop_kill_value_8249 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8341 result = Some nop_kill_value_8341.
Proof.
 intros H8249 Step.
 assert (Member : List.In (8341,address_expr_8341) data_address_expected_nodes).
 { apply (List.nth_error_In data_address_expected_nodes 227%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8341 address_expr_8341 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [address_expr_8341 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8249.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8343 := Gval (Fuint 32) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false].
Theorem nop_kill_step_8343 invalid old current result :
 VM.find 8249 old = Some nop_kill_value_8249 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8343 result = Some nop_kill_value_8343.
Proof.
 intros H8249 Step.
 assert (Member : List.In (8343,address_expr_8343) data_address_expected_nodes).
 { apply (List.nth_error_In data_address_expected_nodes 229%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8343 address_expr_8343 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [address_expr_8343 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8249.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8345 := Gval (Fuint 32) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false].
Theorem nop_kill_step_8345 invalid old current result :
 VM.find 8249 old = Some nop_kill_value_8249 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8345 result = Some nop_kill_value_8345.
Proof.
 intros H8249 Step.
 assert (Member : List.In (8345,address_expr_8345) data_address_expected_nodes).
 { apply (List.nth_error_In data_address_expected_nodes 231%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8345 address_expr_8345 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [address_expr_8345 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8249.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8347 := Gval (Fuint 32) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false].
Theorem nop_kill_step_8347 invalid old current result :
 VM.find 8249 old = Some nop_kill_value_8249 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8347 result = Some nop_kill_value_8347.
Proof.
 intros H8249 Step.
 assert (Member : List.In (8347,address_expr_8347) data_address_expected_nodes).
 { apply (List.nth_error_In data_address_expected_nodes 233%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8347 address_expr_8347 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [address_expr_8347 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8249.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8349 := Gval (Fuint 32) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false].
Theorem nop_kill_step_8349 invalid old current result :
 VM.find 8249 old = Some nop_kill_value_8249 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8349 result = Some nop_kill_value_8349.
Proof.
 intros H8249 Step.
 assert (Member : List.In (8349,address_expr_8349) data_address_expected_nodes).
 { apply (List.nth_error_In data_address_expected_nodes 235%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8349 address_expr_8349 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [address_expr_8349 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8249.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8351 := Gval (Fuint 32) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false].
Theorem nop_kill_step_8351 invalid old current result :
 VM.find 8249 old = Some nop_kill_value_8249 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8351 result = Some nop_kill_value_8351.
Proof.
 intros H8249 Step.
 assert (Member : List.In (8351,address_expr_8351) data_address_expected_nodes).
 { apply (List.nth_error_In data_address_expected_nodes 237%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8351 address_expr_8351 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [address_expr_8351 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8249.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8353 := Gval (Fuint 32) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false].
Theorem nop_kill_step_8353 invalid old current result :
 VM.find 8249 old = Some nop_kill_value_8249 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8353 result = Some nop_kill_value_8353.
Proof.
 intros H8249 Step.
 assert (Member : List.In (8353,address_expr_8353) data_address_expected_nodes).
 { apply (List.nth_error_In data_address_expected_nodes 239%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8353 address_expr_8353 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [address_expr_8353 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8249.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8355 := Gval (Fuint 32) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false].
Theorem nop_kill_step_8355 invalid old current result :
 VM.find 8249 old = Some nop_kill_value_8249 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8355 result = Some nop_kill_value_8355.
Proof.
 intros H8249 Step.
 assert (Member : List.In (8355,address_expr_8355) data_address_expected_nodes).
 { apply (List.nth_error_In data_address_expected_nodes 241%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8355 address_expr_8355 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [address_expr_8355 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8249.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8357 := Gval (Fuint 32) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false].
Theorem nop_kill_step_8357 invalid old current result :
 VM.find 8249 old = Some nop_kill_value_8249 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8357 result = Some nop_kill_value_8357.
Proof.
 intros H8249 Step.
 assert (Member : List.In (8357,address_expr_8357) data_address_expected_nodes).
 { apply (List.nth_error_In data_address_expected_nodes 243%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8357 address_expr_8357 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [address_expr_8357 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8249.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8359 := Gval (Fuint 32) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false].
Theorem nop_kill_step_8359 invalid old current result :
 VM.find 8249 old = Some nop_kill_value_8249 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8359 result = Some nop_kill_value_8359.
Proof.
 intros H8249 Step.
 assert (Member : List.In (8359,address_expr_8359) data_address_expected_nodes).
 { apply (List.nth_error_In data_address_expected_nodes 245%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8359 address_expr_8359 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [address_expr_8359 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8249.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8264 := Gval (Fuint 1) [::false].
Theorem nop_kill_step_8264 invalid old current result :
 VM.find 8263 old = Some nop_kill_value_8263 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8264 result = Some nop_kill_value_8264.
Proof.
 intros H8263 Step.
 assert (Member : List.In (8264,address_expr_8264) data_address_expected_nodes).
 { apply (List.nth_error_In data_address_expected_nodes 150%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8264 address_expr_8264 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [address_expr_8264 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8263.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8266 := Gval (Fuint 1) [::false].
Theorem nop_kill_step_8266 invalid old current result :
 VM.find 8265 old = Some nop_kill_value_8265 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8266 result = Some nop_kill_value_8266.
Proof.
 intros H8265 Step.
 assert (Member : List.In (8266,address_expr_8266) data_address_expected_nodes).
 { apply (List.nth_error_In data_address_expected_nodes 152%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8266 address_expr_8266 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [address_expr_8266 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8265.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8268 := Gval (Fuint 1) [::false].
Theorem nop_kill_step_8268 invalid old current result :
 VM.find 8267 old = Some nop_kill_value_8267 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8268 result = Some nop_kill_value_8268.
Proof.
 intros H8267 Step.
 assert (Member : List.In (8268,address_expr_8268) data_address_expected_nodes).
 { apply (List.nth_error_In data_address_expected_nodes 154%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8268 address_expr_8268 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [address_expr_8268 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8267.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8270 := Gval (Fuint 1) [::false].
Theorem nop_kill_step_8270 invalid old current result :
 VM.find 8269 old = Some nop_kill_value_8269 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8270 result = Some nop_kill_value_8270.
Proof.
 intros H8269 Step.
 assert (Member : List.In (8270,address_expr_8270) data_address_expected_nodes).
 { apply (List.nth_error_In data_address_expected_nodes 156%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8270 address_expr_8270 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [address_expr_8270 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8269.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8272 := Gval (Fuint 1) [::false].
Theorem nop_kill_step_8272 invalid old current result :
 VM.find 8271 old = Some nop_kill_value_8271 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8272 result = Some nop_kill_value_8272.
Proof.
 intros H8271 Step.
 assert (Member : List.In (8272,address_expr_8272) data_address_expected_nodes).
 { apply (List.nth_error_In data_address_expected_nodes 158%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8272 address_expr_8272 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [address_expr_8272 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8271.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8274 := Gval (Fuint 1) [::false].
Theorem nop_kill_step_8274 invalid old current result :
 VM.find 8273 old = Some nop_kill_value_8273 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8274 result = Some nop_kill_value_8274.
Proof.
 intros H8273 Step.
 assert (Member : List.In (8274,address_expr_8274) data_address_expected_nodes).
 { apply (List.nth_error_In data_address_expected_nodes 160%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8274 address_expr_8274 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [address_expr_8274 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8273.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8276 := Gval (Fuint 1) [::false].
Theorem nop_kill_step_8276 invalid old current result :
 VM.find 8275 old = Some nop_kill_value_8275 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8276 result = Some nop_kill_value_8276.
Proof.
 intros H8275 Step.
 assert (Member : List.In (8276,address_expr_8276) data_address_expected_nodes).
 { apply (List.nth_error_In data_address_expected_nodes 162%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8276 address_expr_8276 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [address_expr_8276 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8275.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8278 := Gval (Fuint 1) [::false].
Theorem nop_kill_step_8278 invalid old current result :
 VM.find 8277 old = Some nop_kill_value_8277 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8278 result = Some nop_kill_value_8278.
Proof.
 intros H8277 Step.
 assert (Member : List.In (8278,address_expr_8278) data_address_expected_nodes).
 { apply (List.nth_error_In data_address_expected_nodes 164%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8278 address_expr_8278 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [address_expr_8278 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8277.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8280 := Gval (Fuint 1) [::false].
Theorem nop_kill_step_8280 invalid old current result :
 VM.find 8279 old = Some nop_kill_value_8279 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8280 result = Some nop_kill_value_8280.
Proof.
 intros H8279 Step.
 assert (Member : List.In (8280,address_expr_8280) data_address_expected_nodes).
 { apply (List.nth_error_In data_address_expected_nodes 166%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8280 address_expr_8280 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [address_expr_8280 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8279.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8282 := Gval (Fuint 1) [::false].
Theorem nop_kill_step_8282 invalid old current result :
 VM.find 8281 old = Some nop_kill_value_8281 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8282 result = Some nop_kill_value_8282.
Proof.
 intros H8281 Step.
 assert (Member : List.In (8282,address_expr_8282) data_address_expected_nodes).
 { apply (List.nth_error_In data_address_expected_nodes 168%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8282 address_expr_8282 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [address_expr_8282 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8281.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8284 := Gval (Fuint 1) [::false].
Theorem nop_kill_step_8284 invalid old current result :
 VM.find 8283 old = Some nop_kill_value_8283 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8284 result = Some nop_kill_value_8284.
Proof.
 intros H8283 Step.
 assert (Member : List.In (8284,address_expr_8284) data_address_expected_nodes).
 { apply (List.nth_error_In data_address_expected_nodes 170%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8284 address_expr_8284 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [address_expr_8284 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8283.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8286 := Gval (Fuint 1) [::false].
Theorem nop_kill_step_8286 invalid old current result :
 VM.find 8285 old = Some nop_kill_value_8285 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8286 result = Some nop_kill_value_8286.
Proof.
 intros H8285 Step.
 assert (Member : List.In (8286,address_expr_8286) data_address_expected_nodes).
 { apply (List.nth_error_In data_address_expected_nodes 172%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8286 address_expr_8286 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [address_expr_8286 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8285.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8288 := Gval (Fuint 1) [::false].
Theorem nop_kill_step_8288 invalid old current result :
 VM.find 8287 old = Some nop_kill_value_8287 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8288 result = Some nop_kill_value_8288.
Proof.
 intros H8287 Step.
 assert (Member : List.In (8288,address_expr_8288) data_address_expected_nodes).
 { apply (List.nth_error_In data_address_expected_nodes 174%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8288 address_expr_8288 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [address_expr_8288 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8287.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8290 := Gval (Fuint 1) [::false].
Theorem nop_kill_step_8290 invalid old current result :
 VM.find 8289 old = Some nop_kill_value_8289 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8290 result = Some nop_kill_value_8290.
Proof.
 intros H8289 Step.
 assert (Member : List.In (8290,address_expr_8290) data_address_expected_nodes).
 { apply (List.nth_error_In data_address_expected_nodes 176%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8290 address_expr_8290 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [address_expr_8290 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8289.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8292 := Gval (Fuint 1) [::false].
Theorem nop_kill_step_8292 invalid old current result :
 VM.find 8291 old = Some nop_kill_value_8291 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8292 result = Some nop_kill_value_8292.
Proof.
 intros H8291 Step.
 assert (Member : List.In (8292,address_expr_8292) data_address_expected_nodes).
 { apply (List.nth_error_In data_address_expected_nodes 178%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8292 address_expr_8292 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [address_expr_8292 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8291.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8294 := Gval (Fuint 1) [::false].
Theorem nop_kill_step_8294 invalid old current result :
 VM.find 8293 old = Some nop_kill_value_8293 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8294 result = Some nop_kill_value_8294.
Proof.
 intros H8293 Step.
 assert (Member : List.In (8294,address_expr_8294) data_address_expected_nodes).
 { apply (List.nth_error_In data_address_expected_nodes 180%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8294 address_expr_8294 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [address_expr_8294 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8293.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8296 := Gval (Fuint 1) [::false].
Theorem nop_kill_step_8296 invalid old current result :
 VM.find 8295 old = Some nop_kill_value_8295 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8296 result = Some nop_kill_value_8296.
Proof.
 intros H8295 Step.
 assert (Member : List.In (8296,address_expr_8296) data_address_expected_nodes).
 { apply (List.nth_error_In data_address_expected_nodes 182%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8296 address_expr_8296 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [address_expr_8296 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8295.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8298 := Gval (Fuint 1) [::false].
Theorem nop_kill_step_8298 invalid old current result :
 VM.find 8297 old = Some nop_kill_value_8297 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8298 result = Some nop_kill_value_8298.
Proof.
 intros H8297 Step.
 assert (Member : List.In (8298,address_expr_8298) data_address_expected_nodes).
 { apply (List.nth_error_In data_address_expected_nodes 184%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8298 address_expr_8298 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [address_expr_8298 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8297.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8300 := Gval (Fuint 1) [::true].
Theorem nop_kill_step_8300 invalid old current result :
 VM.find 8299 old = Some nop_kill_value_8299 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8300 result = Some nop_kill_value_8300.
Proof.
 intros H8299 Step.
 assert (Member : List.In (8300,address_expr_8300) data_address_expected_nodes).
 { apply (List.nth_error_In data_address_expected_nodes 186%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8300 address_expr_8300 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [address_expr_8300 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8299.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8302 := Gval (Fuint 1) [::false].
Theorem nop_kill_step_8302 invalid old current result :
 VM.find 8301 old = Some nop_kill_value_8301 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8302 result = Some nop_kill_value_8302.
Proof.
 intros H8301 Step.
 assert (Member : List.In (8302,address_expr_8302) data_address_expected_nodes).
 { apply (List.nth_error_In data_address_expected_nodes 188%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8302 address_expr_8302 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [address_expr_8302 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8301.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8304 := Gval (Fuint 1) [::false].
Theorem nop_kill_step_8304 invalid old current result :
 VM.find 8303 old = Some nop_kill_value_8303 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8304 result = Some nop_kill_value_8304.
Proof.
 intros H8303 Step.
 assert (Member : List.In (8304,address_expr_8304) data_address_expected_nodes).
 { apply (List.nth_error_In data_address_expected_nodes 190%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8304 address_expr_8304 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [address_expr_8304 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8303.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8306 := Gval (Fuint 1) [::false].
Theorem nop_kill_step_8306 invalid old current result :
 VM.find 8305 old = Some nop_kill_value_8305 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8306 result = Some nop_kill_value_8306.
Proof.
 intros H8305 Step.
 assert (Member : List.In (8306,address_expr_8306) data_address_expected_nodes).
 { apply (List.nth_error_In data_address_expected_nodes 192%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8306 address_expr_8306 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [address_expr_8306 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8305.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8308 := Gval (Fuint 1) [::false].
Theorem nop_kill_step_8308 invalid old current result :
 VM.find 8307 old = Some nop_kill_value_8307 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8308 result = Some nop_kill_value_8308.
Proof.
 intros H8307 Step.
 assert (Member : List.In (8308,address_expr_8308) data_address_expected_nodes).
 { apply (List.nth_error_In data_address_expected_nodes 194%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8308 address_expr_8308 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [address_expr_8308 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8307.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8310 := Gval (Fuint 1) [::false].
Theorem nop_kill_step_8310 invalid old current result :
 VM.find 8309 old = Some nop_kill_value_8309 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8310 result = Some nop_kill_value_8310.
Proof.
 intros H8309 Step.
 assert (Member : List.In (8310,address_expr_8310) data_address_expected_nodes).
 { apply (List.nth_error_In data_address_expected_nodes 196%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8310 address_expr_8310 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [address_expr_8310 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8309.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8312 := Gval (Fuint 1) [::false].
Theorem nop_kill_step_8312 invalid old current result :
 VM.find 8311 old = Some nop_kill_value_8311 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8312 result = Some nop_kill_value_8312.
Proof.
 intros H8311 Step.
 assert (Member : List.In (8312,address_expr_8312) data_address_expected_nodes).
 { apply (List.nth_error_In data_address_expected_nodes 198%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8312 address_expr_8312 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [address_expr_8312 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8311.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8314 := Gval (Fuint 1) [::false].
Theorem nop_kill_step_8314 invalid old current result :
 VM.find 8313 old = Some nop_kill_value_8313 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8314 result = Some nop_kill_value_8314.
Proof.
 intros H8313 Step.
 assert (Member : List.In (8314,address_expr_8314) data_address_expected_nodes).
 { apply (List.nth_error_In data_address_expected_nodes 200%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8314 address_expr_8314 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [address_expr_8314 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8313.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8316 := Gval (Fuint 1) [::false].
Theorem nop_kill_step_8316 invalid old current result :
 VM.find 8315 old = Some nop_kill_value_8315 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8316 result = Some nop_kill_value_8316.
Proof.
 intros H8315 Step.
 assert (Member : List.In (8316,address_expr_8316) data_address_expected_nodes).
 { apply (List.nth_error_In data_address_expected_nodes 202%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8316 address_expr_8316 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [address_expr_8316 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8315.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8318 := Gval (Fuint 1) [::false].
Theorem nop_kill_step_8318 invalid old current result :
 VM.find 8317 old = Some nop_kill_value_8317 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8318 result = Some nop_kill_value_8318.
Proof.
 intros H8317 Step.
 assert (Member : List.In (8318,address_expr_8318) data_address_expected_nodes).
 { apply (List.nth_error_In data_address_expected_nodes 204%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8318 address_expr_8318 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [address_expr_8318 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8317.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8320 := Gval (Fuint 1) [::false].
Theorem nop_kill_step_8320 invalid old current result :
 VM.find 8319 old = Some nop_kill_value_8319 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8320 result = Some nop_kill_value_8320.
Proof.
 intros H8319 Step.
 assert (Member : List.In (8320,address_expr_8320) data_address_expected_nodes).
 { apply (List.nth_error_In data_address_expected_nodes 206%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8320 address_expr_8320 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [address_expr_8320 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8319.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8322 := Gval (Fuint 1) [::false].
Theorem nop_kill_step_8322 invalid old current result :
 VM.find 8321 old = Some nop_kill_value_8321 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8322 result = Some nop_kill_value_8322.
Proof.
 intros H8321 Step.
 assert (Member : List.In (8322,address_expr_8322) data_address_expected_nodes).
 { apply (List.nth_error_In data_address_expected_nodes 208%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8322 address_expr_8322 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [address_expr_8322 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8321.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8324 := Gval (Fuint 1) [::false].
Theorem nop_kill_step_8324 invalid old current result :
 VM.find 8323 old = Some nop_kill_value_8323 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8324 result = Some nop_kill_value_8324.
Proof.
 intros H8323 Step.
 assert (Member : List.In (8324,address_expr_8324) data_address_expected_nodes).
 { apply (List.nth_error_In data_address_expected_nodes 210%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8324 address_expr_8324 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [address_expr_8324 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8323.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8326 := Gval (Fuint 1) [::false].
Theorem nop_kill_step_8326 invalid old current result :
 VM.find 8325 old = Some nop_kill_value_8325 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8326 result = Some nop_kill_value_8326.
Proof.
 intros H8325 Step.
 assert (Member : List.In (8326,address_expr_8326) data_address_expected_nodes).
 { apply (List.nth_error_In data_address_expected_nodes 212%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8326 address_expr_8326 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [address_expr_8326 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8325.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8328 := Gval (Fuint 1) [::false].
Theorem nop_kill_step_8328 invalid old current result :
 VM.find 8327 old = Some nop_kill_value_8327 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8328 result = Some nop_kill_value_8328.
Proof.
 intros H8327 Step.
 assert (Member : List.In (8328,address_expr_8328) data_address_expected_nodes).
 { apply (List.nth_error_In data_address_expected_nodes 214%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8328 address_expr_8328 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [address_expr_8328 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8327.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8330 := Gval (Fuint 1) [::false].
Theorem nop_kill_step_8330 invalid old current result :
 VM.find 8329 old = Some nop_kill_value_8329 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8330 result = Some nop_kill_value_8330.
Proof.
 intros H8329 Step.
 assert (Member : List.In (8330,address_expr_8330) data_address_expected_nodes).
 { apply (List.nth_error_In data_address_expected_nodes 216%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8330 address_expr_8330 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [address_expr_8330 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8329.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8332 := Gval (Fuint 1) [::false].
Theorem nop_kill_step_8332 invalid old current result :
 VM.find 8331 old = Some nop_kill_value_8331 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8332 result = Some nop_kill_value_8332.
Proof.
 intros H8331 Step.
 assert (Member : List.In (8332,address_expr_8332) data_address_expected_nodes).
 { apply (List.nth_error_In data_address_expected_nodes 218%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8332 address_expr_8332 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [address_expr_8332 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8331.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8334 := Gval (Fuint 1) [::false].
Theorem nop_kill_step_8334 invalid old current result :
 VM.find 8333 old = Some nop_kill_value_8333 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8334 result = Some nop_kill_value_8334.
Proof.
 intros H8333 Step.
 assert (Member : List.In (8334,address_expr_8334) data_address_expected_nodes).
 { apply (List.nth_error_In data_address_expected_nodes 220%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8334 address_expr_8334 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [address_expr_8334 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8333.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8336 := Gval (Fuint 1) [::false].
Theorem nop_kill_step_8336 invalid old current result :
 VM.find 8335 old = Some nop_kill_value_8335 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8336 result = Some nop_kill_value_8336.
Proof.
 intros H8335 Step.
 assert (Member : List.In (8336,address_expr_8336) data_address_expected_nodes).
 { apply (List.nth_error_In data_address_expected_nodes 222%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8336 address_expr_8336 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [address_expr_8336 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8335.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8338 := Gval (Fuint 1) [::false].
Theorem nop_kill_step_8338 invalid old current result :
 VM.find 8337 old = Some nop_kill_value_8337 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8338 result = Some nop_kill_value_8338.
Proof.
 intros H8337 Step.
 assert (Member : List.In (8338,address_expr_8338) data_address_expected_nodes).
 { apply (List.nth_error_In data_address_expected_nodes 224%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8338 address_expr_8338 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [address_expr_8338 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8337.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8340 := Gval (Fuint 1) [::false].
Theorem nop_kill_step_8340 invalid old current result :
 VM.find 8339 old = Some nop_kill_value_8339 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8340 result = Some nop_kill_value_8340.
Proof.
 intros H8339 Step.
 assert (Member : List.In (8340,address_expr_8340) data_address_expected_nodes).
 { apply (List.nth_error_In data_address_expected_nodes 226%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8340 address_expr_8340 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [address_expr_8340 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8339.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8342 := Gval (Fuint 1) [::false].
Theorem nop_kill_step_8342 invalid old current result :
 VM.find 8341 old = Some nop_kill_value_8341 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8342 result = Some nop_kill_value_8342.
Proof.
 intros H8341 Step.
 assert (Member : List.In (8342,address_expr_8342) data_address_expected_nodes).
 { apply (List.nth_error_In data_address_expected_nodes 228%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8342 address_expr_8342 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [address_expr_8342 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8341.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8344 := Gval (Fuint 1) [::false].
Theorem nop_kill_step_8344 invalid old current result :
 VM.find 8343 old = Some nop_kill_value_8343 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8344 result = Some nop_kill_value_8344.
Proof.
 intros H8343 Step.
 assert (Member : List.In (8344,address_expr_8344) data_address_expected_nodes).
 { apply (List.nth_error_In data_address_expected_nodes 230%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8344 address_expr_8344 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [address_expr_8344 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8343.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8346 := Gval (Fuint 1) [::false].
Theorem nop_kill_step_8346 invalid old current result :
 VM.find 8345 old = Some nop_kill_value_8345 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8346 result = Some nop_kill_value_8346.
Proof.
 intros H8345 Step.
 assert (Member : List.In (8346,address_expr_8346) data_address_expected_nodes).
 { apply (List.nth_error_In data_address_expected_nodes 232%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8346 address_expr_8346 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [address_expr_8346 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8345.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8348 := Gval (Fuint 1) [::false].
Theorem nop_kill_step_8348 invalid old current result :
 VM.find 8347 old = Some nop_kill_value_8347 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8348 result = Some nop_kill_value_8348.
Proof.
 intros H8347 Step.
 assert (Member : List.In (8348,address_expr_8348) data_address_expected_nodes).
 { apply (List.nth_error_In data_address_expected_nodes 234%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8348 address_expr_8348 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [address_expr_8348 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8347.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8350 := Gval (Fuint 1) [::false].
Theorem nop_kill_step_8350 invalid old current result :
 VM.find 8349 old = Some nop_kill_value_8349 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8350 result = Some nop_kill_value_8350.
Proof.
 intros H8349 Step.
 assert (Member : List.In (8350,address_expr_8350) data_address_expected_nodes).
 { apply (List.nth_error_In data_address_expected_nodes 236%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8350 address_expr_8350 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [address_expr_8350 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8349.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8352 := Gval (Fuint 1) [::false].
Theorem nop_kill_step_8352 invalid old current result :
 VM.find 8351 old = Some nop_kill_value_8351 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8352 result = Some nop_kill_value_8352.
Proof.
 intros H8351 Step.
 assert (Member : List.In (8352,address_expr_8352) data_address_expected_nodes).
 { apply (List.nth_error_In data_address_expected_nodes 238%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8352 address_expr_8352 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [address_expr_8352 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8351.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8354 := Gval (Fuint 1) [::false].
Theorem nop_kill_step_8354 invalid old current result :
 VM.find 8353 old = Some nop_kill_value_8353 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8354 result = Some nop_kill_value_8354.
Proof.
 intros H8353 Step.
 assert (Member : List.In (8354,address_expr_8354) data_address_expected_nodes).
 { apply (List.nth_error_In data_address_expected_nodes 240%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8354 address_expr_8354 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [address_expr_8354 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8353.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8356 := Gval (Fuint 1) [::false].
Theorem nop_kill_step_8356 invalid old current result :
 VM.find 8355 old = Some nop_kill_value_8355 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8356 result = Some nop_kill_value_8356.
Proof.
 intros H8355 Step.
 assert (Member : List.In (8356,address_expr_8356) data_address_expected_nodes).
 { apply (List.nth_error_In data_address_expected_nodes 242%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8356 address_expr_8356 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [address_expr_8356 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8355.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8358 := Gval (Fuint 1) [::false].
Theorem nop_kill_step_8358 invalid old current result :
 VM.find 8357 old = Some nop_kill_value_8357 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8358 result = Some nop_kill_value_8358.
Proof.
 intros H8357 Step.
 assert (Member : List.In (8358,address_expr_8358) data_address_expected_nodes).
 { apply (List.nth_error_In data_address_expected_nodes 244%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8358 address_expr_8358 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [address_expr_8358 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8357.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8360 := Gval (Fuint 1) [::false].
Theorem nop_kill_step_8360 invalid old current result :
 VM.find 8359 old = Some nop_kill_value_8359 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8360 result = Some nop_kill_value_8360.
Proof.
 intros H8359 Step.
 assert (Member : List.In (8360,address_expr_8360) data_address_expected_nodes).
 { apply (List.nth_error_In data_address_expected_nodes 246%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes 8360 address_expr_8360 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [address_expr_8360 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8359.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8606 := Gval (Fuint 3) [::false;false;false].
Theorem nop_kill_step_8606 invalid old current result :
 VM.find 8360 old = Some nop_kill_value_8360 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8606 result = Some nop_kill_value_8606.
Proof.
 intros H8360 Step.
 assert (Member : List.In (8606,joint_update_expr_8606) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 1095%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8606 joint_update_expr_8606 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [joint_update_expr_8606 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8360.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8655 := Gval (Fuint 1) [::false].
Theorem nop_kill_step_8655 invalid old current result :
 VM.find 8360 old = Some nop_kill_value_8360 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8655 result = Some nop_kill_value_8655.
Proof.
 intros H8360 Step.
 assert (Member : List.In (8655,joint_update_expr_8655) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 1144%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8655 joint_update_expr_8655 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [joint_update_expr_8655 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8360.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8607 := Gval (Fuint 3) [::false;false;false].
Theorem nop_kill_step_8607 invalid old current result :
 VM.find 8358 old = Some nop_kill_value_8358 ->
 VM.find 8606 old = Some nop_kill_value_8606 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8607 result = Some nop_kill_value_8607.
Proof.
 intros H8358 H8606 Step.
 assert (Member : List.In (8607,joint_update_expr_8607) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 1096%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8607 joint_update_expr_8607 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [joint_update_expr_8607 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8358.
 rewrite H8606.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8656 := Gval (Fuint 1) [::false].
Theorem nop_kill_step_8656 invalid old current result :
 VM.find 8358 old = Some nop_kill_value_8358 ->
 VM.find 8655 old = Some nop_kill_value_8655 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8656 result = Some nop_kill_value_8656.
Proof.
 intros H8358 H8655 Step.
 assert (Member : List.In (8656,joint_update_expr_8656) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 1145%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8656 joint_update_expr_8656 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [joint_update_expr_8656 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8358.
 rewrite H8655.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8608 := Gval (Fuint 3) [::false;false;false].
Theorem nop_kill_step_8608 invalid old current result :
 VM.find 8356 old = Some nop_kill_value_8356 ->
 VM.find 8607 old = Some nop_kill_value_8607 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8608 result = Some nop_kill_value_8608.
Proof.
 intros H8356 H8607 Step.
 assert (Member : List.In (8608,joint_update_expr_8608) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 1097%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8608 joint_update_expr_8608 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [joint_update_expr_8608 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8356.
 rewrite H8607.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8657 := Gval (Fuint 1) [::false].
Theorem nop_kill_step_8657 invalid old current result :
 VM.find 8356 old = Some nop_kill_value_8356 ->
 VM.find 8656 old = Some nop_kill_value_8656 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8657 result = Some nop_kill_value_8657.
Proof.
 intros H8356 H8656 Step.
 assert (Member : List.In (8657,joint_update_expr_8657) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 1146%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8657 joint_update_expr_8657 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [joint_update_expr_8657 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8356.
 rewrite H8656.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8609 := Gval (Fuint 3) [::false;false;false].
Theorem nop_kill_step_8609 invalid old current result :
 VM.find 8354 old = Some nop_kill_value_8354 ->
 VM.find 8608 old = Some nop_kill_value_8608 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8609 result = Some nop_kill_value_8609.
Proof.
 intros H8354 H8608 Step.
 assert (Member : List.In (8609,joint_update_expr_8609) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 1098%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8609 joint_update_expr_8609 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [joint_update_expr_8609 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8354.
 rewrite H8608.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8658 := Gval (Fuint 1) [::false].
Theorem nop_kill_step_8658 invalid old current result :
 VM.find 8354 old = Some nop_kill_value_8354 ->
 VM.find 8657 old = Some nop_kill_value_8657 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8658 result = Some nop_kill_value_8658.
Proof.
 intros H8354 H8657 Step.
 assert (Member : List.In (8658,joint_update_expr_8658) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 1147%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8658 joint_update_expr_8658 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [joint_update_expr_8658 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8354.
 rewrite H8657.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8610 := Gval (Fuint 3) [::false;false;false].
Theorem nop_kill_step_8610 invalid old current result :
 VM.find 8352 old = Some nop_kill_value_8352 ->
 VM.find 8609 old = Some nop_kill_value_8609 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8610 result = Some nop_kill_value_8610.
Proof.
 intros H8352 H8609 Step.
 assert (Member : List.In (8610,joint_update_expr_8610) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 1099%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8610 joint_update_expr_8610 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [joint_update_expr_8610 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8352.
 rewrite H8609.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8659 := Gval (Fuint 1) [::false].
Theorem nop_kill_step_8659 invalid old current result :
 VM.find 8352 old = Some nop_kill_value_8352 ->
 VM.find 8658 old = Some nop_kill_value_8658 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8659 result = Some nop_kill_value_8659.
Proof.
 intros H8352 H8658 Step.
 assert (Member : List.In (8659,joint_update_expr_8659) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 1148%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8659 joint_update_expr_8659 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [joint_update_expr_8659 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8352.
 rewrite H8658.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8611 := Gval (Fuint 3) [::false;false;false].
Theorem nop_kill_step_8611 invalid old current result :
 VM.find 8350 old = Some nop_kill_value_8350 ->
 VM.find 8610 old = Some nop_kill_value_8610 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8611 result = Some nop_kill_value_8611.
Proof.
 intros H8350 H8610 Step.
 assert (Member : List.In (8611,joint_update_expr_8611) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 1100%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8611 joint_update_expr_8611 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [joint_update_expr_8611 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8350.
 rewrite H8610.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8660 := Gval (Fuint 1) [::false].
Theorem nop_kill_step_8660 invalid old current result :
 VM.find 8350 old = Some nop_kill_value_8350 ->
 VM.find 8659 old = Some nop_kill_value_8659 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8660 result = Some nop_kill_value_8660.
Proof.
 intros H8350 H8659 Step.
 assert (Member : List.In (8660,joint_update_expr_8660) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 1149%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8660 joint_update_expr_8660 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [joint_update_expr_8660 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8350.
 rewrite H8659.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8612 := Gval (Fuint 3) [::false;false;false].
Theorem nop_kill_step_8612 invalid old current result :
 VM.find 8348 old = Some nop_kill_value_8348 ->
 VM.find 8611 old = Some nop_kill_value_8611 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8612 result = Some nop_kill_value_8612.
Proof.
 intros H8348 H8611 Step.
 assert (Member : List.In (8612,joint_update_expr_8612) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 1101%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8612 joint_update_expr_8612 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [joint_update_expr_8612 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8348.
 rewrite H8611.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8661 := Gval (Fuint 1) [::false].
Theorem nop_kill_step_8661 invalid old current result :
 VM.find 8348 old = Some nop_kill_value_8348 ->
 VM.find 8660 old = Some nop_kill_value_8660 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8661 result = Some nop_kill_value_8661.
Proof.
 intros H8348 H8660 Step.
 assert (Member : List.In (8661,joint_update_expr_8661) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 1150%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8661 joint_update_expr_8661 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [joint_update_expr_8661 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8348.
 rewrite H8660.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8613 := Gval (Fuint 3) [::false;false;false].
Theorem nop_kill_step_8613 invalid old current result :
 VM.find 8346 old = Some nop_kill_value_8346 ->
 VM.find 8612 old = Some nop_kill_value_8612 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8613 result = Some nop_kill_value_8613.
Proof.
 intros H8346 H8612 Step.
 assert (Member : List.In (8613,joint_update_expr_8613) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 1102%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8613 joint_update_expr_8613 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [joint_update_expr_8613 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8346.
 rewrite H8612.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8662 := Gval (Fuint 1) [::false].
Theorem nop_kill_step_8662 invalid old current result :
 VM.find 8346 old = Some nop_kill_value_8346 ->
 VM.find 8661 old = Some nop_kill_value_8661 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8662 result = Some nop_kill_value_8662.
Proof.
 intros H8346 H8661 Step.
 assert (Member : List.In (8662,joint_update_expr_8662) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 1151%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8662 joint_update_expr_8662 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [joint_update_expr_8662 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8346.
 rewrite H8661.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8614 := Gval (Fuint 3) [::false;false;false].
Theorem nop_kill_step_8614 invalid old current result :
 VM.find 8344 old = Some nop_kill_value_8344 ->
 VM.find 8613 old = Some nop_kill_value_8613 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8614 result = Some nop_kill_value_8614.
Proof.
 intros H8344 H8613 Step.
 assert (Member : List.In (8614,joint_update_expr_8614) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 1103%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8614 joint_update_expr_8614 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [joint_update_expr_8614 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8344.
 rewrite H8613.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8663 := Gval (Fuint 1) [::false].
Theorem nop_kill_step_8663 invalid old current result :
 VM.find 8344 old = Some nop_kill_value_8344 ->
 VM.find 8662 old = Some nop_kill_value_8662 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8663 result = Some nop_kill_value_8663.
Proof.
 intros H8344 H8662 Step.
 assert (Member : List.In (8663,joint_update_expr_8663) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 1152%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8663 joint_update_expr_8663 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [joint_update_expr_8663 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8344.
 rewrite H8662.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8615 := Gval (Fuint 3) [::false;false;false].
Theorem nop_kill_step_8615 invalid old current result :
 VM.find 8342 old = Some nop_kill_value_8342 ->
 VM.find 8614 old = Some nop_kill_value_8614 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8615 result = Some nop_kill_value_8615.
Proof.
 intros H8342 H8614 Step.
 assert (Member : List.In (8615,joint_update_expr_8615) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 1104%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8615 joint_update_expr_8615 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [joint_update_expr_8615 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8342.
 rewrite H8614.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8664 := Gval (Fuint 1) [::false].
Theorem nop_kill_step_8664 invalid old current result :
 VM.find 8342 old = Some nop_kill_value_8342 ->
 VM.find 8663 old = Some nop_kill_value_8663 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8664 result = Some nop_kill_value_8664.
Proof.
 intros H8342 H8663 Step.
 assert (Member : List.In (8664,joint_update_expr_8664) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 1153%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8664 joint_update_expr_8664 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [joint_update_expr_8664 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8342.
 rewrite H8663.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8616 := Gval (Fuint 3) [::false;false;false].
Theorem nop_kill_step_8616 invalid old current result :
 VM.find 8340 old = Some nop_kill_value_8340 ->
 VM.find 8615 old = Some nop_kill_value_8615 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8616 result = Some nop_kill_value_8616.
Proof.
 intros H8340 H8615 Step.
 assert (Member : List.In (8616,joint_update_expr_8616) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 1105%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8616 joint_update_expr_8616 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [joint_update_expr_8616 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8340.
 rewrite H8615.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8665 := Gval (Fuint 1) [::false].
Theorem nop_kill_step_8665 invalid old current result :
 VM.find 8340 old = Some nop_kill_value_8340 ->
 VM.find 8664 old = Some nop_kill_value_8664 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8665 result = Some nop_kill_value_8665.
Proof.
 intros H8340 H8664 Step.
 assert (Member : List.In (8665,joint_update_expr_8665) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 1154%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8665 joint_update_expr_8665 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [joint_update_expr_8665 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8340.
 rewrite H8664.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8617 := Gval (Fuint 3) [::false;false;false].
Theorem nop_kill_step_8617 invalid old current result :
 VM.find 8338 old = Some nop_kill_value_8338 ->
 VM.find 8616 old = Some nop_kill_value_8616 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8617 result = Some nop_kill_value_8617.
Proof.
 intros H8338 H8616 Step.
 assert (Member : List.In (8617,joint_update_expr_8617) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 1106%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8617 joint_update_expr_8617 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [joint_update_expr_8617 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8338.
 rewrite H8616.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8666 := Gval (Fuint 1) [::false].
Theorem nop_kill_step_8666 invalid old current result :
 VM.find 8338 old = Some nop_kill_value_8338 ->
 VM.find 8665 old = Some nop_kill_value_8665 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8666 result = Some nop_kill_value_8666.
Proof.
 intros H8338 H8665 Step.
 assert (Member : List.In (8666,joint_update_expr_8666) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 1155%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8666 joint_update_expr_8666 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [joint_update_expr_8666 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8338.
 rewrite H8665.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8618 := Gval (Fuint 3) [::false;false;false].
Theorem nop_kill_step_8618 invalid old current result :
 VM.find 8336 old = Some nop_kill_value_8336 ->
 VM.find 8617 old = Some nop_kill_value_8617 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8618 result = Some nop_kill_value_8618.
Proof.
 intros H8336 H8617 Step.
 assert (Member : List.In (8618,joint_update_expr_8618) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 1107%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8618 joint_update_expr_8618 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [joint_update_expr_8618 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8336.
 rewrite H8617.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8667 := Gval (Fuint 1) [::false].
Theorem nop_kill_step_8667 invalid old current result :
 VM.find 8336 old = Some nop_kill_value_8336 ->
 VM.find 8666 old = Some nop_kill_value_8666 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8667 result = Some nop_kill_value_8667.
Proof.
 intros H8336 H8666 Step.
 assert (Member : List.In (8667,joint_update_expr_8667) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 1156%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8667 joint_update_expr_8667 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [joint_update_expr_8667 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8336.
 rewrite H8666.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8619 := Gval (Fuint 3) [::false;false;false].
Theorem nop_kill_step_8619 invalid old current result :
 VM.find 8334 old = Some nop_kill_value_8334 ->
 VM.find 8618 old = Some nop_kill_value_8618 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8619 result = Some nop_kill_value_8619.
Proof.
 intros H8334 H8618 Step.
 assert (Member : List.In (8619,joint_update_expr_8619) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 1108%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8619 joint_update_expr_8619 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [joint_update_expr_8619 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8334.
 rewrite H8618.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8668 := Gval (Fuint 1) [::false].
Theorem nop_kill_step_8668 invalid old current result :
 VM.find 8334 old = Some nop_kill_value_8334 ->
 VM.find 8667 old = Some nop_kill_value_8667 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8668 result = Some nop_kill_value_8668.
Proof.
 intros H8334 H8667 Step.
 assert (Member : List.In (8668,joint_update_expr_8668) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 1157%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8668 joint_update_expr_8668 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [joint_update_expr_8668 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8334.
 rewrite H8667.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8620 := Gval (Fuint 3) [::false;false;false].
Theorem nop_kill_step_8620 invalid old current result :
 VM.find 8332 old = Some nop_kill_value_8332 ->
 VM.find 8619 old = Some nop_kill_value_8619 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8620 result = Some nop_kill_value_8620.
Proof.
 intros H8332 H8619 Step.
 assert (Member : List.In (8620,joint_update_expr_8620) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 1109%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8620 joint_update_expr_8620 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [joint_update_expr_8620 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8332.
 rewrite H8619.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8669 := Gval (Fuint 1) [::false].
Theorem nop_kill_step_8669 invalid old current result :
 VM.find 8332 old = Some nop_kill_value_8332 ->
 VM.find 8668 old = Some nop_kill_value_8668 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8669 result = Some nop_kill_value_8669.
Proof.
 intros H8332 H8668 Step.
 assert (Member : List.In (8669,joint_update_expr_8669) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 1158%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8669 joint_update_expr_8669 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [joint_update_expr_8669 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8332.
 rewrite H8668.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8621 := Gval (Fuint 3) [::false;false;false].
Theorem nop_kill_step_8621 invalid old current result :
 VM.find 8330 old = Some nop_kill_value_8330 ->
 VM.find 8620 old = Some nop_kill_value_8620 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8621 result = Some nop_kill_value_8621.
Proof.
 intros H8330 H8620 Step.
 assert (Member : List.In (8621,joint_update_expr_8621) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 1110%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8621 joint_update_expr_8621 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [joint_update_expr_8621 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8330.
 rewrite H8620.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8670 := Gval (Fuint 1) [::false].
Theorem nop_kill_step_8670 invalid old current result :
 VM.find 8330 old = Some nop_kill_value_8330 ->
 VM.find 8669 old = Some nop_kill_value_8669 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8670 result = Some nop_kill_value_8670.
Proof.
 intros H8330 H8669 Step.
 assert (Member : List.In (8670,joint_update_expr_8670) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 1159%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8670 joint_update_expr_8670 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [joint_update_expr_8670 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8330.
 rewrite H8669.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8622 := Gval (Fuint 3) [::false;false;false].
Theorem nop_kill_step_8622 invalid old current result :
 VM.find 8328 old = Some nop_kill_value_8328 ->
 VM.find 8621 old = Some nop_kill_value_8621 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8622 result = Some nop_kill_value_8622.
Proof.
 intros H8328 H8621 Step.
 assert (Member : List.In (8622,joint_update_expr_8622) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 1111%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8622 joint_update_expr_8622 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [joint_update_expr_8622 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8328.
 rewrite H8621.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8671 := Gval (Fuint 1) [::false].
Theorem nop_kill_step_8671 invalid old current result :
 VM.find 8328 old = Some nop_kill_value_8328 ->
 VM.find 8670 old = Some nop_kill_value_8670 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8671 result = Some nop_kill_value_8671.
Proof.
 intros H8328 H8670 Step.
 assert (Member : List.In (8671,joint_update_expr_8671) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 1160%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8671 joint_update_expr_8671 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [joint_update_expr_8671 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8328.
 rewrite H8670.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8623 := Gval (Fuint 3) [::false;false;false].
Theorem nop_kill_step_8623 invalid old current result :
 VM.find 8326 old = Some nop_kill_value_8326 ->
 VM.find 8622 old = Some nop_kill_value_8622 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8623 result = Some nop_kill_value_8623.
Proof.
 intros H8326 H8622 Step.
 assert (Member : List.In (8623,joint_update_expr_8623) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 1112%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8623 joint_update_expr_8623 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [joint_update_expr_8623 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8326.
 rewrite H8622.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8672 := Gval (Fuint 1) [::false].
Theorem nop_kill_step_8672 invalid old current result :
 VM.find 8326 old = Some nop_kill_value_8326 ->
 VM.find 8671 old = Some nop_kill_value_8671 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8672 result = Some nop_kill_value_8672.
Proof.
 intros H8326 H8671 Step.
 assert (Member : List.In (8672,joint_update_expr_8672) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 1161%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8672 joint_update_expr_8672 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [joint_update_expr_8672 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8326.
 rewrite H8671.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8624 := Gval (Fuint 3) [::false;false;false].
Theorem nop_kill_step_8624 invalid old current result :
 VM.find 8324 old = Some nop_kill_value_8324 ->
 VM.find 8623 old = Some nop_kill_value_8623 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8624 result = Some nop_kill_value_8624.
Proof.
 intros H8324 H8623 Step.
 assert (Member : List.In (8624,joint_update_expr_8624) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 1113%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8624 joint_update_expr_8624 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [joint_update_expr_8624 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8324.
 rewrite H8623.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8673 := Gval (Fuint 1) [::false].
Theorem nop_kill_step_8673 invalid old current result :
 VM.find 8324 old = Some nop_kill_value_8324 ->
 VM.find 8672 old = Some nop_kill_value_8672 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8673 result = Some nop_kill_value_8673.
Proof.
 intros H8324 H8672 Step.
 assert (Member : List.In (8673,joint_update_expr_8673) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 1162%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8673 joint_update_expr_8673 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [joint_update_expr_8673 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8324.
 rewrite H8672.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8625 := Gval (Fuint 3) [::false;false;false].
Theorem nop_kill_step_8625 invalid old current result :
 VM.find 8322 old = Some nop_kill_value_8322 ->
 VM.find 8624 old = Some nop_kill_value_8624 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8625 result = Some nop_kill_value_8625.
Proof.
 intros H8322 H8624 Step.
 assert (Member : List.In (8625,joint_update_expr_8625) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 1114%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8625 joint_update_expr_8625 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [joint_update_expr_8625 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8322.
 rewrite H8624.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8674 := Gval (Fuint 1) [::false].
Theorem nop_kill_step_8674 invalid old current result :
 VM.find 8322 old = Some nop_kill_value_8322 ->
 VM.find 8673 old = Some nop_kill_value_8673 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8674 result = Some nop_kill_value_8674.
Proof.
 intros H8322 H8673 Step.
 assert (Member : List.In (8674,joint_update_expr_8674) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 1163%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8674 joint_update_expr_8674 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [joint_update_expr_8674 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8322.
 rewrite H8673.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8626 := Gval (Fuint 3) [::false;false;false].
Theorem nop_kill_step_8626 invalid old current result :
 VM.find 8320 old = Some nop_kill_value_8320 ->
 VM.find 8625 old = Some nop_kill_value_8625 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8626 result = Some nop_kill_value_8626.
Proof.
 intros H8320 H8625 Step.
 assert (Member : List.In (8626,joint_update_expr_8626) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 1115%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8626 joint_update_expr_8626 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [joint_update_expr_8626 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8320.
 rewrite H8625.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8675 := Gval (Fuint 1) [::false].
Theorem nop_kill_step_8675 invalid old current result :
 VM.find 8320 old = Some nop_kill_value_8320 ->
 VM.find 8674 old = Some nop_kill_value_8674 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8675 result = Some nop_kill_value_8675.
Proof.
 intros H8320 H8674 Step.
 assert (Member : List.In (8675,joint_update_expr_8675) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 1164%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8675 joint_update_expr_8675 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [joint_update_expr_8675 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8320.
 rewrite H8674.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8627 := Gval (Fuint 3) [::false;false;false].
Theorem nop_kill_step_8627 invalid old current result :
 VM.find 8318 old = Some nop_kill_value_8318 ->
 VM.find 8626 old = Some nop_kill_value_8626 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8627 result = Some nop_kill_value_8627.
Proof.
 intros H8318 H8626 Step.
 assert (Member : List.In (8627,joint_update_expr_8627) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 1116%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8627 joint_update_expr_8627 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [joint_update_expr_8627 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8318.
 rewrite H8626.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8676 := Gval (Fuint 1) [::false].
Theorem nop_kill_step_8676 invalid old current result :
 VM.find 8318 old = Some nop_kill_value_8318 ->
 VM.find 8675 old = Some nop_kill_value_8675 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8676 result = Some nop_kill_value_8676.
Proof.
 intros H8318 H8675 Step.
 assert (Member : List.In (8676,joint_update_expr_8676) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 1165%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8676 joint_update_expr_8676 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [joint_update_expr_8676 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8318.
 rewrite H8675.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8628 := Gval (Fuint 3) [::false;false;false].
Theorem nop_kill_step_8628 invalid old current result :
 VM.find 8316 old = Some nop_kill_value_8316 ->
 VM.find 8627 old = Some nop_kill_value_8627 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8628 result = Some nop_kill_value_8628.
Proof.
 intros H8316 H8627 Step.
 assert (Member : List.In (8628,joint_update_expr_8628) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 1117%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8628 joint_update_expr_8628 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [joint_update_expr_8628 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8316.
 rewrite H8627.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8677 := Gval (Fuint 1) [::false].
Theorem nop_kill_step_8677 invalid old current result :
 VM.find 8316 old = Some nop_kill_value_8316 ->
 VM.find 8676 old = Some nop_kill_value_8676 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8677 result = Some nop_kill_value_8677.
Proof.
 intros H8316 H8676 Step.
 assert (Member : List.In (8677,joint_update_expr_8677) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 1166%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8677 joint_update_expr_8677 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [joint_update_expr_8677 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8316.
 rewrite H8676.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8629 := Gval (Fuint 3) [::false;false;false].
Theorem nop_kill_step_8629 invalid old current result :
 VM.find 8314 old = Some nop_kill_value_8314 ->
 VM.find 8628 old = Some nop_kill_value_8628 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8629 result = Some nop_kill_value_8629.
Proof.
 intros H8314 H8628 Step.
 assert (Member : List.In (8629,joint_update_expr_8629) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 1118%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8629 joint_update_expr_8629 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [joint_update_expr_8629 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8314.
 rewrite H8628.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8678 := Gval (Fuint 1) [::false].
Theorem nop_kill_step_8678 invalid old current result :
 VM.find 8314 old = Some nop_kill_value_8314 ->
 VM.find 8677 old = Some nop_kill_value_8677 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8678 result = Some nop_kill_value_8678.
Proof.
 intros H8314 H8677 Step.
 assert (Member : List.In (8678,joint_update_expr_8678) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 1167%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8678 joint_update_expr_8678 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [joint_update_expr_8678 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8314.
 rewrite H8677.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8630 := Gval (Fuint 3) [::false;false;false].
Theorem nop_kill_step_8630 invalid old current result :
 VM.find 8312 old = Some nop_kill_value_8312 ->
 VM.find 8629 old = Some nop_kill_value_8629 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8630 result = Some nop_kill_value_8630.
Proof.
 intros H8312 H8629 Step.
 assert (Member : List.In (8630,joint_update_expr_8630) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 1119%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8630 joint_update_expr_8630 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [joint_update_expr_8630 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8312.
 rewrite H8629.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8679 := Gval (Fuint 1) [::false].
Theorem nop_kill_step_8679 invalid old current result :
 VM.find 8312 old = Some nop_kill_value_8312 ->
 VM.find 8678 old = Some nop_kill_value_8678 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8679 result = Some nop_kill_value_8679.
Proof.
 intros H8312 H8678 Step.
 assert (Member : List.In (8679,joint_update_expr_8679) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 1168%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8679 joint_update_expr_8679 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [joint_update_expr_8679 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8312.
 rewrite H8678.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8631 := Gval (Fuint 3) [::false;false;false].
Theorem nop_kill_step_8631 invalid old current result :
 VM.find 8310 old = Some nop_kill_value_8310 ->
 VM.find 8630 old = Some nop_kill_value_8630 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8631 result = Some nop_kill_value_8631.
Proof.
 intros H8310 H8630 Step.
 assert (Member : List.In (8631,joint_update_expr_8631) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 1120%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8631 joint_update_expr_8631 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [joint_update_expr_8631 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8310.
 rewrite H8630.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8680 := Gval (Fuint 1) [::false].
Theorem nop_kill_step_8680 invalid old current result :
 VM.find 8310 old = Some nop_kill_value_8310 ->
 VM.find 8679 old = Some nop_kill_value_8679 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8680 result = Some nop_kill_value_8680.
Proof.
 intros H8310 H8679 Step.
 assert (Member : List.In (8680,joint_update_expr_8680) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 1169%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8680 joint_update_expr_8680 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [joint_update_expr_8680 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8310.
 rewrite H8679.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8632 := Gval (Fuint 3) [::false;false;false].
Theorem nop_kill_step_8632 invalid old current result :
 VM.find 8308 old = Some nop_kill_value_8308 ->
 VM.find 8631 old = Some nop_kill_value_8631 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8632 result = Some nop_kill_value_8632.
Proof.
 intros H8308 H8631 Step.
 assert (Member : List.In (8632,joint_update_expr_8632) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 1121%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8632 joint_update_expr_8632 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [joint_update_expr_8632 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8308.
 rewrite H8631.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8681 := Gval (Fuint 1) [::false].
Theorem nop_kill_step_8681 invalid old current result :
 VM.find 8308 old = Some nop_kill_value_8308 ->
 VM.find 8680 old = Some nop_kill_value_8680 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8681 result = Some nop_kill_value_8681.
Proof.
 intros H8308 H8680 Step.
 assert (Member : List.In (8681,joint_update_expr_8681) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 1170%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8681 joint_update_expr_8681 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [joint_update_expr_8681 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8308.
 rewrite H8680.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8633 := Gval (Fuint 3) [::false;false;false].
Theorem nop_kill_step_8633 invalid old current result :
 VM.find 8306 old = Some nop_kill_value_8306 ->
 VM.find 8632 old = Some nop_kill_value_8632 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8633 result = Some nop_kill_value_8633.
Proof.
 intros H8306 H8632 Step.
 assert (Member : List.In (8633,joint_update_expr_8633) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 1122%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8633 joint_update_expr_8633 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [joint_update_expr_8633 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8306.
 rewrite H8632.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8682 := Gval (Fuint 1) [::false].
Theorem nop_kill_step_8682 invalid old current result :
 VM.find 8306 old = Some nop_kill_value_8306 ->
 VM.find 8681 old = Some nop_kill_value_8681 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8682 result = Some nop_kill_value_8682.
Proof.
 intros H8306 H8681 Step.
 assert (Member : List.In (8682,joint_update_expr_8682) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 1171%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8682 joint_update_expr_8682 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [joint_update_expr_8682 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8306.
 rewrite H8681.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8634 := Gval (Fuint 3) [::false;false;false].
Theorem nop_kill_step_8634 invalid old current result :
 VM.find 8304 old = Some nop_kill_value_8304 ->
 VM.find 8633 old = Some nop_kill_value_8633 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8634 result = Some nop_kill_value_8634.
Proof.
 intros H8304 H8633 Step.
 assert (Member : List.In (8634,joint_update_expr_8634) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 1123%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8634 joint_update_expr_8634 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [joint_update_expr_8634 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8304.
 rewrite H8633.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8683 := Gval (Fuint 1) [::false].
Theorem nop_kill_step_8683 invalid old current result :
 VM.find 8304 old = Some nop_kill_value_8304 ->
 VM.find 8682 old = Some nop_kill_value_8682 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8683 result = Some nop_kill_value_8683.
Proof.
 intros H8304 H8682 Step.
 assert (Member : List.In (8683,joint_update_expr_8683) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 1172%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8683 joint_update_expr_8683 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [joint_update_expr_8683 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8304.
 rewrite H8682.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8635 := Gval (Fuint 3) [::false;false;false].
Theorem nop_kill_step_8635 invalid old current result :
 VM.find 8302 old = Some nop_kill_value_8302 ->
 VM.find 8634 old = Some nop_kill_value_8634 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8635 result = Some nop_kill_value_8635.
Proof.
 intros H8302 H8634 Step.
 assert (Member : List.In (8635,joint_update_expr_8635) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 1124%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8635 joint_update_expr_8635 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [joint_update_expr_8635 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8302.
 rewrite H8634.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8684 := Gval (Fuint 1) [::false].
Theorem nop_kill_step_8684 invalid old current result :
 VM.find 8302 old = Some nop_kill_value_8302 ->
 VM.find 8683 old = Some nop_kill_value_8683 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8684 result = Some nop_kill_value_8684.
Proof.
 intros H8302 H8683 Step.
 assert (Member : List.In (8684,joint_update_expr_8684) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 1173%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8684 joint_update_expr_8684 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [joint_update_expr_8684 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8302.
 rewrite H8683.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8636 := Gval (Fuint 3) [::false;false;false].
Theorem nop_kill_step_8636 invalid old current result :
 VM.find 8300 old = Some nop_kill_value_8300 ->
 VM.find 8635 old = Some nop_kill_value_8635 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8636 result = Some nop_kill_value_8636.
Proof.
 intros H8300 H8635 Step.
 assert (Member : List.In (8636,joint_update_expr_8636) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 1125%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8636 joint_update_expr_8636 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [joint_update_expr_8636 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8300.
 rewrite H8635.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8685 := Gval (Fuint 1) [::false].
Theorem nop_kill_step_8685 invalid old current result :
 VM.find 8300 old = Some nop_kill_value_8300 ->
 VM.find 8684 old = Some nop_kill_value_8684 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8685 result = Some nop_kill_value_8685.
Proof.
 intros H8300 H8684 Step.
 assert (Member : List.In (8685,joint_update_expr_8685) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 1174%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8685 joint_update_expr_8685 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [joint_update_expr_8685 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8300.
 rewrite H8684.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8637 := Gval (Fuint 3) [::false;false;false].
Theorem nop_kill_step_8637 invalid old current result :
 VM.find 8298 old = Some nop_kill_value_8298 ->
 VM.find 8636 old = Some nop_kill_value_8636 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8637 result = Some nop_kill_value_8637.
Proof.
 intros H8298 H8636 Step.
 assert (Member : List.In (8637,joint_update_expr_8637) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 1126%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8637 joint_update_expr_8637 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [joint_update_expr_8637 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8298.
 rewrite H8636.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8686 := Gval (Fuint 1) [::false].
Theorem nop_kill_step_8686 invalid old current result :
 VM.find 8298 old = Some nop_kill_value_8298 ->
 VM.find 8685 old = Some nop_kill_value_8685 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8686 result = Some nop_kill_value_8686.
Proof.
 intros H8298 H8685 Step.
 assert (Member : List.In (8686,joint_update_expr_8686) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 1175%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8686 joint_update_expr_8686 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [joint_update_expr_8686 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8298.
 rewrite H8685.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8638 := Gval (Fuint 3) [::false;false;false].
Theorem nop_kill_step_8638 invalid old current result :
 VM.find 8296 old = Some nop_kill_value_8296 ->
 VM.find 8637 old = Some nop_kill_value_8637 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8638 result = Some nop_kill_value_8638.
Proof.
 intros H8296 H8637 Step.
 assert (Member : List.In (8638,joint_update_expr_8638) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 1127%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8638 joint_update_expr_8638 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [joint_update_expr_8638 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8296.
 rewrite H8637.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8687 := Gval (Fuint 1) [::false].
Theorem nop_kill_step_8687 invalid old current result :
 VM.find 8296 old = Some nop_kill_value_8296 ->
 VM.find 8686 old = Some nop_kill_value_8686 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8687 result = Some nop_kill_value_8687.
Proof.
 intros H8296 H8686 Step.
 assert (Member : List.In (8687,joint_update_expr_8687) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 1176%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8687 joint_update_expr_8687 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [joint_update_expr_8687 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8296.
 rewrite H8686.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8639 := Gval (Fuint 3) [::false;false;false].
Theorem nop_kill_step_8639 invalid old current result :
 VM.find 8294 old = Some nop_kill_value_8294 ->
 VM.find 8638 old = Some nop_kill_value_8638 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8639 result = Some nop_kill_value_8639.
Proof.
 intros H8294 H8638 Step.
 assert (Member : List.In (8639,joint_update_expr_8639) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 1128%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8639 joint_update_expr_8639 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [joint_update_expr_8639 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8294.
 rewrite H8638.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8688 := Gval (Fuint 1) [::false].
Theorem nop_kill_step_8688 invalid old current result :
 VM.find 8294 old = Some nop_kill_value_8294 ->
 VM.find 8687 old = Some nop_kill_value_8687 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8688 result = Some nop_kill_value_8688.
Proof.
 intros H8294 H8687 Step.
 assert (Member : List.In (8688,joint_update_expr_8688) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 1177%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8688 joint_update_expr_8688 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [joint_update_expr_8688 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8294.
 rewrite H8687.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8640 := Gval (Fuint 3) [::false;false;false].
Theorem nop_kill_step_8640 invalid old current result :
 VM.find 8292 old = Some nop_kill_value_8292 ->
 VM.find 8639 old = Some nop_kill_value_8639 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8640 result = Some nop_kill_value_8640.
Proof.
 intros H8292 H8639 Step.
 assert (Member : List.In (8640,joint_update_expr_8640) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 1129%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8640 joint_update_expr_8640 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [joint_update_expr_8640 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8292.
 rewrite H8639.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8689 := Gval (Fuint 1) [::false].
Theorem nop_kill_step_8689 invalid old current result :
 VM.find 8292 old = Some nop_kill_value_8292 ->
 VM.find 8688 old = Some nop_kill_value_8688 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8689 result = Some nop_kill_value_8689.
Proof.
 intros H8292 H8688 Step.
 assert (Member : List.In (8689,joint_update_expr_8689) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 1178%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8689 joint_update_expr_8689 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [joint_update_expr_8689 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8292.
 rewrite H8688.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8641 := Gval (Fuint 3) [::false;false;false].
Theorem nop_kill_step_8641 invalid old current result :
 VM.find 8290 old = Some nop_kill_value_8290 ->
 VM.find 8640 old = Some nop_kill_value_8640 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8641 result = Some nop_kill_value_8641.
Proof.
 intros H8290 H8640 Step.
 assert (Member : List.In (8641,joint_update_expr_8641) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 1130%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8641 joint_update_expr_8641 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [joint_update_expr_8641 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8290.
 rewrite H8640.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8690 := Gval (Fuint 1) [::false].
Theorem nop_kill_step_8690 invalid old current result :
 VM.find 8290 old = Some nop_kill_value_8290 ->
 VM.find 8689 old = Some nop_kill_value_8689 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8690 result = Some nop_kill_value_8690.
Proof.
 intros H8290 H8689 Step.
 assert (Member : List.In (8690,joint_update_expr_8690) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 1179%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8690 joint_update_expr_8690 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [joint_update_expr_8690 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8290.
 rewrite H8689.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8642 := Gval (Fuint 3) [::false;false;false].
Theorem nop_kill_step_8642 invalid old current result :
 VM.find 8288 old = Some nop_kill_value_8288 ->
 VM.find 8641 old = Some nop_kill_value_8641 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8642 result = Some nop_kill_value_8642.
Proof.
 intros H8288 H8641 Step.
 assert (Member : List.In (8642,joint_update_expr_8642) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 1131%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8642 joint_update_expr_8642 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [joint_update_expr_8642 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8288.
 rewrite H8641.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8691 := Gval (Fuint 1) [::false].
Theorem nop_kill_step_8691 invalid old current result :
 VM.find 8288 old = Some nop_kill_value_8288 ->
 VM.find 8690 old = Some nop_kill_value_8690 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8691 result = Some nop_kill_value_8691.
Proof.
 intros H8288 H8690 Step.
 assert (Member : List.In (8691,joint_update_expr_8691) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 1180%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8691 joint_update_expr_8691 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [joint_update_expr_8691 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8288.
 rewrite H8690.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8643 := Gval (Fuint 3) [::false;false;false].
Theorem nop_kill_step_8643 invalid old current result :
 VM.find 8286 old = Some nop_kill_value_8286 ->
 VM.find 8642 old = Some nop_kill_value_8642 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8643 result = Some nop_kill_value_8643.
Proof.
 intros H8286 H8642 Step.
 assert (Member : List.In (8643,joint_update_expr_8643) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 1132%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8643 joint_update_expr_8643 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [joint_update_expr_8643 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8286.
 rewrite H8642.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8692 := Gval (Fuint 1) [::false].
Theorem nop_kill_step_8692 invalid old current result :
 VM.find 8286 old = Some nop_kill_value_8286 ->
 VM.find 8691 old = Some nop_kill_value_8691 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8692 result = Some nop_kill_value_8692.
Proof.
 intros H8286 H8691 Step.
 assert (Member : List.In (8692,joint_update_expr_8692) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 1181%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8692 joint_update_expr_8692 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [joint_update_expr_8692 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8286.
 rewrite H8691.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8644 := Gval (Fuint 3) [::false;false;false].
Theorem nop_kill_step_8644 invalid old current result :
 VM.find 8284 old = Some nop_kill_value_8284 ->
 VM.find 8643 old = Some nop_kill_value_8643 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8644 result = Some nop_kill_value_8644.
Proof.
 intros H8284 H8643 Step.
 assert (Member : List.In (8644,joint_update_expr_8644) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 1133%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8644 joint_update_expr_8644 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [joint_update_expr_8644 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8284.
 rewrite H8643.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8693 := Gval (Fuint 1) [::false].
Theorem nop_kill_step_8693 invalid old current result :
 VM.find 8284 old = Some nop_kill_value_8284 ->
 VM.find 8692 old = Some nop_kill_value_8692 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8693 result = Some nop_kill_value_8693.
Proof.
 intros H8284 H8692 Step.
 assert (Member : List.In (8693,joint_update_expr_8693) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 1182%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8693 joint_update_expr_8693 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [joint_update_expr_8693 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8284.
 rewrite H8692.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8645 := Gval (Fuint 3) [::false;false;false].
Theorem nop_kill_step_8645 invalid old current result :
 VM.find 8282 old = Some nop_kill_value_8282 ->
 VM.find 8644 old = Some nop_kill_value_8644 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8645 result = Some nop_kill_value_8645.
Proof.
 intros H8282 H8644 Step.
 assert (Member : List.In (8645,joint_update_expr_8645) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 1134%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8645 joint_update_expr_8645 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [joint_update_expr_8645 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8282.
 rewrite H8644.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8694 := Gval (Fuint 1) [::false].
Theorem nop_kill_step_8694 invalid old current result :
 VM.find 8282 old = Some nop_kill_value_8282 ->
 VM.find 8693 old = Some nop_kill_value_8693 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8694 result = Some nop_kill_value_8694.
Proof.
 intros H8282 H8693 Step.
 assert (Member : List.In (8694,joint_update_expr_8694) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 1183%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8694 joint_update_expr_8694 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [joint_update_expr_8694 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8282.
 rewrite H8693.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8646 := Gval (Fuint 3) [::false;false;false].
Theorem nop_kill_step_8646 invalid old current result :
 VM.find 8280 old = Some nop_kill_value_8280 ->
 VM.find 8645 old = Some nop_kill_value_8645 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8646 result = Some nop_kill_value_8646.
Proof.
 intros H8280 H8645 Step.
 assert (Member : List.In (8646,joint_update_expr_8646) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 1135%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8646 joint_update_expr_8646 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [joint_update_expr_8646 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8280.
 rewrite H8645.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8695 := Gval (Fuint 1) [::false].
Theorem nop_kill_step_8695 invalid old current result :
 VM.find 8280 old = Some nop_kill_value_8280 ->
 VM.find 8694 old = Some nop_kill_value_8694 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8695 result = Some nop_kill_value_8695.
Proof.
 intros H8280 H8694 Step.
 assert (Member : List.In (8695,joint_update_expr_8695) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 1184%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8695 joint_update_expr_8695 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [joint_update_expr_8695 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8280.
 rewrite H8694.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8647 := Gval (Fuint 3) [::false;false;false].
Theorem nop_kill_step_8647 invalid old current result :
 VM.find 8278 old = Some nop_kill_value_8278 ->
 VM.find 8646 old = Some nop_kill_value_8646 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8647 result = Some nop_kill_value_8647.
Proof.
 intros H8278 H8646 Step.
 assert (Member : List.In (8647,joint_update_expr_8647) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 1136%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8647 joint_update_expr_8647 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [joint_update_expr_8647 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8278.
 rewrite H8646.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8696 := Gval (Fuint 1) [::false].
Theorem nop_kill_step_8696 invalid old current result :
 VM.find 8278 old = Some nop_kill_value_8278 ->
 VM.find 8695 old = Some nop_kill_value_8695 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8696 result = Some nop_kill_value_8696.
Proof.
 intros H8278 H8695 Step.
 assert (Member : List.In (8696,joint_update_expr_8696) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 1185%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8696 joint_update_expr_8696 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [joint_update_expr_8696 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8278.
 rewrite H8695.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8648 := Gval (Fuint 3) [::false;false;false].
Theorem nop_kill_step_8648 invalid old current result :
 VM.find 8276 old = Some nop_kill_value_8276 ->
 VM.find 8647 old = Some nop_kill_value_8647 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8648 result = Some nop_kill_value_8648.
Proof.
 intros H8276 H8647 Step.
 assert (Member : List.In (8648,joint_update_expr_8648) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 1137%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8648 joint_update_expr_8648 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [joint_update_expr_8648 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8276.
 rewrite H8647.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8697 := Gval (Fuint 1) [::false].
Theorem nop_kill_step_8697 invalid old current result :
 VM.find 8276 old = Some nop_kill_value_8276 ->
 VM.find 8696 old = Some nop_kill_value_8696 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8697 result = Some nop_kill_value_8697.
Proof.
 intros H8276 H8696 Step.
 assert (Member : List.In (8697,joint_update_expr_8697) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 1186%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8697 joint_update_expr_8697 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [joint_update_expr_8697 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8276.
 rewrite H8696.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8649 := Gval (Fuint 3) [::false;false;false].
Theorem nop_kill_step_8649 invalid old current result :
 VM.find 8274 old = Some nop_kill_value_8274 ->
 VM.find 8648 old = Some nop_kill_value_8648 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8649 result = Some nop_kill_value_8649.
Proof.
 intros H8274 H8648 Step.
 assert (Member : List.In (8649,joint_update_expr_8649) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 1138%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8649 joint_update_expr_8649 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [joint_update_expr_8649 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8274.
 rewrite H8648.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8698 := Gval (Fuint 1) [::false].
Theorem nop_kill_step_8698 invalid old current result :
 VM.find 8274 old = Some nop_kill_value_8274 ->
 VM.find 8697 old = Some nop_kill_value_8697 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8698 result = Some nop_kill_value_8698.
Proof.
 intros H8274 H8697 Step.
 assert (Member : List.In (8698,joint_update_expr_8698) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 1187%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8698 joint_update_expr_8698 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [joint_update_expr_8698 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8274.
 rewrite H8697.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8650 := Gval (Fuint 3) [::false;false;false].
Theorem nop_kill_step_8650 invalid old current result :
 VM.find 8272 old = Some nop_kill_value_8272 ->
 VM.find 8649 old = Some nop_kill_value_8649 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8650 result = Some nop_kill_value_8650.
Proof.
 intros H8272 H8649 Step.
 assert (Member : List.In (8650,joint_update_expr_8650) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 1139%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8650 joint_update_expr_8650 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [joint_update_expr_8650 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8272.
 rewrite H8649.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8699 := Gval (Fuint 1) [::false].
Theorem nop_kill_step_8699 invalid old current result :
 VM.find 8272 old = Some nop_kill_value_8272 ->
 VM.find 8698 old = Some nop_kill_value_8698 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8699 result = Some nop_kill_value_8699.
Proof.
 intros H8272 H8698 Step.
 assert (Member : List.In (8699,joint_update_expr_8699) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 1188%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8699 joint_update_expr_8699 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [joint_update_expr_8699 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8272.
 rewrite H8698.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8651 := Gval (Fuint 3) [::false;false;false].
Theorem nop_kill_step_8651 invalid old current result :
 VM.find 8270 old = Some nop_kill_value_8270 ->
 VM.find 8650 old = Some nop_kill_value_8650 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8651 result = Some nop_kill_value_8651.
Proof.
 intros H8270 H8650 Step.
 assert (Member : List.In (8651,joint_update_expr_8651) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 1140%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8651 joint_update_expr_8651 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [joint_update_expr_8651 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8270.
 rewrite H8650.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8700 := Gval (Fuint 1) [::false].
Theorem nop_kill_step_8700 invalid old current result :
 VM.find 8270 old = Some nop_kill_value_8270 ->
 VM.find 8699 old = Some nop_kill_value_8699 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8700 result = Some nop_kill_value_8700.
Proof.
 intros H8270 H8699 Step.
 assert (Member : List.In (8700,joint_update_expr_8700) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 1189%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8700 joint_update_expr_8700 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [joint_update_expr_8700 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8270.
 rewrite H8699.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8652 := Gval (Fuint 3) [::false;false;false].
Theorem nop_kill_step_8652 invalid old current result :
 VM.find 8268 old = Some nop_kill_value_8268 ->
 VM.find 8651 old = Some nop_kill_value_8651 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8652 result = Some nop_kill_value_8652.
Proof.
 intros H8268 H8651 Step.
 assert (Member : List.In (8652,joint_update_expr_8652) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 1141%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8652 joint_update_expr_8652 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [joint_update_expr_8652 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8268.
 rewrite H8651.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8701 := Gval (Fuint 1) [::false].
Theorem nop_kill_step_8701 invalid old current result :
 VM.find 8268 old = Some nop_kill_value_8268 ->
 VM.find 8700 old = Some nop_kill_value_8700 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8701 result = Some nop_kill_value_8701.
Proof.
 intros H8268 H8700 Step.
 assert (Member : List.In (8701,joint_update_expr_8701) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 1190%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8701 joint_update_expr_8701 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [joint_update_expr_8701 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8268.
 rewrite H8700.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8653 := Gval (Fuint 3) [::false;false;false].
Theorem nop_kill_step_8653 invalid old current result :
 VM.find 8266 old = Some nop_kill_value_8266 ->
 VM.find 8652 old = Some nop_kill_value_8652 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8653 result = Some nop_kill_value_8653.
Proof.
 intros H8266 H8652 Step.
 assert (Member : List.In (8653,joint_update_expr_8653) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 1142%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8653 joint_update_expr_8653 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [joint_update_expr_8653 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8266.
 rewrite H8652.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8702 := Gval (Fuint 1) [::false].
Theorem nop_kill_step_8702 invalid old current result :
 VM.find 8266 old = Some nop_kill_value_8266 ->
 VM.find 8701 old = Some nop_kill_value_8701 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8702 result = Some nop_kill_value_8702.
Proof.
 intros H8266 H8701 Step.
 assert (Member : List.In (8702,joint_update_expr_8702) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 1191%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8702 joint_update_expr_8702 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [joint_update_expr_8702 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8266.
 rewrite H8701.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8654 := Gval (Fuint 3) [::false;false;false].
Theorem nop_kill_step_8654 invalid old current result :
 VM.find 8264 old = Some nop_kill_value_8264 ->
 VM.find 8653 old = Some nop_kill_value_8653 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8654 result = Some nop_kill_value_8654.
Proof.
 intros H8264 H8653 Step.
 assert (Member : List.In (8654,joint_update_expr_8654) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 1143%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8654 joint_update_expr_8654 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [joint_update_expr_8654 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8264.
 rewrite H8653.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8703 := Gval (Fuint 1) [::false].
Theorem nop_kill_step_8703 invalid old current result :
 VM.find 8264 old = Some nop_kill_value_8264 ->
 VM.find 8702 old = Some nop_kill_value_8702 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8703 result = Some nop_kill_value_8703.
Proof.
 intros H8264 H8702 Step.
 assert (Member : List.In (8703,joint_update_expr_8703) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 1192%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8703 joint_update_expr_8703 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [joint_update_expr_8703 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8264.
 rewrite H8702.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_8256 := Gval (Fuint 3) [::false;false;false].
Theorem nop_kill_step_8256 invalid old current result :
 VM.find 8654 old = Some nop_kill_value_8654 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8256 result = Some nop_kill_value_8256.
Proof.
 intros H8654 Step.
 apply (declared_connection_value 9016 flat_statements joint_update_connection_8256_decl joint_update_connection_8256_mid joint_update_connection_8256_tail
 8256 8654 3 nop_kill_value_8654 nop_kill_value_8256 invalid flat_memories old current result
 joint_update_connection_8256_position joint_update_connection_8256_split joint_update_connection_8256_straight joint_update_connection_8256_mid_safe joint_update_connection_8256_tail_safe joint_update_connection_8256_nonregister (Logic.eq_refl _) H8654);
 [vm_compute;reflexivity|exact Step].
Qed.
Definition nop_kill_value_8998 := Gval (Fuint 1) [::false].
Theorem nop_kill_step_8998 invalid old current result :
 VM.find 8703 old = Some nop_kill_value_8703 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8998 result = Some nop_kill_value_8998.
Proof.
 intros H8703 Step.
 assert (Member : List.In (8998,joint_update_expr_8998) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 1389%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 8998 joint_update_expr_8998 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [joint_update_expr_8998 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite H8703.
 vm_compute. reflexivity.
Qed.
Definition nop_kill_value_90 := Gval (Fuint 3) [::false;false;false].
Theorem nop_kill_step_90 invalid old current result :
 VM.find 8256 old = Some nop_kill_value_8256 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 90 result = Some nop_kill_value_90.
Proof.
 intros H8256 Step.
 apply (declared_connection_value 67 flat_statements joint_update_connection_90_decl joint_update_connection_90_mid joint_update_connection_90_tail
 90 8256 3 nop_kill_value_8256 nop_kill_value_90 invalid flat_memories old current result
 joint_update_connection_90_position joint_update_connection_90_split joint_update_connection_90_straight joint_update_connection_90_mid_safe joint_update_connection_90_tail_safe joint_update_connection_90_nonregister (Logic.eq_refl _) H8256);
 [vm_compute;reflexivity|exact Step].
Qed.
Definition nop_kill_value_8251 := Gval (Fuint 1) [::false].
Theorem nop_kill_step_8251 invalid old current result :
 VM.find 8998 old = Some nop_kill_value_8998 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8251 result = Some nop_kill_value_8251.
Proof.
 intros H8998 Step.
 apply (declared_connection_value 9011 flat_statements joint_update_connection_8251_decl joint_update_connection_8251_mid joint_update_connection_8251_tail
 8251 8998 1 nop_kill_value_8998 nop_kill_value_8251 invalid flat_memories old current result
 joint_update_connection_8251_position joint_update_connection_8251_split joint_update_connection_8251_straight joint_update_connection_8251_mid_safe joint_update_connection_8251_tail_safe joint_update_connection_8251_nonregister (Logic.eq_refl _) H8998);
 [vm_compute;reflexivity|exact Step].
Qed.
Definition nop_kill_value_85 := Gval (Fuint 1) [::false].
Theorem nop_kill_step_85 invalid old current result :
 VM.find 8251 old = Some nop_kill_value_8251 ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 85 result = Some nop_kill_value_85.
Proof.
 intros H8251 Step.
 apply (declared_connection_value 62 flat_statements joint_update_connection_85_decl joint_update_connection_85_mid joint_update_connection_85_tail
 85 8251 1 nop_kill_value_8251 nop_kill_value_85 invalid flat_memories old current result
 joint_update_connection_85_position joint_update_connection_85_split joint_update_connection_85_straight joint_update_connection_85_mid_safe joint_update_connection_85_tail_safe joint_update_connection_85_nonregister (Logic.eq_refl _) H8251);
 [vm_compute;reflexivity|exact Step].
Qed.
Print Assumptions nop_kill_step_85.
Print Assumptions nop_kill_step_90.
