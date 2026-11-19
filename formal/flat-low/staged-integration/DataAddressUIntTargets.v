Require Import CoreSocModel ComparisonNodes ConcreteExtractNode DataAddressPositionCertificate DataAddressSafetyCertificate DataAddressExpressionCertificates FormalDataReaderAddresses.
From Coq Require Import List ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Lemma data_address_target_member_9186 : List.In (9186, address_expr_9186) data_address_expected_nodes.
Proof.
 apply (@List.nth_error_In _ data_address_expected_nodes 444 (9186, address_expr_9186)).
 vm_compute. reflexivity.
Qed.
Lemma data_address_target_uint_9186 inputs path old current result :
 (exists ground bits, VM.find 9182 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists width bits, VM.find 9186 result = Some (Gval (Fuint width) bits).
Proof.
 intros Source Step.
 eapply selected_extract_node_concrete;
 [exact data_address_actual_node_expressions|exact data_address_actual_nodes_safe|
 exact data_address_target_member_9186|exact Source|exact Step].
Qed.
Lemma data_address_target_member_9194 : List.In (9194, address_expr_9194) data_address_expected_nodes.
Proof.
 apply (@List.nth_error_In _ data_address_expected_nodes 445 (9194, address_expr_9194)).
 vm_compute. reflexivity.
Qed.
Lemma data_address_target_uint_9194 inputs path old current result :
 (exists ground bits, VM.find 9182 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists width bits, VM.find 9194 result = Some (Gval (Fuint width) bits).
Proof.
 intros Source Step.
 eapply selected_extract_node_concrete;
 [exact data_address_actual_node_expressions|exact data_address_actual_nodes_safe|
 exact data_address_target_member_9194|exact Source|exact Step].
Qed.
Lemma data_address_target_member_9202 : List.In (9202, address_expr_9202) data_address_expected_nodes.
Proof.
 apply (@List.nth_error_In _ data_address_expected_nodes 446 (9202, address_expr_9202)).
 vm_compute. reflexivity.
Qed.
Lemma data_address_target_uint_9202 inputs path old current result :
 (exists ground bits, VM.find 9182 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists width bits, VM.find 9202 result = Some (Gval (Fuint width) bits).
Proof.
 intros Source Step.
 eapply selected_extract_node_concrete;
 [exact data_address_actual_node_expressions|exact data_address_actual_nodes_safe|
 exact data_address_target_member_9202|exact Source|exact Step].
Qed.
Lemma data_address_target_member_9210 : List.In (9210, address_expr_9210) data_address_expected_nodes.
Proof.
 apply (@List.nth_error_In _ data_address_expected_nodes 447 (9210, address_expr_9210)).
 vm_compute. reflexivity.
Qed.
Lemma data_address_target_uint_9210 inputs path old current result :
 (exists ground bits, VM.find 9182 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists width bits, VM.find 9210 result = Some (Gval (Fuint width) bits).
Proof.
 intros Source Step.
 eapply selected_extract_node_concrete;
 [exact data_address_actual_node_expressions|exact data_address_actual_nodes_safe|
 exact data_address_target_member_9210|exact Source|exact Step].
Qed.
Lemma data_address_target_member_9221 : List.In (9221, address_expr_9221) data_address_expected_nodes.
Proof.
 apply (@List.nth_error_In _ data_address_expected_nodes 452 (9221, address_expr_9221)).
 vm_compute. reflexivity.
Qed.
Lemma data_address_target_uint_9221 inputs path old current result :
 (exists ground bits, VM.find 9182 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists width bits, VM.find 9221 result = Some (Gval (Fuint width) bits).
Proof.
 intros Source Step.
 eapply selected_extract_node_concrete;
 [exact data_address_actual_node_expressions|exact data_address_actual_nodes_safe|
 exact data_address_target_member_9221|exact Source|exact Step].
Qed.
Theorem data_address_sources_from_9182 inputs path old current result :
 (exists ground bits, VM.find 9182 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 data_reader_sources_concrete result.
Proof.
 intros Source Step node Member.
 repeat destruct Member as [Equal|Member]; try contradiction; subst node.
 - exact (data_address_target_uint_9186 inputs path old current result Source Step).
 - exact (data_address_target_uint_9194 inputs path old current result Source Step).
 - exact (data_address_target_uint_9202 inputs path old current result Source Step).
 - exact (data_address_target_uint_9210 inputs path old current result Source Step).
 - exact (data_address_target_uint_9221 inputs path old current result Source Step).
Qed.
Print Assumptions data_address_sources_from_9182.
