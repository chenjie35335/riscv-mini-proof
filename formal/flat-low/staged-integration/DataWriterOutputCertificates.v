Require Import CoreSocModel ComparisonNodes SelectedNodeConcreteGroundOutput DataWriterNodePositions DataWriterExpressionCertificates.
From Coq Require Import ZArith List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Lemma data_writer_node_output_7827 inputs path old current result :
 (exists ground bits, VM.find 1155 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists ground bits, VM.find 7827 result = Some (Gval ground bits).
Proof.
 intros H1155 Step.
 eapply (selected_node_concrete_ground_output data_writer_node_offsets flat_statements data_writer_expected_nodes 7827 writer_expr_7827 inputs path flat_memories old current result).
 - exact data_writer_node_positions.
 - exact data_writer_node_safety.
 - apply (@List.nth_error_In _ data_writer_expected_nodes 0 (7827,writer_expr_7827)). vm_compute. reflexivity.
 - apply writer_ready_7827; assumption.
 - exact Step.
Qed.
Lemma data_writer_node_output_7828 inputs path old current result :
 (exists ground bits, VM.find 7827 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists ground bits, VM.find 7828 result = Some (Gval ground bits).
Proof.
 intros H7827 Step.
 eapply (selected_node_concrete_ground_output data_writer_node_offsets flat_statements data_writer_expected_nodes 7828 writer_expr_7828 inputs path flat_memories old current result).
 - exact data_writer_node_positions.
 - exact data_writer_node_safety.
 - apply (@List.nth_error_In _ data_writer_expected_nodes 1 (7828,writer_expr_7828)). vm_compute. reflexivity.
 - apply writer_ready_7828; assumption.
 - exact Step.
Qed.
Lemma data_writer_node_output_7829 inputs path old current result :
 (exists ground bits, VM.find 1155 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists ground bits, VM.find 7829 result = Some (Gval ground bits).
Proof.
 intros H1155 Step.
 eapply (selected_node_concrete_ground_output data_writer_node_offsets flat_statements data_writer_expected_nodes 7829 writer_expr_7829 inputs path flat_memories old current result).
 - exact data_writer_node_positions.
 - exact data_writer_node_safety.
 - apply (@List.nth_error_In _ data_writer_expected_nodes 2 (7829,writer_expr_7829)). vm_compute. reflexivity.
 - apply writer_ready_7829; assumption.
 - exact Step.
Qed.
Lemma data_writer_node_output_7830 inputs path old current result :
 (exists ground bits, VM.find 7829 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists ground bits, VM.find 7830 result = Some (Gval ground bits).
Proof.
 intros H7829 Step.
 eapply (selected_node_concrete_ground_output data_writer_node_offsets flat_statements data_writer_expected_nodes 7830 writer_expr_7830 inputs path flat_memories old current result).
 - exact data_writer_node_positions.
 - exact data_writer_node_safety.
 - apply (@List.nth_error_In _ data_writer_expected_nodes 3 (7830,writer_expr_7830)). vm_compute. reflexivity.
 - apply writer_ready_7830; assumption.
 - exact Step.
Qed.
Lemma data_writer_node_output_7831 inputs path old current result :
 (exists ground bits, VM.find 7828 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 7830 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists ground bits, VM.find 7831 result = Some (Gval ground bits).
Proof.
 intros H7828 H7830 Step.
 eapply (selected_node_concrete_ground_output data_writer_node_offsets flat_statements data_writer_expected_nodes 7831 writer_expr_7831 inputs path flat_memories old current result).
 - exact data_writer_node_positions.
 - exact data_writer_node_safety.
 - apply (@List.nth_error_In _ data_writer_expected_nodes 4 (7831,writer_expr_7831)). vm_compute. reflexivity.
 - apply writer_ready_7831; assumption.
 - exact Step.
Qed.
Lemma data_writer_node_output_7832 inputs path old current result :
 (exists ground bits, VM.find 7765 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists ground bits, VM.find 7832 result = Some (Gval ground bits).
Proof.
 intros H7765 Step.
 eapply (selected_node_concrete_ground_output data_writer_node_offsets flat_statements data_writer_expected_nodes 7832 writer_expr_7832 inputs path flat_memories old current result).
 - exact data_writer_node_positions.
 - exact data_writer_node_safety.
 - apply (@List.nth_error_In _ data_writer_expected_nodes 5 (7832,writer_expr_7832)). vm_compute. reflexivity.
 - apply writer_ready_7832; assumption.
 - exact Step.
Qed.
Lemma data_writer_node_output_7833 inputs path old current result :
 (exists ground bits, VM.find 91 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists ground bits, VM.find 7833 result = Some (Gval ground bits).
Proof.
 intros H91 Step.
 eapply (selected_node_concrete_ground_output data_writer_node_offsets flat_statements data_writer_expected_nodes 7833 writer_expr_7833 inputs path flat_memories old current result).
 - exact data_writer_node_positions.
 - exact data_writer_node_safety.
 - apply (@List.nth_error_In _ data_writer_expected_nodes 6 (7833,writer_expr_7833)). vm_compute. reflexivity.
 - apply writer_ready_7833; assumption.
 - exact Step.
Qed.
Lemma data_writer_node_output_7834 inputs path old current result :
 (exists ground bits, VM.find 92 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists ground bits, VM.find 7834 result = Some (Gval ground bits).
Proof.
 intros H92 Step.
 eapply (selected_node_concrete_ground_output data_writer_node_offsets flat_statements data_writer_expected_nodes 7834 writer_expr_7834 inputs path flat_memories old current result).
 - exact data_writer_node_positions.
 - exact data_writer_node_safety.
 - apply (@List.nth_error_In _ data_writer_expected_nodes 7 (7834,writer_expr_7834)). vm_compute. reflexivity.
 - apply writer_ready_7834; assumption.
 - exact Step.
Qed.
Lemma data_writer_node_output_7835 inputs path old current result :
 (exists ground bits, VM.find 7833 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 7834 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists ground bits, VM.find 7835 result = Some (Gval ground bits).
Proof.
 intros H7833 H7834 Step.
 eapply (selected_node_concrete_ground_output data_writer_node_offsets flat_statements data_writer_expected_nodes 7835 writer_expr_7835 inputs path flat_memories old current result).
 - exact data_writer_node_positions.
 - exact data_writer_node_safety.
 - apply (@List.nth_error_In _ data_writer_expected_nodes 8 (7835,writer_expr_7835)). vm_compute. reflexivity.
 - apply writer_ready_7835; assumption.
 - exact Step.
Qed.
Lemma data_writer_node_output_7836 inputs path old current result :
 (exists ground bits, VM.find 7832 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 7835 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists ground bits, VM.find 7836 result = Some (Gval ground bits).
Proof.
 intros H7832 H7835 Step.
 eapply (selected_node_concrete_ground_output data_writer_node_offsets flat_statements data_writer_expected_nodes 7836 writer_expr_7836 inputs path flat_memories old current result).
 - exact data_writer_node_positions.
 - exact data_writer_node_safety.
 - apply (@List.nth_error_In _ data_writer_expected_nodes 9 (7836,writer_expr_7836)). vm_compute. reflexivity.
 - apply writer_ready_7836; assumption.
 - exact Step.
Qed.
Lemma data_writer_node_output_7837 inputs path old current result :
 (exists ground bits, VM.find 7819 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 7831 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists ground bits, VM.find 7837 result = Some (Gval ground bits).
Proof.
 intros H7819 H7831 Step.
 eapply (selected_node_concrete_ground_output data_writer_node_offsets flat_statements data_writer_expected_nodes 7837 writer_expr_7837 inputs path flat_memories old current result).
 - exact data_writer_node_positions.
 - exact data_writer_node_safety.
 - apply (@List.nth_error_In _ data_writer_expected_nodes 10 (7837,writer_expr_7837)). vm_compute. reflexivity.
 - apply writer_ready_7837; assumption.
 - exact Step.
Qed.
Lemma data_writer_node_output_7838 inputs path old current result :
 (exists ground bits, VM.find 91 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 7754 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 7765 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists ground bits, VM.find 7838 result = Some (Gval ground bits).
Proof.
 intros H91 H7754 H7765 Step.
 eapply (selected_node_concrete_ground_output data_writer_node_offsets flat_statements data_writer_expected_nodes 7838 writer_expr_7838 inputs path flat_memories old current result).
 - exact data_writer_node_positions.
 - exact data_writer_node_safety.
 - apply (@List.nth_error_In _ data_writer_expected_nodes 11 (7838,writer_expr_7838)). vm_compute. reflexivity.
 - apply writer_ready_7838; assumption.
 - exact Step.
Qed.
Lemma data_writer_node_output_7839 inputs path old current result :
 (exists ground bits, VM.find 1155 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists ground bits, VM.find 7839 result = Some (Gval ground bits).
Proof.
 intros H1155 Step.
 eapply (selected_node_concrete_ground_output data_writer_node_offsets flat_statements data_writer_expected_nodes 7839 writer_expr_7839 inputs path flat_memories old current result).
 - exact data_writer_node_positions.
 - exact data_writer_node_safety.
 - apply (@List.nth_error_In _ data_writer_expected_nodes 12 (7839,writer_expr_7839)). vm_compute. reflexivity.
 - apply writer_ready_7839; assumption.
 - exact Step.
Qed.
Lemma data_writer_node_output_7840 inputs path old current result :
 (exists ground bits, VM.find 7839 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists ground bits, VM.find 7840 result = Some (Gval ground bits).
Proof.
 intros H7839 Step.
 eapply (selected_node_concrete_ground_output data_writer_node_offsets flat_statements data_writer_expected_nodes 7840 writer_expr_7840 inputs path flat_memories old current result).
 - exact data_writer_node_positions.
 - exact data_writer_node_safety.
 - apply (@List.nth_error_In _ data_writer_expected_nodes 13 (7840,writer_expr_7840)). vm_compute. reflexivity.
 - apply writer_ready_7840; assumption.
 - exact Step.
Qed.
Lemma data_writer_node_output_7841 inputs path old current result :
 (exists ground bits, VM.find 1155 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists ground bits, VM.find 7841 result = Some (Gval ground bits).
Proof.
 intros H1155 Step.
 eapply (selected_node_concrete_ground_output data_writer_node_offsets flat_statements data_writer_expected_nodes 7841 writer_expr_7841 inputs path flat_memories old current result).
 - exact data_writer_node_positions.
 - exact data_writer_node_safety.
 - apply (@List.nth_error_In _ data_writer_expected_nodes 14 (7841,writer_expr_7841)). vm_compute. reflexivity.
 - apply writer_ready_7841; assumption.
 - exact Step.
Qed.
Lemma data_writer_node_output_7842 inputs path old current result :
 (exists ground bits, VM.find 7841 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists ground bits, VM.find 7842 result = Some (Gval ground bits).
Proof.
 intros H7841 Step.
 eapply (selected_node_concrete_ground_output data_writer_node_offsets flat_statements data_writer_expected_nodes 7842 writer_expr_7842 inputs path flat_memories old current result).
 - exact data_writer_node_positions.
 - exact data_writer_node_safety.
 - apply (@List.nth_error_In _ data_writer_expected_nodes 15 (7842,writer_expr_7842)). vm_compute. reflexivity.
 - apply writer_ready_7842; assumption.
 - exact Step.
Qed.
Lemma data_writer_node_output_7843 inputs path old current result :
 (exists ground bits, VM.find 7838 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists ground bits, VM.find 7843 result = Some (Gval ground bits).
Proof.
 intros H7838 Step.
 eapply (selected_node_concrete_ground_output data_writer_node_offsets flat_statements data_writer_expected_nodes 7843 writer_expr_7843 inputs path flat_memories old current result).
 - exact data_writer_node_positions.
 - exact data_writer_node_safety.
 - apply (@List.nth_error_In _ data_writer_expected_nodes 16 (7843,writer_expr_7843)). vm_compute. reflexivity.
 - apply writer_ready_7843; assumption.
 - exact Step.
Qed.
Lemma data_writer_node_output_7844 inputs path old current result :
 (exists ground bits, VM.find 7843 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists ground bits, VM.find 7844 result = Some (Gval ground bits).
Proof.
 intros H7843 Step.
 eapply (selected_node_concrete_ground_output data_writer_node_offsets flat_statements data_writer_expected_nodes 7844 writer_expr_7844 inputs path flat_memories old current result).
 - exact data_writer_node_positions.
 - exact data_writer_node_safety.
 - apply (@List.nth_error_In _ data_writer_expected_nodes 17 (7844,writer_expr_7844)). vm_compute. reflexivity.
 - apply writer_ready_7844; assumption.
 - exact Step.
Qed.
Lemma data_writer_node_output_7845 inputs path old current result :
 (exists ground bits, VM.find 7838 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists ground bits, VM.find 7845 result = Some (Gval ground bits).
Proof.
 intros H7838 Step.
 eapply (selected_node_concrete_ground_output data_writer_node_offsets flat_statements data_writer_expected_nodes 7845 writer_expr_7845 inputs path flat_memories old current result).
 - exact data_writer_node_positions.
 - exact data_writer_node_safety.
 - apply (@List.nth_error_In _ data_writer_expected_nodes 18 (7845,writer_expr_7845)). vm_compute. reflexivity.
 - apply writer_ready_7845; assumption.
 - exact Step.
Qed.
Lemma data_writer_node_output_7846 inputs path old current result :
 (exists ground bits, VM.find 7840 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 7844 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 7845 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists ground bits, VM.find 7846 result = Some (Gval ground bits).
Proof.
 intros H7840 H7844 H7845 Step.
 eapply (selected_node_concrete_ground_output data_writer_node_offsets flat_statements data_writer_expected_nodes 7846 writer_expr_7846 inputs path flat_memories old current result).
 - exact data_writer_node_positions.
 - exact data_writer_node_safety.
 - apply (@List.nth_error_In _ data_writer_expected_nodes 19 (7846,writer_expr_7846)). vm_compute. reflexivity.
 - apply writer_ready_7846; assumption.
 - exact Step.
Qed.
Lemma data_writer_node_output_7847 inputs path old current result :
 (exists ground bits, VM.find 7838 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists ground bits, VM.find 7847 result = Some (Gval ground bits).
Proof.
 intros H7838 Step.
 eapply (selected_node_concrete_ground_output data_writer_node_offsets flat_statements data_writer_expected_nodes 7847 writer_expr_7847 inputs path flat_memories old current result).
 - exact data_writer_node_positions.
 - exact data_writer_node_safety.
 - apply (@List.nth_error_In _ data_writer_expected_nodes 20 (7847,writer_expr_7847)). vm_compute. reflexivity.
 - apply writer_ready_7847; assumption.
 - exact Step.
Qed.
Lemma data_writer_node_output_7848 inputs path old current result :
 (exists ground bits, VM.find 7842 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 7846 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 7847 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists ground bits, VM.find 7848 result = Some (Gval ground bits).
Proof.
 intros H7842 H7846 H7847 Step.
 eapply (selected_node_concrete_ground_output data_writer_node_offsets flat_statements data_writer_expected_nodes 7848 writer_expr_7848 inputs path flat_memories old current result).
 - exact data_writer_node_positions.
 - exact data_writer_node_safety.
 - apply (@List.nth_error_In _ data_writer_expected_nodes 21 (7848,writer_expr_7848)). vm_compute. reflexivity.
 - apply writer_ready_7848; assumption.
 - exact Step.
Qed.
Lemma data_writer_node_output_8704 inputs path old current result :
 (exists ground bits, VM.find 8360 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists ground bits, VM.find 8704 result = Some (Gval ground bits).
Proof.
 intros H8360 Step.
 eapply (selected_node_concrete_ground_output data_writer_node_offsets flat_statements data_writer_expected_nodes 8704 writer_expr_8704 inputs path flat_memories old current result).
 - exact data_writer_node_positions.
 - exact data_writer_node_safety.
 - apply (@List.nth_error_In _ data_writer_expected_nodes 22 (8704,writer_expr_8704)). vm_compute. reflexivity.
 - apply writer_ready_8704; assumption.
 - exact Step.
Qed.
Lemma data_writer_node_output_8705 inputs path old current result :
 (exists ground bits, VM.find 8358 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8704 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists ground bits, VM.find 8705 result = Some (Gval ground bits).
Proof.
 intros H8358 H8704 Step.
 eapply (selected_node_concrete_ground_output data_writer_node_offsets flat_statements data_writer_expected_nodes 8705 writer_expr_8705 inputs path flat_memories old current result).
 - exact data_writer_node_positions.
 - exact data_writer_node_safety.
 - apply (@List.nth_error_In _ data_writer_expected_nodes 23 (8705,writer_expr_8705)). vm_compute. reflexivity.
 - apply writer_ready_8705; assumption.
 - exact Step.
Qed.
Lemma data_writer_node_output_8706 inputs path old current result :
 (exists ground bits, VM.find 8356 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8705 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists ground bits, VM.find 8706 result = Some (Gval ground bits).
Proof.
 intros H8356 H8705 Step.
 eapply (selected_node_concrete_ground_output data_writer_node_offsets flat_statements data_writer_expected_nodes 8706 writer_expr_8706 inputs path flat_memories old current result).
 - exact data_writer_node_positions.
 - exact data_writer_node_safety.
 - apply (@List.nth_error_In _ data_writer_expected_nodes 24 (8706,writer_expr_8706)). vm_compute. reflexivity.
 - apply writer_ready_8706; assumption.
 - exact Step.
Qed.
Lemma data_writer_node_output_8707 inputs path old current result :
 (exists ground bits, VM.find 8354 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8706 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists ground bits, VM.find 8707 result = Some (Gval ground bits).
Proof.
 intros H8354 H8706 Step.
 eapply (selected_node_concrete_ground_output data_writer_node_offsets flat_statements data_writer_expected_nodes 8707 writer_expr_8707 inputs path flat_memories old current result).
 - exact data_writer_node_positions.
 - exact data_writer_node_safety.
 - apply (@List.nth_error_In _ data_writer_expected_nodes 25 (8707,writer_expr_8707)). vm_compute. reflexivity.
 - apply writer_ready_8707; assumption.
 - exact Step.
Qed.
Lemma data_writer_node_output_8708 inputs path old current result :
 (exists ground bits, VM.find 8352 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8707 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists ground bits, VM.find 8708 result = Some (Gval ground bits).
Proof.
 intros H8352 H8707 Step.
 eapply (selected_node_concrete_ground_output data_writer_node_offsets flat_statements data_writer_expected_nodes 8708 writer_expr_8708 inputs path flat_memories old current result).
 - exact data_writer_node_positions.
 - exact data_writer_node_safety.
 - apply (@List.nth_error_In _ data_writer_expected_nodes 26 (8708,writer_expr_8708)). vm_compute. reflexivity.
 - apply writer_ready_8708; assumption.
 - exact Step.
Qed.
Lemma data_writer_node_output_8709 inputs path old current result :
 (exists ground bits, VM.find 8350 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8708 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists ground bits, VM.find 8709 result = Some (Gval ground bits).
Proof.
 intros H8350 H8708 Step.
 eapply (selected_node_concrete_ground_output data_writer_node_offsets flat_statements data_writer_expected_nodes 8709 writer_expr_8709 inputs path flat_memories old current result).
 - exact data_writer_node_positions.
 - exact data_writer_node_safety.
 - apply (@List.nth_error_In _ data_writer_expected_nodes 27 (8709,writer_expr_8709)). vm_compute. reflexivity.
 - apply writer_ready_8709; assumption.
 - exact Step.
Qed.
Lemma data_writer_node_output_8710 inputs path old current result :
 (exists ground bits, VM.find 8348 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8709 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists ground bits, VM.find 8710 result = Some (Gval ground bits).
Proof.
 intros H8348 H8709 Step.
 eapply (selected_node_concrete_ground_output data_writer_node_offsets flat_statements data_writer_expected_nodes 8710 writer_expr_8710 inputs path flat_memories old current result).
 - exact data_writer_node_positions.
 - exact data_writer_node_safety.
 - apply (@List.nth_error_In _ data_writer_expected_nodes 28 (8710,writer_expr_8710)). vm_compute. reflexivity.
 - apply writer_ready_8710; assumption.
 - exact Step.
Qed.
Lemma data_writer_node_output_8711 inputs path old current result :
 (exists ground bits, VM.find 8346 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8710 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists ground bits, VM.find 8711 result = Some (Gval ground bits).
Proof.
 intros H8346 H8710 Step.
 eapply (selected_node_concrete_ground_output data_writer_node_offsets flat_statements data_writer_expected_nodes 8711 writer_expr_8711 inputs path flat_memories old current result).
 - exact data_writer_node_positions.
 - exact data_writer_node_safety.
 - apply (@List.nth_error_In _ data_writer_expected_nodes 29 (8711,writer_expr_8711)). vm_compute. reflexivity.
 - apply writer_ready_8711; assumption.
 - exact Step.
Qed.
Lemma data_writer_node_output_8712 inputs path old current result :
 (exists ground bits, VM.find 8344 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8711 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists ground bits, VM.find 8712 result = Some (Gval ground bits).
Proof.
 intros H8344 H8711 Step.
 eapply (selected_node_concrete_ground_output data_writer_node_offsets flat_statements data_writer_expected_nodes 8712 writer_expr_8712 inputs path flat_memories old current result).
 - exact data_writer_node_positions.
 - exact data_writer_node_safety.
 - apply (@List.nth_error_In _ data_writer_expected_nodes 30 (8712,writer_expr_8712)). vm_compute. reflexivity.
 - apply writer_ready_8712; assumption.
 - exact Step.
Qed.
Lemma data_writer_node_output_8713 inputs path old current result :
 (exists ground bits, VM.find 8342 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8712 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists ground bits, VM.find 8713 result = Some (Gval ground bits).
Proof.
 intros H8342 H8712 Step.
 eapply (selected_node_concrete_ground_output data_writer_node_offsets flat_statements data_writer_expected_nodes 8713 writer_expr_8713 inputs path flat_memories old current result).
 - exact data_writer_node_positions.
 - exact data_writer_node_safety.
 - apply (@List.nth_error_In _ data_writer_expected_nodes 31 (8713,writer_expr_8713)). vm_compute. reflexivity.
 - apply writer_ready_8713; assumption.
 - exact Step.
Qed.
Lemma data_writer_node_output_8714 inputs path old current result :
 (exists ground bits, VM.find 8340 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8713 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists ground bits, VM.find 8714 result = Some (Gval ground bits).
Proof.
 intros H8340 H8713 Step.
 eapply (selected_node_concrete_ground_output data_writer_node_offsets flat_statements data_writer_expected_nodes 8714 writer_expr_8714 inputs path flat_memories old current result).
 - exact data_writer_node_positions.
 - exact data_writer_node_safety.
 - apply (@List.nth_error_In _ data_writer_expected_nodes 32 (8714,writer_expr_8714)). vm_compute. reflexivity.
 - apply writer_ready_8714; assumption.
 - exact Step.
Qed.
Lemma data_writer_node_output_8715 inputs path old current result :
 (exists ground bits, VM.find 8338 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8714 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists ground bits, VM.find 8715 result = Some (Gval ground bits).
Proof.
 intros H8338 H8714 Step.
 eapply (selected_node_concrete_ground_output data_writer_node_offsets flat_statements data_writer_expected_nodes 8715 writer_expr_8715 inputs path flat_memories old current result).
 - exact data_writer_node_positions.
 - exact data_writer_node_safety.
 - apply (@List.nth_error_In _ data_writer_expected_nodes 33 (8715,writer_expr_8715)). vm_compute. reflexivity.
 - apply writer_ready_8715; assumption.
 - exact Step.
Qed.
Lemma data_writer_node_output_8716 inputs path old current result :
 (exists ground bits, VM.find 8336 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8715 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists ground bits, VM.find 8716 result = Some (Gval ground bits).
Proof.
 intros H8336 H8715 Step.
 eapply (selected_node_concrete_ground_output data_writer_node_offsets flat_statements data_writer_expected_nodes 8716 writer_expr_8716 inputs path flat_memories old current result).
 - exact data_writer_node_positions.
 - exact data_writer_node_safety.
 - apply (@List.nth_error_In _ data_writer_expected_nodes 34 (8716,writer_expr_8716)). vm_compute. reflexivity.
 - apply writer_ready_8716; assumption.
 - exact Step.
Qed.
Lemma data_writer_node_output_8717 inputs path old current result :
 (exists ground bits, VM.find 8334 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8716 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists ground bits, VM.find 8717 result = Some (Gval ground bits).
Proof.
 intros H8334 H8716 Step.
 eapply (selected_node_concrete_ground_output data_writer_node_offsets flat_statements data_writer_expected_nodes 8717 writer_expr_8717 inputs path flat_memories old current result).
 - exact data_writer_node_positions.
 - exact data_writer_node_safety.
 - apply (@List.nth_error_In _ data_writer_expected_nodes 35 (8717,writer_expr_8717)). vm_compute. reflexivity.
 - apply writer_ready_8717; assumption.
 - exact Step.
Qed.
Lemma data_writer_node_output_8718 inputs path old current result :
 (exists ground bits, VM.find 8332 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8717 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists ground bits, VM.find 8718 result = Some (Gval ground bits).
Proof.
 intros H8332 H8717 Step.
 eapply (selected_node_concrete_ground_output data_writer_node_offsets flat_statements data_writer_expected_nodes 8718 writer_expr_8718 inputs path flat_memories old current result).
 - exact data_writer_node_positions.
 - exact data_writer_node_safety.
 - apply (@List.nth_error_In _ data_writer_expected_nodes 36 (8718,writer_expr_8718)). vm_compute. reflexivity.
 - apply writer_ready_8718; assumption.
 - exact Step.
Qed.
Lemma data_writer_node_output_8719 inputs path old current result :
 (exists ground bits, VM.find 8330 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8718 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists ground bits, VM.find 8719 result = Some (Gval ground bits).
Proof.
 intros H8330 H8718 Step.
 eapply (selected_node_concrete_ground_output data_writer_node_offsets flat_statements data_writer_expected_nodes 8719 writer_expr_8719 inputs path flat_memories old current result).
 - exact data_writer_node_positions.
 - exact data_writer_node_safety.
 - apply (@List.nth_error_In _ data_writer_expected_nodes 37 (8719,writer_expr_8719)). vm_compute. reflexivity.
 - apply writer_ready_8719; assumption.
 - exact Step.
Qed.
Lemma data_writer_node_output_8720 inputs path old current result :
 (exists ground bits, VM.find 8328 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8719 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists ground bits, VM.find 8720 result = Some (Gval ground bits).
Proof.
 intros H8328 H8719 Step.
 eapply (selected_node_concrete_ground_output data_writer_node_offsets flat_statements data_writer_expected_nodes 8720 writer_expr_8720 inputs path flat_memories old current result).
 - exact data_writer_node_positions.
 - exact data_writer_node_safety.
 - apply (@List.nth_error_In _ data_writer_expected_nodes 38 (8720,writer_expr_8720)). vm_compute. reflexivity.
 - apply writer_ready_8720; assumption.
 - exact Step.
Qed.
Lemma data_writer_node_output_8721 inputs path old current result :
 (exists ground bits, VM.find 8326 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8720 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists ground bits, VM.find 8721 result = Some (Gval ground bits).
Proof.
 intros H8326 H8720 Step.
 eapply (selected_node_concrete_ground_output data_writer_node_offsets flat_statements data_writer_expected_nodes 8721 writer_expr_8721 inputs path flat_memories old current result).
 - exact data_writer_node_positions.
 - exact data_writer_node_safety.
 - apply (@List.nth_error_In _ data_writer_expected_nodes 39 (8721,writer_expr_8721)). vm_compute. reflexivity.
 - apply writer_ready_8721; assumption.
 - exact Step.
Qed.
Lemma data_writer_node_output_8722 inputs path old current result :
 (exists ground bits, VM.find 8324 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8721 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists ground bits, VM.find 8722 result = Some (Gval ground bits).
Proof.
 intros H8324 H8721 Step.
 eapply (selected_node_concrete_ground_output data_writer_node_offsets flat_statements data_writer_expected_nodes 8722 writer_expr_8722 inputs path flat_memories old current result).
 - exact data_writer_node_positions.
 - exact data_writer_node_safety.
 - apply (@List.nth_error_In _ data_writer_expected_nodes 40 (8722,writer_expr_8722)). vm_compute. reflexivity.
 - apply writer_ready_8722; assumption.
 - exact Step.
Qed.
Lemma data_writer_node_output_8723 inputs path old current result :
 (exists ground bits, VM.find 8322 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8722 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists ground bits, VM.find 8723 result = Some (Gval ground bits).
Proof.
 intros H8322 H8722 Step.
 eapply (selected_node_concrete_ground_output data_writer_node_offsets flat_statements data_writer_expected_nodes 8723 writer_expr_8723 inputs path flat_memories old current result).
 - exact data_writer_node_positions.
 - exact data_writer_node_safety.
 - apply (@List.nth_error_In _ data_writer_expected_nodes 41 (8723,writer_expr_8723)). vm_compute. reflexivity.
 - apply writer_ready_8723; assumption.
 - exact Step.
Qed.
Lemma data_writer_node_output_8724 inputs path old current result :
 (exists ground bits, VM.find 8320 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8723 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists ground bits, VM.find 8724 result = Some (Gval ground bits).
Proof.
 intros H8320 H8723 Step.
 eapply (selected_node_concrete_ground_output data_writer_node_offsets flat_statements data_writer_expected_nodes 8724 writer_expr_8724 inputs path flat_memories old current result).
 - exact data_writer_node_positions.
 - exact data_writer_node_safety.
 - apply (@List.nth_error_In _ data_writer_expected_nodes 42 (8724,writer_expr_8724)). vm_compute. reflexivity.
 - apply writer_ready_8724; assumption.
 - exact Step.
Qed.
Lemma data_writer_node_output_8725 inputs path old current result :
 (exists ground bits, VM.find 8318 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8724 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists ground bits, VM.find 8725 result = Some (Gval ground bits).
Proof.
 intros H8318 H8724 Step.
 eapply (selected_node_concrete_ground_output data_writer_node_offsets flat_statements data_writer_expected_nodes 8725 writer_expr_8725 inputs path flat_memories old current result).
 - exact data_writer_node_positions.
 - exact data_writer_node_safety.
 - apply (@List.nth_error_In _ data_writer_expected_nodes 43 (8725,writer_expr_8725)). vm_compute. reflexivity.
 - apply writer_ready_8725; assumption.
 - exact Step.
Qed.
Lemma data_writer_node_output_8726 inputs path old current result :
 (exists ground bits, VM.find 8316 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8725 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists ground bits, VM.find 8726 result = Some (Gval ground bits).
Proof.
 intros H8316 H8725 Step.
 eapply (selected_node_concrete_ground_output data_writer_node_offsets flat_statements data_writer_expected_nodes 8726 writer_expr_8726 inputs path flat_memories old current result).
 - exact data_writer_node_positions.
 - exact data_writer_node_safety.
 - apply (@List.nth_error_In _ data_writer_expected_nodes 44 (8726,writer_expr_8726)). vm_compute. reflexivity.
 - apply writer_ready_8726; assumption.
 - exact Step.
Qed.
Lemma data_writer_node_output_8727 inputs path old current result :
 (exists ground bits, VM.find 8314 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8726 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists ground bits, VM.find 8727 result = Some (Gval ground bits).
Proof.
 intros H8314 H8726 Step.
 eapply (selected_node_concrete_ground_output data_writer_node_offsets flat_statements data_writer_expected_nodes 8727 writer_expr_8727 inputs path flat_memories old current result).
 - exact data_writer_node_positions.
 - exact data_writer_node_safety.
 - apply (@List.nth_error_In _ data_writer_expected_nodes 45 (8727,writer_expr_8727)). vm_compute. reflexivity.
 - apply writer_ready_8727; assumption.
 - exact Step.
Qed.
Lemma data_writer_node_output_8728 inputs path old current result :
 (exists ground bits, VM.find 8312 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8727 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists ground bits, VM.find 8728 result = Some (Gval ground bits).
Proof.
 intros H8312 H8727 Step.
 eapply (selected_node_concrete_ground_output data_writer_node_offsets flat_statements data_writer_expected_nodes 8728 writer_expr_8728 inputs path flat_memories old current result).
 - exact data_writer_node_positions.
 - exact data_writer_node_safety.
 - apply (@List.nth_error_In _ data_writer_expected_nodes 46 (8728,writer_expr_8728)). vm_compute. reflexivity.
 - apply writer_ready_8728; assumption.
 - exact Step.
Qed.
Lemma data_writer_node_output_8729 inputs path old current result :
 (exists ground bits, VM.find 8310 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8728 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists ground bits, VM.find 8729 result = Some (Gval ground bits).
Proof.
 intros H8310 H8728 Step.
 eapply (selected_node_concrete_ground_output data_writer_node_offsets flat_statements data_writer_expected_nodes 8729 writer_expr_8729 inputs path flat_memories old current result).
 - exact data_writer_node_positions.
 - exact data_writer_node_safety.
 - apply (@List.nth_error_In _ data_writer_expected_nodes 47 (8729,writer_expr_8729)). vm_compute. reflexivity.
 - apply writer_ready_8729; assumption.
 - exact Step.
Qed.
Lemma data_writer_node_output_8730 inputs path old current result :
 (exists ground bits, VM.find 8308 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8729 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists ground bits, VM.find 8730 result = Some (Gval ground bits).
Proof.
 intros H8308 H8729 Step.
 eapply (selected_node_concrete_ground_output data_writer_node_offsets flat_statements data_writer_expected_nodes 8730 writer_expr_8730 inputs path flat_memories old current result).
 - exact data_writer_node_positions.
 - exact data_writer_node_safety.
 - apply (@List.nth_error_In _ data_writer_expected_nodes 48 (8730,writer_expr_8730)). vm_compute. reflexivity.
 - apply writer_ready_8730; assumption.
 - exact Step.
Qed.
Lemma data_writer_node_output_8731 inputs path old current result :
 (exists ground bits, VM.find 8306 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8730 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists ground bits, VM.find 8731 result = Some (Gval ground bits).
Proof.
 intros H8306 H8730 Step.
 eapply (selected_node_concrete_ground_output data_writer_node_offsets flat_statements data_writer_expected_nodes 8731 writer_expr_8731 inputs path flat_memories old current result).
 - exact data_writer_node_positions.
 - exact data_writer_node_safety.
 - apply (@List.nth_error_In _ data_writer_expected_nodes 49 (8731,writer_expr_8731)). vm_compute. reflexivity.
 - apply writer_ready_8731; assumption.
 - exact Step.
Qed.
Lemma data_writer_node_output_8732 inputs path old current result :
 (exists ground bits, VM.find 8304 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8731 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists ground bits, VM.find 8732 result = Some (Gval ground bits).
Proof.
 intros H8304 H8731 Step.
 eapply (selected_node_concrete_ground_output data_writer_node_offsets flat_statements data_writer_expected_nodes 8732 writer_expr_8732 inputs path flat_memories old current result).
 - exact data_writer_node_positions.
 - exact data_writer_node_safety.
 - apply (@List.nth_error_In _ data_writer_expected_nodes 50 (8732,writer_expr_8732)). vm_compute. reflexivity.
 - apply writer_ready_8732; assumption.
 - exact Step.
Qed.
Lemma data_writer_node_output_8733 inputs path old current result :
 (exists ground bits, VM.find 8302 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8732 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists ground bits, VM.find 8733 result = Some (Gval ground bits).
Proof.
 intros H8302 H8732 Step.
 eapply (selected_node_concrete_ground_output data_writer_node_offsets flat_statements data_writer_expected_nodes 8733 writer_expr_8733 inputs path flat_memories old current result).
 - exact data_writer_node_positions.
 - exact data_writer_node_safety.
 - apply (@List.nth_error_In _ data_writer_expected_nodes 51 (8733,writer_expr_8733)). vm_compute. reflexivity.
 - apply writer_ready_8733; assumption.
 - exact Step.
Qed.
Lemma data_writer_node_output_8734 inputs path old current result :
 (exists ground bits, VM.find 8300 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8733 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists ground bits, VM.find 8734 result = Some (Gval ground bits).
Proof.
 intros H8300 H8733 Step.
 eapply (selected_node_concrete_ground_output data_writer_node_offsets flat_statements data_writer_expected_nodes 8734 writer_expr_8734 inputs path flat_memories old current result).
 - exact data_writer_node_positions.
 - exact data_writer_node_safety.
 - apply (@List.nth_error_In _ data_writer_expected_nodes 52 (8734,writer_expr_8734)). vm_compute. reflexivity.
 - apply writer_ready_8734; assumption.
 - exact Step.
Qed.
Lemma data_writer_node_output_8735 inputs path old current result :
 (exists ground bits, VM.find 8298 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8734 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists ground bits, VM.find 8735 result = Some (Gval ground bits).
Proof.
 intros H8298 H8734 Step.
 eapply (selected_node_concrete_ground_output data_writer_node_offsets flat_statements data_writer_expected_nodes 8735 writer_expr_8735 inputs path flat_memories old current result).
 - exact data_writer_node_positions.
 - exact data_writer_node_safety.
 - apply (@List.nth_error_In _ data_writer_expected_nodes 53 (8735,writer_expr_8735)). vm_compute. reflexivity.
 - apply writer_ready_8735; assumption.
 - exact Step.
Qed.
Lemma data_writer_node_output_8736 inputs path old current result :
 (exists ground bits, VM.find 8296 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8735 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists ground bits, VM.find 8736 result = Some (Gval ground bits).
Proof.
 intros H8296 H8735 Step.
 eapply (selected_node_concrete_ground_output data_writer_node_offsets flat_statements data_writer_expected_nodes 8736 writer_expr_8736 inputs path flat_memories old current result).
 - exact data_writer_node_positions.
 - exact data_writer_node_safety.
 - apply (@List.nth_error_In _ data_writer_expected_nodes 54 (8736,writer_expr_8736)). vm_compute. reflexivity.
 - apply writer_ready_8736; assumption.
 - exact Step.
Qed.
Lemma data_writer_node_output_8737 inputs path old current result :
 (exists ground bits, VM.find 8294 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8736 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists ground bits, VM.find 8737 result = Some (Gval ground bits).
Proof.
 intros H8294 H8736 Step.
 eapply (selected_node_concrete_ground_output data_writer_node_offsets flat_statements data_writer_expected_nodes 8737 writer_expr_8737 inputs path flat_memories old current result).
 - exact data_writer_node_positions.
 - exact data_writer_node_safety.
 - apply (@List.nth_error_In _ data_writer_expected_nodes 55 (8737,writer_expr_8737)). vm_compute. reflexivity.
 - apply writer_ready_8737; assumption.
 - exact Step.
Qed.
Lemma data_writer_node_output_8738 inputs path old current result :
 (exists ground bits, VM.find 8292 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8737 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists ground bits, VM.find 8738 result = Some (Gval ground bits).
Proof.
 intros H8292 H8737 Step.
 eapply (selected_node_concrete_ground_output data_writer_node_offsets flat_statements data_writer_expected_nodes 8738 writer_expr_8738 inputs path flat_memories old current result).
 - exact data_writer_node_positions.
 - exact data_writer_node_safety.
 - apply (@List.nth_error_In _ data_writer_expected_nodes 56 (8738,writer_expr_8738)). vm_compute. reflexivity.
 - apply writer_ready_8738; assumption.
 - exact Step.
Qed.
Lemma data_writer_node_output_8739 inputs path old current result :
 (exists ground bits, VM.find 8290 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8738 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists ground bits, VM.find 8739 result = Some (Gval ground bits).
Proof.
 intros H8290 H8738 Step.
 eapply (selected_node_concrete_ground_output data_writer_node_offsets flat_statements data_writer_expected_nodes 8739 writer_expr_8739 inputs path flat_memories old current result).
 - exact data_writer_node_positions.
 - exact data_writer_node_safety.
 - apply (@List.nth_error_In _ data_writer_expected_nodes 57 (8739,writer_expr_8739)). vm_compute. reflexivity.
 - apply writer_ready_8739; assumption.
 - exact Step.
Qed.
Lemma data_writer_node_output_8740 inputs path old current result :
 (exists ground bits, VM.find 8288 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8739 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists ground bits, VM.find 8740 result = Some (Gval ground bits).
Proof.
 intros H8288 H8739 Step.
 eapply (selected_node_concrete_ground_output data_writer_node_offsets flat_statements data_writer_expected_nodes 8740 writer_expr_8740 inputs path flat_memories old current result).
 - exact data_writer_node_positions.
 - exact data_writer_node_safety.
 - apply (@List.nth_error_In _ data_writer_expected_nodes 58 (8740,writer_expr_8740)). vm_compute. reflexivity.
 - apply writer_ready_8740; assumption.
 - exact Step.
Qed.
Lemma data_writer_node_output_8741 inputs path old current result :
 (exists ground bits, VM.find 8286 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8740 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists ground bits, VM.find 8741 result = Some (Gval ground bits).
Proof.
 intros H8286 H8740 Step.
 eapply (selected_node_concrete_ground_output data_writer_node_offsets flat_statements data_writer_expected_nodes 8741 writer_expr_8741 inputs path flat_memories old current result).
 - exact data_writer_node_positions.
 - exact data_writer_node_safety.
 - apply (@List.nth_error_In _ data_writer_expected_nodes 59 (8741,writer_expr_8741)). vm_compute. reflexivity.
 - apply writer_ready_8741; assumption.
 - exact Step.
Qed.
Lemma data_writer_node_output_8742 inputs path old current result :
 (exists ground bits, VM.find 8284 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8741 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists ground bits, VM.find 8742 result = Some (Gval ground bits).
Proof.
 intros H8284 H8741 Step.
 eapply (selected_node_concrete_ground_output data_writer_node_offsets flat_statements data_writer_expected_nodes 8742 writer_expr_8742 inputs path flat_memories old current result).
 - exact data_writer_node_positions.
 - exact data_writer_node_safety.
 - apply (@List.nth_error_In _ data_writer_expected_nodes 60 (8742,writer_expr_8742)). vm_compute. reflexivity.
 - apply writer_ready_8742; assumption.
 - exact Step.
Qed.
Lemma data_writer_node_output_8743 inputs path old current result :
 (exists ground bits, VM.find 8282 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8742 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists ground bits, VM.find 8743 result = Some (Gval ground bits).
Proof.
 intros H8282 H8742 Step.
 eapply (selected_node_concrete_ground_output data_writer_node_offsets flat_statements data_writer_expected_nodes 8743 writer_expr_8743 inputs path flat_memories old current result).
 - exact data_writer_node_positions.
 - exact data_writer_node_safety.
 - apply (@List.nth_error_In _ data_writer_expected_nodes 61 (8743,writer_expr_8743)). vm_compute. reflexivity.
 - apply writer_ready_8743; assumption.
 - exact Step.
Qed.
Lemma data_writer_node_output_8744 inputs path old current result :
 (exists ground bits, VM.find 8280 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8743 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists ground bits, VM.find 8744 result = Some (Gval ground bits).
Proof.
 intros H8280 H8743 Step.
 eapply (selected_node_concrete_ground_output data_writer_node_offsets flat_statements data_writer_expected_nodes 8744 writer_expr_8744 inputs path flat_memories old current result).
 - exact data_writer_node_positions.
 - exact data_writer_node_safety.
 - apply (@List.nth_error_In _ data_writer_expected_nodes 62 (8744,writer_expr_8744)). vm_compute. reflexivity.
 - apply writer_ready_8744; assumption.
 - exact Step.
Qed.
Lemma data_writer_node_output_8745 inputs path old current result :
 (exists ground bits, VM.find 8278 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8744 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists ground bits, VM.find 8745 result = Some (Gval ground bits).
Proof.
 intros H8278 H8744 Step.
 eapply (selected_node_concrete_ground_output data_writer_node_offsets flat_statements data_writer_expected_nodes 8745 writer_expr_8745 inputs path flat_memories old current result).
 - exact data_writer_node_positions.
 - exact data_writer_node_safety.
 - apply (@List.nth_error_In _ data_writer_expected_nodes 63 (8745,writer_expr_8745)). vm_compute. reflexivity.
 - apply writer_ready_8745; assumption.
 - exact Step.
Qed.
Lemma data_writer_node_output_8746 inputs path old current result :
 (exists ground bits, VM.find 8276 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8745 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists ground bits, VM.find 8746 result = Some (Gval ground bits).
Proof.
 intros H8276 H8745 Step.
 eapply (selected_node_concrete_ground_output data_writer_node_offsets flat_statements data_writer_expected_nodes 8746 writer_expr_8746 inputs path flat_memories old current result).
 - exact data_writer_node_positions.
 - exact data_writer_node_safety.
 - apply (@List.nth_error_In _ data_writer_expected_nodes 64 (8746,writer_expr_8746)). vm_compute. reflexivity.
 - apply writer_ready_8746; assumption.
 - exact Step.
Qed.
Lemma data_writer_node_output_8747 inputs path old current result :
 (exists ground bits, VM.find 8274 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8746 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists ground bits, VM.find 8747 result = Some (Gval ground bits).
Proof.
 intros H8274 H8746 Step.
 eapply (selected_node_concrete_ground_output data_writer_node_offsets flat_statements data_writer_expected_nodes 8747 writer_expr_8747 inputs path flat_memories old current result).
 - exact data_writer_node_positions.
 - exact data_writer_node_safety.
 - apply (@List.nth_error_In _ data_writer_expected_nodes 65 (8747,writer_expr_8747)). vm_compute. reflexivity.
 - apply writer_ready_8747; assumption.
 - exact Step.
Qed.
Lemma data_writer_node_output_8748 inputs path old current result :
 (exists ground bits, VM.find 8272 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8747 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists ground bits, VM.find 8748 result = Some (Gval ground bits).
Proof.
 intros H8272 H8747 Step.
 eapply (selected_node_concrete_ground_output data_writer_node_offsets flat_statements data_writer_expected_nodes 8748 writer_expr_8748 inputs path flat_memories old current result).
 - exact data_writer_node_positions.
 - exact data_writer_node_safety.
 - apply (@List.nth_error_In _ data_writer_expected_nodes 66 (8748,writer_expr_8748)). vm_compute. reflexivity.
 - apply writer_ready_8748; assumption.
 - exact Step.
Qed.
Lemma data_writer_node_output_8749 inputs path old current result :
 (exists ground bits, VM.find 8270 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8748 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists ground bits, VM.find 8749 result = Some (Gval ground bits).
Proof.
 intros H8270 H8748 Step.
 eapply (selected_node_concrete_ground_output data_writer_node_offsets flat_statements data_writer_expected_nodes 8749 writer_expr_8749 inputs path flat_memories old current result).
 - exact data_writer_node_positions.
 - exact data_writer_node_safety.
 - apply (@List.nth_error_In _ data_writer_expected_nodes 67 (8749,writer_expr_8749)). vm_compute. reflexivity.
 - apply writer_ready_8749; assumption.
 - exact Step.
Qed.
Lemma data_writer_node_output_8750 inputs path old current result :
 (exists ground bits, VM.find 8268 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8749 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists ground bits, VM.find 8750 result = Some (Gval ground bits).
Proof.
 intros H8268 H8749 Step.
 eapply (selected_node_concrete_ground_output data_writer_node_offsets flat_statements data_writer_expected_nodes 8750 writer_expr_8750 inputs path flat_memories old current result).
 - exact data_writer_node_positions.
 - exact data_writer_node_safety.
 - apply (@List.nth_error_In _ data_writer_expected_nodes 68 (8750,writer_expr_8750)). vm_compute. reflexivity.
 - apply writer_ready_8750; assumption.
 - exact Step.
Qed.
Lemma data_writer_node_output_8751 inputs path old current result :
 (exists ground bits, VM.find 8266 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8750 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists ground bits, VM.find 8751 result = Some (Gval ground bits).
Proof.
 intros H8266 H8750 Step.
 eapply (selected_node_concrete_ground_output data_writer_node_offsets flat_statements data_writer_expected_nodes 8751 writer_expr_8751 inputs path flat_memories old current result).
 - exact data_writer_node_positions.
 - exact data_writer_node_safety.
 - apply (@List.nth_error_In _ data_writer_expected_nodes 69 (8751,writer_expr_8751)). vm_compute. reflexivity.
 - apply writer_ready_8751; assumption.
 - exact Step.
Qed.
Lemma data_writer_node_output_8752 inputs path old current result :
 (exists ground bits, VM.find 8264 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8751 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists ground bits, VM.find 8752 result = Some (Gval ground bits).
Proof.
 intros H8264 H8751 Step.
 eapply (selected_node_concrete_ground_output data_writer_node_offsets flat_statements data_writer_expected_nodes 8752 writer_expr_8752 inputs path flat_memories old current result).
 - exact data_writer_node_positions.
 - exact data_writer_node_safety.
 - apply (@List.nth_error_In _ data_writer_expected_nodes 70 (8752,writer_expr_8752)). vm_compute. reflexivity.
 - apply writer_ready_8752; assumption.
 - exact Step.
Qed.
Lemma data_writer_node_output_8753 inputs path old current result :
 (exists ground bits, VM.find 8360 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists ground bits, VM.find 8753 result = Some (Gval ground bits).
Proof.
 intros H8360 Step.
 eapply (selected_node_concrete_ground_output data_writer_node_offsets flat_statements data_writer_expected_nodes 8753 writer_expr_8753 inputs path flat_memories old current result).
 - exact data_writer_node_positions.
 - exact data_writer_node_safety.
 - apply (@List.nth_error_In _ data_writer_expected_nodes 71 (8753,writer_expr_8753)). vm_compute. reflexivity.
 - apply writer_ready_8753; assumption.
 - exact Step.
Qed.
Lemma data_writer_node_output_8754 inputs path old current result :
 (exists ground bits, VM.find 8358 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8753 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists ground bits, VM.find 8754 result = Some (Gval ground bits).
Proof.
 intros H8358 H8753 Step.
 eapply (selected_node_concrete_ground_output data_writer_node_offsets flat_statements data_writer_expected_nodes 8754 writer_expr_8754 inputs path flat_memories old current result).
 - exact data_writer_node_positions.
 - exact data_writer_node_safety.
 - apply (@List.nth_error_In _ data_writer_expected_nodes 72 (8754,writer_expr_8754)). vm_compute. reflexivity.
 - apply writer_ready_8754; assumption.
 - exact Step.
Qed.
Lemma data_writer_node_output_8755 inputs path old current result :
 (exists ground bits, VM.find 8356 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8754 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists ground bits, VM.find 8755 result = Some (Gval ground bits).
Proof.
 intros H8356 H8754 Step.
 eapply (selected_node_concrete_ground_output data_writer_node_offsets flat_statements data_writer_expected_nodes 8755 writer_expr_8755 inputs path flat_memories old current result).
 - exact data_writer_node_positions.
 - exact data_writer_node_safety.
 - apply (@List.nth_error_In _ data_writer_expected_nodes 73 (8755,writer_expr_8755)). vm_compute. reflexivity.
 - apply writer_ready_8755; assumption.
 - exact Step.
Qed.
Lemma data_writer_node_output_8756 inputs path old current result :
 (exists ground bits, VM.find 8354 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8755 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists ground bits, VM.find 8756 result = Some (Gval ground bits).
Proof.
 intros H8354 H8755 Step.
 eapply (selected_node_concrete_ground_output data_writer_node_offsets flat_statements data_writer_expected_nodes 8756 writer_expr_8756 inputs path flat_memories old current result).
 - exact data_writer_node_positions.
 - exact data_writer_node_safety.
 - apply (@List.nth_error_In _ data_writer_expected_nodes 74 (8756,writer_expr_8756)). vm_compute. reflexivity.
 - apply writer_ready_8756; assumption.
 - exact Step.
Qed.
Lemma data_writer_node_output_8757 inputs path old current result :
 (exists ground bits, VM.find 8352 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8756 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists ground bits, VM.find 8757 result = Some (Gval ground bits).
Proof.
 intros H8352 H8756 Step.
 eapply (selected_node_concrete_ground_output data_writer_node_offsets flat_statements data_writer_expected_nodes 8757 writer_expr_8757 inputs path flat_memories old current result).
 - exact data_writer_node_positions.
 - exact data_writer_node_safety.
 - apply (@List.nth_error_In _ data_writer_expected_nodes 75 (8757,writer_expr_8757)). vm_compute. reflexivity.
 - apply writer_ready_8757; assumption.
 - exact Step.
Qed.
Lemma data_writer_node_output_8758 inputs path old current result :
 (exists ground bits, VM.find 8350 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8757 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists ground bits, VM.find 8758 result = Some (Gval ground bits).
Proof.
 intros H8350 H8757 Step.
 eapply (selected_node_concrete_ground_output data_writer_node_offsets flat_statements data_writer_expected_nodes 8758 writer_expr_8758 inputs path flat_memories old current result).
 - exact data_writer_node_positions.
 - exact data_writer_node_safety.
 - apply (@List.nth_error_In _ data_writer_expected_nodes 76 (8758,writer_expr_8758)). vm_compute. reflexivity.
 - apply writer_ready_8758; assumption.
 - exact Step.
Qed.
Lemma data_writer_node_output_8759 inputs path old current result :
 (exists ground bits, VM.find 8348 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8758 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists ground bits, VM.find 8759 result = Some (Gval ground bits).
Proof.
 intros H8348 H8758 Step.
 eapply (selected_node_concrete_ground_output data_writer_node_offsets flat_statements data_writer_expected_nodes 8759 writer_expr_8759 inputs path flat_memories old current result).
 - exact data_writer_node_positions.
 - exact data_writer_node_safety.
 - apply (@List.nth_error_In _ data_writer_expected_nodes 77 (8759,writer_expr_8759)). vm_compute. reflexivity.
 - apply writer_ready_8759; assumption.
 - exact Step.
Qed.
Lemma data_writer_node_output_8760 inputs path old current result :
 (exists ground bits, VM.find 8346 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8759 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists ground bits, VM.find 8760 result = Some (Gval ground bits).
Proof.
 intros H8346 H8759 Step.
 eapply (selected_node_concrete_ground_output data_writer_node_offsets flat_statements data_writer_expected_nodes 8760 writer_expr_8760 inputs path flat_memories old current result).
 - exact data_writer_node_positions.
 - exact data_writer_node_safety.
 - apply (@List.nth_error_In _ data_writer_expected_nodes 78 (8760,writer_expr_8760)). vm_compute. reflexivity.
 - apply writer_ready_8760; assumption.
 - exact Step.
Qed.
Lemma data_writer_node_output_8761 inputs path old current result :
 (exists ground bits, VM.find 8344 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8760 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists ground bits, VM.find 8761 result = Some (Gval ground bits).
Proof.
 intros H8344 H8760 Step.
 eapply (selected_node_concrete_ground_output data_writer_node_offsets flat_statements data_writer_expected_nodes 8761 writer_expr_8761 inputs path flat_memories old current result).
 - exact data_writer_node_positions.
 - exact data_writer_node_safety.
 - apply (@List.nth_error_In _ data_writer_expected_nodes 79 (8761,writer_expr_8761)). vm_compute. reflexivity.
 - apply writer_ready_8761; assumption.
 - exact Step.
Qed.
Lemma data_writer_node_output_8762 inputs path old current result :
 (exists ground bits, VM.find 8342 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8761 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists ground bits, VM.find 8762 result = Some (Gval ground bits).
Proof.
 intros H8342 H8761 Step.
 eapply (selected_node_concrete_ground_output data_writer_node_offsets flat_statements data_writer_expected_nodes 8762 writer_expr_8762 inputs path flat_memories old current result).
 - exact data_writer_node_positions.
 - exact data_writer_node_safety.
 - apply (@List.nth_error_In _ data_writer_expected_nodes 80 (8762,writer_expr_8762)). vm_compute. reflexivity.
 - apply writer_ready_8762; assumption.
 - exact Step.
Qed.
Lemma data_writer_node_output_8763 inputs path old current result :
 (exists ground bits, VM.find 8340 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8762 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists ground bits, VM.find 8763 result = Some (Gval ground bits).
Proof.
 intros H8340 H8762 Step.
 eapply (selected_node_concrete_ground_output data_writer_node_offsets flat_statements data_writer_expected_nodes 8763 writer_expr_8763 inputs path flat_memories old current result).
 - exact data_writer_node_positions.
 - exact data_writer_node_safety.
 - apply (@List.nth_error_In _ data_writer_expected_nodes 81 (8763,writer_expr_8763)). vm_compute. reflexivity.
 - apply writer_ready_8763; assumption.
 - exact Step.
Qed.
Lemma data_writer_node_output_8764 inputs path old current result :
 (exists ground bits, VM.find 8338 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8763 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists ground bits, VM.find 8764 result = Some (Gval ground bits).
Proof.
 intros H8338 H8763 Step.
 eapply (selected_node_concrete_ground_output data_writer_node_offsets flat_statements data_writer_expected_nodes 8764 writer_expr_8764 inputs path flat_memories old current result).
 - exact data_writer_node_positions.
 - exact data_writer_node_safety.
 - apply (@List.nth_error_In _ data_writer_expected_nodes 82 (8764,writer_expr_8764)). vm_compute. reflexivity.
 - apply writer_ready_8764; assumption.
 - exact Step.
Qed.
Lemma data_writer_node_output_8765 inputs path old current result :
 (exists ground bits, VM.find 8336 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8764 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists ground bits, VM.find 8765 result = Some (Gval ground bits).
Proof.
 intros H8336 H8764 Step.
 eapply (selected_node_concrete_ground_output data_writer_node_offsets flat_statements data_writer_expected_nodes 8765 writer_expr_8765 inputs path flat_memories old current result).
 - exact data_writer_node_positions.
 - exact data_writer_node_safety.
 - apply (@List.nth_error_In _ data_writer_expected_nodes 83 (8765,writer_expr_8765)). vm_compute. reflexivity.
 - apply writer_ready_8765; assumption.
 - exact Step.
Qed.
Lemma data_writer_node_output_8766 inputs path old current result :
 (exists ground bits, VM.find 8334 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8765 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists ground bits, VM.find 8766 result = Some (Gval ground bits).
Proof.
 intros H8334 H8765 Step.
 eapply (selected_node_concrete_ground_output data_writer_node_offsets flat_statements data_writer_expected_nodes 8766 writer_expr_8766 inputs path flat_memories old current result).
 - exact data_writer_node_positions.
 - exact data_writer_node_safety.
 - apply (@List.nth_error_In _ data_writer_expected_nodes 84 (8766,writer_expr_8766)). vm_compute. reflexivity.
 - apply writer_ready_8766; assumption.
 - exact Step.
Qed.
Lemma data_writer_node_output_8767 inputs path old current result :
 (exists ground bits, VM.find 8332 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8766 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists ground bits, VM.find 8767 result = Some (Gval ground bits).
Proof.
 intros H8332 H8766 Step.
 eapply (selected_node_concrete_ground_output data_writer_node_offsets flat_statements data_writer_expected_nodes 8767 writer_expr_8767 inputs path flat_memories old current result).
 - exact data_writer_node_positions.
 - exact data_writer_node_safety.
 - apply (@List.nth_error_In _ data_writer_expected_nodes 85 (8767,writer_expr_8767)). vm_compute. reflexivity.
 - apply writer_ready_8767; assumption.
 - exact Step.
Qed.
Lemma data_writer_node_output_8768 inputs path old current result :
 (exists ground bits, VM.find 8330 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8767 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists ground bits, VM.find 8768 result = Some (Gval ground bits).
Proof.
 intros H8330 H8767 Step.
 eapply (selected_node_concrete_ground_output data_writer_node_offsets flat_statements data_writer_expected_nodes 8768 writer_expr_8768 inputs path flat_memories old current result).
 - exact data_writer_node_positions.
 - exact data_writer_node_safety.
 - apply (@List.nth_error_In _ data_writer_expected_nodes 86 (8768,writer_expr_8768)). vm_compute. reflexivity.
 - apply writer_ready_8768; assumption.
 - exact Step.
Qed.
Lemma data_writer_node_output_8769 inputs path old current result :
 (exists ground bits, VM.find 8328 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8768 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists ground bits, VM.find 8769 result = Some (Gval ground bits).
Proof.
 intros H8328 H8768 Step.
 eapply (selected_node_concrete_ground_output data_writer_node_offsets flat_statements data_writer_expected_nodes 8769 writer_expr_8769 inputs path flat_memories old current result).
 - exact data_writer_node_positions.
 - exact data_writer_node_safety.
 - apply (@List.nth_error_In _ data_writer_expected_nodes 87 (8769,writer_expr_8769)). vm_compute. reflexivity.
 - apply writer_ready_8769; assumption.
 - exact Step.
Qed.
Lemma data_writer_node_output_8770 inputs path old current result :
 (exists ground bits, VM.find 8326 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8769 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists ground bits, VM.find 8770 result = Some (Gval ground bits).
Proof.
 intros H8326 H8769 Step.
 eapply (selected_node_concrete_ground_output data_writer_node_offsets flat_statements data_writer_expected_nodes 8770 writer_expr_8770 inputs path flat_memories old current result).
 - exact data_writer_node_positions.
 - exact data_writer_node_safety.
 - apply (@List.nth_error_In _ data_writer_expected_nodes 88 (8770,writer_expr_8770)). vm_compute. reflexivity.
 - apply writer_ready_8770; assumption.
 - exact Step.
Qed.
Lemma data_writer_node_output_8771 inputs path old current result :
 (exists ground bits, VM.find 8324 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8770 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists ground bits, VM.find 8771 result = Some (Gval ground bits).
Proof.
 intros H8324 H8770 Step.
 eapply (selected_node_concrete_ground_output data_writer_node_offsets flat_statements data_writer_expected_nodes 8771 writer_expr_8771 inputs path flat_memories old current result).
 - exact data_writer_node_positions.
 - exact data_writer_node_safety.
 - apply (@List.nth_error_In _ data_writer_expected_nodes 89 (8771,writer_expr_8771)). vm_compute. reflexivity.
 - apply writer_ready_8771; assumption.
 - exact Step.
Qed.
Lemma data_writer_node_output_8772 inputs path old current result :
 (exists ground bits, VM.find 8322 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8771 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists ground bits, VM.find 8772 result = Some (Gval ground bits).
Proof.
 intros H8322 H8771 Step.
 eapply (selected_node_concrete_ground_output data_writer_node_offsets flat_statements data_writer_expected_nodes 8772 writer_expr_8772 inputs path flat_memories old current result).
 - exact data_writer_node_positions.
 - exact data_writer_node_safety.
 - apply (@List.nth_error_In _ data_writer_expected_nodes 90 (8772,writer_expr_8772)). vm_compute. reflexivity.
 - apply writer_ready_8772; assumption.
 - exact Step.
Qed.
Lemma data_writer_node_output_8773 inputs path old current result :
 (exists ground bits, VM.find 8320 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8772 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists ground bits, VM.find 8773 result = Some (Gval ground bits).
Proof.
 intros H8320 H8772 Step.
 eapply (selected_node_concrete_ground_output data_writer_node_offsets flat_statements data_writer_expected_nodes 8773 writer_expr_8773 inputs path flat_memories old current result).
 - exact data_writer_node_positions.
 - exact data_writer_node_safety.
 - apply (@List.nth_error_In _ data_writer_expected_nodes 91 (8773,writer_expr_8773)). vm_compute. reflexivity.
 - apply writer_ready_8773; assumption.
 - exact Step.
Qed.
Lemma data_writer_node_output_8774 inputs path old current result :
 (exists ground bits, VM.find 8318 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8773 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists ground bits, VM.find 8774 result = Some (Gval ground bits).
Proof.
 intros H8318 H8773 Step.
 eapply (selected_node_concrete_ground_output data_writer_node_offsets flat_statements data_writer_expected_nodes 8774 writer_expr_8774 inputs path flat_memories old current result).
 - exact data_writer_node_positions.
 - exact data_writer_node_safety.
 - apply (@List.nth_error_In _ data_writer_expected_nodes 92 (8774,writer_expr_8774)). vm_compute. reflexivity.
 - apply writer_ready_8774; assumption.
 - exact Step.
Qed.
Lemma data_writer_node_output_8775 inputs path old current result :
 (exists ground bits, VM.find 8316 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8774 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists ground bits, VM.find 8775 result = Some (Gval ground bits).
Proof.
 intros H8316 H8774 Step.
 eapply (selected_node_concrete_ground_output data_writer_node_offsets flat_statements data_writer_expected_nodes 8775 writer_expr_8775 inputs path flat_memories old current result).
 - exact data_writer_node_positions.
 - exact data_writer_node_safety.
 - apply (@List.nth_error_In _ data_writer_expected_nodes 93 (8775,writer_expr_8775)). vm_compute. reflexivity.
 - apply writer_ready_8775; assumption.
 - exact Step.
Qed.
Lemma data_writer_node_output_8776 inputs path old current result :
 (exists ground bits, VM.find 8314 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8775 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists ground bits, VM.find 8776 result = Some (Gval ground bits).
Proof.
 intros H8314 H8775 Step.
 eapply (selected_node_concrete_ground_output data_writer_node_offsets flat_statements data_writer_expected_nodes 8776 writer_expr_8776 inputs path flat_memories old current result).
 - exact data_writer_node_positions.
 - exact data_writer_node_safety.
 - apply (@List.nth_error_In _ data_writer_expected_nodes 94 (8776,writer_expr_8776)). vm_compute. reflexivity.
 - apply writer_ready_8776; assumption.
 - exact Step.
Qed.
Lemma data_writer_node_output_8777 inputs path old current result :
 (exists ground bits, VM.find 8312 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8776 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists ground bits, VM.find 8777 result = Some (Gval ground bits).
Proof.
 intros H8312 H8776 Step.
 eapply (selected_node_concrete_ground_output data_writer_node_offsets flat_statements data_writer_expected_nodes 8777 writer_expr_8777 inputs path flat_memories old current result).
 - exact data_writer_node_positions.
 - exact data_writer_node_safety.
 - apply (@List.nth_error_In _ data_writer_expected_nodes 95 (8777,writer_expr_8777)). vm_compute. reflexivity.
 - apply writer_ready_8777; assumption.
 - exact Step.
Qed.
Lemma data_writer_node_output_8778 inputs path old current result :
 (exists ground bits, VM.find 8310 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8777 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists ground bits, VM.find 8778 result = Some (Gval ground bits).
Proof.
 intros H8310 H8777 Step.
 eapply (selected_node_concrete_ground_output data_writer_node_offsets flat_statements data_writer_expected_nodes 8778 writer_expr_8778 inputs path flat_memories old current result).
 - exact data_writer_node_positions.
 - exact data_writer_node_safety.
 - apply (@List.nth_error_In _ data_writer_expected_nodes 96 (8778,writer_expr_8778)). vm_compute. reflexivity.
 - apply writer_ready_8778; assumption.
 - exact Step.
Qed.
Lemma data_writer_node_output_8779 inputs path old current result :
 (exists ground bits, VM.find 8308 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8778 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists ground bits, VM.find 8779 result = Some (Gval ground bits).
Proof.
 intros H8308 H8778 Step.
 eapply (selected_node_concrete_ground_output data_writer_node_offsets flat_statements data_writer_expected_nodes 8779 writer_expr_8779 inputs path flat_memories old current result).
 - exact data_writer_node_positions.
 - exact data_writer_node_safety.
 - apply (@List.nth_error_In _ data_writer_expected_nodes 97 (8779,writer_expr_8779)). vm_compute. reflexivity.
 - apply writer_ready_8779; assumption.
 - exact Step.
Qed.
Lemma data_writer_node_output_8780 inputs path old current result :
 (exists ground bits, VM.find 8306 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8779 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists ground bits, VM.find 8780 result = Some (Gval ground bits).
Proof.
 intros H8306 H8779 Step.
 eapply (selected_node_concrete_ground_output data_writer_node_offsets flat_statements data_writer_expected_nodes 8780 writer_expr_8780 inputs path flat_memories old current result).
 - exact data_writer_node_positions.
 - exact data_writer_node_safety.
 - apply (@List.nth_error_In _ data_writer_expected_nodes 98 (8780,writer_expr_8780)). vm_compute. reflexivity.
 - apply writer_ready_8780; assumption.
 - exact Step.
Qed.
Lemma data_writer_node_output_8781 inputs path old current result :
 (exists ground bits, VM.find 8304 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8780 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists ground bits, VM.find 8781 result = Some (Gval ground bits).
Proof.
 intros H8304 H8780 Step.
 eapply (selected_node_concrete_ground_output data_writer_node_offsets flat_statements data_writer_expected_nodes 8781 writer_expr_8781 inputs path flat_memories old current result).
 - exact data_writer_node_positions.
 - exact data_writer_node_safety.
 - apply (@List.nth_error_In _ data_writer_expected_nodes 99 (8781,writer_expr_8781)). vm_compute. reflexivity.
 - apply writer_ready_8781; assumption.
 - exact Step.
Qed.
Lemma data_writer_node_output_8782 inputs path old current result :
 (exists ground bits, VM.find 8302 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8781 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists ground bits, VM.find 8782 result = Some (Gval ground bits).
Proof.
 intros H8302 H8781 Step.
 eapply (selected_node_concrete_ground_output data_writer_node_offsets flat_statements data_writer_expected_nodes 8782 writer_expr_8782 inputs path flat_memories old current result).
 - exact data_writer_node_positions.
 - exact data_writer_node_safety.
 - apply (@List.nth_error_In _ data_writer_expected_nodes 100 (8782,writer_expr_8782)). vm_compute. reflexivity.
 - apply writer_ready_8782; assumption.
 - exact Step.
Qed.
Lemma data_writer_node_output_8783 inputs path old current result :
 (exists ground bits, VM.find 8300 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8782 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists ground bits, VM.find 8783 result = Some (Gval ground bits).
Proof.
 intros H8300 H8782 Step.
 eapply (selected_node_concrete_ground_output data_writer_node_offsets flat_statements data_writer_expected_nodes 8783 writer_expr_8783 inputs path flat_memories old current result).
 - exact data_writer_node_positions.
 - exact data_writer_node_safety.
 - apply (@List.nth_error_In _ data_writer_expected_nodes 101 (8783,writer_expr_8783)). vm_compute. reflexivity.
 - apply writer_ready_8783; assumption.
 - exact Step.
Qed.
Lemma data_writer_node_output_8784 inputs path old current result :
 (exists ground bits, VM.find 8298 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8783 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists ground bits, VM.find 8784 result = Some (Gval ground bits).
Proof.
 intros H8298 H8783 Step.
 eapply (selected_node_concrete_ground_output data_writer_node_offsets flat_statements data_writer_expected_nodes 8784 writer_expr_8784 inputs path flat_memories old current result).
 - exact data_writer_node_positions.
 - exact data_writer_node_safety.
 - apply (@List.nth_error_In _ data_writer_expected_nodes 102 (8784,writer_expr_8784)). vm_compute. reflexivity.
 - apply writer_ready_8784; assumption.
 - exact Step.
Qed.
Lemma data_writer_node_output_8785 inputs path old current result :
 (exists ground bits, VM.find 8296 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8784 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists ground bits, VM.find 8785 result = Some (Gval ground bits).
Proof.
 intros H8296 H8784 Step.
 eapply (selected_node_concrete_ground_output data_writer_node_offsets flat_statements data_writer_expected_nodes 8785 writer_expr_8785 inputs path flat_memories old current result).
 - exact data_writer_node_positions.
 - exact data_writer_node_safety.
 - apply (@List.nth_error_In _ data_writer_expected_nodes 103 (8785,writer_expr_8785)). vm_compute. reflexivity.
 - apply writer_ready_8785; assumption.
 - exact Step.
Qed.
Lemma data_writer_node_output_8786 inputs path old current result :
 (exists ground bits, VM.find 8294 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8785 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists ground bits, VM.find 8786 result = Some (Gval ground bits).
Proof.
 intros H8294 H8785 Step.
 eapply (selected_node_concrete_ground_output data_writer_node_offsets flat_statements data_writer_expected_nodes 8786 writer_expr_8786 inputs path flat_memories old current result).
 - exact data_writer_node_positions.
 - exact data_writer_node_safety.
 - apply (@List.nth_error_In _ data_writer_expected_nodes 104 (8786,writer_expr_8786)). vm_compute. reflexivity.
 - apply writer_ready_8786; assumption.
 - exact Step.
Qed.
Lemma data_writer_node_output_8787 inputs path old current result :
 (exists ground bits, VM.find 8292 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8786 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists ground bits, VM.find 8787 result = Some (Gval ground bits).
Proof.
 intros H8292 H8786 Step.
 eapply (selected_node_concrete_ground_output data_writer_node_offsets flat_statements data_writer_expected_nodes 8787 writer_expr_8787 inputs path flat_memories old current result).
 - exact data_writer_node_positions.
 - exact data_writer_node_safety.
 - apply (@List.nth_error_In _ data_writer_expected_nodes 105 (8787,writer_expr_8787)). vm_compute. reflexivity.
 - apply writer_ready_8787; assumption.
 - exact Step.
Qed.
Lemma data_writer_node_output_8788 inputs path old current result :
 (exists ground bits, VM.find 8290 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8787 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists ground bits, VM.find 8788 result = Some (Gval ground bits).
Proof.
 intros H8290 H8787 Step.
 eapply (selected_node_concrete_ground_output data_writer_node_offsets flat_statements data_writer_expected_nodes 8788 writer_expr_8788 inputs path flat_memories old current result).
 - exact data_writer_node_positions.
 - exact data_writer_node_safety.
 - apply (@List.nth_error_In _ data_writer_expected_nodes 106 (8788,writer_expr_8788)). vm_compute. reflexivity.
 - apply writer_ready_8788; assumption.
 - exact Step.
Qed.
Lemma data_writer_node_output_8789 inputs path old current result :
 (exists ground bits, VM.find 8288 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8788 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists ground bits, VM.find 8789 result = Some (Gval ground bits).
Proof.
 intros H8288 H8788 Step.
 eapply (selected_node_concrete_ground_output data_writer_node_offsets flat_statements data_writer_expected_nodes 8789 writer_expr_8789 inputs path flat_memories old current result).
 - exact data_writer_node_positions.
 - exact data_writer_node_safety.
 - apply (@List.nth_error_In _ data_writer_expected_nodes 107 (8789,writer_expr_8789)). vm_compute. reflexivity.
 - apply writer_ready_8789; assumption.
 - exact Step.
Qed.
Lemma data_writer_node_output_8790 inputs path old current result :
 (exists ground bits, VM.find 8286 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8789 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists ground bits, VM.find 8790 result = Some (Gval ground bits).
Proof.
 intros H8286 H8789 Step.
 eapply (selected_node_concrete_ground_output data_writer_node_offsets flat_statements data_writer_expected_nodes 8790 writer_expr_8790 inputs path flat_memories old current result).
 - exact data_writer_node_positions.
 - exact data_writer_node_safety.
 - apply (@List.nth_error_In _ data_writer_expected_nodes 108 (8790,writer_expr_8790)). vm_compute. reflexivity.
 - apply writer_ready_8790; assumption.
 - exact Step.
Qed.
Lemma data_writer_node_output_8791 inputs path old current result :
 (exists ground bits, VM.find 8284 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8790 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists ground bits, VM.find 8791 result = Some (Gval ground bits).
Proof.
 intros H8284 H8790 Step.
 eapply (selected_node_concrete_ground_output data_writer_node_offsets flat_statements data_writer_expected_nodes 8791 writer_expr_8791 inputs path flat_memories old current result).
 - exact data_writer_node_positions.
 - exact data_writer_node_safety.
 - apply (@List.nth_error_In _ data_writer_expected_nodes 109 (8791,writer_expr_8791)). vm_compute. reflexivity.
 - apply writer_ready_8791; assumption.
 - exact Step.
Qed.
Lemma data_writer_node_output_8792 inputs path old current result :
 (exists ground bits, VM.find 8282 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8791 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists ground bits, VM.find 8792 result = Some (Gval ground bits).
Proof.
 intros H8282 H8791 Step.
 eapply (selected_node_concrete_ground_output data_writer_node_offsets flat_statements data_writer_expected_nodes 8792 writer_expr_8792 inputs path flat_memories old current result).
 - exact data_writer_node_positions.
 - exact data_writer_node_safety.
 - apply (@List.nth_error_In _ data_writer_expected_nodes 110 (8792,writer_expr_8792)). vm_compute. reflexivity.
 - apply writer_ready_8792; assumption.
 - exact Step.
Qed.
Lemma data_writer_node_output_8793 inputs path old current result :
 (exists ground bits, VM.find 8280 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8792 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists ground bits, VM.find 8793 result = Some (Gval ground bits).
Proof.
 intros H8280 H8792 Step.
 eapply (selected_node_concrete_ground_output data_writer_node_offsets flat_statements data_writer_expected_nodes 8793 writer_expr_8793 inputs path flat_memories old current result).
 - exact data_writer_node_positions.
 - exact data_writer_node_safety.
 - apply (@List.nth_error_In _ data_writer_expected_nodes 111 (8793,writer_expr_8793)). vm_compute. reflexivity.
 - apply writer_ready_8793; assumption.
 - exact Step.
Qed.
Lemma data_writer_node_output_8794 inputs path old current result :
 (exists ground bits, VM.find 8278 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8793 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists ground bits, VM.find 8794 result = Some (Gval ground bits).
Proof.
 intros H8278 H8793 Step.
 eapply (selected_node_concrete_ground_output data_writer_node_offsets flat_statements data_writer_expected_nodes 8794 writer_expr_8794 inputs path flat_memories old current result).
 - exact data_writer_node_positions.
 - exact data_writer_node_safety.
 - apply (@List.nth_error_In _ data_writer_expected_nodes 112 (8794,writer_expr_8794)). vm_compute. reflexivity.
 - apply writer_ready_8794; assumption.
 - exact Step.
Qed.
Lemma data_writer_node_output_8795 inputs path old current result :
 (exists ground bits, VM.find 8276 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8794 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists ground bits, VM.find 8795 result = Some (Gval ground bits).
Proof.
 intros H8276 H8794 Step.
 eapply (selected_node_concrete_ground_output data_writer_node_offsets flat_statements data_writer_expected_nodes 8795 writer_expr_8795 inputs path flat_memories old current result).
 - exact data_writer_node_positions.
 - exact data_writer_node_safety.
 - apply (@List.nth_error_In _ data_writer_expected_nodes 113 (8795,writer_expr_8795)). vm_compute. reflexivity.
 - apply writer_ready_8795; assumption.
 - exact Step.
Qed.
Lemma data_writer_node_output_8796 inputs path old current result :
 (exists ground bits, VM.find 8274 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8795 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists ground bits, VM.find 8796 result = Some (Gval ground bits).
Proof.
 intros H8274 H8795 Step.
 eapply (selected_node_concrete_ground_output data_writer_node_offsets flat_statements data_writer_expected_nodes 8796 writer_expr_8796 inputs path flat_memories old current result).
 - exact data_writer_node_positions.
 - exact data_writer_node_safety.
 - apply (@List.nth_error_In _ data_writer_expected_nodes 114 (8796,writer_expr_8796)). vm_compute. reflexivity.
 - apply writer_ready_8796; assumption.
 - exact Step.
Qed.
Lemma data_writer_node_output_8797 inputs path old current result :
 (exists ground bits, VM.find 8272 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8796 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists ground bits, VM.find 8797 result = Some (Gval ground bits).
Proof.
 intros H8272 H8796 Step.
 eapply (selected_node_concrete_ground_output data_writer_node_offsets flat_statements data_writer_expected_nodes 8797 writer_expr_8797 inputs path flat_memories old current result).
 - exact data_writer_node_positions.
 - exact data_writer_node_safety.
 - apply (@List.nth_error_In _ data_writer_expected_nodes 115 (8797,writer_expr_8797)). vm_compute. reflexivity.
 - apply writer_ready_8797; assumption.
 - exact Step.
Qed.
Lemma data_writer_node_output_8798 inputs path old current result :
 (exists ground bits, VM.find 8270 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8797 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists ground bits, VM.find 8798 result = Some (Gval ground bits).
Proof.
 intros H8270 H8797 Step.
 eapply (selected_node_concrete_ground_output data_writer_node_offsets flat_statements data_writer_expected_nodes 8798 writer_expr_8798 inputs path flat_memories old current result).
 - exact data_writer_node_positions.
 - exact data_writer_node_safety.
 - apply (@List.nth_error_In _ data_writer_expected_nodes 116 (8798,writer_expr_8798)). vm_compute. reflexivity.
 - apply writer_ready_8798; assumption.
 - exact Step.
Qed.
Lemma data_writer_node_output_8799 inputs path old current result :
 (exists ground bits, VM.find 8268 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8798 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists ground bits, VM.find 8799 result = Some (Gval ground bits).
Proof.
 intros H8268 H8798 Step.
 eapply (selected_node_concrete_ground_output data_writer_node_offsets flat_statements data_writer_expected_nodes 8799 writer_expr_8799 inputs path flat_memories old current result).
 - exact data_writer_node_positions.
 - exact data_writer_node_safety.
 - apply (@List.nth_error_In _ data_writer_expected_nodes 117 (8799,writer_expr_8799)). vm_compute. reflexivity.
 - apply writer_ready_8799; assumption.
 - exact Step.
Qed.
Lemma data_writer_node_output_8800 inputs path old current result :
 (exists ground bits, VM.find 8266 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8799 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists ground bits, VM.find 8800 result = Some (Gval ground bits).
Proof.
 intros H8266 H8799 Step.
 eapply (selected_node_concrete_ground_output data_writer_node_offsets flat_statements data_writer_expected_nodes 8800 writer_expr_8800 inputs path flat_memories old current result).
 - exact data_writer_node_positions.
 - exact data_writer_node_safety.
 - apply (@List.nth_error_In _ data_writer_expected_nodes 118 (8800,writer_expr_8800)). vm_compute. reflexivity.
 - apply writer_ready_8800; assumption.
 - exact Step.
Qed.
Lemma data_writer_node_output_8801 inputs path old current result :
 (exists ground bits, VM.find 8264 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8800 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists ground bits, VM.find 8801 result = Some (Gval ground bits).
Proof.
 intros H8264 H8800 Step.
 eapply (selected_node_concrete_ground_output data_writer_node_offsets flat_statements data_writer_expected_nodes 8801 writer_expr_8801 inputs path flat_memories old current result).
 - exact data_writer_node_positions.
 - exact data_writer_node_safety.
 - apply (@List.nth_error_In _ data_writer_expected_nodes 119 (8801,writer_expr_8801)). vm_compute. reflexivity.
 - apply writer_ready_8801; assumption.
 - exact Step.
Qed.
Lemma data_writer_node_output_9183 inputs path old current result :
 (exists ground bits, VM.find 39 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists ground bits, VM.find 9183 result = Some (Gval ground bits).
Proof.
 intros H39 Step.
 eapply (selected_node_concrete_ground_output data_writer_node_offsets flat_statements data_writer_expected_nodes 9183 writer_expr_9183 inputs path flat_memories old current result).
 - exact data_writer_node_positions.
 - exact data_writer_node_safety.
 - apply (@List.nth_error_In _ data_writer_expected_nodes 120 (9183,writer_expr_9183)). vm_compute. reflexivity.
 - apply writer_ready_9183; assumption.
 - exact Step.
Qed.
Lemma data_writer_node_output_9184 inputs path old current result :
 (exists ground bits, VM.find 36 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 9183 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists ground bits, VM.find 9184 result = Some (Gval ground bits).
Proof.
 intros H36 H9183 Step.
 eapply (selected_node_concrete_ground_output data_writer_node_offsets flat_statements data_writer_expected_nodes 9184 writer_expr_9184 inputs path flat_memories old current result).
 - exact data_writer_node_positions.
 - exact data_writer_node_safety.
 - apply (@List.nth_error_In _ data_writer_expected_nodes 121 (9184,writer_expr_9184)). vm_compute. reflexivity.
 - apply writer_ready_9184; assumption.
 - exact Step.
Qed.
Lemma data_writer_node_output_9185 inputs path old current result :
 (exists ground bits, VM.find 9184 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists ground bits, VM.find 9185 result = Some (Gval ground bits).
Proof.
 intros H9184 Step.
 eapply (selected_node_concrete_ground_output data_writer_node_offsets flat_statements data_writer_expected_nodes 9185 writer_expr_9185 inputs path flat_memories old current result).
 - exact data_writer_node_positions.
 - exact data_writer_node_safety.
 - apply (@List.nth_error_In _ data_writer_expected_nodes 122 (9185,writer_expr_9185)). vm_compute. reflexivity.
 - apply writer_ready_9185; assumption.
 - exact Step.
Qed.
Lemma data_writer_node_output_9188 inputs path old current result :
 (exists ground bits, VM.find 9187 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists ground bits, VM.find 9188 result = Some (Gval ground bits).
Proof.
 intros H9187 Step.
 eapply (selected_node_concrete_ground_output data_writer_node_offsets flat_statements data_writer_expected_nodes 9188 writer_expr_9188 inputs path flat_memories old current result).
 - exact data_writer_node_positions.
 - exact data_writer_node_safety.
 - apply (@List.nth_error_In _ data_writer_expected_nodes 123 (9188,writer_expr_9188)). vm_compute. reflexivity.
 - apply writer_ready_9188; assumption.
 - exact Step.
Qed.
Lemma data_writer_node_output_9189 inputs path old current result :
 (exists ground bits, VM.find 9188 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists ground bits, VM.find 9189 result = Some (Gval ground bits).
Proof.
 intros H9188 Step.
 eapply (selected_node_concrete_ground_output data_writer_node_offsets flat_statements data_writer_expected_nodes 9189 writer_expr_9189 inputs path flat_memories old current result).
 - exact data_writer_node_positions.
 - exact data_writer_node_safety.
 - apply (@List.nth_error_In _ data_writer_expected_nodes 124 (9189,writer_expr_9189)). vm_compute. reflexivity.
 - apply writer_ready_9189; assumption.
 - exact Step.
Qed.
Lemma data_writer_node_output_9190 inputs path old current result :
 (exists ground bits, VM.find 9189 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists ground bits, VM.find 9190 result = Some (Gval ground bits).
Proof.
 intros H9189 Step.
 eapply (selected_node_concrete_ground_output data_writer_node_offsets flat_statements data_writer_expected_nodes 9190 writer_expr_9190 inputs path flat_memories old current result).
 - exact data_writer_node_positions.
 - exact data_writer_node_safety.
 - apply (@List.nth_error_In _ data_writer_expected_nodes 125 (9190,writer_expr_9190)). vm_compute. reflexivity.
 - apply writer_ready_9190; assumption.
 - exact Step.
Qed.
Lemma data_writer_node_output_9191 inputs path old current result :
 (exists ground bits, VM.find 39 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists ground bits, VM.find 9191 result = Some (Gval ground bits).
Proof.
 intros H39 Step.
 eapply (selected_node_concrete_ground_output data_writer_node_offsets flat_statements data_writer_expected_nodes 9191 writer_expr_9191 inputs path flat_memories old current result).
 - exact data_writer_node_positions.
 - exact data_writer_node_safety.
 - apply (@List.nth_error_In _ data_writer_expected_nodes 126 (9191,writer_expr_9191)). vm_compute. reflexivity.
 - apply writer_ready_9191; assumption.
 - exact Step.
Qed.
Lemma data_writer_node_output_9192 inputs path old current result :
 (exists ground bits, VM.find 36 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 9191 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists ground bits, VM.find 9192 result = Some (Gval ground bits).
Proof.
 intros H36 H9191 Step.
 eapply (selected_node_concrete_ground_output data_writer_node_offsets flat_statements data_writer_expected_nodes 9192 writer_expr_9192 inputs path flat_memories old current result).
 - exact data_writer_node_positions.
 - exact data_writer_node_safety.
 - apply (@List.nth_error_In _ data_writer_expected_nodes 127 (9192,writer_expr_9192)). vm_compute. reflexivity.
 - apply writer_ready_9192; assumption.
 - exact Step.
Qed.
Lemma data_writer_node_output_9193 inputs path old current result :
 (exists ground bits, VM.find 9192 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists ground bits, VM.find 9193 result = Some (Gval ground bits).
Proof.
 intros H9192 Step.
 eapply (selected_node_concrete_ground_output data_writer_node_offsets flat_statements data_writer_expected_nodes 9193 writer_expr_9193 inputs path flat_memories old current result).
 - exact data_writer_node_positions.
 - exact data_writer_node_safety.
 - apply (@List.nth_error_In _ data_writer_expected_nodes 128 (9193,writer_expr_9193)). vm_compute. reflexivity.
 - apply writer_ready_9193; assumption.
 - exact Step.
Qed.
Lemma data_writer_node_output_9196 inputs path old current result :
 (exists ground bits, VM.find 9195 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists ground bits, VM.find 9196 result = Some (Gval ground bits).
Proof.
 intros H9195 Step.
 eapply (selected_node_concrete_ground_output data_writer_node_offsets flat_statements data_writer_expected_nodes 9196 writer_expr_9196 inputs path flat_memories old current result).
 - exact data_writer_node_positions.
 - exact data_writer_node_safety.
 - apply (@List.nth_error_In _ data_writer_expected_nodes 129 (9196,writer_expr_9196)). vm_compute. reflexivity.
 - apply writer_ready_9196; assumption.
 - exact Step.
Qed.
Lemma data_writer_node_output_9197 inputs path old current result :
 (exists ground bits, VM.find 9196 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists ground bits, VM.find 9197 result = Some (Gval ground bits).
Proof.
 intros H9196 Step.
 eapply (selected_node_concrete_ground_output data_writer_node_offsets flat_statements data_writer_expected_nodes 9197 writer_expr_9197 inputs path flat_memories old current result).
 - exact data_writer_node_positions.
 - exact data_writer_node_safety.
 - apply (@List.nth_error_In _ data_writer_expected_nodes 130 (9197,writer_expr_9197)). vm_compute. reflexivity.
 - apply writer_ready_9197; assumption.
 - exact Step.
Qed.
Lemma data_writer_node_output_9198 inputs path old current result :
 (exists ground bits, VM.find 9190 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 9197 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists ground bits, VM.find 9198 result = Some (Gval ground bits).
Proof.
 intros H9190 H9197 Step.
 eapply (selected_node_concrete_ground_output data_writer_node_offsets flat_statements data_writer_expected_nodes 9198 writer_expr_9198 inputs path flat_memories old current result).
 - exact data_writer_node_positions.
 - exact data_writer_node_safety.
 - apply (@List.nth_error_In _ data_writer_expected_nodes 131 (9198,writer_expr_9198)). vm_compute. reflexivity.
 - apply writer_ready_9198; assumption.
 - exact Step.
Qed.
Lemma data_writer_node_output_9199 inputs path old current result :
 (exists ground bits, VM.find 39 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists ground bits, VM.find 9199 result = Some (Gval ground bits).
Proof.
 intros H39 Step.
 eapply (selected_node_concrete_ground_output data_writer_node_offsets flat_statements data_writer_expected_nodes 9199 writer_expr_9199 inputs path flat_memories old current result).
 - exact data_writer_node_positions.
 - exact data_writer_node_safety.
 - apply (@List.nth_error_In _ data_writer_expected_nodes 132 (9199,writer_expr_9199)). vm_compute. reflexivity.
 - apply writer_ready_9199; assumption.
 - exact Step.
Qed.
Lemma data_writer_node_output_9200 inputs path old current result :
 (exists ground bits, VM.find 36 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 9199 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists ground bits, VM.find 9200 result = Some (Gval ground bits).
Proof.
 intros H36 H9199 Step.
 eapply (selected_node_concrete_ground_output data_writer_node_offsets flat_statements data_writer_expected_nodes 9200 writer_expr_9200 inputs path flat_memories old current result).
 - exact data_writer_node_positions.
 - exact data_writer_node_safety.
 - apply (@List.nth_error_In _ data_writer_expected_nodes 133 (9200,writer_expr_9200)). vm_compute. reflexivity.
 - apply writer_ready_9200; assumption.
 - exact Step.
Qed.
Lemma data_writer_node_output_9201 inputs path old current result :
 (exists ground bits, VM.find 9200 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists ground bits, VM.find 9201 result = Some (Gval ground bits).
Proof.
 intros H9200 Step.
 eapply (selected_node_concrete_ground_output data_writer_node_offsets flat_statements data_writer_expected_nodes 9201 writer_expr_9201 inputs path flat_memories old current result).
 - exact data_writer_node_positions.
 - exact data_writer_node_safety.
 - apply (@List.nth_error_In _ data_writer_expected_nodes 134 (9201,writer_expr_9201)). vm_compute. reflexivity.
 - apply writer_ready_9201; assumption.
 - exact Step.
Qed.
Lemma data_writer_node_output_9204 inputs path old current result :
 (exists ground bits, VM.find 9203 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists ground bits, VM.find 9204 result = Some (Gval ground bits).
Proof.
 intros H9203 Step.
 eapply (selected_node_concrete_ground_output data_writer_node_offsets flat_statements data_writer_expected_nodes 9204 writer_expr_9204 inputs path flat_memories old current result).
 - exact data_writer_node_positions.
 - exact data_writer_node_safety.
 - apply (@List.nth_error_In _ data_writer_expected_nodes 135 (9204,writer_expr_9204)). vm_compute. reflexivity.
 - apply writer_ready_9204; assumption.
 - exact Step.
Qed.
Lemma data_writer_node_output_9205 inputs path old current result :
 (exists ground bits, VM.find 9204 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists ground bits, VM.find 9205 result = Some (Gval ground bits).
Proof.
 intros H9204 Step.
 eapply (selected_node_concrete_ground_output data_writer_node_offsets flat_statements data_writer_expected_nodes 9205 writer_expr_9205 inputs path flat_memories old current result).
 - exact data_writer_node_positions.
 - exact data_writer_node_safety.
 - apply (@List.nth_error_In _ data_writer_expected_nodes 136 (9205,writer_expr_9205)). vm_compute. reflexivity.
 - apply writer_ready_9205; assumption.
 - exact Step.
Qed.
Lemma data_writer_node_output_9206 inputs path old current result :
 (exists ground bits, VM.find 9198 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 9205 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists ground bits, VM.find 9206 result = Some (Gval ground bits).
Proof.
 intros H9198 H9205 Step.
 eapply (selected_node_concrete_ground_output data_writer_node_offsets flat_statements data_writer_expected_nodes 9206 writer_expr_9206 inputs path flat_memories old current result).
 - exact data_writer_node_positions.
 - exact data_writer_node_safety.
 - apply (@List.nth_error_In _ data_writer_expected_nodes 137 (9206,writer_expr_9206)). vm_compute. reflexivity.
 - apply writer_ready_9206; assumption.
 - exact Step.
Qed.
Lemma data_writer_node_output_9207 inputs path old current result :
 (exists ground bits, VM.find 39 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists ground bits, VM.find 9207 result = Some (Gval ground bits).
Proof.
 intros H39 Step.
 eapply (selected_node_concrete_ground_output data_writer_node_offsets flat_statements data_writer_expected_nodes 9207 writer_expr_9207 inputs path flat_memories old current result).
 - exact data_writer_node_positions.
 - exact data_writer_node_safety.
 - apply (@List.nth_error_In _ data_writer_expected_nodes 138 (9207,writer_expr_9207)). vm_compute. reflexivity.
 - apply writer_ready_9207; assumption.
 - exact Step.
Qed.
Lemma data_writer_node_output_9208 inputs path old current result :
 (exists ground bits, VM.find 36 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 9207 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists ground bits, VM.find 9208 result = Some (Gval ground bits).
Proof.
 intros H36 H9207 Step.
 eapply (selected_node_concrete_ground_output data_writer_node_offsets flat_statements data_writer_expected_nodes 9208 writer_expr_9208 inputs path flat_memories old current result).
 - exact data_writer_node_positions.
 - exact data_writer_node_safety.
 - apply (@List.nth_error_In _ data_writer_expected_nodes 139 (9208,writer_expr_9208)). vm_compute. reflexivity.
 - apply writer_ready_9208; assumption.
 - exact Step.
Qed.
Lemma data_writer_node_output_9209 inputs path old current result :
 (exists ground bits, VM.find 9208 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists ground bits, VM.find 9209 result = Some (Gval ground bits).
Proof.
 intros H9208 Step.
 eapply (selected_node_concrete_ground_output data_writer_node_offsets flat_statements data_writer_expected_nodes 9209 writer_expr_9209 inputs path flat_memories old current result).
 - exact data_writer_node_positions.
 - exact data_writer_node_safety.
 - apply (@List.nth_error_In _ data_writer_expected_nodes 140 (9209,writer_expr_9209)). vm_compute. reflexivity.
 - apply writer_ready_9209; assumption.
 - exact Step.
Qed.
Lemma data_writer_node_output_9212 inputs path old current result :
 (exists ground bits, VM.find 9211 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists ground bits, VM.find 9212 result = Some (Gval ground bits).
Proof.
 intros H9211 Step.
 eapply (selected_node_concrete_ground_output data_writer_node_offsets flat_statements data_writer_expected_nodes 9212 writer_expr_9212 inputs path flat_memories old current result).
 - exact data_writer_node_positions.
 - exact data_writer_node_safety.
 - apply (@List.nth_error_In _ data_writer_expected_nodes 141 (9212,writer_expr_9212)). vm_compute. reflexivity.
 - apply writer_ready_9212; assumption.
 - exact Step.
Qed.
Lemma data_writer_node_output_9213 inputs path old current result :
 (exists ground bits, VM.find 9212 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists ground bits, VM.find 9213 result = Some (Gval ground bits).
Proof.
 intros H9212 Step.
 eapply (selected_node_concrete_ground_output data_writer_node_offsets flat_statements data_writer_expected_nodes 9213 writer_expr_9213 inputs path flat_memories old current result).
 - exact data_writer_node_positions.
 - exact data_writer_node_safety.
 - apply (@List.nth_error_In _ data_writer_expected_nodes 142 (9213,writer_expr_9213)). vm_compute. reflexivity.
 - apply writer_ready_9213; assumption.
 - exact Step.
Qed.
Lemma data_writer_node_output_9214 inputs path old current result :
 (exists ground bits, VM.find 9206 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 9213 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists ground bits, VM.find 9214 result = Some (Gval ground bits).
Proof.
 intros H9206 H9213 Step.
 eapply (selected_node_concrete_ground_output data_writer_node_offsets flat_statements data_writer_expected_nodes 9214 writer_expr_9214 inputs path flat_memories old current result).
 - exact data_writer_node_positions.
 - exact data_writer_node_safety.
 - apply (@List.nth_error_In _ data_writer_expected_nodes 143 (9214,writer_expr_9214)). vm_compute. reflexivity.
 - apply writer_ready_9214; assumption.
 - exact Step.
Qed.
Lemma data_writer_node_output_9223 inputs path old current result :
 (exists ground bits, VM.find 39 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists ground bits, VM.find 9223 result = Some (Gval ground bits).
Proof.
 intros H39 Step.
 eapply (selected_node_concrete_ground_output data_writer_node_offsets flat_statements data_writer_expected_nodes 9223 writer_expr_9223 inputs path flat_memories old current result).
 - exact data_writer_node_positions.
 - exact data_writer_node_safety.
 - apply (@List.nth_error_In _ data_writer_expected_nodes 144 (9223,writer_expr_9223)). vm_compute. reflexivity.
 - apply writer_ready_9223; assumption.
 - exact Step.
Qed.
Lemma data_writer_node_output_9224 inputs path old current result :
 (exists ground bits, VM.find 9182 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists ground bits, VM.find 9224 result = Some (Gval ground bits).
Proof.
 intros H9182 Step.
 eapply (selected_node_concrete_ground_output data_writer_node_offsets flat_statements data_writer_expected_nodes 9224 writer_expr_9224 inputs path flat_memories old current result).
 - exact data_writer_node_positions.
 - exact data_writer_node_safety.
 - apply (@List.nth_error_In _ data_writer_expected_nodes 145 (9224,writer_expr_9224)). vm_compute. reflexivity.
 - apply writer_ready_9224; assumption.
 - exact Step.
Qed.
Lemma data_writer_node_output_9225 inputs path old current result :
 (exists ground bits, VM.find 9223 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 9224 old = Some (Gval (Fuint ground) bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists ground bits, VM.find 9225 result = Some (Gval ground bits).
Proof.
 intros H9223 H9224 Step.
 eapply (selected_node_concrete_ground_output data_writer_node_offsets flat_statements data_writer_expected_nodes 9225 writer_expr_9225 inputs path flat_memories old current result).
 - exact data_writer_node_positions.
 - exact data_writer_node_safety.
 - apply (@List.nth_error_In _ data_writer_expected_nodes 146 (9225,writer_expr_9225)). vm_compute. reflexivity.
 - apply writer_ready_9225; assumption.
 - exact Step.
Qed.
Lemma data_writer_node_output_9227 inputs path old current result :
 (exists ground bits, VM.find 9223 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists ground bits, VM.find 9227 result = Some (Gval ground bits).
Proof.
 intros H9223 Step.
 eapply (selected_node_concrete_ground_output data_writer_node_offsets flat_statements data_writer_expected_nodes 9227 writer_expr_9227 inputs path flat_memories old current result).
 - exact data_writer_node_positions.
 - exact data_writer_node_safety.
 - apply (@List.nth_error_In _ data_writer_expected_nodes 147 (9227,writer_expr_9227)). vm_compute. reflexivity.
 - apply writer_ready_9227; assumption.
 - exact Step.
Qed.
Lemma data_writer_node_output_9228 inputs path old current result :
 (exists ground bits, VM.find 9223 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists ground bits, VM.find 9228 result = Some (Gval ground bits).
Proof.
 intros H9223 Step.
 eapply (selected_node_concrete_ground_output data_writer_node_offsets flat_statements data_writer_expected_nodes 9228 writer_expr_9228 inputs path flat_memories old current result).
 - exact data_writer_node_positions.
 - exact data_writer_node_safety.
 - apply (@List.nth_error_In _ data_writer_expected_nodes 148 (9228,writer_expr_9228)). vm_compute. reflexivity.
 - apply writer_ready_9228; assumption.
 - exact Step.
Qed.
Lemma data_writer_node_output_9229 inputs path old current result :
 (exists ground bits, VM.find 9214 old = Some (Gval (Fuint ground) bits)) ->
 (exists ground bits, VM.find 9223 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists ground bits, VM.find 9229 result = Some (Gval ground bits).
Proof.
 intros H9214 H9223 Step.
 eapply (selected_node_concrete_ground_output data_writer_node_offsets flat_statements data_writer_expected_nodes 9229 writer_expr_9229 inputs path flat_memories old current result).
 - exact data_writer_node_positions.
 - exact data_writer_node_safety.
 - apply (@List.nth_error_In _ data_writer_expected_nodes 149 (9229,writer_expr_9229)). vm_compute. reflexivity.
 - apply writer_ready_9229; assumption.
 - exact Step.
Qed.
Lemma data_writer_node_output_9230 inputs path old current result :
 (exists ground bits, VM.find 36 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 9225 old = Some (Gval (Fuint ground) bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists ground bits, VM.find 9230 result = Some (Gval ground bits).
Proof.
 intros H36 H9225 Step.
 eapply (selected_node_concrete_ground_output data_writer_node_offsets flat_statements data_writer_expected_nodes 9230 writer_expr_9230 inputs path flat_memories old current result).
 - exact data_writer_node_positions.
 - exact data_writer_node_safety.
 - apply (@List.nth_error_In _ data_writer_expected_nodes 150 (9230,writer_expr_9230)). vm_compute. reflexivity.
 - apply writer_ready_9230; assumption.
 - exact Step.
Qed.
Lemma data_writer_node_output_9232 inputs path old current result :
 (exists ground bits, VM.find 36 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 9227 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists ground bits, VM.find 9232 result = Some (Gval ground bits).
Proof.
 intros H36 H9227 Step.
 eapply (selected_node_concrete_ground_output data_writer_node_offsets flat_statements data_writer_expected_nodes 9232 writer_expr_9232 inputs path flat_memories old current result).
 - exact data_writer_node_positions.
 - exact data_writer_node_safety.
 - apply (@List.nth_error_In _ data_writer_expected_nodes 151 (9232,writer_expr_9232)). vm_compute. reflexivity.
 - apply writer_ready_9232; assumption.
 - exact Step.
Qed.
Lemma data_writer_node_output_9233 inputs path old current result :
 (exists ground bits, VM.find 36 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 9228 old = Some (Gval (Fuint ground) bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists ground bits, VM.find 9233 result = Some (Gval ground bits).
Proof.
 intros H36 H9228 Step.
 eapply (selected_node_concrete_ground_output data_writer_node_offsets flat_statements data_writer_expected_nodes 9233 writer_expr_9233 inputs path flat_memories old current result).
 - exact data_writer_node_positions.
 - exact data_writer_node_safety.
 - apply (@List.nth_error_In _ data_writer_expected_nodes 152 (9233,writer_expr_9233)). vm_compute. reflexivity.
 - apply writer_ready_9233; assumption.
 - exact Step.
Qed.
Lemma data_writer_node_output_9234 inputs path old current result :
 (exists ground bits, VM.find 36 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 9229 old = Some (Gval (Fuint ground) bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists ground bits, VM.find 9234 result = Some (Gval ground bits).
Proof.
 intros H36 H9229 Step.
 eapply (selected_node_concrete_ground_output data_writer_node_offsets flat_statements data_writer_expected_nodes 9234 writer_expr_9234 inputs path flat_memories old current result).
 - exact data_writer_node_positions.
 - exact data_writer_node_safety.
 - apply (@List.nth_error_In _ data_writer_expected_nodes 153 (9234,writer_expr_9234)). vm_compute. reflexivity.
 - apply writer_ready_9234; assumption.
 - exact Step.
Qed.
Print Assumptions data_writer_node_output_9234.
