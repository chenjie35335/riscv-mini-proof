Require Import CoreSocModel ComparisonNodes SelectedUIntNodeCongruence X0ConcreteExpressionCertificates X0UIntExpressionCertificates X0ConcretePositionCertificate.
From Coq Require Import ZArith List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Theorem exception_node_140_congruent invalid left right next_left next_right :
 (exists width bits, VM.find 123 left = Some (Gval (Fuint width) bits)) ->
 VM.find 123 left = VM.find 123 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 140 next_left = VM.find 140 next_right.
Proof.
 intros H123 E123 L R.
 apply (x0_selected_uint_node_congruent 140 x0_concrete_expr_140 invalid left right next_left next_right).
 - apply (List.nth_error_In x0_expected_nodes 0). vm_compute. reflexivity.
 - intro site. cbn [x0_concrete_expr_140 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E123.
   reflexivity.
 - intros site value Eval.
   destruct (x0_uint_result_140 invalid site flat_memories left value H123 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Theorem exception_node_141_congruent invalid left right next_left next_right :
 (exists width bits, VM.find 123 left = Some (Gval (Fuint width) bits)) ->
 VM.find 123 left = VM.find 123 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 141 next_left = VM.find 141 next_right.
Proof.
 intros H123 E123 L R.
 apply (x0_selected_uint_node_congruent 141 x0_concrete_expr_141 invalid left right next_left next_right).
 - apply (List.nth_error_In x0_expected_nodes 1). vm_compute. reflexivity.
 - intro site. cbn [x0_concrete_expr_141 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E123.
   reflexivity.
 - intros site value Eval.
   destruct (x0_uint_result_141 invalid site flat_memories left value H123 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Theorem exception_node_284_congruent invalid left right next_left next_right :
 (exists width bits, VM.find 118 left = Some (Gval (Fuint width) bits)) ->
 VM.find 118 left = VM.find 118 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 284 next_left = VM.find 284 next_right.
Proof.
 intros H118 E118 L R.
 apply (x0_selected_uint_node_congruent 284 x0_concrete_expr_284 invalid left right next_left next_right).
 - apply (List.nth_error_In x0_expected_nodes 4). vm_compute. reflexivity.
 - intro site. cbn [x0_concrete_expr_284 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E118.
   reflexivity.
 - intros site value Eval.
   destruct (x0_uint_result_284 invalid site flat_memories left value H118 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Theorem exception_node_393_congruent invalid left right next_left next_right :
 (exists width bits, VM.find 118 left = Some (Gval (Fuint width) bits)) ->
 VM.find 118 left = VM.find 118 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 393 next_left = VM.find 393 next_right.
Proof.
 intros H118 E118 L R.
 apply (x0_selected_uint_node_congruent 393 x0_concrete_expr_393 invalid left right next_left next_right).
 - apply (List.nth_error_In x0_expected_nodes 108). vm_compute. reflexivity.
 - intro site. cbn [x0_concrete_expr_393 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E118.
   reflexivity.
 - intros site value Eval.
   destruct (x0_uint_result_393 invalid site flat_memories left value H118 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Theorem exception_node_394_congruent invalid left right next_left next_right :
 (exists width bits, VM.find 118 left = Some (Gval (Fuint width) bits)) ->
 VM.find 118 left = VM.find 118 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 394 next_left = VM.find 394 next_right.
Proof.
 intros H118 E118 L R.
 apply (x0_selected_uint_node_congruent 394 x0_concrete_expr_394 invalid left right next_left next_right).
 - apply (List.nth_error_In x0_expected_nodes 109). vm_compute. reflexivity.
 - intro site. cbn [x0_concrete_expr_394 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E118.
   reflexivity.
 - intros site value Eval.
   destruct (x0_uint_result_394 invalid site flat_memories left value H118 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Theorem exception_node_407_congruent invalid left right next_left next_right :
 (exists width bits, VM.find 122 left = Some (Gval (Fuint width) bits)) ->
 VM.find 122 left = VM.find 122 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 407 next_left = VM.find 407 next_right.
Proof.
 intros H122 E122 L R.
 apply (x0_selected_uint_node_congruent 407 x0_concrete_expr_407 invalid left right next_left next_right).
 - apply (List.nth_error_In x0_expected_nodes 113). vm_compute. reflexivity.
 - intro site. cbn [x0_concrete_expr_407 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E122.
   reflexivity.
 - intros site value Eval.
   destruct (x0_uint_result_407 invalid site flat_memories left value H122 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Theorem exception_node_409_congruent invalid left right next_left next_right :
 (exists width bits, VM.find 122 left = Some (Gval (Fuint width) bits)) ->
 VM.find 122 left = VM.find 122 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 409 next_left = VM.find 409 next_right.
Proof.
 intros H122 E122 L R.
 apply (x0_selected_uint_node_congruent 409 x0_concrete_expr_409 invalid left right next_left next_right).
 - apply (List.nth_error_In x0_expected_nodes 115). vm_compute. reflexivity.
 - intro site. cbn [x0_concrete_expr_409 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E122.
   reflexivity.
 - intros site value Eval.
   destruct (x0_uint_result_409 invalid site flat_memories left value H122 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Theorem exception_node_411_congruent invalid left right next_left next_right :
 (exists width bits, VM.find 122 left = Some (Gval (Fuint width) bits)) ->
 VM.find 122 left = VM.find 122 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 411 next_left = VM.find 411 next_right.
Proof.
 intros H122 E122 L R.
 apply (x0_selected_uint_node_congruent 411 x0_concrete_expr_411 invalid left right next_left next_right).
 - apply (List.nth_error_In x0_expected_nodes 117). vm_compute. reflexivity.
 - intro site. cbn [x0_concrete_expr_411 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E122.
   reflexivity.
 - intros site value Eval.
   destruct (x0_uint_result_411 invalid site flat_memories left value H122 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Theorem exception_node_412_congruent invalid left right next_left next_right :
 (exists width bits, VM.find 122 left = Some (Gval (Fuint width) bits)) ->
 VM.find 122 left = VM.find 122 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 412 next_left = VM.find 412 next_right.
Proof.
 intros H122 E122 L R.
 apply (x0_selected_uint_node_congruent 412 x0_concrete_expr_412 invalid left right next_left next_right).
 - apply (List.nth_error_In x0_expected_nodes 118). vm_compute. reflexivity.
 - intro site. cbn [x0_concrete_expr_412 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E122.
   reflexivity.
 - intros site value Eval.
   destruct (x0_uint_result_412 invalid site flat_memories left value H122 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Theorem exception_node_413_congruent invalid left right next_left next_right :
 (exists width bits, VM.find 126 left = Some (Gval (Fuint width) bits)) ->
 VM.find 126 left = VM.find 126 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 413 next_left = VM.find 413 next_right.
Proof.
 intros H126 E126 L R.
 apply (x0_selected_uint_node_congruent 413 x0_concrete_expr_413 invalid left right next_left next_right).
 - apply (List.nth_error_In x0_expected_nodes 119). vm_compute. reflexivity.
 - intro site. cbn [x0_concrete_expr_413 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E126.
   reflexivity.
 - intros site value Eval.
   destruct (x0_uint_result_413 invalid site flat_memories left value H126 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Theorem exception_node_415_congruent invalid left right next_left next_right :
 (exists width bits, VM.find 126 left = Some (Gval (Fuint width) bits)) ->
 VM.find 126 left = VM.find 126 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 415 next_left = VM.find 415 next_right.
Proof.
 intros H126 E126 L R.
 apply (x0_selected_uint_node_congruent 415 x0_concrete_expr_415 invalid left right next_left next_right).
 - apply (List.nth_error_In x0_expected_nodes 121). vm_compute. reflexivity.
 - intro site. cbn [x0_concrete_expr_415 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E126.
   reflexivity.
 - intros site value Eval.
   destruct (x0_uint_result_415 invalid site flat_memories left value H126 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Theorem exception_node_417_congruent invalid left right next_left next_right :
 (exists width bits, VM.find 126 left = Some (Gval (Fuint width) bits)) ->
 VM.find 126 left = VM.find 126 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 417 next_left = VM.find 417 next_right.
Proof.
 intros H126 E126 L R.
 apply (x0_selected_uint_node_congruent 417 x0_concrete_expr_417 invalid left right next_left next_right).
 - apply (List.nth_error_In x0_expected_nodes 123). vm_compute. reflexivity.
 - intro site. cbn [x0_concrete_expr_417 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E126.
   reflexivity.
 - intros site value Eval.
   destruct (x0_uint_result_417 invalid site flat_memories left value H126 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Theorem exception_node_419_congruent invalid left right next_left next_right :
 (exists width bits, VM.find 122 left = Some (Gval (Fuint width) bits)) ->
 VM.find 122 left = VM.find 122 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 419 next_left = VM.find 419 next_right.
Proof.
 intros H122 E122 L R.
 apply (x0_selected_uint_node_congruent 419 x0_concrete_expr_419 invalid left right next_left next_right).
 - apply (List.nth_error_In x0_expected_nodes 125). vm_compute. reflexivity.
 - intro site. cbn [x0_concrete_expr_419 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E122.
   reflexivity.
 - intros site value Eval.
   destruct (x0_uint_result_419 invalid site flat_memories left value H122 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Theorem exception_node_421_congruent invalid left right next_left next_right :
 (exists width bits, VM.find 122 left = Some (Gval (Fuint width) bits)) ->
 VM.find 122 left = VM.find 122 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 421 next_left = VM.find 421 next_right.
Proof.
 intros H122 E122 L R.
 apply (x0_selected_uint_node_congruent 421 x0_concrete_expr_421 invalid left right next_left next_right).
 - apply (List.nth_error_In x0_expected_nodes 127). vm_compute. reflexivity.
 - intro site. cbn [x0_concrete_expr_421 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E122.
   reflexivity.
 - intros site value Eval.
   destruct (x0_uint_result_421 invalid site flat_memories left value H122 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Theorem exception_node_422_congruent invalid left right next_left next_right :
 (exists width bits, VM.find 125 left = Some (Gval (Fuint width) bits)) ->
 VM.find 125 left = VM.find 125 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 422 next_left = VM.find 422 next_right.
Proof.
 intros H125 E125 L R.
 apply (x0_selected_uint_node_congruent 422 x0_concrete_expr_422 invalid left right next_left next_right).
 - apply (List.nth_error_In x0_expected_nodes 128). vm_compute. reflexivity.
 - intro site. cbn [x0_concrete_expr_422 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E125.
   reflexivity.
 - intros site value Eval.
   destruct (x0_uint_result_422 invalid site flat_memories left value H125 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Theorem exception_node_424_congruent invalid left right next_left next_right :
 (exists width bits, VM.find 125 left = Some (Gval (Fuint width) bits)) ->
 VM.find 125 left = VM.find 125 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 424 next_left = VM.find 424 next_right.
Proof.
 intros H125 E125 L R.
 apply (x0_selected_uint_node_congruent 424 x0_concrete_expr_424 invalid left right next_left next_right).
 - apply (List.nth_error_In x0_expected_nodes 130). vm_compute. reflexivity.
 - intro site. cbn [x0_concrete_expr_424 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E125.
   reflexivity.
 - intros site value Eval.
   destruct (x0_uint_result_424 invalid site flat_memories left value H125 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Theorem exception_node_429_congruent invalid left right next_left next_right :
 (exists width bits, VM.find 118 left = Some (Gval (Fuint width) bits)) ->
 VM.find 118 left = VM.find 118 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 429 next_left = VM.find 429 next_right.
Proof.
 intros H118 E118 L R.
 apply (x0_selected_uint_node_congruent 429 x0_concrete_expr_429 invalid left right next_left next_right).
 - apply (List.nth_error_In x0_expected_nodes 135). vm_compute. reflexivity.
 - intro site. cbn [x0_concrete_expr_429 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E118.
   reflexivity.
 - intros site value Eval.
   destruct (x0_uint_result_429 invalid site flat_memories left value H118 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Theorem exception_node_282_congruent invalid left right next_left next_right :
 (exists width bits, VM.find 140 left = Some (Gval (Fuint width) bits)) ->
 VM.find 140 left = VM.find 140 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 282 next_left = VM.find 282 next_right.
Proof.
 intros H140 E140 L R.
 apply (x0_selected_uint_node_congruent 282 x0_concrete_expr_282 invalid left right next_left next_right).
 - apply (List.nth_error_In x0_expected_nodes 2). vm_compute. reflexivity.
 - intro site. cbn [x0_concrete_expr_282 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E140.
   reflexivity.
 - intros site value Eval.
   destruct (x0_uint_result_282 invalid site flat_memories left value H140 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Theorem exception_node_285_congruent invalid left right next_left next_right :
 (exists width bits, VM.find 140 left = Some (Gval (Fuint width) bits)) ->
 VM.find 140 left = VM.find 140 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 285 next_left = VM.find 285 next_right.
Proof.
 intros H140 E140 L R.
 apply (x0_selected_uint_node_congruent 285 x0_concrete_expr_285 invalid left right next_left next_right).
 - apply (List.nth_error_In x0_expected_nodes 5). vm_compute. reflexivity.
 - intro site. cbn [x0_concrete_expr_285 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E140.
   reflexivity.
 - intros site value Eval.
   destruct (x0_uint_result_285 invalid site flat_memories left value H140 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Theorem exception_node_288_congruent invalid left right next_left next_right :
 (exists width bits, VM.find 140 left = Some (Gval (Fuint width) bits)) ->
 VM.find 140 left = VM.find 140 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 288 next_left = VM.find 288 next_right.
Proof.
 intros H140 E140 L R.
 apply (x0_selected_uint_node_congruent 288 x0_concrete_expr_288 invalid left right next_left next_right).
 - apply (List.nth_error_In x0_expected_nodes 8). vm_compute. reflexivity.
 - intro site. cbn [x0_concrete_expr_288 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E140.
   reflexivity.
 - intros site value Eval.
   destruct (x0_uint_result_288 invalid site flat_memories left value H140 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Theorem exception_node_291_congruent invalid left right next_left next_right :
 (exists width bits, VM.find 140 left = Some (Gval (Fuint width) bits)) ->
 VM.find 140 left = VM.find 140 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 291 next_left = VM.find 291 next_right.
Proof.
 intros H140 E140 L R.
 apply (x0_selected_uint_node_congruent 291 x0_concrete_expr_291 invalid left right next_left next_right).
 - apply (List.nth_error_In x0_expected_nodes 11). vm_compute. reflexivity.
 - intro site. cbn [x0_concrete_expr_291 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E140.
   reflexivity.
 - intros site value Eval.
   destruct (x0_uint_result_291 invalid site flat_memories left value H140 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Theorem exception_node_293_congruent invalid left right next_left next_right :
 (exists width bits, VM.find 140 left = Some (Gval (Fuint width) bits)) ->
 VM.find 140 left = VM.find 140 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 293 next_left = VM.find 293 next_right.
Proof.
 intros H140 E140 L R.
 apply (x0_selected_uint_node_congruent 293 x0_concrete_expr_293 invalid left right next_left next_right).
 - apply (List.nth_error_In x0_expected_nodes 13). vm_compute. reflexivity.
 - intro site. cbn [x0_concrete_expr_293 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E140.
   reflexivity.
 - intros site value Eval.
   destruct (x0_uint_result_293 invalid site flat_memories left value H140 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Theorem exception_node_301_congruent invalid left right next_left next_right :
 (exists width bits, VM.find 140 left = Some (Gval (Fuint width) bits)) ->
 VM.find 140 left = VM.find 140 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 301 next_left = VM.find 301 next_right.
Proof.
 intros H140 E140 L R.
 apply (x0_selected_uint_node_congruent 301 x0_concrete_expr_301 invalid left right next_left next_right).
 - apply (List.nth_error_In x0_expected_nodes 16). vm_compute. reflexivity.
 - intro site. cbn [x0_concrete_expr_301 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E140.
   reflexivity.
 - intros site value Eval.
   destruct (x0_uint_result_301 invalid site flat_memories left value H140 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Theorem exception_node_303_congruent invalid left right next_left next_right :
 (exists width bits, VM.find 140 left = Some (Gval (Fuint width) bits)) ->
 VM.find 140 left = VM.find 140 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 303 next_left = VM.find 303 next_right.
Proof.
 intros H140 E140 L R.
 apply (x0_selected_uint_node_congruent 303 x0_concrete_expr_303 invalid left right next_left next_right).
 - apply (List.nth_error_In x0_expected_nodes 18). vm_compute. reflexivity.
 - intro site. cbn [x0_concrete_expr_303 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E140.
   reflexivity.
 - intros site value Eval.
   destruct (x0_uint_result_303 invalid site flat_memories left value H140 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Theorem exception_node_305_congruent invalid left right next_left next_right :
 (exists width bits, VM.find 140 left = Some (Gval (Fuint width) bits)) ->
 VM.find 140 left = VM.find 140 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 305 next_left = VM.find 305 next_right.
Proof.
 intros H140 E140 L R.
 apply (x0_selected_uint_node_congruent 305 x0_concrete_expr_305 invalid left right next_left next_right).
 - apply (List.nth_error_In x0_expected_nodes 20). vm_compute. reflexivity.
 - intro site. cbn [x0_concrete_expr_305 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E140.
   reflexivity.
 - intros site value Eval.
   destruct (x0_uint_result_305 invalid site flat_memories left value H140 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Theorem exception_node_307_congruent invalid left right next_left next_right :
 (exists width bits, VM.find 140 left = Some (Gval (Fuint width) bits)) ->
 VM.find 140 left = VM.find 140 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 307 next_left = VM.find 307 next_right.
Proof.
 intros H140 E140 L R.
 apply (x0_selected_uint_node_congruent 307 x0_concrete_expr_307 invalid left right next_left next_right).
 - apply (List.nth_error_In x0_expected_nodes 22). vm_compute. reflexivity.
 - intro site. cbn [x0_concrete_expr_307 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E140.
   reflexivity.
 - intros site value Eval.
   destruct (x0_uint_result_307 invalid site flat_memories left value H140 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Theorem exception_node_309_congruent invalid left right next_left next_right :
 (exists width bits, VM.find 140 left = Some (Gval (Fuint width) bits)) ->
 VM.find 140 left = VM.find 140 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 309 next_left = VM.find 309 next_right.
Proof.
 intros H140 E140 L R.
 apply (x0_selected_uint_node_congruent 309 x0_concrete_expr_309 invalid left right next_left next_right).
 - apply (List.nth_error_In x0_expected_nodes 24). vm_compute. reflexivity.
 - intro site. cbn [x0_concrete_expr_309 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E140.
   reflexivity.
 - intros site value Eval.
   destruct (x0_uint_result_309 invalid site flat_memories left value H140 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Theorem exception_node_311_congruent invalid left right next_left next_right :
 (exists width bits, VM.find 140 left = Some (Gval (Fuint width) bits)) ->
 VM.find 140 left = VM.find 140 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 311 next_left = VM.find 311 next_right.
Proof.
 intros H140 E140 L R.
 apply (x0_selected_uint_node_congruent 311 x0_concrete_expr_311 invalid left right next_left next_right).
 - apply (List.nth_error_In x0_expected_nodes 26). vm_compute. reflexivity.
 - intro site. cbn [x0_concrete_expr_311 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E140.
   reflexivity.
 - intros site value Eval.
   destruct (x0_uint_result_311 invalid site flat_memories left value H140 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Theorem exception_node_313_congruent invalid left right next_left next_right :
 (exists width bits, VM.find 140 left = Some (Gval (Fuint width) bits)) ->
 VM.find 140 left = VM.find 140 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 313 next_left = VM.find 313 next_right.
Proof.
 intros H140 E140 L R.
 apply (x0_selected_uint_node_congruent 313 x0_concrete_expr_313 invalid left right next_left next_right).
 - apply (List.nth_error_In x0_expected_nodes 28). vm_compute. reflexivity.
 - intro site. cbn [x0_concrete_expr_313 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E140.
   reflexivity.
 - intros site value Eval.
   destruct (x0_uint_result_313 invalid site flat_memories left value H140 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Theorem exception_node_315_congruent invalid left right next_left next_right :
 (exists width bits, VM.find 140 left = Some (Gval (Fuint width) bits)) ->
 VM.find 140 left = VM.find 140 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 315 next_left = VM.find 315 next_right.
Proof.
 intros H140 E140 L R.
 apply (x0_selected_uint_node_congruent 315 x0_concrete_expr_315 invalid left right next_left next_right).
 - apply (List.nth_error_In x0_expected_nodes 30). vm_compute. reflexivity.
 - intro site. cbn [x0_concrete_expr_315 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E140.
   reflexivity.
 - intros site value Eval.
   destruct (x0_uint_result_315 invalid site flat_memories left value H140 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Theorem exception_node_317_congruent invalid left right next_left next_right :
 (exists width bits, VM.find 140 left = Some (Gval (Fuint width) bits)) ->
 VM.find 140 left = VM.find 140 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 317 next_left = VM.find 317 next_right.
Proof.
 intros H140 E140 L R.
 apply (x0_selected_uint_node_congruent 317 x0_concrete_expr_317 invalid left right next_left next_right).
 - apply (List.nth_error_In x0_expected_nodes 32). vm_compute. reflexivity.
 - intro site. cbn [x0_concrete_expr_317 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E140.
   reflexivity.
 - intros site value Eval.
   destruct (x0_uint_result_317 invalid site flat_memories left value H140 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Theorem exception_node_319_congruent invalid left right next_left next_right :
 (exists width bits, VM.find 140 left = Some (Gval (Fuint width) bits)) ->
 VM.find 140 left = VM.find 140 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 319 next_left = VM.find 319 next_right.
Proof.
 intros H140 E140 L R.
 apply (x0_selected_uint_node_congruent 319 x0_concrete_expr_319 invalid left right next_left next_right).
 - apply (List.nth_error_In x0_expected_nodes 34). vm_compute. reflexivity.
 - intro site. cbn [x0_concrete_expr_319 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E140.
   reflexivity.
 - intros site value Eval.
   destruct (x0_uint_result_319 invalid site flat_memories left value H140 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Theorem exception_node_321_congruent invalid left right next_left next_right :
 (exists width bits, VM.find 140 left = Some (Gval (Fuint width) bits)) ->
 VM.find 140 left = VM.find 140 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 321 next_left = VM.find 321 next_right.
Proof.
 intros H140 E140 L R.
 apply (x0_selected_uint_node_congruent 321 x0_concrete_expr_321 invalid left right next_left next_right).
 - apply (List.nth_error_In x0_expected_nodes 36). vm_compute. reflexivity.
 - intro site. cbn [x0_concrete_expr_321 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E140.
   reflexivity.
 - intros site value Eval.
   destruct (x0_uint_result_321 invalid site flat_memories left value H140 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Theorem exception_node_323_congruent invalid left right next_left next_right :
 (exists width bits, VM.find 140 left = Some (Gval (Fuint width) bits)) ->
 VM.find 140 left = VM.find 140 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 323 next_left = VM.find 323 next_right.
Proof.
 intros H140 E140 L R.
 apply (x0_selected_uint_node_congruent 323 x0_concrete_expr_323 invalid left right next_left next_right).
 - apply (List.nth_error_In x0_expected_nodes 38). vm_compute. reflexivity.
 - intro site. cbn [x0_concrete_expr_323 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E140.
   reflexivity.
 - intros site value Eval.
   destruct (x0_uint_result_323 invalid site flat_memories left value H140 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Theorem exception_node_325_congruent invalid left right next_left next_right :
 (exists width bits, VM.find 140 left = Some (Gval (Fuint width) bits)) ->
 VM.find 140 left = VM.find 140 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 325 next_left = VM.find 325 next_right.
Proof.
 intros H140 E140 L R.
 apply (x0_selected_uint_node_congruent 325 x0_concrete_expr_325 invalid left right next_left next_right).
 - apply (List.nth_error_In x0_expected_nodes 40). vm_compute. reflexivity.
 - intro site. cbn [x0_concrete_expr_325 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E140.
   reflexivity.
 - intros site value Eval.
   destruct (x0_uint_result_325 invalid site flat_memories left value H140 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Theorem exception_node_327_congruent invalid left right next_left next_right :
 (exists width bits, VM.find 140 left = Some (Gval (Fuint width) bits)) ->
 VM.find 140 left = VM.find 140 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 327 next_left = VM.find 327 next_right.
Proof.
 intros H140 E140 L R.
 apply (x0_selected_uint_node_congruent 327 x0_concrete_expr_327 invalid left right next_left next_right).
 - apply (List.nth_error_In x0_expected_nodes 42). vm_compute. reflexivity.
 - intro site. cbn [x0_concrete_expr_327 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E140.
   reflexivity.
 - intros site value Eval.
   destruct (x0_uint_result_327 invalid site flat_memories left value H140 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Theorem exception_node_329_congruent invalid left right next_left next_right :
 (exists width bits, VM.find 140 left = Some (Gval (Fuint width) bits)) ->
 VM.find 140 left = VM.find 140 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 329 next_left = VM.find 329 next_right.
Proof.
 intros H140 E140 L R.
 apply (x0_selected_uint_node_congruent 329 x0_concrete_expr_329 invalid left right next_left next_right).
 - apply (List.nth_error_In x0_expected_nodes 44). vm_compute. reflexivity.
 - intro site. cbn [x0_concrete_expr_329 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E140.
   reflexivity.
 - intros site value Eval.
   destruct (x0_uint_result_329 invalid site flat_memories left value H140 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Theorem exception_node_331_congruent invalid left right next_left next_right :
 (exists width bits, VM.find 140 left = Some (Gval (Fuint width) bits)) ->
 VM.find 140 left = VM.find 140 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 331 next_left = VM.find 331 next_right.
Proof.
 intros H140 E140 L R.
 apply (x0_selected_uint_node_congruent 331 x0_concrete_expr_331 invalid left right next_left next_right).
 - apply (List.nth_error_In x0_expected_nodes 46). vm_compute. reflexivity.
 - intro site. cbn [x0_concrete_expr_331 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E140.
   reflexivity.
 - intros site value Eval.
   destruct (x0_uint_result_331 invalid site flat_memories left value H140 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Theorem exception_node_333_congruent invalid left right next_left next_right :
 (exists width bits, VM.find 140 left = Some (Gval (Fuint width) bits)) ->
 VM.find 140 left = VM.find 140 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 333 next_left = VM.find 333 next_right.
Proof.
 intros H140 E140 L R.
 apply (x0_selected_uint_node_congruent 333 x0_concrete_expr_333 invalid left right next_left next_right).
 - apply (List.nth_error_In x0_expected_nodes 48). vm_compute. reflexivity.
 - intro site. cbn [x0_concrete_expr_333 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E140.
   reflexivity.
 - intros site value Eval.
   destruct (x0_uint_result_333 invalid site flat_memories left value H140 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Theorem exception_node_335_congruent invalid left right next_left next_right :
 (exists width bits, VM.find 140 left = Some (Gval (Fuint width) bits)) ->
 VM.find 140 left = VM.find 140 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 335 next_left = VM.find 335 next_right.
Proof.
 intros H140 E140 L R.
 apply (x0_selected_uint_node_congruent 335 x0_concrete_expr_335 invalid left right next_left next_right).
 - apply (List.nth_error_In x0_expected_nodes 50). vm_compute. reflexivity.
 - intro site. cbn [x0_concrete_expr_335 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E140.
   reflexivity.
 - intros site value Eval.
   destruct (x0_uint_result_335 invalid site flat_memories left value H140 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Theorem exception_node_337_congruent invalid left right next_left next_right :
 (exists width bits, VM.find 140 left = Some (Gval (Fuint width) bits)) ->
 VM.find 140 left = VM.find 140 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 337 next_left = VM.find 337 next_right.
Proof.
 intros H140 E140 L R.
 apply (x0_selected_uint_node_congruent 337 x0_concrete_expr_337 invalid left right next_left next_right).
 - apply (List.nth_error_In x0_expected_nodes 52). vm_compute. reflexivity.
 - intro site. cbn [x0_concrete_expr_337 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E140.
   reflexivity.
 - intros site value Eval.
   destruct (x0_uint_result_337 invalid site flat_memories left value H140 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Theorem exception_node_339_congruent invalid left right next_left next_right :
 (exists width bits, VM.find 140 left = Some (Gval (Fuint width) bits)) ->
 VM.find 140 left = VM.find 140 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 339 next_left = VM.find 339 next_right.
Proof.
 intros H140 E140 L R.
 apply (x0_selected_uint_node_congruent 339 x0_concrete_expr_339 invalid left right next_left next_right).
 - apply (List.nth_error_In x0_expected_nodes 54). vm_compute. reflexivity.
 - intro site. cbn [x0_concrete_expr_339 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E140.
   reflexivity.
 - intros site value Eval.
   destruct (x0_uint_result_339 invalid site flat_memories left value H140 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Theorem exception_node_341_congruent invalid left right next_left next_right :
 (exists width bits, VM.find 140 left = Some (Gval (Fuint width) bits)) ->
 VM.find 140 left = VM.find 140 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 341 next_left = VM.find 341 next_right.
Proof.
 intros H140 E140 L R.
 apply (x0_selected_uint_node_congruent 341 x0_concrete_expr_341 invalid left right next_left next_right).
 - apply (List.nth_error_In x0_expected_nodes 56). vm_compute. reflexivity.
 - intro site. cbn [x0_concrete_expr_341 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E140.
   reflexivity.
 - intros site value Eval.
   destruct (x0_uint_result_341 invalid site flat_memories left value H140 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Theorem exception_node_343_congruent invalid left right next_left next_right :
 (exists width bits, VM.find 140 left = Some (Gval (Fuint width) bits)) ->
 VM.find 140 left = VM.find 140 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 343 next_left = VM.find 343 next_right.
Proof.
 intros H140 E140 L R.
 apply (x0_selected_uint_node_congruent 343 x0_concrete_expr_343 invalid left right next_left next_right).
 - apply (List.nth_error_In x0_expected_nodes 58). vm_compute. reflexivity.
 - intro site. cbn [x0_concrete_expr_343 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E140.
   reflexivity.
 - intros site value Eval.
   destruct (x0_uint_result_343 invalid site flat_memories left value H140 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Theorem exception_node_345_congruent invalid left right next_left next_right :
 (exists width bits, VM.find 140 left = Some (Gval (Fuint width) bits)) ->
 VM.find 140 left = VM.find 140 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 345 next_left = VM.find 345 next_right.
Proof.
 intros H140 E140 L R.
 apply (x0_selected_uint_node_congruent 345 x0_concrete_expr_345 invalid left right next_left next_right).
 - apply (List.nth_error_In x0_expected_nodes 60). vm_compute. reflexivity.
 - intro site. cbn [x0_concrete_expr_345 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E140.
   reflexivity.
 - intros site value Eval.
   destruct (x0_uint_result_345 invalid site flat_memories left value H140 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Theorem exception_node_347_congruent invalid left right next_left next_right :
 (exists width bits, VM.find 140 left = Some (Gval (Fuint width) bits)) ->
 VM.find 140 left = VM.find 140 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 347 next_left = VM.find 347 next_right.
Proof.
 intros H140 E140 L R.
 apply (x0_selected_uint_node_congruent 347 x0_concrete_expr_347 invalid left right next_left next_right).
 - apply (List.nth_error_In x0_expected_nodes 62). vm_compute. reflexivity.
 - intro site. cbn [x0_concrete_expr_347 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E140.
   reflexivity.
 - intros site value Eval.
   destruct (x0_uint_result_347 invalid site flat_memories left value H140 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Theorem exception_node_349_congruent invalid left right next_left next_right :
 (exists width bits, VM.find 140 left = Some (Gval (Fuint width) bits)) ->
 VM.find 140 left = VM.find 140 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 349 next_left = VM.find 349 next_right.
Proof.
 intros H140 E140 L R.
 apply (x0_selected_uint_node_congruent 349 x0_concrete_expr_349 invalid left right next_left next_right).
 - apply (List.nth_error_In x0_expected_nodes 64). vm_compute. reflexivity.
 - intro site. cbn [x0_concrete_expr_349 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E140.
   reflexivity.
 - intros site value Eval.
   destruct (x0_uint_result_349 invalid site flat_memories left value H140 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Theorem exception_node_351_congruent invalid left right next_left next_right :
 (exists width bits, VM.find 140 left = Some (Gval (Fuint width) bits)) ->
 VM.find 140 left = VM.find 140 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 351 next_left = VM.find 351 next_right.
Proof.
 intros H140 E140 L R.
 apply (x0_selected_uint_node_congruent 351 x0_concrete_expr_351 invalid left right next_left next_right).
 - apply (List.nth_error_In x0_expected_nodes 66). vm_compute. reflexivity.
 - intro site. cbn [x0_concrete_expr_351 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E140.
   reflexivity.
 - intros site value Eval.
   destruct (x0_uint_result_351 invalid site flat_memories left value H140 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Theorem exception_node_353_congruent invalid left right next_left next_right :
 (exists width bits, VM.find 140 left = Some (Gval (Fuint width) bits)) ->
 VM.find 140 left = VM.find 140 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 353 next_left = VM.find 353 next_right.
Proof.
 intros H140 E140 L R.
 apply (x0_selected_uint_node_congruent 353 x0_concrete_expr_353 invalid left right next_left next_right).
 - apply (List.nth_error_In x0_expected_nodes 68). vm_compute. reflexivity.
 - intro site. cbn [x0_concrete_expr_353 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E140.
   reflexivity.
 - intros site value Eval.
   destruct (x0_uint_result_353 invalid site flat_memories left value H140 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Theorem exception_node_355_congruent invalid left right next_left next_right :
 (exists width bits, VM.find 140 left = Some (Gval (Fuint width) bits)) ->
 VM.find 140 left = VM.find 140 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 355 next_left = VM.find 355 next_right.
Proof.
 intros H140 E140 L R.
 apply (x0_selected_uint_node_congruent 355 x0_concrete_expr_355 invalid left right next_left next_right).
 - apply (List.nth_error_In x0_expected_nodes 70). vm_compute. reflexivity.
 - intro site. cbn [x0_concrete_expr_355 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E140.
   reflexivity.
 - intros site value Eval.
   destruct (x0_uint_result_355 invalid site flat_memories left value H140 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Theorem exception_node_357_congruent invalid left right next_left next_right :
 (exists width bits, VM.find 140 left = Some (Gval (Fuint width) bits)) ->
 VM.find 140 left = VM.find 140 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 357 next_left = VM.find 357 next_right.
Proof.
 intros H140 E140 L R.
 apply (x0_selected_uint_node_congruent 357 x0_concrete_expr_357 invalid left right next_left next_right).
 - apply (List.nth_error_In x0_expected_nodes 72). vm_compute. reflexivity.
 - intro site. cbn [x0_concrete_expr_357 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E140.
   reflexivity.
 - intros site value Eval.
   destruct (x0_uint_result_357 invalid site flat_memories left value H140 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Theorem exception_node_387_congruent invalid left right next_left next_right :
 (exists width bits, VM.find 140 left = Some (Gval (Fuint width) bits)) ->
 VM.find 140 left = VM.find 140 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 387 next_left = VM.find 387 next_right.
Proof.
 intros H140 E140 L R.
 apply (x0_selected_uint_node_congruent 387 x0_concrete_expr_387 invalid left right next_left next_right).
 - apply (List.nth_error_In x0_expected_nodes 102). vm_compute. reflexivity.
 - intro site. cbn [x0_concrete_expr_387 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E140.
   reflexivity.
 - intros site value Eval.
   destruct (x0_uint_result_387 invalid site flat_memories left value H140 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Theorem exception_node_389_congruent invalid left right next_left next_right :
 (exists width bits, VM.find 140 left = Some (Gval (Fuint width) bits)) ->
 VM.find 140 left = VM.find 140 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 389 next_left = VM.find 389 next_right.
Proof.
 intros H140 E140 L R.
 apply (x0_selected_uint_node_congruent 389 x0_concrete_expr_389 invalid left right next_left next_right).
 - apply (List.nth_error_In x0_expected_nodes 104). vm_compute. reflexivity.
 - intro site. cbn [x0_concrete_expr_389 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E140.
   reflexivity.
 - intros site value Eval.
   destruct (x0_uint_result_389 invalid site flat_memories left value H140 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Theorem exception_node_391_congruent invalid left right next_left next_right :
 (exists width bits, VM.find 140 left = Some (Gval (Fuint width) bits)) ->
 VM.find 140 left = VM.find 140 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 391 next_left = VM.find 391 next_right.
Proof.
 intros H140 E140 L R.
 apply (x0_selected_uint_node_congruent 391 x0_concrete_expr_391 invalid left right next_left next_right).
 - apply (List.nth_error_In x0_expected_nodes 106). vm_compute. reflexivity.
 - intro site. cbn [x0_concrete_expr_391 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E140.
   reflexivity.
 - intros site value Eval.
   destruct (x0_uint_result_391 invalid site flat_memories left value H140 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Theorem exception_node_395_congruent invalid left right next_left next_right :
 (exists width bits, VM.find 141 left = Some (Gval (Fuint width) bits)) ->
 VM.find 141 left = VM.find 141 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 395 next_left = VM.find 395 next_right.
Proof.
 intros H141 E141 L R.
 apply (x0_selected_uint_node_congruent 395 x0_concrete_expr_395 invalid left right next_left next_right).
 - apply (List.nth_error_In x0_expected_nodes 110). vm_compute. reflexivity.
 - intro site. cbn [x0_concrete_expr_395 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E141.
   reflexivity.
 - intros site value Eval.
   destruct (x0_uint_result_395 invalid site flat_memories left value H141 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Theorem exception_node_408_congruent invalid left right next_left next_right :
 (exists width bits, VM.find 127 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 407 left = Some (Gval (Fuint width) bits)) ->
 VM.find 127 left = VM.find 127 right ->
 VM.find 407 left = VM.find 407 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 408 next_left = VM.find 408 next_right.
Proof.
 intros H127 H407 E127 E407 L R.
 apply (x0_selected_uint_node_congruent 408 x0_concrete_expr_408 invalid left right next_left next_right).
 - apply (List.nth_error_In x0_expected_nodes 114). vm_compute. reflexivity.
 - intro site. cbn [x0_concrete_expr_408 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E127.
   rewrite E407.
   reflexivity.
 - intros site value Eval.
   destruct (x0_uint_result_408 invalid site flat_memories left value H127 H407 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Theorem exception_node_410_congruent invalid left right next_left next_right :
 (exists width bits, VM.find 409 left = Some (Gval (Fuint width) bits)) ->
 VM.find 409 left = VM.find 409 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 410 next_left = VM.find 410 next_right.
Proof.
 intros H409 E409 L R.
 apply (x0_selected_uint_node_congruent 410 x0_concrete_expr_410 invalid left right next_left next_right).
 - apply (List.nth_error_In x0_expected_nodes 116). vm_compute. reflexivity.
 - intro site. cbn [x0_concrete_expr_410 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E409.
   reflexivity.
 - intros site value Eval.
   destruct (x0_uint_result_410 invalid site flat_memories left value H409 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Theorem exception_node_420_congruent invalid left right next_left next_right :
 (exists width bits, VM.find 419 left = Some (Gval (Fuint width) bits)) ->
 VM.find 419 left = VM.find 419 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 420 next_left = VM.find 420 next_right.
Proof.
 intros H419 E419 L R.
 apply (x0_selected_uint_node_congruent 420 x0_concrete_expr_420 invalid left right next_left next_right).
 - apply (List.nth_error_In x0_expected_nodes 126). vm_compute. reflexivity.
 - intro site. cbn [x0_concrete_expr_420 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E419.
   reflexivity.
 - intros site value Eval.
   destruct (x0_uint_result_420 invalid site flat_memories left value H419 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Theorem exception_node_430_congruent invalid left right next_left next_right :
 (exists width bits, VM.find 429 left = Some (Gval (Fuint width) bits)) ->
 VM.find 429 left = VM.find 429 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 430 next_left = VM.find 430 next_right.
Proof.
 intros H429 E429 L R.
 apply (x0_selected_uint_node_congruent 430 x0_concrete_expr_430 invalid left right next_left next_right).
 - apply (List.nth_error_In x0_expected_nodes 136). vm_compute. reflexivity.
 - intro site. cbn [x0_concrete_expr_430 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E429.
   reflexivity.
 - intros site value Eval.
   destruct (x0_uint_result_430 invalid site flat_memories left value H429 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Theorem exception_node_283_congruent invalid left right next_left next_right :
 (exists width bits, VM.find 150 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 282 left = Some (Gval (Fuint width) bits)) ->
 VM.find 150 left = VM.find 150 right ->
 VM.find 282 left = VM.find 282 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 283 next_left = VM.find 283 next_right.
Proof.
 intros H150 H282 E150 E282 L R.
 apply (x0_selected_uint_node_congruent 283 x0_concrete_expr_283 invalid left right next_left next_right).
 - apply (List.nth_error_In x0_expected_nodes 3). vm_compute. reflexivity.
 - intro site. cbn [x0_concrete_expr_283 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E150.
   rewrite E282.
   reflexivity.
 - intros site value Eval.
   destruct (x0_uint_result_283 invalid site flat_memories left value H150 H282 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Theorem exception_node_286_congruent invalid left right next_left next_right :
 (exists width bits, VM.find 285 left = Some (Gval (Fuint width) bits)) ->
 VM.find 285 left = VM.find 285 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 286 next_left = VM.find 286 next_right.
Proof.
 intros H285 E285 L R.
 apply (x0_selected_uint_node_congruent 286 x0_concrete_expr_286 invalid left right next_left next_right).
 - apply (List.nth_error_In x0_expected_nodes 6). vm_compute. reflexivity.
 - intro site. cbn [x0_concrete_expr_286 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E285.
   reflexivity.
 - intros site value Eval.
   destruct (x0_uint_result_286 invalid site flat_memories left value H285 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Theorem exception_node_289_congruent invalid left right next_left next_right :
 (exists width bits, VM.find 288 left = Some (Gval (Fuint width) bits)) ->
 VM.find 288 left = VM.find 288 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 289 next_left = VM.find 289 next_right.
Proof.
 intros H288 E288 L R.
 apply (x0_selected_uint_node_congruent 289 x0_concrete_expr_289 invalid left right next_left next_right).
 - apply (List.nth_error_In x0_expected_nodes 9). vm_compute. reflexivity.
 - intro site. cbn [x0_concrete_expr_289 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E288.
   reflexivity.
 - intros site value Eval.
   destruct (x0_uint_result_289 invalid site flat_memories left value H288 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Theorem exception_node_292_congruent invalid left right next_left next_right :
 (exists width bits, VM.find 284 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 291 left = Some (Gval (Fuint width) bits)) ->
 VM.find 284 left = VM.find 284 right ->
 VM.find 291 left = VM.find 291 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 292 next_left = VM.find 292 next_right.
Proof.
 intros H284 H291 E284 E291 L R.
 apply (x0_selected_uint_node_congruent 292 x0_concrete_expr_292 invalid left right next_left next_right).
 - apply (List.nth_error_In x0_expected_nodes 12). vm_compute. reflexivity.
 - intro site. cbn [x0_concrete_expr_292 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E284.
   rewrite E291.
   reflexivity.
 - intros site value Eval.
   destruct (x0_uint_result_292 invalid site flat_memories left value H284 H291 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Theorem exception_node_294_congruent invalid left right next_left next_right :
 (exists width bits, VM.find 293 left = Some (Gval (Fuint width) bits)) ->
 VM.find 293 left = VM.find 293 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 294 next_left = VM.find 294 next_right.
Proof.
 intros H293 E293 L R.
 apply (x0_selected_uint_node_congruent 294 x0_concrete_expr_294 invalid left right next_left next_right).
 - apply (List.nth_error_In x0_expected_nodes 14). vm_compute. reflexivity.
 - intro site. cbn [x0_concrete_expr_294 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E293.
   reflexivity.
 - intros site value Eval.
   destruct (x0_uint_result_294 invalid site flat_memories left value H293 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Theorem exception_node_302_congruent invalid left right next_left next_right :
 (exists width bits, VM.find 301 left = Some (Gval (Fuint width) bits)) ->
 VM.find 301 left = VM.find 301 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 302 next_left = VM.find 302 next_right.
Proof.
 intros H301 E301 L R.
 apply (x0_selected_uint_node_congruent 302 x0_concrete_expr_302 invalid left right next_left next_right).
 - apply (List.nth_error_In x0_expected_nodes 17). vm_compute. reflexivity.
 - intro site. cbn [x0_concrete_expr_302 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E301.
   reflexivity.
 - intros site value Eval.
   destruct (x0_uint_result_302 invalid site flat_memories left value H301 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Theorem exception_node_304_congruent invalid left right next_left next_right :
 (exists width bits, VM.find 303 left = Some (Gval (Fuint width) bits)) ->
 VM.find 303 left = VM.find 303 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 304 next_left = VM.find 304 next_right.
Proof.
 intros H303 E303 L R.
 apply (x0_selected_uint_node_congruent 304 x0_concrete_expr_304 invalid left right next_left next_right).
 - apply (List.nth_error_In x0_expected_nodes 19). vm_compute. reflexivity.
 - intro site. cbn [x0_concrete_expr_304 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E303.
   reflexivity.
 - intros site value Eval.
   destruct (x0_uint_result_304 invalid site flat_memories left value H303 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Theorem exception_node_306_congruent invalid left right next_left next_right :
 (exists width bits, VM.find 305 left = Some (Gval (Fuint width) bits)) ->
 VM.find 305 left = VM.find 305 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 306 next_left = VM.find 306 next_right.
Proof.
 intros H305 E305 L R.
 apply (x0_selected_uint_node_congruent 306 x0_concrete_expr_306 invalid left right next_left next_right).
 - apply (List.nth_error_In x0_expected_nodes 21). vm_compute. reflexivity.
 - intro site. cbn [x0_concrete_expr_306 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E305.
   reflexivity.
 - intros site value Eval.
   destruct (x0_uint_result_306 invalid site flat_memories left value H305 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Theorem exception_node_308_congruent invalid left right next_left next_right :
 (exists width bits, VM.find 307 left = Some (Gval (Fuint width) bits)) ->
 VM.find 307 left = VM.find 307 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 308 next_left = VM.find 308 next_right.
Proof.
 intros H307 E307 L R.
 apply (x0_selected_uint_node_congruent 308 x0_concrete_expr_308 invalid left right next_left next_right).
 - apply (List.nth_error_In x0_expected_nodes 23). vm_compute. reflexivity.
 - intro site. cbn [x0_concrete_expr_308 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E307.
   reflexivity.
 - intros site value Eval.
   destruct (x0_uint_result_308 invalid site flat_memories left value H307 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Theorem exception_node_310_congruent invalid left right next_left next_right :
 (exists width bits, VM.find 309 left = Some (Gval (Fuint width) bits)) ->
 VM.find 309 left = VM.find 309 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 310 next_left = VM.find 310 next_right.
Proof.
 intros H309 E309 L R.
 apply (x0_selected_uint_node_congruent 310 x0_concrete_expr_310 invalid left right next_left next_right).
 - apply (List.nth_error_In x0_expected_nodes 25). vm_compute. reflexivity.
 - intro site. cbn [x0_concrete_expr_310 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E309.
   reflexivity.
 - intros site value Eval.
   destruct (x0_uint_result_310 invalid site flat_memories left value H309 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Theorem exception_node_312_congruent invalid left right next_left next_right :
 (exists width bits, VM.find 311 left = Some (Gval (Fuint width) bits)) ->
 VM.find 311 left = VM.find 311 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 312 next_left = VM.find 312 next_right.
Proof.
 intros H311 E311 L R.
 apply (x0_selected_uint_node_congruent 312 x0_concrete_expr_312 invalid left right next_left next_right).
 - apply (List.nth_error_In x0_expected_nodes 27). vm_compute. reflexivity.
 - intro site. cbn [x0_concrete_expr_312 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E311.
   reflexivity.
 - intros site value Eval.
   destruct (x0_uint_result_312 invalid site flat_memories left value H311 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Theorem exception_node_314_congruent invalid left right next_left next_right :
 (exists width bits, VM.find 313 left = Some (Gval (Fuint width) bits)) ->
 VM.find 313 left = VM.find 313 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 314 next_left = VM.find 314 next_right.
Proof.
 intros H313 E313 L R.
 apply (x0_selected_uint_node_congruent 314 x0_concrete_expr_314 invalid left right next_left next_right).
 - apply (List.nth_error_In x0_expected_nodes 29). vm_compute. reflexivity.
 - intro site. cbn [x0_concrete_expr_314 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E313.
   reflexivity.
 - intros site value Eval.
   destruct (x0_uint_result_314 invalid site flat_memories left value H313 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Theorem exception_node_316_congruent invalid left right next_left next_right :
 (exists width bits, VM.find 315 left = Some (Gval (Fuint width) bits)) ->
 VM.find 315 left = VM.find 315 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 316 next_left = VM.find 316 next_right.
Proof.
 intros H315 E315 L R.
 apply (x0_selected_uint_node_congruent 316 x0_concrete_expr_316 invalid left right next_left next_right).
 - apply (List.nth_error_In x0_expected_nodes 31). vm_compute. reflexivity.
 - intro site. cbn [x0_concrete_expr_316 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E315.
   reflexivity.
 - intros site value Eval.
   destruct (x0_uint_result_316 invalid site flat_memories left value H315 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Theorem exception_node_318_congruent invalid left right next_left next_right :
 (exists width bits, VM.find 317 left = Some (Gval (Fuint width) bits)) ->
 VM.find 317 left = VM.find 317 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 318 next_left = VM.find 318 next_right.
Proof.
 intros H317 E317 L R.
 apply (x0_selected_uint_node_congruent 318 x0_concrete_expr_318 invalid left right next_left next_right).
 - apply (List.nth_error_In x0_expected_nodes 33). vm_compute. reflexivity.
 - intro site. cbn [x0_concrete_expr_318 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E317.
   reflexivity.
 - intros site value Eval.
   destruct (x0_uint_result_318 invalid site flat_memories left value H317 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Theorem exception_node_320_congruent invalid left right next_left next_right :
 (exists width bits, VM.find 319 left = Some (Gval (Fuint width) bits)) ->
 VM.find 319 left = VM.find 319 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 320 next_left = VM.find 320 next_right.
Proof.
 intros H319 E319 L R.
 apply (x0_selected_uint_node_congruent 320 x0_concrete_expr_320 invalid left right next_left next_right).
 - apply (List.nth_error_In x0_expected_nodes 35). vm_compute. reflexivity.
 - intro site. cbn [x0_concrete_expr_320 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E319.
   reflexivity.
 - intros site value Eval.
   destruct (x0_uint_result_320 invalid site flat_memories left value H319 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Theorem exception_node_322_congruent invalid left right next_left next_right :
 (exists width bits, VM.find 321 left = Some (Gval (Fuint width) bits)) ->
 VM.find 321 left = VM.find 321 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 322 next_left = VM.find 322 next_right.
Proof.
 intros H321 E321 L R.
 apply (x0_selected_uint_node_congruent 322 x0_concrete_expr_322 invalid left right next_left next_right).
 - apply (List.nth_error_In x0_expected_nodes 37). vm_compute. reflexivity.
 - intro site. cbn [x0_concrete_expr_322 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E321.
   reflexivity.
 - intros site value Eval.
   destruct (x0_uint_result_322 invalid site flat_memories left value H321 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Theorem exception_node_324_congruent invalid left right next_left next_right :
 (exists width bits, VM.find 323 left = Some (Gval (Fuint width) bits)) ->
 VM.find 323 left = VM.find 323 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 324 next_left = VM.find 324 next_right.
Proof.
 intros H323 E323 L R.
 apply (x0_selected_uint_node_congruent 324 x0_concrete_expr_324 invalid left right next_left next_right).
 - apply (List.nth_error_In x0_expected_nodes 39). vm_compute. reflexivity.
 - intro site. cbn [x0_concrete_expr_324 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E323.
   reflexivity.
 - intros site value Eval.
   destruct (x0_uint_result_324 invalid site flat_memories left value H323 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Theorem exception_node_326_congruent invalid left right next_left next_right :
 (exists width bits, VM.find 325 left = Some (Gval (Fuint width) bits)) ->
 VM.find 325 left = VM.find 325 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 326 next_left = VM.find 326 next_right.
Proof.
 intros H325 E325 L R.
 apply (x0_selected_uint_node_congruent 326 x0_concrete_expr_326 invalid left right next_left next_right).
 - apply (List.nth_error_In x0_expected_nodes 41). vm_compute. reflexivity.
 - intro site. cbn [x0_concrete_expr_326 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E325.
   reflexivity.
 - intros site value Eval.
   destruct (x0_uint_result_326 invalid site flat_memories left value H325 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Theorem exception_node_328_congruent invalid left right next_left next_right :
 (exists width bits, VM.find 327 left = Some (Gval (Fuint width) bits)) ->
 VM.find 327 left = VM.find 327 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 328 next_left = VM.find 328 next_right.
Proof.
 intros H327 E327 L R.
 apply (x0_selected_uint_node_congruent 328 x0_concrete_expr_328 invalid left right next_left next_right).
 - apply (List.nth_error_In x0_expected_nodes 43). vm_compute. reflexivity.
 - intro site. cbn [x0_concrete_expr_328 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E327.
   reflexivity.
 - intros site value Eval.
   destruct (x0_uint_result_328 invalid site flat_memories left value H327 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Theorem exception_node_330_congruent invalid left right next_left next_right :
 (exists width bits, VM.find 329 left = Some (Gval (Fuint width) bits)) ->
 VM.find 329 left = VM.find 329 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 330 next_left = VM.find 330 next_right.
Proof.
 intros H329 E329 L R.
 apply (x0_selected_uint_node_congruent 330 x0_concrete_expr_330 invalid left right next_left next_right).
 - apply (List.nth_error_In x0_expected_nodes 45). vm_compute. reflexivity.
 - intro site. cbn [x0_concrete_expr_330 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E329.
   reflexivity.
 - intros site value Eval.
   destruct (x0_uint_result_330 invalid site flat_memories left value H329 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Theorem exception_node_332_congruent invalid left right next_left next_right :
 (exists width bits, VM.find 331 left = Some (Gval (Fuint width) bits)) ->
 VM.find 331 left = VM.find 331 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 332 next_left = VM.find 332 next_right.
Proof.
 intros H331 E331 L R.
 apply (x0_selected_uint_node_congruent 332 x0_concrete_expr_332 invalid left right next_left next_right).
 - apply (List.nth_error_In x0_expected_nodes 47). vm_compute. reflexivity.
 - intro site. cbn [x0_concrete_expr_332 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E331.
   reflexivity.
 - intros site value Eval.
   destruct (x0_uint_result_332 invalid site flat_memories left value H331 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Theorem exception_node_334_congruent invalid left right next_left next_right :
 (exists width bits, VM.find 333 left = Some (Gval (Fuint width) bits)) ->
 VM.find 333 left = VM.find 333 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 334 next_left = VM.find 334 next_right.
Proof.
 intros H333 E333 L R.
 apply (x0_selected_uint_node_congruent 334 x0_concrete_expr_334 invalid left right next_left next_right).
 - apply (List.nth_error_In x0_expected_nodes 49). vm_compute. reflexivity.
 - intro site. cbn [x0_concrete_expr_334 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E333.
   reflexivity.
 - intros site value Eval.
   destruct (x0_uint_result_334 invalid site flat_memories left value H333 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Theorem exception_node_336_congruent invalid left right next_left next_right :
 (exists width bits, VM.find 335 left = Some (Gval (Fuint width) bits)) ->
 VM.find 335 left = VM.find 335 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 336 next_left = VM.find 336 next_right.
Proof.
 intros H335 E335 L R.
 apply (x0_selected_uint_node_congruent 336 x0_concrete_expr_336 invalid left right next_left next_right).
 - apply (List.nth_error_In x0_expected_nodes 51). vm_compute. reflexivity.
 - intro site. cbn [x0_concrete_expr_336 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E335.
   reflexivity.
 - intros site value Eval.
   destruct (x0_uint_result_336 invalid site flat_memories left value H335 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Theorem exception_node_338_congruent invalid left right next_left next_right :
 (exists width bits, VM.find 337 left = Some (Gval (Fuint width) bits)) ->
 VM.find 337 left = VM.find 337 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 338 next_left = VM.find 338 next_right.
Proof.
 intros H337 E337 L R.
 apply (x0_selected_uint_node_congruent 338 x0_concrete_expr_338 invalid left right next_left next_right).
 - apply (List.nth_error_In x0_expected_nodes 53). vm_compute. reflexivity.
 - intro site. cbn [x0_concrete_expr_338 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E337.
   reflexivity.
 - intros site value Eval.
   destruct (x0_uint_result_338 invalid site flat_memories left value H337 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Theorem exception_node_340_congruent invalid left right next_left next_right :
 (exists width bits, VM.find 339 left = Some (Gval (Fuint width) bits)) ->
 VM.find 339 left = VM.find 339 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 340 next_left = VM.find 340 next_right.
Proof.
 intros H339 E339 L R.
 apply (x0_selected_uint_node_congruent 340 x0_concrete_expr_340 invalid left right next_left next_right).
 - apply (List.nth_error_In x0_expected_nodes 55). vm_compute. reflexivity.
 - intro site. cbn [x0_concrete_expr_340 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E339.
   reflexivity.
 - intros site value Eval.
   destruct (x0_uint_result_340 invalid site flat_memories left value H339 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Theorem exception_node_342_congruent invalid left right next_left next_right :
 (exists width bits, VM.find 341 left = Some (Gval (Fuint width) bits)) ->
 VM.find 341 left = VM.find 341 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 342 next_left = VM.find 342 next_right.
Proof.
 intros H341 E341 L R.
 apply (x0_selected_uint_node_congruent 342 x0_concrete_expr_342 invalid left right next_left next_right).
 - apply (List.nth_error_In x0_expected_nodes 57). vm_compute. reflexivity.
 - intro site. cbn [x0_concrete_expr_342 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E341.
   reflexivity.
 - intros site value Eval.
   destruct (x0_uint_result_342 invalid site flat_memories left value H341 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Theorem exception_node_344_congruent invalid left right next_left next_right :
 (exists width bits, VM.find 343 left = Some (Gval (Fuint width) bits)) ->
 VM.find 343 left = VM.find 343 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 344 next_left = VM.find 344 next_right.
Proof.
 intros H343 E343 L R.
 apply (x0_selected_uint_node_congruent 344 x0_concrete_expr_344 invalid left right next_left next_right).
 - apply (List.nth_error_In x0_expected_nodes 59). vm_compute. reflexivity.
 - intro site. cbn [x0_concrete_expr_344 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E343.
   reflexivity.
 - intros site value Eval.
   destruct (x0_uint_result_344 invalid site flat_memories left value H343 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Theorem exception_node_346_congruent invalid left right next_left next_right :
 (exists width bits, VM.find 345 left = Some (Gval (Fuint width) bits)) ->
 VM.find 345 left = VM.find 345 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 346 next_left = VM.find 346 next_right.
Proof.
 intros H345 E345 L R.
 apply (x0_selected_uint_node_congruent 346 x0_concrete_expr_346 invalid left right next_left next_right).
 - apply (List.nth_error_In x0_expected_nodes 61). vm_compute. reflexivity.
 - intro site. cbn [x0_concrete_expr_346 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E345.
   reflexivity.
 - intros site value Eval.
   destruct (x0_uint_result_346 invalid site flat_memories left value H345 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Theorem exception_node_348_congruent invalid left right next_left next_right :
 (exists width bits, VM.find 347 left = Some (Gval (Fuint width) bits)) ->
 VM.find 347 left = VM.find 347 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 348 next_left = VM.find 348 next_right.
Proof.
 intros H347 E347 L R.
 apply (x0_selected_uint_node_congruent 348 x0_concrete_expr_348 invalid left right next_left next_right).
 - apply (List.nth_error_In x0_expected_nodes 63). vm_compute. reflexivity.
 - intro site. cbn [x0_concrete_expr_348 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E347.
   reflexivity.
 - intros site value Eval.
   destruct (x0_uint_result_348 invalid site flat_memories left value H347 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Theorem exception_node_350_congruent invalid left right next_left next_right :
 (exists width bits, VM.find 349 left = Some (Gval (Fuint width) bits)) ->
 VM.find 349 left = VM.find 349 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 350 next_left = VM.find 350 next_right.
Proof.
 intros H349 E349 L R.
 apply (x0_selected_uint_node_congruent 350 x0_concrete_expr_350 invalid left right next_left next_right).
 - apply (List.nth_error_In x0_expected_nodes 65). vm_compute. reflexivity.
 - intro site. cbn [x0_concrete_expr_350 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E349.
   reflexivity.
 - intros site value Eval.
   destruct (x0_uint_result_350 invalid site flat_memories left value H349 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Theorem exception_node_352_congruent invalid left right next_left next_right :
 (exists width bits, VM.find 351 left = Some (Gval (Fuint width) bits)) ->
 VM.find 351 left = VM.find 351 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 352 next_left = VM.find 352 next_right.
Proof.
 intros H351 E351 L R.
 apply (x0_selected_uint_node_congruent 352 x0_concrete_expr_352 invalid left right next_left next_right).
 - apply (List.nth_error_In x0_expected_nodes 67). vm_compute. reflexivity.
 - intro site. cbn [x0_concrete_expr_352 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E351.
   reflexivity.
 - intros site value Eval.
   destruct (x0_uint_result_352 invalid site flat_memories left value H351 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Theorem exception_node_354_congruent invalid left right next_left next_right :
 (exists width bits, VM.find 353 left = Some (Gval (Fuint width) bits)) ->
 VM.find 353 left = VM.find 353 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 354 next_left = VM.find 354 next_right.
Proof.
 intros H353 E353 L R.
 apply (x0_selected_uint_node_congruent 354 x0_concrete_expr_354 invalid left right next_left next_right).
 - apply (List.nth_error_In x0_expected_nodes 69). vm_compute. reflexivity.
 - intro site. cbn [x0_concrete_expr_354 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E353.
   reflexivity.
 - intros site value Eval.
   destruct (x0_uint_result_354 invalid site flat_memories left value H353 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Theorem exception_node_356_congruent invalid left right next_left next_right :
 (exists width bits, VM.find 355 left = Some (Gval (Fuint width) bits)) ->
 VM.find 355 left = VM.find 355 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 356 next_left = VM.find 356 next_right.
Proof.
 intros H355 E355 L R.
 apply (x0_selected_uint_node_congruent 356 x0_concrete_expr_356 invalid left right next_left next_right).
 - apply (List.nth_error_In x0_expected_nodes 71). vm_compute. reflexivity.
 - intro site. cbn [x0_concrete_expr_356 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E355.
   reflexivity.
 - intros site value Eval.
   destruct (x0_uint_result_356 invalid site flat_memories left value H355 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Theorem exception_node_358_congruent invalid left right next_left next_right :
 (exists width bits, VM.find 357 left = Some (Gval (Fuint width) bits)) ->
 VM.find 357 left = VM.find 357 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 358 next_left = VM.find 358 next_right.
Proof.
 intros H357 E357 L R.
 apply (x0_selected_uint_node_congruent 358 x0_concrete_expr_358 invalid left right next_left next_right).
 - apply (List.nth_error_In x0_expected_nodes 73). vm_compute. reflexivity.
 - intro site. cbn [x0_concrete_expr_358 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E357.
   reflexivity.
 - intros site value Eval.
   destruct (x0_uint_result_358 invalid site flat_memories left value H357 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Theorem exception_node_388_congruent invalid left right next_left next_right :
 (exists width bits, VM.find 387 left = Some (Gval (Fuint width) bits)) ->
 VM.find 387 left = VM.find 387 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 388 next_left = VM.find 388 next_right.
Proof.
 intros H387 E387 L R.
 apply (x0_selected_uint_node_congruent 388 x0_concrete_expr_388 invalid left right next_left next_right).
 - apply (List.nth_error_In x0_expected_nodes 103). vm_compute. reflexivity.
 - intro site. cbn [x0_concrete_expr_388 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E387.
   reflexivity.
 - intros site value Eval.
   destruct (x0_uint_result_388 invalid site flat_memories left value H387 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Theorem exception_node_396_congruent invalid left right next_left next_right :
 (exists width bits, VM.find 394 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 395 left = Some (Gval (Fuint width) bits)) ->
 VM.find 394 left = VM.find 394 right ->
 VM.find 395 left = VM.find 395 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 396 next_left = VM.find 396 next_right.
Proof.
 intros H394 H395 E394 E395 L R.
 apply (x0_selected_uint_node_congruent 396 x0_concrete_expr_396 invalid left right next_left next_right).
 - apply (List.nth_error_In x0_expected_nodes 111). vm_compute. reflexivity.
 - intro site. cbn [x0_concrete_expr_396 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E394.
   rewrite E395.
   reflexivity.
 - intros site value Eval.
   destruct (x0_uint_result_396 invalid site flat_memories left value H394 H395 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Theorem exception_node_414_congruent invalid left right next_left next_right :
 (exists width bits, VM.find 410 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 413 left = Some (Gval (Fuint width) bits)) ->
 VM.find 410 left = VM.find 410 right ->
 VM.find 413 left = VM.find 413 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 414 next_left = VM.find 414 next_right.
Proof.
 intros H410 H413 E410 E413 L R.
 apply (x0_selected_uint_node_congruent 414 x0_concrete_expr_414 invalid left right next_left next_right).
 - apply (List.nth_error_In x0_expected_nodes 120). vm_compute. reflexivity.
 - intro site. cbn [x0_concrete_expr_414 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E410.
   rewrite E413.
   reflexivity.
 - intros site value Eval.
   destruct (x0_uint_result_414 invalid site flat_memories left value H410 H413 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Theorem exception_node_423_congruent invalid left right next_left next_right :
 (exists width bits, VM.find 420 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 422 left = Some (Gval (Fuint width) bits)) ->
 VM.find 420 left = VM.find 420 right ->
 VM.find 422 left = VM.find 422 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 423 next_left = VM.find 423 next_right.
Proof.
 intros H420 H422 E420 E422 L R.
 apply (x0_selected_uint_node_congruent 423 x0_concrete_expr_423 invalid left right next_left next_right).
 - apply (List.nth_error_In x0_expected_nodes 129). vm_compute. reflexivity.
 - intro site. cbn [x0_concrete_expr_423 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E420.
   rewrite E422.
   reflexivity.
 - intros site value Eval.
   destruct (x0_uint_result_423 invalid site flat_memories left value H420 H422 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Theorem exception_node_426_congruent invalid left right next_left next_right :
 (exists width bits, VM.find 124 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 408 left = Some (Gval (Fuint width) bits)) ->
 VM.find 124 left = VM.find 124 right ->
 VM.find 408 left = VM.find 408 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 426 next_left = VM.find 426 next_right.
Proof.
 intros H124 H408 E124 E408 L R.
 apply (x0_selected_uint_node_congruent 426 x0_concrete_expr_426 invalid left right next_left next_right).
 - apply (List.nth_error_In x0_expected_nodes 132). vm_compute. reflexivity.
 - intro site. cbn [x0_concrete_expr_426 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E124.
   rewrite E408.
   reflexivity.
 - intros site value Eval.
   destruct (x0_uint_result_426 invalid site flat_memories left value H124 H408 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Theorem exception_node_287_congruent invalid left right next_left next_right :
 (exists width bits, VM.find 284 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 286 left = Some (Gval (Fuint width) bits)) ->
 VM.find 284 left = VM.find 284 right ->
 VM.find 286 left = VM.find 286 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 287 next_left = VM.find 287 next_right.
Proof.
 intros H284 H286 E284 E286 L R.
 apply (x0_selected_uint_node_congruent 287 x0_concrete_expr_287 invalid left right next_left next_right).
 - apply (List.nth_error_In x0_expected_nodes 7). vm_compute. reflexivity.
 - intro site. cbn [x0_concrete_expr_287 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E284.
   rewrite E286.
   reflexivity.
 - intros site value Eval.
   destruct (x0_uint_result_287 invalid site flat_memories left value H284 H286 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Theorem exception_node_295_congruent invalid left right next_left next_right :
 (exists width bits, VM.find 292 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 294 left = Some (Gval (Fuint width) bits)) ->
 VM.find 292 left = VM.find 292 right ->
 VM.find 294 left = VM.find 294 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 295 next_left = VM.find 295 next_right.
Proof.
 intros H292 H294 E292 E294 L R.
 apply (x0_selected_uint_node_congruent 295 x0_concrete_expr_295 invalid left right next_left next_right).
 - apply (List.nth_error_In x0_expected_nodes 15). vm_compute. reflexivity.
 - intro site. cbn [x0_concrete_expr_295 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E292.
   rewrite E294.
   reflexivity.
 - intros site value Eval.
   destruct (x0_uint_result_295 invalid site flat_memories left value H292 H294 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Theorem exception_node_359_congruent invalid left right next_left next_right :
 (exists width bits, VM.find 302 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 304 left = Some (Gval (Fuint width) bits)) ->
 VM.find 302 left = VM.find 302 right ->
 VM.find 304 left = VM.find 304 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 359 next_left = VM.find 359 next_right.
Proof.
 intros H302 H304 E302 E304 L R.
 apply (x0_selected_uint_node_congruent 359 x0_concrete_expr_359 invalid left right next_left next_right).
 - apply (List.nth_error_In x0_expected_nodes 74). vm_compute. reflexivity.
 - intro site. cbn [x0_concrete_expr_359 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E302.
   rewrite E304.
   reflexivity.
 - intros site value Eval.
   destruct (x0_uint_result_359 invalid site flat_memories left value H302 H304 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Theorem exception_node_390_congruent invalid left right next_left next_right :
 (exists width bits, VM.find 388 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 389 left = Some (Gval (Fuint width) bits)) ->
 VM.find 388 left = VM.find 388 right ->
 VM.find 389 left = VM.find 389 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 390 next_left = VM.find 390 next_right.
Proof.
 intros H388 H389 E388 E389 L R.
 apply (x0_selected_uint_node_congruent 390 x0_concrete_expr_390 invalid left right next_left next_right).
 - apply (List.nth_error_In x0_expected_nodes 105). vm_compute. reflexivity.
 - intro site. cbn [x0_concrete_expr_390 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E388.
   rewrite E389.
   reflexivity.
 - intros site value Eval.
   destruct (x0_uint_result_390 invalid site flat_memories left value H388 H389 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Theorem exception_node_397_congruent invalid left right next_left next_right :
 (exists width bits, VM.find 393 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 396 left = Some (Gval (Fuint width) bits)) ->
 VM.find 393 left = VM.find 393 right ->
 VM.find 396 left = VM.find 396 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 397 next_left = VM.find 397 next_right.
Proof.
 intros H393 H396 E393 E396 L R.
 apply (x0_selected_uint_node_congruent 397 x0_concrete_expr_397 invalid left right next_left next_right).
 - apply (List.nth_error_In x0_expected_nodes 112). vm_compute. reflexivity.
 - intro site. cbn [x0_concrete_expr_397 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E393.
   rewrite E396.
   reflexivity.
 - intros site value Eval.
   destruct (x0_uint_result_397 invalid site flat_memories left value H393 H396 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Theorem exception_node_416_congruent invalid left right next_left next_right :
 (exists width bits, VM.find 411 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 414 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 415 left = Some (Gval (Fuint width) bits)) ->
 VM.find 411 left = VM.find 411 right ->
 VM.find 414 left = VM.find 414 right ->
 VM.find 415 left = VM.find 415 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 416 next_left = VM.find 416 next_right.
Proof.
 intros H411 H414 H415 E411 E414 E415 L R.
 apply (x0_selected_uint_node_congruent 416 x0_concrete_expr_416 invalid left right next_left next_right).
 - apply (List.nth_error_In x0_expected_nodes 122). vm_compute. reflexivity.
 - intro site. cbn [x0_concrete_expr_416 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E411.
   rewrite E414.
   rewrite E415.
   reflexivity.
 - intros site value Eval.
   destruct (x0_uint_result_416 invalid site flat_memories left value H411 H414 H415 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Theorem exception_node_425_congruent invalid left right next_left next_right :
 (exists width bits, VM.find 421 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 423 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 424 left = Some (Gval (Fuint width) bits)) ->
 VM.find 421 left = VM.find 421 right ->
 VM.find 423 left = VM.find 423 right ->
 VM.find 424 left = VM.find 424 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 425 next_left = VM.find 425 next_right.
Proof.
 intros H421 H423 H424 E421 E423 E424 L R.
 apply (x0_selected_uint_node_congruent 425 x0_concrete_expr_425 invalid left right next_left next_right).
 - apply (List.nth_error_In x0_expected_nodes 131). vm_compute. reflexivity.
 - intro site. cbn [x0_concrete_expr_425 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E421.
   rewrite E423.
   rewrite E424.
   reflexivity.
 - intros site value Eval.
   destruct (x0_uint_result_425 invalid site flat_memories left value H421 H423 H424 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Theorem exception_node_432_congruent invalid left right next_left next_right :
 (exists width bits, VM.find 283 left = Some (Gval (Fuint width) bits)) ->
 VM.find 283 left = VM.find 283 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 432 next_left = VM.find 432 next_right.
Proof.
 intros H283 E283 L R.
 apply (x0_selected_uint_node_congruent 432 x0_concrete_expr_432 invalid left right next_left next_right).
 - apply (List.nth_error_In x0_expected_nodes 138). vm_compute. reflexivity.
 - intro site. cbn [x0_concrete_expr_432 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E283.
   reflexivity.
 - intros site value Eval.
   destruct (x0_uint_result_432 invalid site flat_memories left value H283 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Theorem exception_node_438_congruent invalid left right next_left next_right :
 (exists width bits, VM.find 283 left = Some (Gval (Fuint width) bits)) ->
 VM.find 283 left = VM.find 283 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 438 next_left = VM.find 438 next_right.
Proof.
 intros H283 E283 L R.
 apply (x0_selected_uint_node_congruent 438 x0_concrete_expr_438 invalid left right next_left next_right).
 - apply (List.nth_error_In x0_expected_nodes 144). vm_compute. reflexivity.
 - intro site. cbn [x0_concrete_expr_438 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E283.
   reflexivity.
 - intros site value Eval.
   destruct (x0_uint_result_438 invalid site flat_memories left value H283 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Theorem exception_node_290_congruent invalid left right next_left next_right :
 (exists width bits, VM.find 287 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 289 left = Some (Gval (Fuint width) bits)) ->
 VM.find 287 left = VM.find 287 right ->
 VM.find 289 left = VM.find 289 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 290 next_left = VM.find 290 next_right.
Proof.
 intros H287 H289 E287 E289 L R.
 apply (x0_selected_uint_node_congruent 290 x0_concrete_expr_290 invalid left right next_left next_right).
 - apply (List.nth_error_In x0_expected_nodes 10). vm_compute. reflexivity.
 - intro site. cbn [x0_concrete_expr_290 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E287.
   rewrite E289.
   reflexivity.
 - intros site value Eval.
   destruct (x0_uint_result_290 invalid site flat_memories left value H287 H289 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Theorem exception_node_360_congruent invalid left right next_left next_right :
 (exists width bits, VM.find 306 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 359 left = Some (Gval (Fuint width) bits)) ->
 VM.find 306 left = VM.find 306 right ->
 VM.find 359 left = VM.find 359 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 360 next_left = VM.find 360 next_right.
Proof.
 intros H306 H359 E306 E359 L R.
 apply (x0_selected_uint_node_congruent 360 x0_concrete_expr_360 invalid left right next_left next_right).
 - apply (List.nth_error_In x0_expected_nodes 75). vm_compute. reflexivity.
 - intro site. cbn [x0_concrete_expr_360 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E306.
   rewrite E359.
   reflexivity.
 - intros site value Eval.
   destruct (x0_uint_result_360 invalid site flat_memories left value H306 H359 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Theorem exception_node_392_congruent invalid left right next_left next_right :
 (exists width bits, VM.find 390 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 391 left = Some (Gval (Fuint width) bits)) ->
 VM.find 390 left = VM.find 390 right ->
 VM.find 391 left = VM.find 391 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 392 next_left = VM.find 392 next_right.
Proof.
 intros H390 H391 E390 E391 L R.
 apply (x0_selected_uint_node_congruent 392 x0_concrete_expr_392 invalid left right next_left next_right).
 - apply (List.nth_error_In x0_expected_nodes 107). vm_compute. reflexivity.
 - intro site. cbn [x0_concrete_expr_392 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E390.
   rewrite E391.
   reflexivity.
 - intros site value Eval.
   destruct (x0_uint_result_392 invalid site flat_memories left value H390 H391 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Theorem exception_node_418_congruent invalid left right next_left next_right :
 (exists width bits, VM.find 412 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 416 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 417 left = Some (Gval (Fuint width) bits)) ->
 VM.find 412 left = VM.find 412 right ->
 VM.find 416 left = VM.find 416 right ->
 VM.find 417 left = VM.find 417 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 418 next_left = VM.find 418 next_right.
Proof.
 intros H412 H416 H417 E412 E416 E417 L R.
 apply (x0_selected_uint_node_congruent 418 x0_concrete_expr_418 invalid left right next_left next_right).
 - apply (List.nth_error_In x0_expected_nodes 124). vm_compute. reflexivity.
 - intro site. cbn [x0_concrete_expr_418 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E412.
   rewrite E416.
   rewrite E417.
   reflexivity.
 - intros site value Eval.
   destruct (x0_uint_result_418 invalid site flat_memories left value H412 H416 H417 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Theorem exception_node_439_congruent invalid left right next_left next_right :
 (exists width bits, VM.find 284 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 438 left = Some (Gval (Fuint width) bits)) ->
 VM.find 284 left = VM.find 284 right ->
 VM.find 438 left = VM.find 438 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 439 next_left = VM.find 439 next_right.
Proof.
 intros H284 H438 E284 E438 L R.
 apply (x0_selected_uint_node_congruent 439 x0_concrete_expr_439 invalid left right next_left next_right).
 - apply (List.nth_error_In x0_expected_nodes 145). vm_compute. reflexivity.
 - intro site. cbn [x0_concrete_expr_439 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E284.
   rewrite E438.
   reflexivity.
 - intros site value Eval.
   destruct (x0_uint_result_439 invalid site flat_memories left value H284 H438 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Theorem exception_node_361_congruent invalid left right next_left next_right :
 (exists width bits, VM.find 308 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 360 left = Some (Gval (Fuint width) bits)) ->
 VM.find 308 left = VM.find 308 right ->
 VM.find 360 left = VM.find 360 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 361 next_left = VM.find 361 next_right.
Proof.
 intros H308 H360 E308 E360 L R.
 apply (x0_selected_uint_node_congruent 361 x0_concrete_expr_361 invalid left right next_left next_right).
 - apply (List.nth_error_In x0_expected_nodes 76). vm_compute. reflexivity.
 - intro site. cbn [x0_concrete_expr_361 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E308.
   rewrite E360.
   reflexivity.
 - intros site value Eval.
   destruct (x0_uint_result_361 invalid site flat_memories left value H308 H360 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Theorem exception_node_427_congruent invalid left right next_left next_right :
 (exists width bits, VM.find 418 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 426 left = Some (Gval (Fuint width) bits)) ->
 VM.find 418 left = VM.find 418 right ->
 VM.find 426 left = VM.find 426 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 427 next_left = VM.find 427 next_right.
Proof.
 intros H418 H426 E418 E426 L R.
 apply (x0_selected_uint_node_congruent 427 x0_concrete_expr_427 invalid left right next_left next_right).
 - apply (List.nth_error_In x0_expected_nodes 133). vm_compute. reflexivity.
 - intro site. cbn [x0_concrete_expr_427 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E418.
   rewrite E426.
   reflexivity.
 - intros site value Eval.
   destruct (x0_uint_result_427 invalid site flat_memories left value H418 H426 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Theorem exception_node_436_congruent invalid left right next_left next_right :
 (exists width bits, VM.find 392 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 397 left = Some (Gval (Fuint width) bits)) ->
 VM.find 392 left = VM.find 392 right ->
 VM.find 397 left = VM.find 397 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 436 next_left = VM.find 436 next_right.
Proof.
 intros H392 H397 E392 E397 L R.
 apply (x0_selected_uint_node_congruent 436 x0_concrete_expr_436 invalid left right next_left next_right).
 - apply (List.nth_error_In x0_expected_nodes 142). vm_compute. reflexivity.
 - intro site. cbn [x0_concrete_expr_436 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E392.
   rewrite E397.
   reflexivity.
 - intros site value Eval.
   destruct (x0_uint_result_436 invalid site flat_memories left value H392 H397 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Theorem exception_node_362_congruent invalid left right next_left next_right :
 (exists width bits, VM.find 310 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 361 left = Some (Gval (Fuint width) bits)) ->
 VM.find 310 left = VM.find 310 right ->
 VM.find 361 left = VM.find 361 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 362 next_left = VM.find 362 next_right.
Proof.
 intros H310 H361 E310 E361 L R.
 apply (x0_selected_uint_node_congruent 362 x0_concrete_expr_362 invalid left right next_left next_right).
 - apply (List.nth_error_In x0_expected_nodes 77). vm_compute. reflexivity.
 - intro site. cbn [x0_concrete_expr_362 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E310.
   rewrite E361.
   reflexivity.
 - intros site value Eval.
   destruct (x0_uint_result_362 invalid site flat_memories left value H310 H361 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Theorem exception_node_428_congruent invalid left right next_left next_right :
 (exists width bits, VM.find 425 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 427 left = Some (Gval (Fuint width) bits)) ->
 VM.find 425 left = VM.find 425 right ->
 VM.find 427 left = VM.find 427 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 428 next_left = VM.find 428 next_right.
Proof.
 intros H425 H427 E425 E427 L R.
 apply (x0_selected_uint_node_congruent 428 x0_concrete_expr_428 invalid left right next_left next_right).
 - apply (List.nth_error_In x0_expected_nodes 134). vm_compute. reflexivity.
 - intro site. cbn [x0_concrete_expr_428 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E425.
   rewrite E427.
   reflexivity.
 - intros site value Eval.
   destruct (x0_uint_result_428 invalid site flat_memories left value H425 H427 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Theorem exception_node_363_congruent invalid left right next_left next_right :
 (exists width bits, VM.find 312 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 362 left = Some (Gval (Fuint width) bits)) ->
 VM.find 312 left = VM.find 312 right ->
 VM.find 362 left = VM.find 362 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 363 next_left = VM.find 363 next_right.
Proof.
 intros H312 H362 E312 E362 L R.
 apply (x0_selected_uint_node_congruent 363 x0_concrete_expr_363 invalid left right next_left next_right).
 - apply (List.nth_error_In x0_expected_nodes 78). vm_compute. reflexivity.
 - intro site. cbn [x0_concrete_expr_363 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E312.
   rewrite E362.
   reflexivity.
 - intros site value Eval.
   destruct (x0_uint_result_363 invalid site flat_memories left value H312 H362 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Theorem exception_node_364_congruent invalid left right next_left next_right :
 (exists width bits, VM.find 314 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 363 left = Some (Gval (Fuint width) bits)) ->
 VM.find 314 left = VM.find 314 right ->
 VM.find 363 left = VM.find 363 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 364 next_left = VM.find 364 next_right.
Proof.
 intros H314 H363 E314 E363 L R.
 apply (x0_selected_uint_node_congruent 364 x0_concrete_expr_364 invalid left right next_left next_right).
 - apply (List.nth_error_In x0_expected_nodes 79). vm_compute. reflexivity.
 - intro site. cbn [x0_concrete_expr_364 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E314.
   rewrite E363.
   reflexivity.
 - intros site value Eval.
   destruct (x0_uint_result_364 invalid site flat_memories left value H314 H363 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Theorem exception_node_365_congruent invalid left right next_left next_right :
 (exists width bits, VM.find 316 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 364 left = Some (Gval (Fuint width) bits)) ->
 VM.find 316 left = VM.find 316 right ->
 VM.find 364 left = VM.find 364 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 365 next_left = VM.find 365 next_right.
Proof.
 intros H316 H364 E316 E364 L R.
 apply (x0_selected_uint_node_congruent 365 x0_concrete_expr_365 invalid left right next_left next_right).
 - apply (List.nth_error_In x0_expected_nodes 80). vm_compute. reflexivity.
 - intro site. cbn [x0_concrete_expr_365 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E316.
   rewrite E364.
   reflexivity.
 - intros site value Eval.
   destruct (x0_uint_result_365 invalid site flat_memories left value H316 H364 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Theorem exception_node_366_congruent invalid left right next_left next_right :
 (exists width bits, VM.find 318 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 365 left = Some (Gval (Fuint width) bits)) ->
 VM.find 318 left = VM.find 318 right ->
 VM.find 365 left = VM.find 365 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 366 next_left = VM.find 366 next_right.
Proof.
 intros H318 H365 E318 E365 L R.
 apply (x0_selected_uint_node_congruent 366 x0_concrete_expr_366 invalid left right next_left next_right).
 - apply (List.nth_error_In x0_expected_nodes 81). vm_compute. reflexivity.
 - intro site. cbn [x0_concrete_expr_366 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E318.
   rewrite E365.
   reflexivity.
 - intros site value Eval.
   destruct (x0_uint_result_366 invalid site flat_memories left value H318 H365 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Theorem exception_node_367_congruent invalid left right next_left next_right :
 (exists width bits, VM.find 320 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 366 left = Some (Gval (Fuint width) bits)) ->
 VM.find 320 left = VM.find 320 right ->
 VM.find 366 left = VM.find 366 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 367 next_left = VM.find 367 next_right.
Proof.
 intros H320 H366 E320 E366 L R.
 apply (x0_selected_uint_node_congruent 367 x0_concrete_expr_367 invalid left right next_left next_right).
 - apply (List.nth_error_In x0_expected_nodes 82). vm_compute. reflexivity.
 - intro site. cbn [x0_concrete_expr_367 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E320.
   rewrite E366.
   reflexivity.
 - intros site value Eval.
   destruct (x0_uint_result_367 invalid site flat_memories left value H320 H366 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Theorem exception_node_368_congruent invalid left right next_left next_right :
 (exists width bits, VM.find 322 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 367 left = Some (Gval (Fuint width) bits)) ->
 VM.find 322 left = VM.find 322 right ->
 VM.find 367 left = VM.find 367 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 368 next_left = VM.find 368 next_right.
Proof.
 intros H322 H367 E322 E367 L R.
 apply (x0_selected_uint_node_congruent 368 x0_concrete_expr_368 invalid left right next_left next_right).
 - apply (List.nth_error_In x0_expected_nodes 83). vm_compute. reflexivity.
 - intro site. cbn [x0_concrete_expr_368 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E322.
   rewrite E367.
   reflexivity.
 - intros site value Eval.
   destruct (x0_uint_result_368 invalid site flat_memories left value H322 H367 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Theorem exception_node_369_congruent invalid left right next_left next_right :
 (exists width bits, VM.find 324 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 368 left = Some (Gval (Fuint width) bits)) ->
 VM.find 324 left = VM.find 324 right ->
 VM.find 368 left = VM.find 368 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 369 next_left = VM.find 369 next_right.
Proof.
 intros H324 H368 E324 E368 L R.
 apply (x0_selected_uint_node_congruent 369 x0_concrete_expr_369 invalid left right next_left next_right).
 - apply (List.nth_error_In x0_expected_nodes 84). vm_compute. reflexivity.
 - intro site. cbn [x0_concrete_expr_369 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E324.
   rewrite E368.
   reflexivity.
 - intros site value Eval.
   destruct (x0_uint_result_369 invalid site flat_memories left value H324 H368 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Theorem exception_node_370_congruent invalid left right next_left next_right :
 (exists width bits, VM.find 326 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 369 left = Some (Gval (Fuint width) bits)) ->
 VM.find 326 left = VM.find 326 right ->
 VM.find 369 left = VM.find 369 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 370 next_left = VM.find 370 next_right.
Proof.
 intros H326 H369 E326 E369 L R.
 apply (x0_selected_uint_node_congruent 370 x0_concrete_expr_370 invalid left right next_left next_right).
 - apply (List.nth_error_In x0_expected_nodes 85). vm_compute. reflexivity.
 - intro site. cbn [x0_concrete_expr_370 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E326.
   rewrite E369.
   reflexivity.
 - intros site value Eval.
   destruct (x0_uint_result_370 invalid site flat_memories left value H326 H369 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Theorem exception_node_371_congruent invalid left right next_left next_right :
 (exists width bits, VM.find 328 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 370 left = Some (Gval (Fuint width) bits)) ->
 VM.find 328 left = VM.find 328 right ->
 VM.find 370 left = VM.find 370 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 371 next_left = VM.find 371 next_right.
Proof.
 intros H328 H370 E328 E370 L R.
 apply (x0_selected_uint_node_congruent 371 x0_concrete_expr_371 invalid left right next_left next_right).
 - apply (List.nth_error_In x0_expected_nodes 86). vm_compute. reflexivity.
 - intro site. cbn [x0_concrete_expr_371 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E328.
   rewrite E370.
   reflexivity.
 - intros site value Eval.
   destruct (x0_uint_result_371 invalid site flat_memories left value H328 H370 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Theorem exception_node_372_congruent invalid left right next_left next_right :
 (exists width bits, VM.find 330 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 371 left = Some (Gval (Fuint width) bits)) ->
 VM.find 330 left = VM.find 330 right ->
 VM.find 371 left = VM.find 371 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 372 next_left = VM.find 372 next_right.
Proof.
 intros H330 H371 E330 E371 L R.
 apply (x0_selected_uint_node_congruent 372 x0_concrete_expr_372 invalid left right next_left next_right).
 - apply (List.nth_error_In x0_expected_nodes 87). vm_compute. reflexivity.
 - intro site. cbn [x0_concrete_expr_372 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E330.
   rewrite E371.
   reflexivity.
 - intros site value Eval.
   destruct (x0_uint_result_372 invalid site flat_memories left value H330 H371 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Theorem exception_node_373_congruent invalid left right next_left next_right :
 (exists width bits, VM.find 332 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 372 left = Some (Gval (Fuint width) bits)) ->
 VM.find 332 left = VM.find 332 right ->
 VM.find 372 left = VM.find 372 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 373 next_left = VM.find 373 next_right.
Proof.
 intros H332 H372 E332 E372 L R.
 apply (x0_selected_uint_node_congruent 373 x0_concrete_expr_373 invalid left right next_left next_right).
 - apply (List.nth_error_In x0_expected_nodes 88). vm_compute. reflexivity.
 - intro site. cbn [x0_concrete_expr_373 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E332.
   rewrite E372.
   reflexivity.
 - intros site value Eval.
   destruct (x0_uint_result_373 invalid site flat_memories left value H332 H372 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Theorem exception_node_374_congruent invalid left right next_left next_right :
 (exists width bits, VM.find 334 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 373 left = Some (Gval (Fuint width) bits)) ->
 VM.find 334 left = VM.find 334 right ->
 VM.find 373 left = VM.find 373 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 374 next_left = VM.find 374 next_right.
Proof.
 intros H334 H373 E334 E373 L R.
 apply (x0_selected_uint_node_congruent 374 x0_concrete_expr_374 invalid left right next_left next_right).
 - apply (List.nth_error_In x0_expected_nodes 89). vm_compute. reflexivity.
 - intro site. cbn [x0_concrete_expr_374 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E334.
   rewrite E373.
   reflexivity.
 - intros site value Eval.
   destruct (x0_uint_result_374 invalid site flat_memories left value H334 H373 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Theorem exception_node_375_congruent invalid left right next_left next_right :
 (exists width bits, VM.find 336 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 374 left = Some (Gval (Fuint width) bits)) ->
 VM.find 336 left = VM.find 336 right ->
 VM.find 374 left = VM.find 374 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 375 next_left = VM.find 375 next_right.
Proof.
 intros H336 H374 E336 E374 L R.
 apply (x0_selected_uint_node_congruent 375 x0_concrete_expr_375 invalid left right next_left next_right).
 - apply (List.nth_error_In x0_expected_nodes 90). vm_compute. reflexivity.
 - intro site. cbn [x0_concrete_expr_375 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E336.
   rewrite E374.
   reflexivity.
 - intros site value Eval.
   destruct (x0_uint_result_375 invalid site flat_memories left value H336 H374 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Theorem exception_node_376_congruent invalid left right next_left next_right :
 (exists width bits, VM.find 338 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 375 left = Some (Gval (Fuint width) bits)) ->
 VM.find 338 left = VM.find 338 right ->
 VM.find 375 left = VM.find 375 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 376 next_left = VM.find 376 next_right.
Proof.
 intros H338 H375 E338 E375 L R.
 apply (x0_selected_uint_node_congruent 376 x0_concrete_expr_376 invalid left right next_left next_right).
 - apply (List.nth_error_In x0_expected_nodes 91). vm_compute. reflexivity.
 - intro site. cbn [x0_concrete_expr_376 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E338.
   rewrite E375.
   reflexivity.
 - intros site value Eval.
   destruct (x0_uint_result_376 invalid site flat_memories left value H338 H375 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Theorem exception_node_377_congruent invalid left right next_left next_right :
 (exists width bits, VM.find 340 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 376 left = Some (Gval (Fuint width) bits)) ->
 VM.find 340 left = VM.find 340 right ->
 VM.find 376 left = VM.find 376 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 377 next_left = VM.find 377 next_right.
Proof.
 intros H340 H376 E340 E376 L R.
 apply (x0_selected_uint_node_congruent 377 x0_concrete_expr_377 invalid left right next_left next_right).
 - apply (List.nth_error_In x0_expected_nodes 92). vm_compute. reflexivity.
 - intro site. cbn [x0_concrete_expr_377 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E340.
   rewrite E376.
   reflexivity.
 - intros site value Eval.
   destruct (x0_uint_result_377 invalid site flat_memories left value H340 H376 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Theorem exception_node_378_congruent invalid left right next_left next_right :
 (exists width bits, VM.find 342 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 377 left = Some (Gval (Fuint width) bits)) ->
 VM.find 342 left = VM.find 342 right ->
 VM.find 377 left = VM.find 377 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 378 next_left = VM.find 378 next_right.
Proof.
 intros H342 H377 E342 E377 L R.
 apply (x0_selected_uint_node_congruent 378 x0_concrete_expr_378 invalid left right next_left next_right).
 - apply (List.nth_error_In x0_expected_nodes 93). vm_compute. reflexivity.
 - intro site. cbn [x0_concrete_expr_378 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E342.
   rewrite E377.
   reflexivity.
 - intros site value Eval.
   destruct (x0_uint_result_378 invalid site flat_memories left value H342 H377 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Theorem exception_node_379_congruent invalid left right next_left next_right :
 (exists width bits, VM.find 344 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 378 left = Some (Gval (Fuint width) bits)) ->
 VM.find 344 left = VM.find 344 right ->
 VM.find 378 left = VM.find 378 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 379 next_left = VM.find 379 next_right.
Proof.
 intros H344 H378 E344 E378 L R.
 apply (x0_selected_uint_node_congruent 379 x0_concrete_expr_379 invalid left right next_left next_right).
 - apply (List.nth_error_In x0_expected_nodes 94). vm_compute. reflexivity.
 - intro site. cbn [x0_concrete_expr_379 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E344.
   rewrite E378.
   reflexivity.
 - intros site value Eval.
   destruct (x0_uint_result_379 invalid site flat_memories left value H344 H378 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Theorem exception_node_380_congruent invalid left right next_left next_right :
 (exists width bits, VM.find 346 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 379 left = Some (Gval (Fuint width) bits)) ->
 VM.find 346 left = VM.find 346 right ->
 VM.find 379 left = VM.find 379 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 380 next_left = VM.find 380 next_right.
Proof.
 intros H346 H379 E346 E379 L R.
 apply (x0_selected_uint_node_congruent 380 x0_concrete_expr_380 invalid left right next_left next_right).
 - apply (List.nth_error_In x0_expected_nodes 95). vm_compute. reflexivity.
 - intro site. cbn [x0_concrete_expr_380 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E346.
   rewrite E379.
   reflexivity.
 - intros site value Eval.
   destruct (x0_uint_result_380 invalid site flat_memories left value H346 H379 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Theorem exception_node_381_congruent invalid left right next_left next_right :
 (exists width bits, VM.find 348 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 380 left = Some (Gval (Fuint width) bits)) ->
 VM.find 348 left = VM.find 348 right ->
 VM.find 380 left = VM.find 380 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 381 next_left = VM.find 381 next_right.
Proof.
 intros H348 H380 E348 E380 L R.
 apply (x0_selected_uint_node_congruent 381 x0_concrete_expr_381 invalid left right next_left next_right).
 - apply (List.nth_error_In x0_expected_nodes 96). vm_compute. reflexivity.
 - intro site. cbn [x0_concrete_expr_381 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E348.
   rewrite E380.
   reflexivity.
 - intros site value Eval.
   destruct (x0_uint_result_381 invalid site flat_memories left value H348 H380 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Theorem exception_node_382_congruent invalid left right next_left next_right :
 (exists width bits, VM.find 350 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 381 left = Some (Gval (Fuint width) bits)) ->
 VM.find 350 left = VM.find 350 right ->
 VM.find 381 left = VM.find 381 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 382 next_left = VM.find 382 next_right.
Proof.
 intros H350 H381 E350 E381 L R.
 apply (x0_selected_uint_node_congruent 382 x0_concrete_expr_382 invalid left right next_left next_right).
 - apply (List.nth_error_In x0_expected_nodes 97). vm_compute. reflexivity.
 - intro site. cbn [x0_concrete_expr_382 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E350.
   rewrite E381.
   reflexivity.
 - intros site value Eval.
   destruct (x0_uint_result_382 invalid site flat_memories left value H350 H381 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Theorem exception_node_383_congruent invalid left right next_left next_right :
 (exists width bits, VM.find 352 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 382 left = Some (Gval (Fuint width) bits)) ->
 VM.find 352 left = VM.find 352 right ->
 VM.find 382 left = VM.find 382 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 383 next_left = VM.find 383 next_right.
Proof.
 intros H352 H382 E352 E382 L R.
 apply (x0_selected_uint_node_congruent 383 x0_concrete_expr_383 invalid left right next_left next_right).
 - apply (List.nth_error_In x0_expected_nodes 98). vm_compute. reflexivity.
 - intro site. cbn [x0_concrete_expr_383 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E352.
   rewrite E382.
   reflexivity.
 - intros site value Eval.
   destruct (x0_uint_result_383 invalid site flat_memories left value H352 H382 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Theorem exception_node_384_congruent invalid left right next_left next_right :
 (exists width bits, VM.find 354 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 383 left = Some (Gval (Fuint width) bits)) ->
 VM.find 354 left = VM.find 354 right ->
 VM.find 383 left = VM.find 383 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 384 next_left = VM.find 384 next_right.
Proof.
 intros H354 H383 E354 E383 L R.
 apply (x0_selected_uint_node_congruent 384 x0_concrete_expr_384 invalid left right next_left next_right).
 - apply (List.nth_error_In x0_expected_nodes 99). vm_compute. reflexivity.
 - intro site. cbn [x0_concrete_expr_384 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E354.
   rewrite E383.
   reflexivity.
 - intros site value Eval.
   destruct (x0_uint_result_384 invalid site flat_memories left value H354 H383 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Theorem exception_node_385_congruent invalid left right next_left next_right :
 (exists width bits, VM.find 356 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 384 left = Some (Gval (Fuint width) bits)) ->
 VM.find 356 left = VM.find 356 right ->
 VM.find 384 left = VM.find 384 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 385 next_left = VM.find 385 next_right.
Proof.
 intros H356 H384 E356 E384 L R.
 apply (x0_selected_uint_node_congruent 385 x0_concrete_expr_385 invalid left right next_left next_right).
 - apply (List.nth_error_In x0_expected_nodes 100). vm_compute. reflexivity.
 - intro site. cbn [x0_concrete_expr_385 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E356.
   rewrite E384.
   reflexivity.
 - intros site value Eval.
   destruct (x0_uint_result_385 invalid site flat_memories left value H356 H384 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Theorem exception_node_386_congruent invalid left right next_left next_right :
 (exists width bits, VM.find 358 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 385 left = Some (Gval (Fuint width) bits)) ->
 VM.find 358 left = VM.find 358 right ->
 VM.find 385 left = VM.find 385 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 386 next_left = VM.find 386 next_right.
Proof.
 intros H358 H385 E358 E385 L R.
 apply (x0_selected_uint_node_congruent 386 x0_concrete_expr_386 invalid left right next_left next_right).
 - apply (List.nth_error_In x0_expected_nodes 101). vm_compute. reflexivity.
 - intro site. cbn [x0_concrete_expr_386 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E358.
   rewrite E385.
   reflexivity.
 - intros site value Eval.
   destruct (x0_uint_result_386 invalid site flat_memories left value H358 H385 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Theorem exception_node_431_congruent invalid left right next_left next_right :
 (exists width bits, VM.find 386 left = Some (Gval (Fuint width) bits)) ->
 VM.find 386 left = VM.find 386 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 431 next_left = VM.find 431 next_right.
Proof.
 intros H386 E386 L R.
 apply (x0_selected_uint_node_congruent 431 x0_concrete_expr_431 invalid left right next_left next_right).
 - apply (List.nth_error_In x0_expected_nodes 137). vm_compute. reflexivity.
 - intro site. cbn [x0_concrete_expr_431 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E386.
   reflexivity.
 - intros site value Eval.
   destruct (x0_uint_result_431 invalid site flat_memories left value H386 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Theorem exception_node_433_congruent invalid left right next_left next_right :
 (exists width bits, VM.find 431 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 432 left = Some (Gval (Fuint width) bits)) ->
 VM.find 431 left = VM.find 431 right ->
 VM.find 432 left = VM.find 432 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 433 next_left = VM.find 433 next_right.
Proof.
 intros H431 H432 E431 E432 L R.
 apply (x0_selected_uint_node_congruent 433 x0_concrete_expr_433 invalid left right next_left next_right).
 - apply (List.nth_error_In x0_expected_nodes 139). vm_compute. reflexivity.
 - intro site. cbn [x0_concrete_expr_433 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E431.
   rewrite E432.
   reflexivity.
 - intros site value Eval.
   destruct (x0_uint_result_433 invalid site flat_memories left value H431 H432 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Theorem exception_node_434_congruent invalid left right next_left next_right :
 (exists width bits, VM.find 430 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 433 left = Some (Gval (Fuint width) bits)) ->
 VM.find 430 left = VM.find 430 right ->
 VM.find 433 left = VM.find 433 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 434 next_left = VM.find 434 next_right.
Proof.
 intros H430 H433 E430 E433 L R.
 apply (x0_selected_uint_node_congruent 434 x0_concrete_expr_434 invalid left right next_left next_right).
 - apply (List.nth_error_In x0_expected_nodes 140). vm_compute. reflexivity.
 - intro site. cbn [x0_concrete_expr_434 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E430.
   rewrite E433.
   reflexivity.
 - intros site value Eval.
   destruct (x0_uint_result_434 invalid site flat_memories left value H430 H433 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Theorem exception_node_435_congruent invalid left right next_left next_right :
 (exists width bits, VM.find 428 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 434 left = Some (Gval (Fuint width) bits)) ->
 VM.find 428 left = VM.find 428 right ->
 VM.find 434 left = VM.find 434 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 435 next_left = VM.find 435 next_right.
Proof.
 intros H428 H434 E428 E434 L R.
 apply (x0_selected_uint_node_congruent 435 x0_concrete_expr_435 invalid left right next_left next_right).
 - apply (List.nth_error_In x0_expected_nodes 141). vm_compute. reflexivity.
 - intro site. cbn [x0_concrete_expr_435 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E428.
   rewrite E434.
   reflexivity.
 - intros site value Eval.
   destruct (x0_uint_result_435 invalid site flat_memories left value H428 H434 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Theorem exception_node_437_congruent invalid left right next_left next_right :
 (exists width bits, VM.find 435 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 436 left = Some (Gval (Fuint width) bits)) ->
 VM.find 435 left = VM.find 435 right ->
 VM.find 436 left = VM.find 436 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 437 next_left = VM.find 437 next_right.
Proof.
 intros H435 H436 E435 E436 L R.
 apply (x0_selected_uint_node_congruent 437 x0_concrete_expr_437 invalid left right next_left next_right).
 - apply (List.nth_error_In x0_expected_nodes 143). vm_compute. reflexivity.
 - intro site. cbn [x0_concrete_expr_437 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E435.
   rewrite E436.
   reflexivity.
 - intros site value Eval.
   destruct (x0_uint_result_437 invalid site flat_memories left value H435 H436 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Theorem exception_node_440_congruent invalid left right next_left next_right :
 (exists width bits, VM.find 437 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 439 left = Some (Gval (Fuint width) bits)) ->
 VM.find 437 left = VM.find 437 right ->
 VM.find 439 left = VM.find 439 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 440 next_left = VM.find 440 next_right.
Proof.
 intros H437 H439 E437 E439 L R.
 apply (x0_selected_uint_node_congruent 440 x0_concrete_expr_440 invalid left right next_left next_right).
 - apply (List.nth_error_In x0_expected_nodes 146). vm_compute. reflexivity.
 - intro site. cbn [x0_concrete_expr_440 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E437.
   rewrite E439.
   reflexivity.
 - intros site value Eval.
   destruct (x0_uint_result_440 invalid site flat_memories left value H437 H439 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Theorem exception_node_441_congruent invalid left right next_left next_right :
 (exists width bits, VM.find 290 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 440 left = Some (Gval (Fuint width) bits)) ->
 VM.find 290 left = VM.find 290 right ->
 VM.find 440 left = VM.find 440 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 441 next_left = VM.find 441 next_right.
Proof.
 intros H290 H440 E290 E440 L R.
 apply (x0_selected_uint_node_congruent 441 x0_concrete_expr_441 invalid left right next_left next_right).
 - apply (List.nth_error_In x0_expected_nodes 147). vm_compute. reflexivity.
 - intro site. cbn [x0_concrete_expr_441 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E290.
   rewrite E440.
   reflexivity.
 - intros site value Eval.
   destruct (x0_uint_result_441 invalid site flat_memories left value H290 H440 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Theorem exception_node_442_congruent invalid left right next_left next_right :
 (exists width bits, VM.find 295 left = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 441 left = Some (Gval (Fuint width) bits)) ->
 VM.find 295 left = VM.find 295 right ->
 VM.find 441 left = VM.find 441 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 442 next_left = VM.find 442 next_right.
Proof.
 intros H295 H441 E295 E441 L R.
 apply (x0_selected_uint_node_congruent 442 x0_concrete_expr_442 invalid left right next_left next_right).
 - apply (List.nth_error_In x0_expected_nodes 148). vm_compute. reflexivity.
 - intro site. cbn [x0_concrete_expr_442 eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
   rewrite E295.
   rewrite E441.
   reflexivity.
 - intros site value Eval.
   destruct (x0_uint_result_442 invalid site flat_memories left value H295 H441 Eval) as [width [bits Value]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Print Assumptions exception_node_442_congruent.
