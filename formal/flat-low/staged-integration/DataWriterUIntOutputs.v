Require Import CoreSocModel ComparisonNodes DataWriterExpressionCertificates DataWriterNodePositions SelectedNodeConcreteOutput ConcreteGroundOrUInt ConcreteExtractNode ConcreteGroundConditionValidIf ConcreteUIntOperations ConcreteUIntScalarExpressions ConcreteScalarExpressions.
From Coq Require Import ZArith List.
From mathcomp Require Import ssreflect ssrbool ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From nbits Require Import NBits.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Lemma writer_uint_result_9214 inputs path site mm old result :
 (exists ground bits, VM.find 9206 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 9213 old = Some (Gval ground bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm writer_expr_9214 old old = Some result -> concrete_uint_value result.
Proof.
 intros [g9206 [b9206 H9206]].
 intros [g9213 [b9213 H9213]].
 intro Eval. unfold writer_expr_9214 in Eval. cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H9206 ?H9213 in Eval.
 eapply ground_or_uint; exact Eval.
Qed.
Theorem data_writer_uint_output_9214 inputs path old current result :
 (exists ground bits, VM.find 9206 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 9213 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists width bits, VM.find 9214 result = Some (Gval (Fuint width) bits).
Proof.
 intros H9206 H9213 Step.
 eapply (selected_node_concrete_output data_writer_node_offsets flat_statements data_writer_expected_nodes 9214 writer_expr_9214 inputs path flat_memories old current result).
 - exact data_writer_node_positions.
 - exact data_writer_node_safety.
 - apply (@List.nth_error_In _ data_writer_expected_nodes 143 (9214,writer_expr_9214)). vm_compute. reflexivity.
 - apply writer_ready_9214; assumption.
 - intros location value Eval.
   destruct (writer_uint_result_9214 inputs path location flat_memories old value H9206 H9213 Eval) as [w [b Value]].
   subst value. exists w. reflexivity.
 - exact Step.
Qed.
Lemma writer_uint_result_9224 inputs path site mm old result :
 (exists ground bits, VM.find 9182 old = Some (Gval ground bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm writer_expr_9224 old old = Some result -> concrete_uint_value result.
Proof.
 intros [g9182 [b9182 H9182]].
 intro Eval. unfold writer_expr_9224 in Eval. cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H9182 in Eval.
 destruct g9182; cbn [eval_unop] in Eval; try discriminate Eval;
 repeat match type of Eval with context [if ?c then _ else _] => destruct c end;
 try discriminate Eval; inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Theorem data_writer_uint_output_9224 inputs path old current result :
 (exists ground bits, VM.find 9182 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists width bits, VM.find 9224 result = Some (Gval (Fuint width) bits).
Proof.
 intros H9182 Step.
 eapply (selected_node_concrete_output data_writer_node_offsets flat_statements data_writer_expected_nodes 9224 writer_expr_9224 inputs path flat_memories old current result).
 - exact data_writer_node_positions.
 - exact data_writer_node_safety.
 - apply (@List.nth_error_In _ data_writer_expected_nodes 145 (9224,writer_expr_9224)). vm_compute. reflexivity.
 - apply writer_ready_9224; assumption.
 - intros location value Eval.
   destruct (writer_uint_result_9224 inputs path location flat_memories old value H9182 Eval) as [w [b Value]].
   subst value. exists w. reflexivity.
 - exact Step.
Qed.
Lemma writer_uint_result_9225 inputs path site mm old result :
 (exists ground bits, VM.find 9223 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 9224 old = Some (Gval (Fuint ground) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm writer_expr_9225 old old = Some result -> concrete_uint_value result.
Proof.
 intros [g9223 [b9223 H9223]].
 intros [g9224 [b9224 H9224]].
 unfold writer_expr_9225. eapply formal_ground_condition_uint_validif with (width := g9224).
 - eapply scalar_ready_ref; eassumption.
 - eapply uint_ready_ref; eassumption.
 - unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref]. rewrite H9224. reflexivity.
Qed.
Theorem data_writer_uint_output_9225 inputs path old current result :
 (exists ground bits, VM.find 9223 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 9224 old = Some (Gval (Fuint ground) bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists width bits, VM.find 9225 result = Some (Gval (Fuint width) bits).
Proof.
 intros H9223 H9224 Step.
 eapply (selected_node_concrete_output data_writer_node_offsets flat_statements data_writer_expected_nodes 9225 writer_expr_9225 inputs path flat_memories old current result).
 - exact data_writer_node_positions.
 - exact data_writer_node_safety.
 - apply (@List.nth_error_In _ data_writer_expected_nodes 146 (9225,writer_expr_9225)). vm_compute. reflexivity.
 - apply writer_ready_9225; assumption.
 - intros location value Eval.
   destruct (writer_uint_result_9225 inputs path location flat_memories old value H9223 H9224 Eval) as [w [b Value]].
   subst value. exists w. reflexivity.
 - exact Step.
Qed.
Lemma writer_uint_result_9227 inputs path site mm old result :
 (exists ground bits, VM.find 9223 old = Some (Gval ground bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm writer_expr_9227 old old = Some result -> concrete_uint_value result.
Proof.
 intros [g9223 [b9223 H9223]].
 intro Eval. unfold writer_expr_9227 in Eval. cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H9223 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H9223 in Eval.
 destruct g9223;
 cbn [validif_policy_result type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 repeat match type of Eval with context [if ?c then _ else _] => destruct c; cbn in Eval end;
 try discriminate Eval; inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Theorem data_writer_uint_output_9227 inputs path old current result :
 (exists ground bits, VM.find 9223 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists width bits, VM.find 9227 result = Some (Gval (Fuint width) bits).
Proof.
 intros H9223 Step.
 eapply (selected_node_concrete_output data_writer_node_offsets flat_statements data_writer_expected_nodes 9227 writer_expr_9227 inputs path flat_memories old current result).
 - exact data_writer_node_positions.
 - exact data_writer_node_safety.
 - apply (@List.nth_error_In _ data_writer_expected_nodes 147 (9227,writer_expr_9227)). vm_compute. reflexivity.
 - apply writer_ready_9227; assumption.
 - intros location value Eval.
   destruct (writer_uint_result_9227 inputs path location flat_memories old value H9223 Eval) as [w [b Value]].
   subst value. exists w. reflexivity.
 - exact Step.
Qed.
Lemma writer_uint_result_9228 inputs path site mm old result :
 (exists ground bits, VM.find 9223 old = Some (Gval ground bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm writer_expr_9228 old old = Some result -> concrete_uint_value result.
Proof.
 intros [g9223 [b9223 H9223]].
 unfold writer_expr_9228. eapply formal_ground_condition_uint_validif with (width := 1%nat).
 - eapply scalar_ready_ref; eassumption.
 - apply uint_ready_const.
 - unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref]. reflexivity.
Qed.
Theorem data_writer_uint_output_9228 inputs path old current result :
 (exists ground bits, VM.find 9223 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists width bits, VM.find 9228 result = Some (Gval (Fuint width) bits).
Proof.
 intros H9223 Step.
 eapply (selected_node_concrete_output data_writer_node_offsets flat_statements data_writer_expected_nodes 9228 writer_expr_9228 inputs path flat_memories old current result).
 - exact data_writer_node_positions.
 - exact data_writer_node_safety.
 - apply (@List.nth_error_In _ data_writer_expected_nodes 148 (9228,writer_expr_9228)). vm_compute. reflexivity.
 - apply writer_ready_9228; assumption.
 - intros location value Eval.
   destruct (writer_uint_result_9228 inputs path location flat_memories old value H9223 Eval) as [w [b Value]].
   subst value. exists w. reflexivity.
 - exact Step.
Qed.
Lemma writer_uint_result_9229 inputs path site mm old result :
 (exists ground bits, VM.find 9214 old = Some (Gval (Fuint ground) bits)) ->
 (exists ground bits, VM.find 9223 old = Some (Gval ground bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm writer_expr_9229 old old = Some result -> concrete_uint_value result.
Proof.
 intros [g9214 [b9214 H9214]].
 intros [g9223 [b9223 H9223]].
 unfold writer_expr_9229. eapply formal_ground_condition_uint_validif with (width := g9214).
 - eapply scalar_ready_ref; eassumption.
 - eapply uint_ready_ref; eassumption.
 - unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref]. rewrite H9214. reflexivity.
Qed.
Theorem data_writer_uint_output_9229 inputs path old current result :
 (exists ground bits, VM.find 9214 old = Some (Gval (Fuint ground) bits)) ->
 (exists ground bits, VM.find 9223 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists width bits, VM.find 9229 result = Some (Gval (Fuint width) bits).
Proof.
 intros H9214 H9223 Step.
 eapply (selected_node_concrete_output data_writer_node_offsets flat_statements data_writer_expected_nodes 9229 writer_expr_9229 inputs path flat_memories old current result).
 - exact data_writer_node_positions.
 - exact data_writer_node_safety.
 - apply (@List.nth_error_In _ data_writer_expected_nodes 149 (9229,writer_expr_9229)). vm_compute. reflexivity.
 - apply writer_ready_9229; assumption.
 - intros location value Eval.
   destruct (writer_uint_result_9229 inputs path location flat_memories old value H9214 H9223 Eval) as [w [b Value]].
   subst value. exists w. reflexivity.
 - exact Step.
Qed.
Lemma writer_uint_result_9230 inputs path site mm old result :
 (exists ground bits, VM.find 36 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 9225 old = Some (Gval (Fuint ground) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm writer_expr_9230 old old = Some result -> concrete_uint_value result.
Proof.
 intros [g36 [b36 H36]].
 intros [g9225 [b9225 H9225]].
 unfold writer_expr_9230. eapply formal_ground_condition_uint_validif with (width := g9225).
 - eapply scalar_ready_ref; eassumption.
 - eapply uint_ready_ref; eassumption.
 - unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref]. rewrite H9225. reflexivity.
Qed.
Theorem data_writer_uint_output_9230 inputs path old current result :
 (exists ground bits, VM.find 36 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 9225 old = Some (Gval (Fuint ground) bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists width bits, VM.find 9230 result = Some (Gval (Fuint width) bits).
Proof.
 intros H36 H9225 Step.
 eapply (selected_node_concrete_output data_writer_node_offsets flat_statements data_writer_expected_nodes 9230 writer_expr_9230 inputs path flat_memories old current result).
 - exact data_writer_node_positions.
 - exact data_writer_node_safety.
 - apply (@List.nth_error_In _ data_writer_expected_nodes 150 (9230,writer_expr_9230)). vm_compute. reflexivity.
 - apply writer_ready_9230; assumption.
 - intros location value Eval.
   destruct (writer_uint_result_9230 inputs path location flat_memories old value H36 H9225 Eval) as [w [b Value]].
   subst value. exists w. reflexivity.
 - exact Step.
Qed.
Lemma writer_uint_result_9232 inputs path site mm old result :
 (exists ground bits, VM.find 36 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 9227 old = Some (Gval ground bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm writer_expr_9232 old old = Some result -> concrete_uint_value result.
Proof.
 intros [g36 [b36 H36]].
 intros [g9227 [b9227 H9227]].
 intro Eval. unfold writer_expr_9232 in Eval. cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H36 ?H9227 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H36 ?H9227 in Eval.
 destruct g36; destruct g9227;
 cbn [validif_policy_result type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 repeat match type of Eval with context [if ?c then _ else _] => destruct c; cbn in Eval end;
 try discriminate Eval; inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Theorem data_writer_uint_output_9232 inputs path old current result :
 (exists ground bits, VM.find 36 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 9227 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists width bits, VM.find 9232 result = Some (Gval (Fuint width) bits).
Proof.
 intros H36 H9227 Step.
 eapply (selected_node_concrete_output data_writer_node_offsets flat_statements data_writer_expected_nodes 9232 writer_expr_9232 inputs path flat_memories old current result).
 - exact data_writer_node_positions.
 - exact data_writer_node_safety.
 - apply (@List.nth_error_In _ data_writer_expected_nodes 151 (9232,writer_expr_9232)). vm_compute. reflexivity.
 - apply writer_ready_9232; assumption.
 - intros location value Eval.
   destruct (writer_uint_result_9232 inputs path location flat_memories old value H36 H9227 Eval) as [w [b Value]].
   subst value. exists w. reflexivity.
 - exact Step.
Qed.
Lemma writer_uint_result_9233 inputs path site mm old result :
 (exists ground bits, VM.find 36 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 9228 old = Some (Gval (Fuint ground) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm writer_expr_9233 old old = Some result -> concrete_uint_value result.
Proof.
 intros [g36 [b36 H36]].
 intros [g9228 [b9228 H9228]].
 unfold writer_expr_9233. eapply formal_ground_condition_uint_validif with (width := g9228).
 - eapply scalar_ready_ref; eassumption.
 - eapply uint_ready_ref; eassumption.
 - unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref]. rewrite H9228. reflexivity.
Qed.
Theorem data_writer_uint_output_9233 inputs path old current result :
 (exists ground bits, VM.find 36 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 9228 old = Some (Gval (Fuint ground) bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists width bits, VM.find 9233 result = Some (Gval (Fuint width) bits).
Proof.
 intros H36 H9228 Step.
 eapply (selected_node_concrete_output data_writer_node_offsets flat_statements data_writer_expected_nodes 9233 writer_expr_9233 inputs path flat_memories old current result).
 - exact data_writer_node_positions.
 - exact data_writer_node_safety.
 - apply (@List.nth_error_In _ data_writer_expected_nodes 152 (9233,writer_expr_9233)). vm_compute. reflexivity.
 - apply writer_ready_9233; assumption.
 - intros location value Eval.
   destruct (writer_uint_result_9233 inputs path location flat_memories old value H36 H9228 Eval) as [w [b Value]].
   subst value. exists w. reflexivity.
 - exact Step.
Qed.
Lemma writer_uint_result_9234 inputs path site mm old result :
 (exists ground bits, VM.find 36 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 9229 old = Some (Gval (Fuint ground) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm writer_expr_9234 old old = Some result -> concrete_uint_value result.
Proof.
 intros [g36 [b36 H36]].
 intros [g9229 [b9229 H9229]].
 unfold writer_expr_9234. eapply formal_ground_condition_uint_validif with (width := g9229).
 - eapply scalar_ready_ref; eassumption.
 - eapply uint_ready_ref; eassumption.
 - unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref]. rewrite H9229. reflexivity.
Qed.
Theorem data_writer_uint_output_9234 inputs path old current result :
 (exists ground bits, VM.find 36 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 9229 old = Some (Gval (Fuint ground) bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists width bits, VM.find 9234 result = Some (Gval (Fuint width) bits).
Proof.
 intros H36 H9229 Step.
 eapply (selected_node_concrete_output data_writer_node_offsets flat_statements data_writer_expected_nodes 9234 writer_expr_9234 inputs path flat_memories old current result).
 - exact data_writer_node_positions.
 - exact data_writer_node_safety.
 - apply (@List.nth_error_In _ data_writer_expected_nodes 153 (9234,writer_expr_9234)). vm_compute. reflexivity.
 - apply writer_ready_9234; assumption.
 - intros location value Eval.
   destruct (writer_uint_result_9234 inputs path location flat_memories old value H36 H9229 Eval) as [w [b Value]].
   subst value. exists w. reflexivity.
 - exact Step.
Qed.
Print Assumptions data_writer_uint_output_9234.
