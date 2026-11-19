Require Import CoreSocModel ComparisonNodes ComparisonTruth FormalComparisonNodes.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From nbits Require Import NBits.
From firrtl Require Import Env_with_implicit_widths Firrtl_with_implicit_widths
 HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Lemma assertion_0_from_enabled_agreement invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 (generated_expr_true (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 7567))) (@Econst VarOrder.T (Fuint 1) [::true])) result -> comparison_inputs_agree old 1474 1519) ->
 generated_assert_m0_0_local result.
Proof.
 intros Step Agree. unfold generated_assert_m0_0_local. intro Enabled.
 apply known_true_node.
 rewrite (formal_comparison_0_iteration invalid old current result Step).
 apply agreeing_ref_comparison. exact (Agree Enabled).
Qed.
Lemma assertion_1_from_enabled_agreement invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 (generated_expr_true (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 7569))) (@Eref VarOrder.T (@Eid VarOrder.T 7572))) (@Econst VarOrder.T (Fuint 1) [::true])) result -> comparison_inputs_agree old 1475 1520) ->
 generated_assert_m0_1_local result.
Proof.
 intros Step Agree. unfold generated_assert_m0_1_local. intro Enabled.
 apply known_true_node.
 rewrite (formal_comparison_1_iteration invalid old current result Step).
 apply agreeing_ref_comparison. exact (Agree Enabled).
Qed.
Lemma assertion_2_from_enabled_agreement invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 (generated_expr_true (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 7569))) (@Eref VarOrder.T (@Eid VarOrder.T 7576))) (@Econst VarOrder.T (Fuint 1) [::true])) result -> comparison_inputs_agree old 1476 1521) ->
 generated_assert_m0_2_local result.
Proof.
 intros Step Agree. unfold generated_assert_m0_2_local. intro Enabled.
 apply known_true_node.
 rewrite (formal_comparison_2_iteration invalid old current result Step).
 apply agreeing_ref_comparison. exact (Agree Enabled).
Qed.
Lemma assertion_3_from_enabled_agreement invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 (generated_expr_true (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 7580))) (@Econst VarOrder.T (Fuint 1) [::true])) result -> comparison_inputs_agree old 1478 1523) ->
 generated_assert_m0_3_local result.
Proof.
 intros Step Agree. unfold generated_assert_m0_3_local. intro Enabled.
 apply known_true_node.
 rewrite (formal_comparison_3_iteration invalid old current result Step).
 apply agreeing_ref_comparison. exact (Agree Enabled).
Qed.
Lemma assertion_4_from_enabled_agreement invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 (generated_expr_true (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 7582))) (@Eref VarOrder.T (@Eid VarOrder.T 7585))) (@Econst VarOrder.T (Fuint 1) [::true])) result -> comparison_inputs_agree old 1479 1524) ->
 generated_assert_m0_4_local result.
Proof.
 intros Step Agree. unfold generated_assert_m0_4_local. intro Enabled.
 apply known_true_node.
 rewrite (formal_comparison_4_iteration invalid old current result Step).
 apply agreeing_ref_comparison. exact (Agree Enabled).
Qed.
Lemma assertion_5_from_enabled_agreement invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 (generated_expr_true (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 7582))) (@Eref VarOrder.T (@Eid VarOrder.T 7589))) (@Econst VarOrder.T (Fuint 1) [::true])) result -> comparison_inputs_agree old 1481 1526) ->
 generated_assert_m0_5_local result.
Proof.
 intros Step Agree. unfold generated_assert_m0_5_local. intro Enabled.
 apply known_true_node.
 rewrite (formal_comparison_5_iteration invalid old current result Step).
 apply agreeing_ref_comparison. exact (Agree Enabled).
Qed.
Lemma assertion_6_from_enabled_agreement invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 (generated_expr_true (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 7582))) (@Eref VarOrder.T (@Eid VarOrder.T 7593))) (@Econst VarOrder.T (Fuint 1) [::true])) result -> comparison_inputs_agree old 1480 1525) ->
 generated_assert_m0_6_local result.
Proof.
 intros Step Agree. unfold generated_assert_m0_6_local. intro Enabled.
 apply known_true_node.
 rewrite (formal_comparison_6_iteration invalid old current result Step).
 apply agreeing_ref_comparison. exact (Agree Enabled).
Qed.
Lemma assertion_7_from_enabled_agreement invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 (generated_expr_true (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 1395))) (@Eref VarOrder.T (@Eid VarOrder.T 7597))) (@Econst VarOrder.T (Fuint 1) [::true])) result -> comparison_inputs_agree old 1397 1559) ->
 generated_assert_m0_7_local result.
Proof.
 intros Step Agree. unfold generated_assert_m0_7_local. intro Enabled.
 apply known_true_node.
 rewrite (formal_comparison_7_iteration invalid old current result Step).
 apply agreeing_ref_comparison. exact (Agree Enabled).
Qed.
Lemma assertion_8_from_enabled_agreement invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 (generated_expr_true (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 1395))) (@Eref VarOrder.T (@Eid VarOrder.T 7601))) (@Econst VarOrder.T (Fuint 1) [::true])) result -> comparison_inputs_agree old 1399 1597) ->
 generated_assert_m0_8_local result.
Proof.
 intros Step Agree. unfold generated_assert_m0_8_local. intro Enabled.
 apply known_true_node.
 rewrite (formal_comparison_8_iteration invalid old current result Step).
 apply agreeing_ref_comparison. exact (Agree Enabled).
Qed.
Lemma assertion_9_from_enabled_agreement invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 (generated_expr_true (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 1395))) (@Eref VarOrder.T (@Eid VarOrder.T 7605))) (@Econst VarOrder.T (Fuint 1) [::true])) result -> comparison_inputs_agree old 1400 1598) ->
 generated_assert_m0_9_local result.
Proof.
 intros Step Agree. unfold generated_assert_m0_9_local. intro Enabled.
 apply known_true_node.
 rewrite (formal_comparison_9_iteration invalid old current result Step).
 apply agreeing_ref_comparison. exact (Agree Enabled).
Qed.
Lemma assertion_10_from_enabled_agreement invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 (generated_expr_true (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 1395))) (@Eref VarOrder.T (@Eid VarOrder.T 7609))) (@Econst VarOrder.T (Fuint 1) [::true])) result -> comparison_inputs_agree old 1401 1599) ->
 generated_assert_m0_10_local result.
Proof.
 intros Step Agree. unfold generated_assert_m0_10_local. intro Enabled.
 apply known_true_node.
 rewrite (formal_comparison_10_iteration invalid old current result Step).
 apply agreeing_ref_comparison. exact (Agree Enabled).
Qed.
Lemma assertion_11_from_enabled_agreement invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 (generated_expr_true (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 1395))) (@Eref VarOrder.T (@Eid VarOrder.T 7613))) (@Econst VarOrder.T (Fuint 1) [::true])) result -> comparison_inputs_agree old 1402 1600) ->
 generated_assert_m0_11_local result.
Proof.
 intros Step Agree. unfold generated_assert_m0_11_local. intro Enabled.
 apply known_true_node.
 rewrite (formal_comparison_11_iteration invalid old current result Step).
 apply agreeing_ref_comparison. exact (Agree Enabled).
Qed.
Lemma assertion_12_from_enabled_agreement invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 (generated_expr_true (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 1395))) (@Eref VarOrder.T (@Eid VarOrder.T 7617))) (@Econst VarOrder.T (Fuint 1) [::true])) result -> comparison_inputs_agree old 1403 1601) ->
 generated_assert_m0_12_local result.
Proof.
 intros Step Agree. unfold generated_assert_m0_12_local. intro Enabled.
 apply known_true_node.
 rewrite (formal_comparison_12_iteration invalid old current result Step).
 apply agreeing_ref_comparison. exact (Agree Enabled).
Qed.
Lemma assertion_13_from_enabled_agreement invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 (generated_expr_true (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 1395))) (@Eref VarOrder.T (@Eid VarOrder.T 7621))) (@Econst VarOrder.T (Fuint 1) [::true])) result -> comparison_inputs_agree old 1404 1602) ->
 generated_assert_m0_13_local result.
Proof.
 intros Step Agree. unfold generated_assert_m0_13_local. intro Enabled.
 apply known_true_node.
 rewrite (formal_comparison_13_iteration invalid old current result Step).
 apply agreeing_ref_comparison. exact (Agree Enabled).
Qed.
Lemma assertion_14_from_enabled_agreement invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 (generated_expr_true (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 1395))) (@Eref VarOrder.T (@Eid VarOrder.T 7625))) (@Econst VarOrder.T (Fuint 1) [::true])) result -> comparison_inputs_agree old 1405 1603) ->
 generated_assert_m0_14_local result.
Proof.
 intros Step Agree. unfold generated_assert_m0_14_local. intro Enabled.
 apply known_true_node.
 rewrite (formal_comparison_14_iteration invalid old current result Step).
 apply agreeing_ref_comparison. exact (Agree Enabled).
Qed.
Lemma assertion_15_from_enabled_agreement invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 (generated_expr_true (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 1395))) (@Eref VarOrder.T (@Eid VarOrder.T 7629))) (@Econst VarOrder.T (Fuint 1) [::true])) result -> comparison_inputs_agree old 1406 1604) ->
 generated_assert_m0_15_local result.
Proof.
 intros Step Agree. unfold generated_assert_m0_15_local. intro Enabled.
 apply known_true_node.
 rewrite (formal_comparison_15_iteration invalid old current result Step).
 apply agreeing_ref_comparison. exact (Agree Enabled).
Qed.
Lemma assertion_16_from_enabled_agreement invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 (generated_expr_true (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 1395))) (@Eref VarOrder.T (@Eid VarOrder.T 7633))) (@Econst VarOrder.T (Fuint 1) [::true])) result -> comparison_inputs_agree old 1407 1605) ->
 generated_assert_m0_16_local result.
Proof.
 intros Step Agree. unfold generated_assert_m0_16_local. intro Enabled.
 apply known_true_node.
 rewrite (formal_comparison_16_iteration invalid old current result Step).
 apply agreeing_ref_comparison. exact (Agree Enabled).
Qed.
Lemma assertion_17_from_enabled_agreement invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 (generated_expr_true (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 1395))) (@Eref VarOrder.T (@Eid VarOrder.T 7637))) (@Econst VarOrder.T (Fuint 1) [::true])) result -> comparison_inputs_agree old 1408 1606) ->
 generated_assert_m0_17_local result.
Proof.
 intros Step Agree. unfold generated_assert_m0_17_local. intro Enabled.
 apply known_true_node.
 rewrite (formal_comparison_17_iteration invalid old current result Step).
 apply agreeing_ref_comparison. exact (Agree Enabled).
Qed.
Lemma assertion_18_from_enabled_agreement invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 (generated_expr_true (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 1395))) (@Eref VarOrder.T (@Eid VarOrder.T 7641))) (@Econst VarOrder.T (Fuint 1) [::true])) result -> comparison_inputs_agree old 1409 1607) ->
 generated_assert_m0_18_local result.
Proof.
 intros Step Agree. unfold generated_assert_m0_18_local. intro Enabled.
 apply known_true_node.
 rewrite (formal_comparison_18_iteration invalid old current result Step).
 apply agreeing_ref_comparison. exact (Agree Enabled).
Qed.
Lemma assertion_19_from_enabled_agreement invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 (generated_expr_true (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 1395))) (@Eref VarOrder.T (@Eid VarOrder.T 7645))) (@Econst VarOrder.T (Fuint 1) [::true])) result -> comparison_inputs_agree old 1410 1608) ->
 generated_assert_m0_19_local result.
Proof.
 intros Step Agree. unfold generated_assert_m0_19_local. intro Enabled.
 apply known_true_node.
 rewrite (formal_comparison_19_iteration invalid old current result Step).
 apply agreeing_ref_comparison. exact (Agree Enabled).
Qed.
Lemma assertion_20_from_enabled_agreement invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 (generated_expr_true (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 1395))) (@Eref VarOrder.T (@Eid VarOrder.T 7649))) (@Econst VarOrder.T (Fuint 1) [::true])) result -> comparison_inputs_agree old 1411 1609) ->
 generated_assert_m0_20_local result.
Proof.
 intros Step Agree. unfold generated_assert_m0_20_local. intro Enabled.
 apply known_true_node.
 rewrite (formal_comparison_20_iteration invalid old current result Step).
 apply agreeing_ref_comparison. exact (Agree Enabled).
Qed.
Lemma assertion_21_from_enabled_agreement invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 (generated_expr_true (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 1395))) (@Eref VarOrder.T (@Eid VarOrder.T 7653))) (@Econst VarOrder.T (Fuint 1) [::true])) result -> comparison_inputs_agree old 1412 1610) ->
 generated_assert_m0_21_local result.
Proof.
 intros Step Agree. unfold generated_assert_m0_21_local. intro Enabled.
 apply known_true_node.
 rewrite (formal_comparison_21_iteration invalid old current result Step).
 apply agreeing_ref_comparison. exact (Agree Enabled).
Qed.
Lemma assertion_22_from_enabled_agreement invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 (generated_expr_true (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 1395))) (@Eref VarOrder.T (@Eid VarOrder.T 7657))) (@Econst VarOrder.T (Fuint 1) [::true])) result -> comparison_inputs_agree old 1413 1611) ->
 generated_assert_m0_22_local result.
Proof.
 intros Step Agree. unfold generated_assert_m0_22_local. intro Enabled.
 apply known_true_node.
 rewrite (formal_comparison_22_iteration invalid old current result Step).
 apply agreeing_ref_comparison. exact (Agree Enabled).
Qed.
Lemma assertion_23_from_enabled_agreement invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 (generated_expr_true (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 1395))) (@Eref VarOrder.T (@Eid VarOrder.T 7661))) (@Econst VarOrder.T (Fuint 1) [::true])) result -> comparison_inputs_agree old 1414 1612) ->
 generated_assert_m0_23_local result.
Proof.
 intros Step Agree. unfold generated_assert_m0_23_local. intro Enabled.
 apply known_true_node.
 rewrite (formal_comparison_23_iteration invalid old current result Step).
 apply agreeing_ref_comparison. exact (Agree Enabled).
Qed.
Lemma assertion_24_from_enabled_agreement invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 (generated_expr_true (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 1395))) (@Eref VarOrder.T (@Eid VarOrder.T 7665))) (@Econst VarOrder.T (Fuint 1) [::true])) result -> comparison_inputs_agree old 1415 1613) ->
 generated_assert_m0_24_local result.
Proof.
 intros Step Agree. unfold generated_assert_m0_24_local. intro Enabled.
 apply known_true_node.
 rewrite (formal_comparison_24_iteration invalid old current result Step).
 apply agreeing_ref_comparison. exact (Agree Enabled).
Qed.
Lemma assertion_25_from_enabled_agreement invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 (generated_expr_true (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 1395))) (@Eref VarOrder.T (@Eid VarOrder.T 7669))) (@Econst VarOrder.T (Fuint 1) [::true])) result -> comparison_inputs_agree old 1416 1614) ->
 generated_assert_m0_25_local result.
Proof.
 intros Step Agree. unfold generated_assert_m0_25_local. intro Enabled.
 apply known_true_node.
 rewrite (formal_comparison_25_iteration invalid old current result Step).
 apply agreeing_ref_comparison. exact (Agree Enabled).
Qed.
Lemma assertion_26_from_enabled_agreement invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 (generated_expr_true (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 1395))) (@Eref VarOrder.T (@Eid VarOrder.T 7673))) (@Econst VarOrder.T (Fuint 1) [::true])) result -> comparison_inputs_agree old 1417 1615) ->
 generated_assert_m0_26_local result.
Proof.
 intros Step Agree. unfold generated_assert_m0_26_local. intro Enabled.
 apply known_true_node.
 rewrite (formal_comparison_26_iteration invalid old current result Step).
 apply agreeing_ref_comparison. exact (Agree Enabled).
Qed.
Lemma assertion_27_from_enabled_agreement invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 (generated_expr_true (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 1395))) (@Eref VarOrder.T (@Eid VarOrder.T 7677))) (@Econst VarOrder.T (Fuint 1) [::true])) result -> comparison_inputs_agree old 1418 1616) ->
 generated_assert_m0_27_local result.
Proof.
 intros Step Agree. unfold generated_assert_m0_27_local. intro Enabled.
 apply known_true_node.
 rewrite (formal_comparison_27_iteration invalid old current result Step).
 apply agreeing_ref_comparison. exact (Agree Enabled).
Qed.
Lemma assertion_28_from_enabled_agreement invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 (generated_expr_true (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 1395))) (@Eref VarOrder.T (@Eid VarOrder.T 7681))) (@Econst VarOrder.T (Fuint 1) [::true])) result -> comparison_inputs_agree old 1419 1617) ->
 generated_assert_m0_28_local result.
Proof.
 intros Step Agree. unfold generated_assert_m0_28_local. intro Enabled.
 apply known_true_node.
 rewrite (formal_comparison_28_iteration invalid old current result Step).
 apply agreeing_ref_comparison. exact (Agree Enabled).
Qed.
Lemma assertion_29_from_enabled_agreement invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 (generated_expr_true (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 1395))) (@Eref VarOrder.T (@Eid VarOrder.T 7685))) (@Econst VarOrder.T (Fuint 1) [::true])) result -> comparison_inputs_agree old 1420 1618) ->
 generated_assert_m0_29_local result.
Proof.
 intros Step Agree. unfold generated_assert_m0_29_local. intro Enabled.
 apply known_true_node.
 rewrite (formal_comparison_29_iteration invalid old current result Step).
 apply agreeing_ref_comparison. exact (Agree Enabled).
Qed.
Lemma assertion_30_from_enabled_agreement invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 (generated_expr_true (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 1395))) (@Eref VarOrder.T (@Eid VarOrder.T 7689))) (@Econst VarOrder.T (Fuint 1) [::true])) result -> comparison_inputs_agree old 1421 1619) ->
 generated_assert_m0_30_local result.
Proof.
 intros Step Agree. unfold generated_assert_m0_30_local. intro Enabled.
 apply known_true_node.
 rewrite (formal_comparison_30_iteration invalid old current result Step).
 apply agreeing_ref_comparison. exact (Agree Enabled).
Qed.
Lemma assertion_31_from_enabled_agreement invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 (generated_expr_true (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 1395))) (@Eref VarOrder.T (@Eid VarOrder.T 7693))) (@Econst VarOrder.T (Fuint 1) [::true])) result -> comparison_inputs_agree old 1422 1620) ->
 generated_assert_m0_31_local result.
Proof.
 intros Step Agree. unfold generated_assert_m0_31_local. intro Enabled.
 apply known_true_node.
 rewrite (formal_comparison_31_iteration invalid old current result Step).
 apply agreeing_ref_comparison. exact (Agree Enabled).
Qed.
Lemma assertion_32_from_enabled_agreement invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 (generated_expr_true (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 1395))) (@Eref VarOrder.T (@Eid VarOrder.T 7697))) (@Econst VarOrder.T (Fuint 1) [::true])) result -> comparison_inputs_agree old 1423 1621) ->
 generated_assert_m0_32_local result.
Proof.
 intros Step Agree. unfold generated_assert_m0_32_local. intro Enabled.
 apply known_true_node.
 rewrite (formal_comparison_32_iteration invalid old current result Step).
 apply agreeing_ref_comparison. exact (Agree Enabled).
Qed.
Lemma assertion_33_from_enabled_agreement invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 (generated_expr_true (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 1395))) (@Eref VarOrder.T (@Eid VarOrder.T 7701))) (@Econst VarOrder.T (Fuint 1) [::true])) result -> comparison_inputs_agree old 1424 1622) ->
 generated_assert_m0_33_local result.
Proof.
 intros Step Agree. unfold generated_assert_m0_33_local. intro Enabled.
 apply known_true_node.
 rewrite (formal_comparison_33_iteration invalid old current result Step).
 apply agreeing_ref_comparison. exact (Agree Enabled).
Qed.
Lemma assertion_34_from_enabled_agreement invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 (generated_expr_true (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 1395))) (@Eref VarOrder.T (@Eid VarOrder.T 7705))) (@Econst VarOrder.T (Fuint 1) [::true])) result -> comparison_inputs_agree old 1425 1623) ->
 generated_assert_m0_34_local result.
Proof.
 intros Step Agree. unfold generated_assert_m0_34_local. intro Enabled.
 apply known_true_node.
 rewrite (formal_comparison_34_iteration invalid old current result Step).
 apply agreeing_ref_comparison. exact (Agree Enabled).
Qed.
Lemma assertion_35_from_enabled_agreement invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 (generated_expr_true (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 1395))) (@Eref VarOrder.T (@Eid VarOrder.T 7709))) (@Econst VarOrder.T (Fuint 1) [::true])) result -> comparison_inputs_agree old 1426 1624) ->
 generated_assert_m0_35_local result.
Proof.
 intros Step Agree. unfold generated_assert_m0_35_local. intro Enabled.
 apply known_true_node.
 rewrite (formal_comparison_35_iteration invalid old current result Step).
 apply agreeing_ref_comparison. exact (Agree Enabled).
Qed.
Lemma assertion_36_from_enabled_agreement invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 (generated_expr_true (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 1395))) (@Eref VarOrder.T (@Eid VarOrder.T 7713))) (@Econst VarOrder.T (Fuint 1) [::true])) result -> comparison_inputs_agree old 1427 1625) ->
 generated_assert_m0_36_local result.
Proof.
 intros Step Agree. unfold generated_assert_m0_36_local. intro Enabled.
 apply known_true_node.
 rewrite (formal_comparison_36_iteration invalid old current result Step).
 apply agreeing_ref_comparison. exact (Agree Enabled).
Qed.
Lemma assertion_37_from_enabled_agreement invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 (generated_expr_true (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 1395))) (@Eref VarOrder.T (@Eid VarOrder.T 7717))) (@Econst VarOrder.T (Fuint 1) [::true])) result -> comparison_inputs_agree old 1428 1626) ->
 generated_assert_m0_37_local result.
Proof.
 intros Step Agree. unfold generated_assert_m0_37_local. intro Enabled.
 apply known_true_node.
 rewrite (formal_comparison_37_iteration invalid old current result Step).
 apply agreeing_ref_comparison. exact (Agree Enabled).
Qed.
Lemma assertion_38_from_enabled_agreement invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 (generated_expr_true (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 1395))) (@Eref VarOrder.T (@Eid VarOrder.T 7721))) (@Econst VarOrder.T (Fuint 1) [::true])) result -> comparison_inputs_agree old 1429 1627) ->
 generated_assert_m0_38_local result.
Proof.
 intros Step Agree. unfold generated_assert_m0_38_local. intro Enabled.
 apply known_true_node.
 rewrite (formal_comparison_38_iteration invalid old current result Step).
 apply agreeing_ref_comparison. exact (Agree Enabled).
Qed.
Lemma assertion_39_from_enabled_agreement invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 (generated_expr_true (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 1395))) (@Eref VarOrder.T (@Eid VarOrder.T 7725))) (@Econst VarOrder.T (Fuint 1) [::true])) result -> comparison_inputs_agree old 1430 1628) ->
 generated_assert_m0_39_local result.
Proof.
 intros Step Agree. unfold generated_assert_m0_39_local. intro Enabled.
 apply known_true_node.
 rewrite (formal_comparison_39_iteration invalid old current result Step).
 apply agreeing_ref_comparison. exact (Agree Enabled).
Qed.
Lemma assertion_40_from_enabled_agreement invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 (generated_expr_true (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 7727))) (@Eref VarOrder.T (@Eid VarOrder.T 7730))) (@Econst VarOrder.T (Fuint 1) [::true])) result -> comparison_inputs_agree old 1469 1667) ->
 generated_assert_m0_40_local result.
Proof.
 intros Step Agree. unfold generated_assert_m0_40_local. intro Enabled.
 apply known_true_node.
 rewrite (formal_comparison_40_iteration invalid old current result Step).
 apply agreeing_ref_comparison. exact (Agree Enabled).
Qed.
Lemma assertion_41_from_enabled_agreement invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 (generated_expr_true (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 7727))) (@Eref VarOrder.T (@Eid VarOrder.T 7734))) (@Econst VarOrder.T (Fuint 1) [::true])) result -> comparison_inputs_agree old 1470 1668) ->
 generated_assert_m0_41_local result.
Proof.
 intros Step Agree. unfold generated_assert_m0_41_local. intro Enabled.
 apply known_true_node.
 rewrite (formal_comparison_41_iteration invalid old current result Step).
 apply agreeing_ref_comparison. exact (Agree Enabled).
Qed.
Lemma assertion_42_from_enabled_agreement invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 (generated_expr_true (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 7727))) (@Eref VarOrder.T (@Eid VarOrder.T 7738))) (@Econst VarOrder.T (Fuint 1) [::true])) result -> comparison_inputs_agree old 1471 1669) ->
 generated_assert_m0_42_local result.
Proof.
 intros Step Agree. unfold generated_assert_m0_42_local. intro Enabled.
 apply known_true_node.
 rewrite (formal_comparison_42_iteration invalid old current result Step).
 apply agreeing_ref_comparison. exact (Agree Enabled).
Qed.
Lemma assertion_43_from_enabled_agreement invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 (generated_expr_true (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 7727))) (@Eref VarOrder.T (@Eid VarOrder.T 7742))) (@Econst VarOrder.T (Fuint 1) [::true])) result -> comparison_inputs_agree old 1472 1670) ->
 generated_assert_m0_43_local result.
Proof.
 intros Step Agree. unfold generated_assert_m0_43_local. intro Enabled.
 apply known_true_node.
 rewrite (formal_comparison_43_iteration invalid old current result Step).
 apply agreeing_ref_comparison. exact (Agree Enabled).
Qed.
Lemma assertion_44_from_enabled_agreement invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 (generated_expr_true (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 7727))) (@Eref VarOrder.T (@Eid VarOrder.T 7746))) (@Econst VarOrder.T (Fuint 1) [::true])) result -> comparison_inputs_agree old 1473 1671) ->
 generated_assert_m0_44_local result.
Proof.
 intros Step Agree. unfold generated_assert_m0_44_local. intro Enabled.
 apply known_true_node.
 rewrite (formal_comparison_44_iteration invalid old current result Step).
 apply agreeing_ref_comparison. exact (Agree Enabled).
Qed.
Print Assumptions assertion_44_from_enabled_agreement.
