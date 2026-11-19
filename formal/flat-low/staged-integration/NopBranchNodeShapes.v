Require Import NopBranchShapes CoreSocModel ComparisonNodes FormalTypedNodeEquation SelectedNodeSafety FormalSuccessfulNodeEvaluation JointUpdateNodePositions JointUpdateExpressionCertificates NormalizedBit.
From Coq Require Import ZArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Theorem nop_branch_shape_1363 invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value, VM.find 1363 result = Some value /\ normalized_bit value.
Proof.
 intro Step. eapply (nop_branch_node_shape 1363 joint_update_expr_1363 _ invalid old current result).
 - apply (List.nth_error_In joint_update_expected_nodes 851%nat). vm_compute. reflexivity.
 - intros site value Eval.
   cbn [joint_update_expr_1363 eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
   destruct (VM.find 1362 old) as [source|]; [|discriminate Eval].
   eapply nop_branch_reduction_or_normalized;exact Eval.
 - exact nop_branch_normalized_type.
 - exact Step.
Qed.
Theorem nop_branch_shape_1364 invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value, VM.find 1364 result = Some value /\ normalized_bit value.
Proof.
 intro Step. eapply (nop_branch_node_shape 1364 joint_update_expr_1364 _ invalid old current result).
 - apply (List.nth_error_In joint_update_expected_nodes 852%nat). vm_compute. reflexivity.
 - intros site value Eval.
   cbn [joint_update_expr_1364 eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
   destruct (VM.find 1363 old) as [source|]; [|discriminate Eval].
   eapply nop_branch_comparison_false_normalized;exact Eval.
 - exact nop_branch_normalized_type.
 - exact Step.
Qed.
Theorem nop_branch_shape_1374 invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value, VM.find 1374 result = Some value /\ normalized_bit value.
Proof.
 intro Step. eapply (nop_branch_node_shape 1374 joint_update_expr_1374 _ invalid old current result).
 - apply (List.nth_error_In joint_update_expected_nodes 862%nat). vm_compute. reflexivity.
 - intros site value Eval.
   cbn [joint_update_expr_1374 eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
   destruct (VM.find 1370 old) as [source|]; [|discriminate Eval].
   eapply nop_branch_comparison_false_normalized;exact Eval.
 - exact nop_branch_normalized_type.
 - exact Step.
Qed.
Theorem nop_branch_shape_1375 invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value, VM.find 1375 result = Some value /\ normalized_bit value.
Proof.
 intro Step. eapply (nop_branch_node_shape 1375 joint_update_expr_1375 _ invalid old current result).
 - apply (List.nth_error_In joint_update_expected_nodes 863%nat). vm_compute. reflexivity.
 - intros site value Eval.
   cbn [joint_update_expr_1375 eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
   destruct (VM.find 1373 old) as [source|]; [|discriminate Eval].
   eapply nop_branch_comparison_false_normalized;exact Eval.
 - exact nop_branch_normalized_type.
 - exact Step.
Qed.
Theorem nop_branch_shape_1368 invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value, VM.find 1368 result = Some value /\ (fun value => type_of_val value = Gtyp (Fuint 1)) value.
Proof.
 intro Step. eapply (nop_branch_node_shape 1368 joint_update_expr_1368 _ invalid old current result).
 - apply (List.nth_error_In joint_update_expected_nodes 856%nat). vm_compute. reflexivity.
 - intros site value Eval.
   cbn [joint_update_expr_1368 eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
   destruct (VM.find 1362 old) as [source|]; [|discriminate Eval].
   exact (nop_branch_extract_result_type 31 31 source value Eval).
 - intros value Typed; exact Typed.
 - exact Step.
Qed.
Theorem nop_branch_shape_1369 invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value, VM.find 1369 result = Some value /\ (fun value => type_of_val value = Gtyp (Fuint 1)) value.
Proof.
 intro Step. eapply (nop_branch_node_shape 1369 joint_update_expr_1369 _ invalid old current result).
 - apply (List.nth_error_In joint_update_expected_nodes 857%nat). vm_compute. reflexivity.
 - intros site value Eval.
   cbn [joint_update_expr_1369 eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
   destruct (VM.find 1357 old) as [source|]; [|discriminate Eval].
   exact (nop_branch_extract_result_type 31 31 source value Eval).
 - intros value Typed; exact Typed.
 - exact Step.
Qed.
Theorem nop_branch_shape_1371 invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value, VM.find 1371 result = Some value /\ (fun value => type_of_val value = Gtyp (Fuint 1)) value.
Proof.
 intro Step. eapply (nop_branch_node_shape 1371 joint_update_expr_1371 _ invalid old current result).
 - apply (List.nth_error_In joint_update_expected_nodes 859%nat). vm_compute. reflexivity.
 - intros site value Eval.
   cbn [joint_update_expr_1371 eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
   destruct (VM.find 1362 old) as [source|]; [|discriminate Eval].
   exact (nop_branch_extract_result_type 31 31 source value Eval).
 - intros value Typed; exact Typed.
 - exact Step.
Qed.
Theorem nop_branch_shape_1372 invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value, VM.find 1372 result = Some value /\ (fun value => type_of_val value = Gtyp (Fuint 1)) value.
Proof.
 intro Step. eapply (nop_branch_node_shape 1372 joint_update_expr_1372 _ invalid old current result).
 - apply (List.nth_error_In joint_update_expected_nodes 860%nat). vm_compute. reflexivity.
 - intros site value Eval.
   cbn [joint_update_expr_1372 eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
   destruct (VM.find 1358 old) as [source|]; [|discriminate Eval].
   exact (nop_branch_extract_result_type 31 31 source value Eval).
 - intros value Typed; exact Typed.
 - exact Step.
Qed.
Theorem nop_branch_shape_1370 invalid s0 s1 s2 :
 formal_value_iter invalid flat_memories s0 false s0 flat_statements = Some s1 ->
 formal_value_iter invalid flat_memories s1 false s1 flat_statements = Some s2 ->
 exists value, VM.find 1370 s2 = Some value /\ normalized_bit value.
Proof.
 intros Step1 Step2.
 destruct (nop_branch_shape_1368 invalid s0 s0 s1 Step1) as [left [Left LeftType]].
 destruct (nop_branch_shape_1369 invalid s0 s0 s1 Step1) as [right [Right RightType]].
 eapply (nop_branch_node_shape 1370 joint_update_expr_1370 _ invalid s1 s1 s2).
 - apply (List.nth_error_In joint_update_expected_nodes 858%nat). vm_compute. reflexivity.
 - intros site value Eval.
   change (eval_hfexpr_with_memory flat_memories joint_update_expr_1370 s1 s1 = Some value) in Eval.
   exact (nop_branch_mux_normalized flat_memories s1 (@Eref VarOrder.T (@Eid VarOrder.T 1367)) 1368 1369 left right value Left LeftType Right RightType Eval).
 - exact nop_branch_normalized_type.
 - exact Step2.
Qed.
Theorem nop_branch_shape_1373 invalid s0 s1 s2 :
 formal_value_iter invalid flat_memories s0 false s0 flat_statements = Some s1 ->
 formal_value_iter invalid flat_memories s1 false s1 flat_statements = Some s2 ->
 exists value, VM.find 1373 s2 = Some value /\ normalized_bit value.
Proof.
 intros Step1 Step2.
 destruct (nop_branch_shape_1371 invalid s0 s0 s1 Step1) as [left [Left LeftType]].
 destruct (nop_branch_shape_1372 invalid s0 s0 s1 Step1) as [right [Right RightType]].
 eapply (nop_branch_node_shape 1373 joint_update_expr_1373 _ invalid s1 s1 s2).
 - apply (List.nth_error_In joint_update_expected_nodes 861%nat). vm_compute. reflexivity.
 - intros site value Eval.
   change (eval_hfexpr_with_memory flat_memories joint_update_expr_1373 s1 s1 = Some value) in Eval.
   exact (nop_branch_mux_normalized flat_memories s1 (@Eref VarOrder.T (@Eid VarOrder.T 1367)) 1371 1372 left right value Left LeftType Right RightType Eval).
 - exact nop_branch_normalized_type.
 - exact Step2.
Qed.
