Require Import UIntResizeRoundtrip RFBooleanMux RFCompareArithmetic ALUOutputTransfer ReferenceRedirectSpine JointUpdateNodePositions JointUpdateExpressionCertificates JointUpdateConnectionCertificates FormalDeclaredConnection CoreSocModel ComparisonNodes.
From Coq Require Import NArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Theorem rf_compare_guards unsigned invalid s0 s1 s2 :
 VM.find 1153 s0=Some(Gval(Fuint 4)[::true;unsigned;true;false]) ->
 formal_value_iter invalid flat_memories s0 false s0 flat_statements=Some s1 ->
 formal_value_iter invalid flat_memories s1 false s1 flat_statements=Some s2 ->
 VM.find 1281 s2=Some(Gval(Fuint 1)[::false]) /\VM.find 1284 s2=Some(Gval(Fuint 1)[::true]).
Proof.
 intros Mode S1 S2.
assert(V1279:VM.find 1279 s1=Some(Gval(Fuint 1)[::false])).
{eapply(reference_redirect_ground_step joint_update_node_offsets joint_update_expected_nodes 1279 joint_update_expr_1279);[exact joint_update_node_positions|exact joint_update_node_safety|apply(List.nth_error_In joint_update_expected_nodes 824%nat);vm_compute;reflexivity| |exact S1].
intro site. cbn[joint_update_expr_1279 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Mode;destruct unsigned;reflexivity. }
assert(V1280:VM.find 1280 s1=Some(Gval(Fuint 1)[::false])).
{eapply(reference_redirect_ground_step joint_update_node_offsets joint_update_expected_nodes 1280 joint_update_expr_1280);[exact joint_update_node_positions|exact joint_update_node_safety|apply(List.nth_error_In joint_update_expected_nodes 825%nat);vm_compute;reflexivity| |exact S1].
intro site. cbn[joint_update_expr_1280 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Mode;destruct unsigned;reflexivity. }
assert(V1282:VM.find 1282 s1=Some(Gval(Fuint 1)[::negb unsigned])).
{eapply(reference_redirect_ground_step joint_update_node_offsets joint_update_expected_nodes 1282 joint_update_expr_1282);[exact joint_update_node_positions|exact joint_update_node_safety|apply(List.nth_error_In joint_update_expected_nodes 827%nat);vm_compute;reflexivity| |exact S1].
intro site. cbn[joint_update_expr_1282 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Mode;destruct unsigned;reflexivity. }
assert(V1283:VM.find 1283 s1=Some(Gval(Fuint 1)[::unsigned])).
{eapply(reference_redirect_ground_step joint_update_node_offsets joint_update_expected_nodes 1283 joint_update_expr_1283);[exact joint_update_node_positions|exact joint_update_node_safety|apply(List.nth_error_In joint_update_expected_nodes 828%nat);vm_compute;reflexivity| |exact S1].
intro site. cbn[joint_update_expr_1283 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Mode;destruct unsigned;reflexivity. }
split.
- eapply(reference_redirect_ground_step joint_update_node_offsets joint_update_expected_nodes 1281 joint_update_expr_1281);[exact joint_update_node_positions|exact joint_update_node_safety|apply(List.nth_error_In joint_update_expected_nodes 826%nat);vm_compute;reflexivity| |exact S2].
intro site. cbn[joint_update_expr_1281 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite V1279 V1280;destruct unsigned;reflexivity.
- eapply(reference_redirect_ground_step joint_update_node_offsets joint_update_expected_nodes 1284 joint_update_expr_1284);[exact joint_update_node_positions|exact joint_update_node_safety|apply(List.nth_error_In joint_update_expected_nodes 829%nat);vm_compute;reflexivity| |exact S2].
intro site. cbn[joint_update_expr_1284 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite V1282 V1283;destruct unsigned;reflexivity.
Qed.
Theorem rf_compare_output_history unsigned invalid s0 s1 s2 s3 s4 s5 bit :
 VM.find 1153 s0=Some(Gval(Fuint 4)[::true;unsigned;true;false]) ->
 VM.find 1153 s1=Some(Gval(Fuint 4)[::true;unsigned;true;false]) ->
 VM.find 1170 s2=Some(Gval(Fuint 1)[::bit]) ->
 formal_value_iter invalid flat_memories s0 false s0 flat_statements=Some s1 ->
 formal_value_iter invalid flat_memories s1 false s1 flat_statements=Some s2 ->
 formal_value_iter invalid flat_memories s2 false s2 flat_statements=Some s3 ->
 formal_value_iter invalid flat_memories s3 false s3 flat_statements=Some s4 ->
 formal_value_iter invalid flat_memories s4 false s4 flat_statements=Some s5 ->
 VM.find 1154 s5=Some(Gval(Fuint 32)(zext_to 32[::bit])).
Proof.
 intros Mode0 Mode1 Bit S1 S2 S3 S4 S5.
 pose proof(proj2(rf_compare_guards unsigned invalid s0 s1 s2 Mode0 S1 S2))as Select.
 pose proof(proj1(rf_compare_guards unsigned invalid s1 s2 s3 Mode1 S2 S3))as NotSum.
 destruct(rf_boolean_mux joint_update_node_offsets joint_update_expected_nodes 1302 (@Eref VarOrder.T(@Eid VarOrder.T 1284)) 1170 1301 invalid s2 s3 true (Gval(Fuint 1)[::bit]) bit joint_update_node_positions joint_update_node_safety
 ltac:(apply(List.nth_error_In joint_update_expected_nodes 847%nat);vm_compute;reflexivity)
 ltac:(intro site;exact Select) Bit ltac:(exists 1%nat;split;[lia|reflexivity]) S3)as[value[Value Shape]].
 destruct(rf_boolean_mux joint_update_node_offsets joint_update_expected_nodes 1303 (@Eref VarOrder.T(@Eid VarOrder.T 1281)) 1161 1302 invalid s3 s4 false value bit joint_update_node_positions joint_update_node_safety
 ltac:(apply(List.nth_error_In joint_update_expected_nodes 848%nat);vm_compute;reflexivity)
 ltac:(intro site;exact NotSum) Value Shape S4)as[result[Result[width[Wide Word]]]].
 subst result.
 eapply(declared_connection_value 1229 flat_statements joint_update_connection_1154_decl joint_update_connection_1154_mid joint_update_connection_1154_tail 1154 1303 32 (Gval(Fuint width)(zext_to width[::bit])));
 [exact joint_update_connection_1154_position|exact joint_update_connection_1154_split|exact joint_update_connection_1154_straight|exact joint_update_connection_1154_mid_safe|exact joint_update_connection_1154_tail_safe|exact joint_update_connection_1154_nonregister|reflexivity|exact Result| |exact S5].
 cbn[adapt_hvalue_as_type]. f_equal;f_equal.
 rewrite<-(take_oversize(n:=width)(s:=[::bit])ltac:(apply/leP;exact Wide))at 1.
 apply(resize_uint_roundtrip_widen 1);[reflexivity|reflexivity|apply/leP;exact Wide].
Qed.
