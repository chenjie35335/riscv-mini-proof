Require Import RFSelectedLowMux RFReferenceWriteEffect RFShiftCenter RFShiftCenterSize RFShiftDatapath ReferencePCTargetSemantics ALUOutputTransfer ReferenceRedirectSpine JointUpdateNodePositions JointUpdateExpressionCertificates JointUpdateConnectionCertificates FormalDeclaredConnection CoreSocModel ComparisonNodes.
From Coq Require Import NArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Theorem rf_upper_dut_copy_output invalid history limit start word :
 size word=32%nat ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter invalid flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 (forall t,(start<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1153(history t)=Some(Gval(Fuint 4)(from_N 4 11))) ->
 (forall t,(start<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1152(history t)=Some(Gval(Fuint 32)word)) ->
 forall t,(Nat.add start 11<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1154(history t)=Some(Gval(Fuint 32)word).
Proof.
 intros Size Steps Mode Word.
 assert(G1279:forall t,(Nat.add start 1<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1279(history t)=Some(Gval(Fuint 1)[::false])).
 { intros[|t]Lo Hi;[lia|]. eapply(reference_redirect_ground_step joint_update_node_offsets joint_update_expected_nodes 1279 joint_update_expr_1279);
 [exact joint_update_node_positions|exact joint_update_node_safety|apply(List.nth_error_In joint_update_expected_nodes 824%nat);vm_compute;reflexivity| |apply Steps;lia].
 intro site. cbn[joint_update_expr_1279 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite(Mode t ltac:(lia)ltac:(lia)). reflexivity. }
 assert(G1280:forall t,(Nat.add start 1<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1280(history t)=Some(Gval(Fuint 1)[::false])).
 { intros[|t]Lo Hi;[lia|]. eapply(reference_redirect_ground_step joint_update_node_offsets joint_update_expected_nodes 1280 joint_update_expr_1280);
 [exact joint_update_node_positions|exact joint_update_node_safety|apply(List.nth_error_In joint_update_expected_nodes 825%nat);vm_compute;reflexivity| |apply Steps;lia].
 intro site. cbn[joint_update_expr_1280 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite(Mode t ltac:(lia)ltac:(lia)). reflexivity. }
 assert(G1282:forall t,(Nat.add start 1<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1282(history t)=Some(Gval(Fuint 1)[::false])).
 { intros[|t]Lo Hi;[lia|]. eapply(reference_redirect_ground_step joint_update_node_offsets joint_update_expected_nodes 1282 joint_update_expr_1282);
 [exact joint_update_node_positions|exact joint_update_node_safety|apply(List.nth_error_In joint_update_expected_nodes 827%nat);vm_compute;reflexivity| |apply Steps;lia].
 intro site. cbn[joint_update_expr_1282 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite(Mode t ltac:(lia)ltac:(lia)). reflexivity. }
 assert(G1283:forall t,(Nat.add start 1<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1283(history t)=Some(Gval(Fuint 1)[::false])).
 { intros[|t]Lo Hi;[lia|]. eapply(reference_redirect_ground_step joint_update_node_offsets joint_update_expected_nodes 1283 joint_update_expr_1283);
 [exact joint_update_node_positions|exact joint_update_node_safety|apply(List.nth_error_In joint_update_expected_nodes 828%nat);vm_compute;reflexivity| |apply Steps;lia].
 intro site. cbn[joint_update_expr_1283 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite(Mode t ltac:(lia)ltac:(lia)). reflexivity. }
 assert(G1285:forall t,(Nat.add start 1<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1285(history t)=Some(Gval(Fuint 1)[::false])).
 { intros[|t]Lo Hi;[lia|]. eapply(reference_redirect_ground_step joint_update_node_offsets joint_update_expected_nodes 1285 joint_update_expr_1285);
 [exact joint_update_node_positions|exact joint_update_node_safety|apply(List.nth_error_In joint_update_expected_nodes 830%nat);vm_compute;reflexivity| |apply Steps;lia].
 intro site. cbn[joint_update_expr_1285 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite(Mode t ltac:(lia)ltac:(lia)). reflexivity. }
 assert(G1286:forall t,(Nat.add start 1<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1286(history t)=Some(Gval(Fuint 1)[::false])).
 { intros[|t]Lo Hi;[lia|]. eapply(reference_redirect_ground_step joint_update_node_offsets joint_update_expected_nodes 1286 joint_update_expr_1286);
 [exact joint_update_node_positions|exact joint_update_node_safety|apply(List.nth_error_In joint_update_expected_nodes 831%nat);vm_compute;reflexivity| |apply Steps;lia].
 intro site. cbn[joint_update_expr_1286 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite(Mode t ltac:(lia)ltac:(lia)). reflexivity. }
 assert(G1288:forall t,(Nat.add start 1<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1288(history t)=Some(Gval(Fuint 1)[::false])).
 { intros[|t]Lo Hi;[lia|]. eapply(reference_redirect_ground_step joint_update_node_offsets joint_update_expected_nodes 1288 joint_update_expr_1288);
 [exact joint_update_node_positions|exact joint_update_node_safety|apply(List.nth_error_In joint_update_expected_nodes 833%nat);vm_compute;reflexivity| |apply Steps;lia].
 intro site. cbn[joint_update_expr_1288 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite(Mode t ltac:(lia)ltac:(lia)). reflexivity. }
 assert(G1289:forall t,(Nat.add start 1<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1289(history t)=Some(Gval(Fuint 1)[::false])).
 { intros[|t]Lo Hi;[lia|]. eapply(reference_redirect_ground_step joint_update_node_offsets joint_update_expected_nodes 1289 joint_update_expr_1289);
 [exact joint_update_node_positions|exact joint_update_node_safety|apply(List.nth_error_In joint_update_expected_nodes 834%nat);vm_compute;reflexivity| |apply Steps;lia].
 intro site. cbn[joint_update_expr_1289 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite(Mode t ltac:(lia)ltac:(lia)). reflexivity. }
 assert(G1291:forall t,(Nat.add start 1<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1291(history t)=Some(Gval(Fuint 1)[::false])).
 { intros[|t]Lo Hi;[lia|]. eapply(reference_redirect_ground_step joint_update_node_offsets joint_update_expected_nodes 1291 joint_update_expr_1291);
 [exact joint_update_node_positions|exact joint_update_node_safety|apply(List.nth_error_In joint_update_expected_nodes 836%nat);vm_compute;reflexivity| |apply Steps;lia].
 intro site. cbn[joint_update_expr_1291 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite(Mode t ltac:(lia)ltac:(lia)). reflexivity. }
 assert(G1293:forall t,(Nat.add start 1<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1293(history t)=Some(Gval(Fuint 1)[::false])).
 { intros[|t]Lo Hi;[lia|]. eapply(reference_redirect_ground_step joint_update_node_offsets joint_update_expected_nodes 1293 joint_update_expr_1293);
 [exact joint_update_node_positions|exact joint_update_node_safety|apply(List.nth_error_In joint_update_expected_nodes 838%nat);vm_compute;reflexivity| |apply Steps;lia].
 intro site. cbn[joint_update_expr_1293 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite(Mode t ltac:(lia)ltac:(lia)). reflexivity. }
 assert(G1295:forall t,(Nat.add start 1<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1295(history t)=Some(Gval(Fuint 1)[::false])).
 { intros[|t]Lo Hi;[lia|]. eapply(reference_redirect_ground_step joint_update_node_offsets joint_update_expected_nodes 1295 joint_update_expr_1295);
 [exact joint_update_node_positions|exact joint_update_node_safety|apply(List.nth_error_In joint_update_expected_nodes 840%nat);vm_compute;reflexivity| |apply Steps;lia].
 intro site. cbn[joint_update_expr_1295 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite(Mode t ltac:(lia)ltac:(lia)). reflexivity. }
 assert(G1281:forall t,(Nat.add start 2<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1281(history t)=Some(Gval(Fuint 1)[::false])).
 { intros[|t]Lo Hi;[lia|]. eapply(reference_redirect_ground_step joint_update_node_offsets joint_update_expected_nodes 1281 joint_update_expr_1281);
 [exact joint_update_node_positions|exact joint_update_node_safety|apply(List.nth_error_In joint_update_expected_nodes 826%nat);vm_compute;reflexivity| |apply Steps;lia].
 intro site. cbn[joint_update_expr_1281 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite(G1279 t ltac:(lia)ltac:(lia))(G1280 t ltac:(lia)ltac:(lia)). reflexivity. }
 assert(G1284:forall t,(Nat.add start 2<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1284(history t)=Some(Gval(Fuint 1)[::false])).
 { intros[|t]Lo Hi;[lia|]. eapply(reference_redirect_ground_step joint_update_node_offsets joint_update_expected_nodes 1284 joint_update_expr_1284);
 [exact joint_update_node_positions|exact joint_update_node_safety|apply(List.nth_error_In joint_update_expected_nodes 829%nat);vm_compute;reflexivity| |apply Steps;lia].
 intro site. cbn[joint_update_expr_1284 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite(G1282 t ltac:(lia)ltac:(lia))(G1283 t ltac:(lia)ltac:(lia)). reflexivity. }
 assert(G1287:forall t,(Nat.add start 2<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1287(history t)=Some(Gval(Fuint 1)[::false])).
 { intros[|t]Lo Hi;[lia|]. eapply(reference_redirect_ground_step joint_update_node_offsets joint_update_expected_nodes 1287 joint_update_expr_1287);
 [exact joint_update_node_positions|exact joint_update_node_safety|apply(List.nth_error_In joint_update_expected_nodes 832%nat);vm_compute;reflexivity| |apply Steps;lia].
 intro site. cbn[joint_update_expr_1287 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite(G1285 t ltac:(lia)ltac:(lia))(G1286 t ltac:(lia)ltac:(lia)). reflexivity. }
 assert(V0:forall t,(start<=t)%coq_nat ->(t<=limit)%coq_nat ->exists value,VM.find 1152(history t)=Some value /\rf_reference_low_word word value).
 { intros t Lo Hi. exists(Gval(Fuint 32)word). split;[apply Word;assumption|]. exists 32%nat,word. repeat split;try reflexivity;try exact Size. rewrite <-Size;apply take_size. }
 assert(V1:forall t,(Nat.add start 3<=t)%coq_nat ->(t<=limit)%coq_nat ->exists value,VM.find 1296(history t)=Some value /\rf_reference_low_word word value).
 { intros[|t]Lo Hi;[lia|]. destruct(V0 t ltac:(lia)ltac:(lia))as[value[Value Low]].
 exact(rf_selected_low_mux joint_update_node_offsets joint_update_expected_nodes 1296 _ 1151 1152 invalid(history t)(history(S t))false value word
 joint_update_node_positions joint_update_node_safety ltac:(apply(List.nth_error_In joint_update_expected_nodes 841%nat);vm_compute;reflexivity)
 ltac:(intro site;exact(G1295 t ltac:(lia)ltac:(lia)))Value Low(Steps t ltac:(lia))). }
 assert(V2:forall t,(Nat.add start 4<=t)%coq_nat ->(t<=limit)%coq_nat ->exists value,VM.find 1297(history t)=Some value /\rf_reference_low_word word value).
 { intros[|t]Lo Hi;[lia|]. destruct(V1 t ltac:(lia)ltac:(lia))as[value[Value Low]].
 exact(rf_selected_low_mux joint_update_node_offsets joint_update_expected_nodes 1297 _ 1294 1296 invalid(history t)(history(S t))false value word
 joint_update_node_positions joint_update_node_safety ltac:(apply(List.nth_error_In joint_update_expected_nodes 842%nat);vm_compute;reflexivity)
 ltac:(intro site;exact(G1293 t ltac:(lia)ltac:(lia)))Value Low(Steps t ltac:(lia))). }
 assert(V3:forall t,(Nat.add start 5<=t)%coq_nat ->(t<=limit)%coq_nat ->exists value,VM.find 1298(history t)=Some value /\rf_reference_low_word word value).
 { intros[|t]Lo Hi;[lia|]. destruct(V2 t ltac:(lia)ltac:(lia))as[value[Value Low]].
 exact(rf_selected_low_mux joint_update_node_offsets joint_update_expected_nodes 1298 _ 1292 1297 invalid(history t)(history(S t))false value word
 joint_update_node_positions joint_update_node_safety ltac:(apply(List.nth_error_In joint_update_expected_nodes 843%nat);vm_compute;reflexivity)
 ltac:(intro site;exact(G1291 t ltac:(lia)ltac:(lia)))Value Low(Steps t ltac:(lia))). }
 assert(V4:forall t,(Nat.add start 6<=t)%coq_nat ->(t<=limit)%coq_nat ->exists value,VM.find 1299(history t)=Some value /\rf_reference_low_word word value).
 { intros[|t]Lo Hi;[lia|]. destruct(V3 t ltac:(lia)ltac:(lia))as[value[Value Low]].
 exact(rf_selected_low_mux joint_update_node_offsets joint_update_expected_nodes 1299 _ 1290 1298 invalid(history t)(history(S t))false value word
 joint_update_node_positions joint_update_node_safety ltac:(apply(List.nth_error_In joint_update_expected_nodes 844%nat);vm_compute;reflexivity)
 ltac:(intro site;exact(G1289 t ltac:(lia)ltac:(lia)))Value Low(Steps t ltac:(lia))). }
 assert(V5:forall t,(Nat.add start 7<=t)%coq_nat ->(t<=limit)%coq_nat ->exists value,VM.find 1300(history t)=Some value /\rf_reference_low_word word value).
 { intros[|t]Lo Hi;[lia|]. destruct(V4 t ltac:(lia)ltac:(lia))as[value[Value Low]].
 exact(rf_selected_low_mux joint_update_node_offsets joint_update_expected_nodes 1300 _ 1278 1299 invalid(history t)(history(S t))false value word
 joint_update_node_positions joint_update_node_safety ltac:(apply(List.nth_error_In joint_update_expected_nodes 845%nat);vm_compute;reflexivity)
 ltac:(intro site;exact(G1288 t ltac:(lia)ltac:(lia)))Value Low(Steps t ltac:(lia))). }
 assert(V6:forall t,(Nat.add start 8<=t)%coq_nat ->(t<=limit)%coq_nat ->exists value,VM.find 1301(history t)=Some value /\rf_reference_low_word word value).
 { intros[|t]Lo Hi;[lia|]. destruct(V5 t ltac:(lia)ltac:(lia))as[value[Value Low]].
 exact(rf_selected_low_mux joint_update_node_offsets joint_update_expected_nodes 1301 _ 1229 1300 invalid(history t)(history(S t))false value word
 joint_update_node_positions joint_update_node_safety ltac:(apply(List.nth_error_In joint_update_expected_nodes 846%nat);vm_compute;reflexivity)
 ltac:(intro site;exact(G1287 t ltac:(lia)ltac:(lia)))Value Low(Steps t ltac:(lia))). }
 assert(V7:forall t,(Nat.add start 9<=t)%coq_nat ->(t<=limit)%coq_nat ->exists value,VM.find 1302(history t)=Some value /\rf_reference_low_word word value).
 { intros[|t]Lo Hi;[lia|]. destruct(V6 t ltac:(lia)ltac:(lia))as[value[Value Low]].
 exact(rf_selected_low_mux joint_update_node_offsets joint_update_expected_nodes 1302 _ 1170 1301 invalid(history t)(history(S t))false value word
 joint_update_node_positions joint_update_node_safety ltac:(apply(List.nth_error_In joint_update_expected_nodes 847%nat);vm_compute;reflexivity)
 ltac:(intro site;exact(G1284 t ltac:(lia)ltac:(lia)))Value Low(Steps t ltac:(lia))). }
 assert(V8:forall t,(Nat.add start 10<=t)%coq_nat ->(t<=limit)%coq_nat ->exists value,VM.find 1303(history t)=Some value /\rf_reference_low_word word value).
 { intros[|t]Lo Hi;[lia|]. destruct(V7 t ltac:(lia)ltac:(lia))as[value[Value Low]].
 exact(rf_selected_low_mux joint_update_node_offsets joint_update_expected_nodes 1303 _ 1161 1302 invalid(history t)(history(S t))false value word
 joint_update_node_positions joint_update_node_safety ltac:(apply(List.nth_error_In joint_update_expected_nodes 848%nat);vm_compute;reflexivity)
 ltac:(intro site;exact(G1281 t ltac:(lia)ltac:(lia)))Value Low(Steps t ltac:(lia))). }
 intros[|t]Lo Hi;[lia|]. destruct(V8 t ltac:(lia)ltac:(lia))as[value[Value[width[raw[Equal[RawSize[Wide Low]]]]]]]. subst value.
 eapply(declared_connection_value 1229 flat_statements joint_update_connection_1154_decl joint_update_connection_1154_mid joint_update_connection_1154_tail 1154 1303 32 (Gval(Fuint width)raw));
 [exact joint_update_connection_1154_position|exact joint_update_connection_1154_split|exact joint_update_connection_1154_straight|exact joint_update_connection_1154_mid_safe|exact joint_update_connection_1154_tail_safe|exact joint_update_connection_1154_nonregister|reflexivity|exact Value| |apply Steps;lia].
 cbn[adapt_hvalue_as_type]. rewrite Low. unfold zext_to,zext. rewrite Size subnn cats0. reflexivity.
Qed.
