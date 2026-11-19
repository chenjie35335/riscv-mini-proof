Require Import RFSelectedLowMux RFReferenceWriteEffect RFShiftCenter RFShiftCenterSize RFShiftDatapath ReferencePCTargetSemantics ALUOutputTransfer ReferenceRedirectSpine JointUpdateNodePositions JointUpdateExpressionCertificates JointUpdateConnectionCertificates FormalDeclaredConnection CoreSocModel ComparisonNodes.
From Coq Require Import NArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Definition rf_shift_mode direction arithmetic :=if direction then [::arithmetic;false;false;true] else [::false;true;true;false].
Theorem rf_shift_guards invalid s0 s1 s2 direction arithmetic :
 VM.find 1153 s0=Some(Gval(Fuint 4)(rf_shift_mode direction arithmetic)) ->
 formal_value_iter invalid flat_memories s0 false s0 flat_statements=Some s1 ->
 formal_value_iter invalid flat_memories s1 false s1 flat_statements=Some s2 ->
 VM.find 1281 s2=Some(Gval(Fuint 1)[::false]) /\VM.find 1284 s2=Some(Gval(Fuint 1)[::false]) /\
 VM.find 1287 s2=Some(Gval(Fuint 1)[::direction]) /\VM.find 1288 s1=Some(Gval(Fuint 1)[::negb direction]).
Proof.
 intros Mode S1 S2.
 assert(V1279:VM.find 1279 s1=Some(Gval(Fuint 1)[::false])).
 { eapply(reference_redirect_ground_step joint_update_node_offsets joint_update_expected_nodes 1279 joint_update_expr_1279);
 [exact joint_update_node_positions|exact joint_update_node_safety|apply(List.nth_error_In joint_update_expected_nodes 824%nat);vm_compute;reflexivity| |exact S1].
 intro site. cbn[joint_update_expr_1279 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Mode. destruct direction,arithmetic;reflexivity. }
 assert(V1280:VM.find 1280 s1=Some(Gval(Fuint 1)[::false])).
 { eapply(reference_redirect_ground_step joint_update_node_offsets joint_update_expected_nodes 1280 joint_update_expr_1280);
 [exact joint_update_node_positions|exact joint_update_node_safety|apply(List.nth_error_In joint_update_expected_nodes 825%nat);vm_compute;reflexivity| |exact S1].
 intro site. cbn[joint_update_expr_1280 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Mode. destruct direction,arithmetic;reflexivity. }
 assert(V1282:VM.find 1282 s1=Some(Gval(Fuint 1)[::false])).
 { eapply(reference_redirect_ground_step joint_update_node_offsets joint_update_expected_nodes 1282 joint_update_expr_1282);
 [exact joint_update_node_positions|exact joint_update_node_safety|apply(List.nth_error_In joint_update_expected_nodes 827%nat);vm_compute;reflexivity| |exact S1].
 intro site. cbn[joint_update_expr_1282 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Mode. destruct direction,arithmetic;reflexivity. }
 assert(V1283:VM.find 1283 s1=Some(Gval(Fuint 1)[::false])).
 { eapply(reference_redirect_ground_step joint_update_node_offsets joint_update_expected_nodes 1283 joint_update_expr_1283);
 [exact joint_update_node_positions|exact joint_update_node_safety|apply(List.nth_error_In joint_update_expected_nodes 828%nat);vm_compute;reflexivity| |exact S1].
 intro site. cbn[joint_update_expr_1283 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Mode. destruct direction,arithmetic;reflexivity. }
 assert(V1285:VM.find 1285 s1=Some(Gval(Fuint 1)[::direction && arithmetic])).
 { eapply(reference_redirect_ground_step joint_update_node_offsets joint_update_expected_nodes 1285 joint_update_expr_1285);
 [exact joint_update_node_positions|exact joint_update_node_safety|apply(List.nth_error_In joint_update_expected_nodes 830%nat);vm_compute;reflexivity| |exact S1].
 intro site. cbn[joint_update_expr_1285 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Mode. destruct direction,arithmetic;reflexivity. }
 assert(V1286:VM.find 1286 s1=Some(Gval(Fuint 1)[::direction && negb arithmetic])).
 { eapply(reference_redirect_ground_step joint_update_node_offsets joint_update_expected_nodes 1286 joint_update_expr_1286);
 [exact joint_update_node_positions|exact joint_update_node_safety|apply(List.nth_error_In joint_update_expected_nodes 831%nat);vm_compute;reflexivity| |exact S1].
 intro site. cbn[joint_update_expr_1286 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Mode. destruct direction,arithmetic;reflexivity. }
 assert(V1288:VM.find 1288 s1=Some(Gval(Fuint 1)[::negb direction])).
 { eapply(reference_redirect_ground_step joint_update_node_offsets joint_update_expected_nodes 1288 joint_update_expr_1288);
 [exact joint_update_node_positions|exact joint_update_node_safety|apply(List.nth_error_In joint_update_expected_nodes 833%nat);vm_compute;reflexivity| |exact S1].
 intro site. cbn[joint_update_expr_1288 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Mode. destruct direction,arithmetic;reflexivity. }
 assert(V1281:VM.find 1281 s2=Some(Gval(Fuint 1)[::false])).
 { eapply(reference_redirect_ground_step joint_update_node_offsets joint_update_expected_nodes 1281 joint_update_expr_1281);
 [exact joint_update_node_positions|exact joint_update_node_safety|apply(List.nth_error_In joint_update_expected_nodes 826%nat);vm_compute;reflexivity| |exact S2].
 intro site. cbn[joint_update_expr_1281 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite V1279 V1280. destruct direction,arithmetic;reflexivity. }
 assert(V1284:VM.find 1284 s2=Some(Gval(Fuint 1)[::false])).
 { eapply(reference_redirect_ground_step joint_update_node_offsets joint_update_expected_nodes 1284 joint_update_expr_1284);
 [exact joint_update_node_positions|exact joint_update_node_safety|apply(List.nth_error_In joint_update_expected_nodes 829%nat);vm_compute;reflexivity| |exact S2].
 intro site. cbn[joint_update_expr_1284 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite V1282 V1283. destruct direction,arithmetic;reflexivity. }
 assert(V1287:VM.find 1287 s2=Some(Gval(Fuint 1)[::direction])).
 { eapply(reference_redirect_ground_step joint_update_node_offsets joint_update_expected_nodes 1287 joint_update_expr_1287);
 [exact joint_update_node_positions|exact joint_update_node_safety|apply(List.nth_error_In joint_update_expected_nodes 832%nat);vm_compute;reflexivity| |exact S2].
 intro site. cbn[joint_update_expr_1287 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite V1285 V1286. destruct direction,arithmetic;reflexivity. }
repeat split;assumption.
Qed.
Lemma rf_shift_low_self word :size word=32%nat ->rf_reference_low_word word(Gval(Fuint 32)word).
Proof. intro Size. exists 32%nat,word. repeat split;try reflexivity;try exact Size. rewrite<-Size;apply take_size. Qed.
Theorem rf_shift_output_history invalid history limit direction arithmetic word :
 size word=32%nat ->
 (forall t,(t<=limit)%coq_nat ->VM.find 1153(history t)=Some(Gval(Fuint 4)(rf_shift_mode direction arithmetic))) ->
 (forall t,(49<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find(if direction then 1229 else 1278)(history t)=Some(Gval(Fuint 32)word)) ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter invalid flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 forall t,(54<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1154(history t)=Some(Gval(Fuint 32)word).
Proof.
 intros Size Modes Values Steps t Lower Upper.
 assert(Guards:forall u,(2<=u)%coq_nat ->(u<=limit)%coq_nat ->
 VM.find 1281(history u)=Some(Gval(Fuint 1)[::false]) /\VM.find 1284(history u)=Some(Gval(Fuint 1)[::false]) /\VM.find 1287(history u)=Some(Gval(Fuint 1)[::direction])).
 { intros [|[|u]] Lo Hi;try lia. destruct(rf_shift_guards invalid(history u)(history(S u))(history(S(S u)))direction arithmetic(Modes u ltac:(lia))(Steps u ltac:(lia))(Steps(S u)ltac:(lia)))as[A[B[C D]]]. repeat split;assumption. }
 assert(Chosen:exists value,VM.find 1301(history(Nat.sub t 3))=Some value /\rf_reference_low_word word value).
 { destruct direction.
 - eapply(rf_selected_low_mux joint_update_node_offsets joint_update_expected_nodes 1301 _ 1229 1300 invalid(history(Nat.sub t 4))(history(Nat.sub t 3))true(Gval(Fuint 32)word)word);
 [exact joint_update_node_positions|exact joint_update_node_safety|apply(List.nth_error_In joint_update_expected_nodes 846%nat);vm_compute;reflexivity| |apply Values;lia|apply rf_shift_low_self;exact Size|].
 + intro site;exact(proj2(proj2(Guards(Nat.sub t 4)ltac:(lia)ltac:(lia)))).
 + replace(Nat.sub t 3)with(S(Nat.sub t 4))by lia;apply Steps;lia.
 - assert(G:VM.find 1288(history(Nat.sub t 5))=Some(Gval(Fuint 1)[::true])).
   { replace(Nat.sub t 5)with(S(Nat.sub t 6))by lia.
     exact(proj2(proj2(proj2(rf_shift_guards invalid(history(Nat.sub t 6))(history(S(Nat.sub t 6)))(history(S(S(Nat.sub t 6))))false arithmetic(Modes (Nat.sub t 6) ltac:(lia))(Steps (Nat.sub t 6) ltac:(lia))(Steps (S(Nat.sub t 6)) ltac:(lia)))))). }
   destruct(rf_selected_low_mux joint_update_node_offsets joint_update_expected_nodes 1300 _ 1278 1299 invalid(history(Nat.sub t 5))(history(S(Nat.sub t 5)))true(Gval(Fuint 32)word)word joint_update_node_positions joint_update_node_safety ltac:(apply(List.nth_error_In joint_update_expected_nodes 845%nat);vm_compute;reflexivity)ltac:(intro site;exact G)(Values (Nat.sub t 5) ltac:(lia)ltac:(lia))(rf_shift_low_self word Size)(Steps (Nat.sub t 5) ltac:(lia)))as[v[V L]].
   replace(S(Nat.sub t 5))with(Nat.sub t 4)in V by lia.
   eapply(rf_selected_low_mux joint_update_node_offsets joint_update_expected_nodes 1301 _ 1229 1300 invalid(history(Nat.sub t 4))(history(Nat.sub t 3))false v word);
   [exact joint_update_node_positions|exact joint_update_node_safety|apply(List.nth_error_In joint_update_expected_nodes 846%nat);vm_compute;reflexivity| |exact V|exact L|].
   + intro site;exact(proj2(proj2(Guards(Nat.sub t 4)ltac:(lia)ltac:(lia)))).
   + replace(Nat.sub t 3)with(S(Nat.sub t 4))by lia;apply Steps;lia. }
 destruct Chosen as[v[V L]].
 destruct(rf_selected_low_mux joint_update_node_offsets joint_update_expected_nodes 1302 _ 1170 1301 invalid(history(Nat.sub t 3))(history(S(Nat.sub t 3)))false v word joint_update_node_positions joint_update_node_safety ltac:(apply(List.nth_error_In joint_update_expected_nodes 847%nat);vm_compute;reflexivity)ltac:(intro site;exact(proj1(proj2(Guards(Nat.sub t 3)ltac:(lia)ltac:(lia)))))V L(Steps (Nat.sub t 3) ltac:(lia)))as[v2[V2 L2]].
 replace(S(Nat.sub t 3))with(Nat.sub t 2)in V2 by lia.
 destruct(rf_selected_low_mux joint_update_node_offsets joint_update_expected_nodes 1303 _ 1161 1302 invalid(history(Nat.sub t 2))(history(S(Nat.sub t 2)))false v2 word joint_update_node_positions joint_update_node_safety ltac:(apply(List.nth_error_In joint_update_expected_nodes 848%nat);vm_compute;reflexivity)ltac:(intro site;exact(proj1(Guards(Nat.sub t 2)ltac:(lia)ltac:(lia))))V2 L2(Steps (Nat.sub t 2) ltac:(lia)))as[v3[V3 L3]].
 replace(S(Nat.sub t 2))with(Nat.sub t 1)in V3 by lia.
 destruct L3 as[width[raw[Equal[RawSize[Wide Low]]]]]. subst v3.
 replace t with(S(Nat.sub t 1))at 1 by lia.
 eapply(declared_connection_value 1229 flat_statements joint_update_connection_1154_decl joint_update_connection_1154_mid joint_update_connection_1154_tail 1154 1303 32 (Gval(Fuint width)raw));
 [exact joint_update_connection_1154_position|exact joint_update_connection_1154_split|exact joint_update_connection_1154_straight|exact joint_update_connection_1154_mid_safe|exact joint_update_connection_1154_tail_safe|exact joint_update_connection_1154_nonregister|reflexivity|exact V3| |apply Steps;lia].
 cbn[adapt_hvalue_as_type]. rewrite Low. unfold zext_to,zext. rewrite Size subnn cats0. reflexivity.
Qed.
