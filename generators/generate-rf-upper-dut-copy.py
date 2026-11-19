from pathlib import Path
root=Path(__file__).resolve().parents[2];b=root/'formal/flat-low/staged-integration'
head=(b/'RFShiftOutput.v').read_text().split('Definition rf_shift_mode')[0]
s=head+r'''Theorem rf_upper_dut_copy_output invalid history limit start word :
 size word=32%nat ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter invalid flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 (forall t,(start<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1153(history t)=Some(Gval(Fuint 4)(from_N 4 11))) ->
 (forall t,(start<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1152(history t)=Some(Gval(Fuint 32)word)) ->
 forall t,(Nat.add start 11<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1154(history t)=Some(Gval(Fuint 32)word).
Proof.
 intros Size Steps Mode Word.
'''
for node in [1279,1280,1282,1283,1285,1286,1288,1289,1291,1293,1295]:
 s+=fr''' assert(G{node}:forall t,(Nat.add start 1<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find {node}(history t)=Some(Gval(Fuint 1)[::false])).
 {{ intros[|t]Lo Hi;[lia|]. eapply(reference_redirect_ground_step joint_update_node_offsets joint_update_expected_nodes {node} joint_update_expr_{node});
 [exact joint_update_node_positions|exact joint_update_node_safety|apply(List.nth_error_In joint_update_expected_nodes {node-455}%nat);vm_compute;reflexivity| |apply Steps;lia].
 intro site. cbn[joint_update_expr_{node} eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite(Mode t ltac:(lia)ltac:(lia)). reflexivity. }}
'''
for node,a,c in [(1281,1279,1280),(1284,1282,1283),(1287,1285,1286)]:
 s+=fr''' assert(G{node}:forall t,(Nat.add start 2<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find {node}(history t)=Some(Gval(Fuint 1)[::false])).
 {{ intros[|t]Lo Hi;[lia|]. eapply(reference_redirect_ground_step joint_update_node_offsets joint_update_expected_nodes {node} joint_update_expr_{node});
 [exact joint_update_node_positions|exact joint_update_node_safety|apply(List.nth_error_In joint_update_expected_nodes {node-455}%nat);vm_compute;reflexivity| |apply Steps;lia].
 intro site. cbn[joint_update_expr_{node} eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite(G{a} t ltac:(lia)ltac:(lia))(G{c} t ltac:(lia)ltac:(lia)). reflexivity. }}
'''
s+=r''' assert(V0:forall t,(start<=t)%coq_nat ->(t<=limit)%coq_nat ->exists value,VM.find 1152(history t)=Some value /\rf_reference_low_word word value).
 { intros t Lo Hi. exists(Gval(Fuint 32)word). split;[apply Word;assumption|]. exists 32%nat,word. repeat split;try reflexivity;try exact Size. rewrite <-Size;apply take_size. }
'''
for stage,(node,guard,yes,no) in enumerate([(1296,1295,1151,1152),(1297,1293,1294,1296),(1298,1291,1292,1297),(1299,1289,1290,1298),(1300,1288,1278,1299),(1301,1287,1229,1300),(1302,1284,1170,1301),(1303,1281,1161,1302)],1):
 s+=fr''' assert(V{stage}:forall t,(Nat.add start {stage+2}<=t)%coq_nat ->(t<=limit)%coq_nat ->exists value,VM.find {node}(history t)=Some value /\rf_reference_low_word word value).
 {{ intros[|t]Lo Hi;[lia|]. destruct(V{stage-1} t ltac:(lia)ltac:(lia))as[value[Value Low]].
 exact(rf_selected_low_mux joint_update_node_offsets joint_update_expected_nodes {node} _ {yes} {no} invalid(history t)(history(S t))false value word
 joint_update_node_positions joint_update_node_safety ltac:(apply(List.nth_error_In joint_update_expected_nodes {node-455}%nat);vm_compute;reflexivity)
 ltac:(intro site;exact(G{guard} t ltac:(lia)ltac:(lia)))Value Low(Steps t ltac:(lia))). }}
'''
s+=r''' intros[|t]Lo Hi;[lia|]. destruct(V8 t ltac:(lia)ltac:(lia))as[value[Value[width[raw[Equal[RawSize[Wide Low]]]]]]]. subst value.
 eapply(declared_connection_value 1229 flat_statements joint_update_connection_1154_decl joint_update_connection_1154_mid joint_update_connection_1154_tail 1154 1303 32 (Gval(Fuint width)raw));
 [exact joint_update_connection_1154_position|exact joint_update_connection_1154_split|exact joint_update_connection_1154_straight|exact joint_update_connection_1154_mid_safe|exact joint_update_connection_1154_tail_safe|exact joint_update_connection_1154_nonregister|reflexivity|exact Value| |apply Steps;lia].
 cbn[adapt_hvalue_as_type]. rewrite Low. unfold zext_to,zext. rewrite Size subnn cats0. reflexivity.
Qed.
'''
(b/'RFUpperDUTCopyOutput.v').write_text(s)
