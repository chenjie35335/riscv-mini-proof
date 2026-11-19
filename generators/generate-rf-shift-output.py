from pathlib import Path
root=Path(__file__).resolve().parents[2];p=root/'formal/flat-low/staged-integration'
s='''Require Import RFSelectedLowMux RFReferenceWriteEffect RFShiftCenter RFShiftCenterSize RFShiftDatapath ReferencePCTargetSemantics ALUOutputTransfer ReferenceRedirectSpine JointUpdateNodePositions JointUpdateExpressionCertificates JointUpdateConnectionCertificates FormalDeclaredConnection CoreSocModel ComparisonNodes.
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
 VM.find 1281 s2=Some(Gval(Fuint 1)[::false]) /\\VM.find 1284 s2=Some(Gval(Fuint 1)[::false]) /\\
 VM.find 1287 s2=Some(Gval(Fuint 1)[::direction]) /\\VM.find 1288 s1=Some(Gval(Fuint 1)[::negb direction]).
Proof.
 intros Mode S1 S2.
'''
for n,val in [(1279,'false'),(1280,'false'),(1282,'false'),(1283,'false'),(1285,'direction && arithmetic'),(1286,'direction && negb arithmetic'),(1288,'negb direction')]:
 s+=f''' assert(V{n}:VM.find {n} s1=Some(Gval(Fuint 1)[::{val}])).
 {{ eapply(reference_redirect_ground_step joint_update_node_offsets joint_update_expected_nodes {n} joint_update_expr_{n});
 [exact joint_update_node_positions|exact joint_update_node_safety|apply(List.nth_error_In joint_update_expected_nodes {n-455}%nat);vm_compute;reflexivity| |exact S1].
 intro site. cbn[joint_update_expr_{n} eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Mode. destruct direction,arithmetic;reflexivity. }}
'''
for n,a,b,val in [(1281,1279,1280,'false'),(1284,1282,1283,'false'),(1287,1285,1286,'direction')]:
 s+=f''' assert(V{n}:VM.find {n} s2=Some(Gval(Fuint 1)[::{val}])).
 {{ eapply(reference_redirect_ground_step joint_update_node_offsets joint_update_expected_nodes {n} joint_update_expr_{n});
 [exact joint_update_node_positions|exact joint_update_node_safety|apply(List.nth_error_In joint_update_expected_nodes {n-455}%nat);vm_compute;reflexivity| |exact S2].
 intro site. cbn[joint_update_expr_{n} eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite V{a} V{b}. destruct direction,arithmetic;reflexivity. }}
'''
s+='repeat split;assumption.\nQed.\n'
s+='''Lemma rf_shift_low_self word :size word=32%nat ->rf_reference_low_word word(Gval(Fuint 32)word).
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
 VM.find 1281(history u)=Some(Gval(Fuint 1)[::false]) /\\VM.find 1284(history u)=Some(Gval(Fuint 1)[::false]) /\\VM.find 1287(history u)=Some(Gval(Fuint 1)[::direction])).
 { intros [|[|u]] Lo Hi;try lia. destruct(rf_shift_guards invalid(history u)(history(S u))(history(S(S u)))direction arithmetic(Modes u ltac:(lia))(Steps u ltac:(lia))(Steps(S u)ltac:(lia)))as[A[B[C D]]]. repeat split;assumption. }
 assert(Chosen:exists value,VM.find 1301(history(Nat.sub t 3))=Some value /\\rf_reference_low_word word value).
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
'''
for node,cond,yes,no,offset,idx in [(1302,1284,1170,1301,3,847),(1303,1281,1161,1302,2,848)]:
 guard='proj1(proj2' if cond==1284 else 'proj1'
 g=f'proj1(proj2(Guards(Nat.sub t {offset})ltac:(lia)ltac:(lia)))' if cond==1284 else f'proj1(Guards(Nat.sub t {offset})ltac:(lia)ltac:(lia))'
 outv='v2'if node==1302 else'v3';inval='v'if node==1302 else'v2';lookup='V'if node==1302 else'V2';low='L'if node==1302 else'L2';lookout='V2'if node==1302 else'V3';lowout='L2'if node==1302 else'L3'
 s+=f''' destruct(rf_selected_low_mux joint_update_node_offsets joint_update_expected_nodes {node} _ {yes} {no} invalid(history(Nat.sub t {offset}))(history(S(Nat.sub t {offset})))false {inval} word joint_update_node_positions joint_update_node_safety ltac:(apply(List.nth_error_In joint_update_expected_nodes {idx}%nat);vm_compute;reflexivity)ltac:(intro site;exact({g})){lookup} {low}(Steps (Nat.sub t {offset}) ltac:(lia)))as[{outv}[{lookout} {lowout}]].
 replace(S(Nat.sub t {offset}))with(Nat.sub t {offset-1})in {lookout} by lia.
'''
s+=''' destruct L3 as[width[raw[Equal[RawSize[Wide Low]]]]]. subst v3.
 replace t with(S(Nat.sub t 1))at 1 by lia.
 eapply(declared_connection_value 1229 flat_statements joint_update_connection_1154_decl joint_update_connection_1154_mid joint_update_connection_1154_tail 1154 1303 32 (Gval(Fuint width)raw));
 [exact joint_update_connection_1154_position|exact joint_update_connection_1154_split|exact joint_update_connection_1154_straight|exact joint_update_connection_1154_mid_safe|exact joint_update_connection_1154_tail_safe|exact joint_update_connection_1154_nonregister|reflexivity|exact V3| |apply Steps;lia].
 cbn[adapt_hvalue_as_type]. rewrite Low. unfold zext_to,zext. rewrite Size subnn cats0. reflexivity.
Qed.
'''
(p/'RFShiftOutput.v').write_text(s)
