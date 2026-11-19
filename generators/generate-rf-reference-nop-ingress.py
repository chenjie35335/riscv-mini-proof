"""Actual reference RF storage-to-read-port wiring, shared indexed certificates."""
from pathlib import Path
import re
root=Path(__file__).resolve().parents[2];p=root/'formal/flat-low/staged-integration';s=(root/'formal/flat-low/CoreSocModel.v').read_text()
q=[m.start() for m in re.finditer(r'\(@Qcons VarOrder.T ',s)]
from bisect import bisect_right
pos=lambda at:bisect_right(q,at)-1
decl=[];conn=[]
for i in range(32):
 m=re.search(r'\(@Swire VarOrder.T '+str(1717+i)+r' ',s);decl.append(pos(m.start()))
 m=re.search(r'\(@Sfcnct VarOrder.T \(@Eid VarOrder.T '+str(1717+i)+r'\) \(@Eref VarOrder.T \(@Eid VarOrder.T '+str(7299+i)+r'\)\)\)',s);assert m;conn.append(pos(m.start()))
base=(p/'RFReferenceNopExit.v').read_text();out=base[:base.index('Definition rf_exit_node')]
out+='Require Import ReferenceControlExpressions ReferenceControlNodeCertificates0 ReferenceRedirectSpine.\n'
out+='Definition rf_ingress_port (index:nat) := N.of_nat (Nat.add 1717 index).\nDefinition rf_ingress_source (index:nat) := N.of_nat (Nat.add 7299 index).\n'
for name,data in [('decl_position',decl),('connect_position',conn)]:
 out+=f'Definition rf_ingress_{name} (index:nat) : nat := nth 0%nat [::'+ ';'.join(str(x)+'%nat' for x in data)+'] index.\n'
out+="""Lemma rf_ingress_wire_certificates (index:nat) : (index < 32)%coq_nat ->
 declared_wire_check flat_memories flat_statements (rf_ingress_decl_position index)
 (Nat.sub (rf_ingress_connect_position index) (S (rf_ingress_decl_position index)))
 (rf_ingress_port index) (rf_ingress_source index) 32 = true.
Proof. intros Upper.
 do 32 (destruct index as [|index]; [vm_compute;reflexivity|]). lia.
Qed.
"""
out+='''Lemma rf_reference_old_wire index invalid old current result word :
 (index < 32)%coq_nat -> size word = 32%nat ->
 VM.find (rf_ingress_source index) old = Some (Gval (Fuint 32) word) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find (rf_ingress_port index) result = Some (Gval (Fuint 32) word).
Proof.
 intros Bound Size Input Step.
 eapply (declared_wire_checked_value flat_memories flat_statements (rf_ingress_decl_position index)
 (Nat.sub (rf_ingress_connect_position index) (S (rf_ingress_decl_position index))) (rf_ingress_port index) (rf_ingress_source index) 32);
 [apply rf_ingress_wire_certificates;exact Bound|exact Input| |exact Step].
 change (Some (Gval (Fuint 32%nat) (zext_to 32%nat (take 32%nat word))) = Some (Gval (Fuint 32%nat) word)).
 rewrite -Size take_size.
 unfold zext_to,zext. rewrite subnn cats0. reflexivity.
Qed.
'''
# Exact aliases already present in the shared PC/control node certificate list.
t=(p/'ReferenceControlNodeCertificates0.v').read_text();ids=list(map(int,re.findall(r'\((\d+),reference_control_expr_',t)))
for i in range(32):assert 2177-i in ids
out+='''Theorem rf_reference_old_word_ingress (index:nat) invalid s0 s1 s2 word :
 (index < 32)%coq_nat -> size word = 32%nat ->
 VM.find (N.of_nat (Nat.add 7299 index)) s0 = Some (Gval (Fuint 32) word) ->
 formal_value_iter invalid flat_memories s0 false s0 flat_statements = Some s1 ->
 formal_value_iter invalid flat_memories s1 false s1 flat_statements = Some s2 ->
 VM.find (N.of_nat (Nat.sub 2177 index)) s2 = Some (Gval (Fuint 32) word).
Proof.
 intros Bound Size Input S1 S2.
 pose proof (rf_reference_old_wire index invalid s0 s0 s1 word Bound Size Input S1) as Wire.
'''
for i in range(32):
 n=2177-i
 out+=f''' destruct index as [|index].
 - eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes {n} reference_control_expr_{n});
 [exact reference_control_0_positions|exact reference_control_0_safety| | |exact S2].
 + apply (List.nth_error_In reference_control_0_nodes {ids.index(n)}%nat). vm_compute. reflexivity.
 + intros site. cbn [reference_control_expr_{n} eval_hfexpr_validif_policy eval_href_validif_policy]. exact Wire.
'''
out+=' lia.\nQed.\n';(p/'RFReferenceNopIngress.v').write_text(out)
