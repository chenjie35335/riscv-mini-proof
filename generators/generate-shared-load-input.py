"""Batch certificates for actual shared load data aliases."""
from pathlib import Path
import re,bisect
root=Path(__file__).resolve().parents[2];base=root/'formal/flat-low';s=(base/'CoreSocModel.v').read_text()
q=[m.start() for m in re.finditer(r'\(@Qcons VarOrder.T ',s)]
pos=lambda t:bisect.bisect_right(q,s.index(t))-1
nodes=[(3347,1712),(8079,82),(8080,8079),(8201,8080)]
positions=[pos(f'(@Snode VarOrder.T {n} ') for n,_ in nodes]
offsets=[positions[0]]+[b-a-1 for a,b in zip(positions,positions[1:])]
wires=[(1477,8201),(1522,1477),(1712,1522)]
d=[pos(f'(@Swire VarOrder.T {n} ') for n,_ in wires]
c=[pos(f'(@Sfcnct VarOrder.T (@Eid VarOrder.T {n}) (@Eref VarOrder.T (@Eid VarOrder.T {r})))') for n,r in wires]
seq=lambda xs:'[::'+';'.join(str(x)+'%nat' for x in xs)+']'
out='''Require Import CoreSocModel ComparisonNodes SelectedNodeSafety X0ConcretePositionCertificate X0ConcreteSafetyCertificate FormalTypedNodeEquation FormalDeclaredWireCheck RFWritebackSelection.
From Coq Require Import ZArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
'''
out+='Definition shared_load_nodes : seq (VarOrder.T * hfexpr VarOrder.T) := [::'+';'.join(f'({n},@Eref VarOrder.T (@Eid VarOrder.T {r}))' for n,r in nodes)+'].\n'
out+='Definition shared_load_offsets := '+seq(offsets)+'.\n'
out+='''Lemma shared_load_positions : select_node_offsets shared_load_offsets flat_statements = Some shared_load_nodes.
Proof. vm_compute. reflexivity. Qed.
Lemma shared_load_safety : selected_node_safety flat_memories flat_statements shared_load_offsets flat_statements = true.
Proof. vm_compute. reflexivity. Qed.
'''
for name,xs in [('position',d),('distance',[b-a-1 for a,b in zip(d,c)])]:out+=f'Definition shared_load_wire_{name} index := nth 0%nat '+seq(xs)+' index.\n'
out+='Definition shared_load_wire_target index := nth 0 [::1477;1522;1712] index.\nDefinition shared_load_wire_source index := nth 0 [::8201;1477;1522] index.\n'
out+='''Lemma shared_load_wire_certificate index : (index < 3)%coq_nat ->
 declared_wire_check flat_memories flat_statements (shared_load_wire_position index) (shared_load_wire_distance index)
 (shared_load_wire_target index) (shared_load_wire_source index) 32 = true.
Proof. intros Bound. do 3 (destruct index as [|index]; [vm_compute;reflexivity|]). lia. Qed.
Local Opaque flat_statements flat_memories generated_modules generated_top.
'''
p=base/'staged-integration/SharedLoadInput.v';mark='(* Shared transport proofs. *)';tail=p.read_text().split(mark,1)[1] if p.exists() and mark in p.read_text() else '\n';p.write_text(out+mark+tail)
