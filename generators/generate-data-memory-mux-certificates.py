"""Certify four actual RAM bypass mux outputs in the flattened model."""
from pathlib import Path
import re
root=Path(__file__).resolve().parents[2]; p=root/'formal/flat-low/staged-integration'
model=(root/'formal/flat-low/CoreSocModel.v').read_text()
rows=[(9187,2,9185),(9195,3,9193),(9203,4,9201),(9211,5,9209)]
positions=[]
for node,port,condition in rows:
 m=re.search(r'\(@Snode VarOrder.T '+str(node)+r' ',model); assert m
 positions.append(len(re.findall(r'\(@Qcons VarOrder.T ',model[:m.start()]))-1)
last=-1; offsets=[]
for pos in positions: offsets.append(pos-last-1);last=pos
out='''Require Import CoreSocModel ComparisonNodes ConcreteDataReaderMux ConcreteMemoryRead X0ConcretePositionCertificate X0ConcreteSafetyCertificate SelectedNodeConcreteEvaluation.
From Coq Require Import ZArith List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
'''
for node,port,c in rows:
 out+=f'Definition data_memory_mux_expr_{node} : hfexpr VarOrder.T := @Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T {c})) (@Eref VarOrder.T (@Eid VarOrder.T 38)) (data_reader_expression {port}).\n'
out+='Definition data_memory_mux_offsets : seq nat := [::'+';'.join(f'{n}%nat' for n in offsets)+'].\n'
out+='Definition data_memory_mux_nodes : seq (VarOrder.T * hfexpr VarOrder.T) := [::'+';'.join(f'({n},data_memory_mux_expr_{n})' for n,_,_ in rows)+'].\n'
out+='''Lemma data_memory_mux_positions : select_node_offsets data_memory_mux_offsets flat_statements = Some data_memory_mux_nodes.
Proof. vm_compute. reflexivity. Qed.
Lemma data_memory_mux_safety : selected_node_safety flat_memories flat_statements data_memory_mux_offsets flat_statements = true.
Proof. vm_compute. reflexivity. Qed.
Local Opaque flat_statements flat_memories generated_modules generated_top.
'''
for i,(n,port,c) in enumerate(rows):
 out+=f'''Theorem data_memory_mux_output_{n} inputs path old current result values address width :
 VM.find 9179 old = Some (Aval (Gtyp (Fuint 32)) values) ->
 concrete_uint_array 32 values ->
 read_memory_port_field old 9178 {port} 1 = Some (Gval (Fuint 1) [::true]) ->
 read_memory_port_field old 9178 {port} 0 = Some (Gval (Fuint width) address) ->
 (exists ground bits, VM.find {c} old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 38 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists ground bits, VM.find {n} result = Some (Gval ground bits).
Proof.
 intros Storage Concrete Enable Address [cg [cb Condition]] [sg [sb Source]] Step.
 eapply (selected_node_from_concrete_evaluation data_memory_mux_offsets flat_statements data_memory_mux_nodes {n} data_memory_mux_expr_{n} inputs path flat_memories old current result).
 - exact data_memory_mux_positions.
 - exact data_memory_mux_safety.
 - apply (@List.nth_error_In _ data_memory_mux_nodes {i} ({n},data_memory_mux_expr_{n})). vm_compute. reflexivity.
 - intros location value Eval. unfold data_memory_mux_expr_{n} in Eval.
   eapply data_reader_mux_concrete; [|exact Storage|exact Concrete|exact Enable|exact Address|exact Condition|exact Source|exact Eval].
   do {port-1} right. left. reflexivity.
 - exact Step.
Qed.
'''
out+='Print Assumptions data_memory_mux_output_9211.\n'
f=p/'DataMemoryMuxCertificates.v'
if not f.exists() or f.read_text()!=out:f.write_text(out)
