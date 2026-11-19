"""Compose exact transfers and congruences over shared actual histories."""
import json,re
from pathlib import Path
root=Path(__file__).resolve().parents[2];base=root/'formal/flat-low'
entries=json.loads((base/'exception-stability-cone.json').read_text())['nodes']
s=(base/'staged-integration/JointBoundaryRegisters.v').read_text().split('Lemma joint_boundary_register_check',1)[0]
joint=[tuple(map(int,x)) for x in re.findall(r'\((\d+),(\d+)\)',s)]
header='''Require Import CoreSocModel ComparisonNodes ExceptionNodeCongruence ExceptionWireCongruence JointBoundaryRegisters JointUpdateBoundaryHistory ConcreteRegisterInitialization X0ConcreteOutputCertificates X0ConcreteConnectionOutputs.
From Coq Require Import ZArith List Lia PeanoNat.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
'''
common=''' (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
'''
out=header
for e in entries:
 n,r,kind=e['id'],e['rank'],e['kind']
 if kind=='register':
  w=next(w for node,w in joint if node==n)
  out+=f'''Lemma exception_member_{n} : List.In ({n}%nat,{w}%nat) joint_boundary_registers.
Proof. apply (List.nth_error_In joint_boundary_registers {joint.index((n,w))}). vm_compute. reflexivity. Qed.
'''
 out+=f'Theorem exception_concrete_{n}_history inputs path history limit :\n'+common+fr''' forall time, ({r} <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find {n} (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
'''
 if kind=='register':
  out+=f''' rewrite (joint_update_register_history_same _ history limit {n} {w} exception_member_{n} Steps time Upper).
 destruct (Boundary {n}%nat {w}%nat exception_member_{n}) as [bits [Size Lookup]].
 exists {w}%nat, bits. exact Lookup.
'''
 else:
  out+=' destruct time as [|time]; [lia|].\n'
  call=f'x0_node_output_{n} inputs path' if kind=='Snode' else f'x0_connection_output_{n} (formal_invalid_policy inputs path)'
  out+=f' apply ({call} (history time) (history time) (history (S time))).\n'
  for d in e['dependencies']:out+=f' - apply (exception_concrete_{d}_history inputs path history limit Boundary Steps time); lia.\n'
  out+=(' - ' if e['dependencies'] else ' ')+'apply Steps. lia.\n'
 out+='Qed.\n'
 out+=f'Theorem exception_stable_{n}_history inputs path history limit :\n'+common+f''' forall t u, ({r} <= t)%coq_nat -> ({r} <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find {n} (history t) = VM.find {n} (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
'''
 if kind=='register':
  out+=f''' rewrite (joint_update_register_history_same _ history limit {n} {w} exception_member_{n} Steps t UT).
 rewrite (joint_update_register_history_same _ history limit {n} {w} exception_member_{n} Steps u UU). reflexivity.
'''
 else:
  out+=' destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].\n'
  label='node' if kind=='Snode' else 'wire'
  out+=f' apply (exception_{label}_{n}_congruent (formal_invalid_policy inputs path) (history t) (history u) (history (S t)) (history (S u))).\n'
  if kind=='Snode':
   for d in e['dependencies']:out+=f' - apply (exception_concrete_{d}_history inputs path history limit Boundary Steps t); lia.\n'
  for d in e['dependencies']:out+=f' - apply (exception_stable_{d}_history inputs path history limit Boundary Steps t u); lia.\n'
  out+=' - apply Steps. lia.\n - apply Steps. lia.\n'
 out+='Qed.\n'
out+='Print Assumptions exception_stable_128_history.\n'
p=base/'staged-integration/ExceptionStabilityHistory.v'
if not p.exists() or p.read_text()!=out:p.write_text(out)
