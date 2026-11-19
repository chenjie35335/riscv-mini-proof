"""Batched ground propagation for scalar joint-register update sources."""
import contextlib,io,json,runpy
from pathlib import Path
root=Path(__file__).resolve().parents[2];p=root/'formal/flat-low/staged-integration'
with contextlib.redirect_stdout(io.StringIO()):a=runpy.run_path(str(root/'scripts/audit-x0-concrete-cone.py'))
rows=json.loads((root/'formal/flat-low/joint-update-dependency-ranks.json').read_text())['nodes']
address={r['id'] for r in json.loads((root/'formal/flat-low/data-address-dependency-ranks.json').read_text())['nodes']}
writer={r['id'] for r in json.loads((root/'formal/flat-low/data-writer-dependency-ranks.json').read_text())['nodes']}
out='''Require Import CoreSocModel ComparisonNodes JointUpdateDependencyRanks JointUpdateOutputCertificates JointUpdateConnectionCertificates DataAddressOutputCertificates DataAddressConnectionCertificates DataAddressUnaryConnection DataWriterOutputCertificates DataWriterConnectionCertificates CheckedDependencyHistory FormalFlatInvalidWire JointUpdateConstantWire.
From Coq Require Import ZArith List Arith Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Definition joint_update_ground_at (env : VM.t hvalue) (node : nat) :=
 exists ground bits, VM.find (N.of_nat node) env = Some (Gval ground bits).
Definition joint_update_transfer old result entry := let '(node,(rank,dependencies)) := entry in
 (0 < rank)%coq_nat ->
 (forall source, List.In source dependencies -> joint_update_ground_at old source) ->
 joint_update_ground_at result node.
'''
pre=''' (exists width bits, VM.find (N.of_nat 851) old = Some (Gval (Fuint width) bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
'''
chunks=[rows[i:i+24] for i in range(0,len(rows),24)]
for i,chunk in enumerate(chunks):
 name=f'joint_update_chunk_{i}'
 out+=f'Definition {name} : list (nat * (nat * list nat)) := [::'+';'.join(f"({r['id']},({r['rank']},[::"+';'.join(map(str,r['dependencies']))+']))' for r in chunk)+'].\n'
 out+=f'Lemma {name}_transfers inputs path old current result :\n'+pre+f' List.Forall (joint_update_transfer old result) {name}.\nProof.\n intros Typed851 Step. unfold {name}.\n'
 for r in chunk:
  n,ds=r['id'],r['dependencies'];out+=' constructor.\n { unfold joint_update_transfer. intros Positive Sources.\n'
  if not r['rank']:out+='   lia. }\n';continue
  e=a['drivers'][n][0]
  for j,d in enumerate(ds):
   out+=f'   pose proof (Sources {d} ltac:(do {j} right; left; reflexivity)) as S{d}.\n'
  out+='   unfold joint_update_ground_at.\n'
  prefix='data_address' if n in address else ('data_writer' if n in writer else 'joint_update')
  if e['kind']=='Snode':
   assert 'Evalidif' not in e['expression'] or n in [884,919] or not ds,n
   args=' '.join('Typed851' if n in [884,919] and d==851 else f'S{d}' for d in ds)
   out+=f'   exact ({prefix}_node_output_{n} inputs path old current result {args} Step). }}\n'
  elif n==25:
   out+='   do 2 eexists. exact (joint_constant_wire_25_output (formal_invalid_policy inputs path) old current result Step). }\n'
  elif e['kind']=='Sinvalid':
   out+=f'   destruct (flat_invalid_wire_{n}_concrete inputs path old current result Step) as [bits [Value Size]].\n   do 2 eexists; exact Value. }}\n'
  else:
   out+=f'   destruct ({prefix}_connection_{n}_output (formal_invalid_policy inputs path) old current result S{ds[0]} Step) as [bits Value].\n   do 2 eexists; exact Value. }}\n'
 out+=' constructor.\nQed.\n'
out+='Theorem joint_update_dependency_transfers inputs path old current result :\n'+pre+' List.Forall (joint_update_transfer old result) joint_update_dependency_ranks.\nProof.\n intros Typed851 Step.\n'
expr='[::]'
for i in reversed(range(len(chunks))):expr=f'(List.app joint_update_chunk_{i} {expr})'
out+=f' change (List.Forall (joint_update_transfer old result) {expr}).\n'
for i in range(len(chunks)):out+=f' apply List.Forall_app. split; [exact (joint_update_chunk_{i}_transfers inputs path old current result Typed851 Step)|].\n'
out+=' constructor.\nQed.\n'
out+='''Theorem joint_update_ground_history inputs path history limit :
 (forall time node dependencies, (time <= limit)%coq_nat ->
 List.In (node,(0%nat,dependencies)) joint_update_dependency_ranks -> joint_update_ground_at (history time) node) ->
 (forall time, (time < limit)%coq_nat -> exists width bits,
 VM.find (N.of_nat 851) (history time) = Some (Gval (Fuint width) bits)) ->
 (forall time, (time < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path)
 flat_memories (history time) false (history time) flat_statements = Some (history (S time))) ->
 forall time node rank dependencies, (time <= limit)%coq_nat ->
 List.In (node,(rank,dependencies)) joint_update_dependency_ranks -> (rank <= time)%coq_nat ->
 joint_update_ground_at (history time) node.
Proof.
 intros Boundary Typed851 Steps.
 apply (checked_dependency_history joint_update_dependency_ranks (fun time node => joint_update_ground_at (history time) node) limit joint_update_dependency_ranks_checked Boundary).
 intros time node rank dependencies Within Member Positive Sources.
 pose proof (joint_update_dependency_transfers inputs path (history time) (history time) (history (S time)) (Typed851 time Within) (Steps time Within)) as Transfers.
 rewrite List.Forall_forall in Transfers.
 exact (Transfers (node,(rank,dependencies)) Member Positive Sources).
Qed.
Print Assumptions joint_update_ground_history.
'''
f=p/'JointUpdateGraphPropagation.v'
if not f.exists() or f.read_text()!=out:f.write_text(out)
print(f'Generated {len(rows)} semantic transfers in {len(chunks)} batches.')
