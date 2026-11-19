"""Batched mixed-ground/UInt semantic propagation with explicit RAM premises."""
import contextlib,io,json,re,runpy
from pathlib import Path
root=Path(__file__).resolve().parents[2];p=root/'formal/flat-low/staged-integration'
with contextlib.redirect_stdout(io.StringIO()):a=runpy.run_path(str(root/'scripts/audit-x0-concrete-cone.py'))
rows=json.loads((root/'formal/flat-low/data-writer-dependency-ranks.json').read_text())['nodes']
old={r['id'] for r in json.loads((root/'formal/flat-low/data-address-dependency-ranks.json').read_text())['nodes']}
strong={9214,9224,9225,9227,9228,9229,9230,9232,9233,9234}
bodies={884:851,919:851,9225:9224,9229:9214,9230:9225,9233:9228,9234:9229}
mem={9187:2,9195:3,9203:4,9211:5}
out='''Require Import CoreSocModel ComparisonNodes DataWriterDependencyRanks DataAddressOutputCertificates DataAddressConnectionCertificates DataAddressUnaryConnection DataWriterOutputCertificates DataWriterConnectionCertificates DataWriterUIntOutputs DataMemoryMuxCertificates ConcreteMemoryRead CheckedDependencyHistory.
From Coq Require Import ZArith List Arith Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Definition writer_uint_required (node : nat) := List.existsb (N.eqb (N.of_nat node))
 [::'''+ ';'.join(f'N.of_nat {n}' for n in sorted(strong|{851}))+'''].
Definition writer_concrete_at (env : VM.t hvalue) (node : nat) : Prop :=
 if writer_uint_required node then exists width bits, VM.find (N.of_nat node) env = Some (Gval (Fuint width) bits)
 else exists ground bits, VM.find (N.of_nat node) env = Some (Gval ground bits).
Lemma writer_concrete_ground env node : writer_concrete_at env node ->
 exists ground bits, VM.find (N.of_nat node) env = Some (Gval ground bits).
Proof.
 unfold writer_concrete_at. destruct (writer_uint_required node); intro Value; [|exact Value].
 destruct Value as [width [bits Value]]. exists (Fuint width), bits. exact Value.
Qed.
Definition writer_memory_ready env := exists values,
 VM.find (N.of_nat 9179) env = Some (Aval (Gtyp (Fuint 32)) values) /\\
 concrete_uint_array 32 values /\\
 forall port, List.In port [::N.of_nat 2;N.of_nat 3;N.of_nat 4;N.of_nat 5] ->
 read_memory_port_field env (N.of_nat 9178) port (N.of_nat 1) = Some (Gval (Fuint 1) [::true]) /\\
 exists width address, read_memory_port_field env (N.of_nat 9178) port (N.of_nat 0) = Some (Gval (Fuint width) address).
Definition writer_transfer old result entry := let '(node,(rank,dependencies)) := entry in
 (0 < rank)%coq_nat ->
 (forall source, List.In source dependencies -> writer_concrete_at old source) ->
 writer_concrete_at result node.
'''
chunks=[rows[i:i+24] for i in range(0,len(rows),24)]
pre=''' writer_memory_ready old ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
'''
for chunk_index,chunk in enumerate(chunks):
 name=f'data_writer_chunk_{chunk_index}'
 out+=f'Definition {name} : list (nat * (nat * list nat)) := [::'+ ';'.join(f"({r['id']},({r['rank']},[::"+';'.join(map(str,r['dependencies']))+']))' for r in chunk)+'].\n'
 out+=f'Lemma {name}_transfers inputs path old current result :\n'+pre+f' List.Forall (writer_transfer old result) {name}.\nProof.\n intros Memory Step. unfold {name}.\n'
 for row in chunk:
  n,ds=row['id'],row['dependencies']
  out+=' constructor.\n { unfold writer_transfer. intros Positive Sources.\n'
  if row['rank']==0:out+='   lia. }\n';continue
  for i,d in enumerate(ds):
   out+=f'   pose proof (Sources {d} ltac:(do {i} right; left; reflexivity)) as S{d}.\n'
   if bodies.get(n)!=d:out+=f'   apply writer_concrete_ground in S{d}.\n'
  out+='   change (exists '+('width bits, VM.find (N.of_nat '+str(n)+') result = Some (Gval (Fuint width) bits)).\n' if n in strong else 'ground bits, VM.find (N.of_nat '+str(n)+') result = Some (Gval ground bits)).\n')
  if n in mem:
   port=mem[n];condition=n-2
   out+='   destruct Memory as [values [Storage [Concrete Ports]]].\n'
   out+=f'   destruct (Ports (N.of_nat {port}) ltac:(do {port-2} right; left; reflexivity)) as [Enable [width [address Address]]].\n'
   out+=f'   exact (data_memory_mux_output_{n} inputs path old current result values address width Storage Concrete Enable Address S{condition} S38 Step). }}\n'
  elif a['drivers'][n][0]['kind']=='Snode':
   prefix='data_writer_uint_output_' if n in strong else ('data_address_node_output_' if n in old else 'data_writer_node_output_')
   out+=f'   exact ({prefix}{n} inputs path old current result '+' '.join(f'S{d}' for d in ds)+' Step). }\n'
  else:
   prefix='data_address_connection_' if n in old else 'data_writer_connection_'
   out+=f'   destruct ({prefix}{n}_output (formal_invalid_policy inputs path) old current result S{ds[0]} Step) as [bits Value].\n   do 2 eexists; exact Value. }}\n'
 out+=' constructor.\nQed.\n'
out+='Theorem data_writer_dependency_transfers inputs path old current result :\n'+pre+' List.Forall (writer_transfer old result) data_writer_dependency_ranks.\nProof.\n intros Memory Step.\n'
expr='[::]'
for i in reversed(range(len(chunks))):expr=f'(List.app data_writer_chunk_{i} {expr})'
out+=f' change (List.Forall (writer_transfer old result) {expr}).\n'
for i in range(len(chunks)):
 out+=f' apply List.Forall_app. split; [exact (data_writer_chunk_{i}_transfers inputs path old current result Memory Step)|].\n'
out+=' constructor.\nQed.\n'
out+='''Theorem data_writer_concrete_history inputs path history limit :
 (forall time node dependencies, (time <= limit)%coq_nat ->
 List.In (node,(0%nat,dependencies)) data_writer_dependency_ranks -> writer_concrete_at (history time) node) ->
 (forall time, (time < limit)%coq_nat -> writer_memory_ready (history time)) ->
 (forall time, (time < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path)
 flat_memories (history time) false (history time) flat_statements = Some (history (S time))) ->
 forall time node rank dependencies, (time <= limit)%coq_nat ->
 List.In (node,(rank,dependencies)) data_writer_dependency_ranks -> (rank <= time)%coq_nat ->
 writer_concrete_at (history time) node.
Proof.
 intros Boundary Memory Steps.
 apply (checked_dependency_history data_writer_dependency_ranks (fun time node => writer_concrete_at (history time) node) limit data_writer_dependency_ranks_checked Boundary).
 intros time node rank dependencies Within Member Positive Sources.
 pose proof (data_writer_dependency_transfers inputs path (history time) (history time) (history (S time)) (Memory time Within) (Steps time Within)) as Transfers.
 rewrite List.Forall_forall in Transfers.
 exact (Transfers (node,(rank,dependencies)) Member Positive Sources).
Qed.
Print Assumptions data_writer_concrete_history.
'''
f=p/'DataWriterGraphPropagation.v'
if not f.exists() or f.read_text()!=out:f.write_text(out)
print(f'Generated {len(rows)} transfers in {len(chunks)} checked batches.')
