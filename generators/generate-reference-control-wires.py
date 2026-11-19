"""Actual typed wire observation and congruence for reference controls."""
from pathlib import Path
import json
root=Path(__file__).resolve().parents[2];base=root/'formal/flat-low';out=base/'staged-integration'
rows=[r for r in json.loads((base/'reference-control-stability-plan.json').read_text())['nodes'] if r['kind']=='Sfcnct']
header='''Require Import CoreSocModel ComparisonNodes FormalDeclaredConnection FormalDeclaredConnectionObservation FormalDeclaredConnectionCongruence FormalStatementSegments FormalTypedNodeFrames FormalTypedNodeEquation ScalarNodeFrames RegisterInvariants ScalarSinkTypes DataAddressConnectionCertificates JointUpdateConnectionCertificates.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
'''
for block in range(4):
 text=header
 for r in rows[block*12:(block+1)*12]:
  n=r['id'];src=r['dependencies'][0];w=r['width'];a=r['declaration_position'];b=r['position'];p=f'reference_control_wire_{n}'
  if n in [24,65]: c=f'joint_update_connection_{n}'
  elif n in [33,40,74,81]: c=f'data_address_connection_{n}'
  else:
   c=p
   text+=f'''Definition {c}_decl := match straight_drop {a+1} flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition {c}_mid := take_statements {b-a-1} {c}_decl.
Definition {c}_tail := match straight_drop {b+1} flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma {c}_position : straight_drop {a} flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T {n} (Gtyp (Fuint {w}))) {c}_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma {c}_split : {c}_decl = statement_append {c}_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T {n}) (@Eref VarOrder.T (@Eid VarOrder.T {src}))) {c}_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma {c}_straight : straight_statements {c}_mid.
Proof. vm_compute. exact I. Qed.
Lemma {c}_mid_safe : formal_typed_suffix_safe flat_memories {n} {c}_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma {c}_tail_safe : formal_typed_suffix_safe flat_memories {n} {c}_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma {c}_nonregister : has_register {n} flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
'''
  params=f'{a} flat_statements {c}_decl {c}_mid {c}_tail {n} {src} {w}'
  cert=f'{c}_position {c}_split {c}_straight {c}_mid_safe {c}_tail_safe {c}_nonregister (Logic.eq_refl _)'
  text+=f'''Theorem {p}_congruent invalid left right next_left next_right :
 VM.find {src} left = VM.find {src} right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find {n} next_left = VM.find {n} next_right.
Proof. exact (declared_connection_congruence {params} invalid flat_memories left right next_left next_right {cert}). Qed.
Theorem {p}_ground invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find {n} result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intro Step. destruct (declared_connection_observation {params} invalid flat_memories old current result {cert} Step)
 as [source [value [Source [Adapt Value]]]].
 exists value, (Fuint {w}). split; [exact Value|]. exact (adapted_uint_result_type source {w} value Adapt).
Qed.
'''
  # Escape is followed by a space (not a physical newline) in the conjunction above.
 pth=out/f'ReferenceControlWires{block}.v'
 if not pth.exists() or pth.read_text()!=text:pth.write_text(text)
print('generated',len(rows),'typed wire interfaces in 4 blocks')
