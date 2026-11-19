"""Reuse existing connection certificates in the early-bubble control cone."""
from pathlib import Path
import json,re
root=Path(__file__).resolve().parents[2];base=root/'formal/flat-low';proof=base/'staged-integration'
model=(base/'CoreSocModel.v').read_text()
plan=json.loads((base/'early-bubble-stability-plan.json').read_text())
registers=set(map(int,re.findall(r'\(@Sreg VarOrder.T (\d+) ',model)))
snodes=set(map(int,re.findall(r'\(@Snode VarOrder.T (\d+) ',model)))
catalogs={name:(proof/(name+'.v')).read_text() for name in ['DataAddressConnectionCertificates','JointUpdateConnectionCertificates']}
header='''Require Import CoreSocModel ComparisonNodes FormalDeclaredConnectionCongruence DataAddressConnectionCertificates JointUpdateConnectionCertificates.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
'''
out=header;count=0
for row in plan['nodes']:
 n=row['id']
 if n in registers|snodes:continue
 assert len(row['dependencies'])==1,row
 source=row['dependencies'][0]
 driver=re.search(r'\(@Sfcnct VarOrder.T \(@Eid VarOrder.T '+str(n)+r'\) \(@Eref VarOrder.T \(@Eid VarOrder.T '+str(source)+r'\)\)\)',model)
 assert driver,n
 matches=[]
 for name,text in catalogs.items():
  matches.extend((name,m[1],int(m[2]),int(m[3])) for m in re.finditer(r'Lemma (\w+)_position\s*:\s*straight_drop (\d+) flat_statements = Some \(@Qcons VarOrder.T \(@Swire VarOrder.T '+str(n)+r' \(Gtyp \(Fuint (\d+)\)\)\)',text))
 assert len(matches)==1,(n,matches)
 _,prefix,pos,width=matches[0]
 out+=f'''Theorem early_control_wire_{n}_congruent invalid left right next_left next_right :
 VM.find {source} left = VM.find {source} right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find {n} next_left = VM.find {n} next_right.
Proof.
 intros Equal Left Right.
 exact (declared_connection_congruence {pos} flat_statements {prefix}_decl {prefix}_mid {prefix}_tail
 {n} {source} {width} invalid flat_memories left right next_left next_right
 {prefix}_position {prefix}_split {prefix}_straight {prefix}_mid_safe {prefix}_tail_safe
 {prefix}_nonregister (Logic.eq_refl _) Equal Left Right).
Qed.
Theorem early_control_wire_{n}_output invalid old current result :
 (exists ground bits, VM.find {source} old = Some (Gval ground bits)) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists bits, VM.find {n} result = Some (Gval (Fuint {width}) bits).
Proof. exact ({prefix}_output invalid old current result). Qed.
'''
 count+=1
out+='Print Assumptions early_control_wire_85_congruent.\nPrint Assumptions early_control_wire_1360_congruent.\nPrint Assumptions early_control_wire_1360_output.\n'
p=proof/'EarlyControlWireCongruence.v'
if not p.exists() or p.read_text()!=out:p.write_text(out)
print('Generated',count,'wire congruence/output pairs')
