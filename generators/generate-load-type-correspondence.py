"""Verify Scala ld_type table against fixed flattened nodes; preserve proof tail."""
from pathlib import Path
import re,bisect
root=Path(__file__).resolve().parents[2];base=root/'formal/flat-low';model=(base/'CoreSocModel.v').read_text()
nodes={}
for m in re.finditer(r'\(@Snode VarOrder.T (\d+) ',model):
 a=m.end();depth=0
 for b in range(a,len(model)):
  depth+=(model[b]=='(')-(model[b]==')')
  if depth==0:break
 nodes[int(m[1])]=model[a:b+1]
def constant(n):
 bits=re.search(r'\[::([^]]*)\]',nodes[n])[1]
 return sum((b.strip()=='true')<<i for i,b in enumerate(bits.split(';')))
values=[constant(8801-i) for i in range(49)]
control=(root/'src/main/scala/mini/Control.scala').read_text();constants={n:int(v) for n,v in re.findall(r'val (\w+) = (\d+)\.U',control)}
scala=[constants[fields.split(',')[8].strip()] for name,fields in re.findall(r'(\w+)\s*-> List\(([^\n]+)\)',control)]
assert values==scala,(values,scala)
ids=list(map(int,re.findall(r'\((\d+),writer_expr_', (base/'staged-integration/DataWriterNodePositions.v').read_text())))
indices=[ids.index(8801-i) for i in range(49)]
q=[m.start() for m in re.finditer(r'\(@Qcons VarOrder.T ',model)]
pos=lambda t:bisect.bisect_right(q,model.index(t))-1
out='''Require Import DataWriterNodePositions DataWriterExpressionCertificates DUTRedirectDecode CoreSocModel ComparisonNodes FormalDeclaredWireCheck JointUpdateNodePositions JointUpdateExpressionCertificates ReferenceRedirectSpine JointBoundaryRegisters JointUpdateBoundaryHistory FormalPCDecodeInputConnections.
From Coq Require Import NArith ZArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
'''
out+='Definition load_type_values : seq N := [::'+';'.join(map(str,values))+'].\n'
out+='Definition load_type_indices : seq nat := [::'+';'.join(str(i)+'%nat' for i in indices)+'].\n'
for target,source in [(8258,8801),(92,8258)]:
 d=pos(f'(@Swire VarOrder.T {target} ');c=pos(f'(@Sfcnct VarOrder.T (@Eid VarOrder.T {target}) (@Eref VarOrder.T (@Eid VarOrder.T {source})))')
 out+=f'''Lemma load_type_wire_{target}_checked : declared_wire_check flat_memories flat_statements {d}%nat {c-d-1}%nat {target} {source} 3%nat = true.
Proof. vm_compute. reflexivity. Qed.
'''
out+='Local Opaque flat_statements flat_memories generated_modules generated_top.\n'
p=base/'staged-integration/LoadTypeCorrespondence.v';mark='(* Load type decode and pipeline correspondence. *)';tail=p.read_text().split(mark,1)[1] if p.exists() and mark in p.read_text() else '\n';p.write_text(out+mark+tail)
print('Verified all 49 Scala ld_type rows and actual mux certificate indices.')
