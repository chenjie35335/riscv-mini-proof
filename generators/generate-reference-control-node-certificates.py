from pathlib import Path
import json
root=Path(__file__).resolve().parents[2];base=root/'formal/flat-low';proof=base/'staged-integration'
rows=json.loads((base/'reference-control-stability-plan.json').read_text())['nodes'];nodes=sorted([r for r in rows if r['kind']=='Snode'],key=lambda r:r['position'])
header='''Require Import CoreSocModel ComparisonNodes.
From Coq Require Import ZArith List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
'''
def write(name,s):
 p=proof/(name+'.v')
 if not p.exists() or p.read_text()!=s:p.write_text(s)
write('ReferenceControlExpressions',header+''.join(f"Definition reference_control_expr_{r['id']} := {r['expression']}.\n" for r in nodes))
for block in range(4):
 chunk=nodes[block*300:(block+1)*300];last=-1;offset=[]
 for r in chunk:offset.append(r['position']-last-1);last=r['position']
 name=f'reference_control_{block}'
 s=header+'Require Import X0ConcretePositionCertificate X0ConcreteSafetyCertificate ReferenceControlExpressions.\n'
 s+=f'Definition {name}_offsets : seq nat := [::'+ ';'.join(str(n)+'%nat' for n in offset)+'].\n'
 s+=f'Definition {name}_nodes : seq (VarOrder.T * hfexpr VarOrder.T) := [::'+ ';'.join(f"({r['id']},reference_control_expr_{r['id']})" for r in chunk)+'].\n'
 s+=f'''Lemma {name}_positions : select_node_offsets {name}_offsets flat_statements = Some {name}_nodes.
Proof. vm_compute. reflexivity. Qed.
Lemma {name}_safety : selected_node_safety flat_memories flat_statements {name}_offsets flat_statements = true.
Proof. vm_compute. reflexivity. Qed.
'''
 write(f'ReferenceControlNodeCertificates{block}',s)
print('generated',len(nodes),'expressions and 4 certificate blocks')
