"""Certify joint update nodes absent from existing address and writer certificates."""
import contextlib,io,json,re,runpy
from pathlib import Path
root=Path(__file__).resolve().parents[2];p=root/'formal/flat-low/staged-integration'
with contextlib.redirect_stdout(io.StringIO()):a=runpy.run_path(str(root/'scripts/audit-x0-concrete-cone.py'))
old=set()
for prior in ['data-address','data-writer']:
 old.update(r['id'] for r in json.loads((root/f'formal/flat-low/{prior}-dependency-ranks.json').read_text())['nodes'])
rows=json.loads((root/'formal/flat-low/joint-update-dependency-ranks.json').read_text())['nodes']
nodes={r['id']:a['drivers'][r['id']][0] for r in rows if r['id'] not in old and r['rank'] and a['drivers'][r['id']][0]['kind']=='Snode' and not a['drivers'][r['id']][0]['aggregate_reference']}
bodies={}
def write(n,s):
 f=p/n
 if not f.exists() or f.read_text()!=s:f.write_text(s)
header='''From Coq Require Import ZArith List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
'''
out='Require Import ConcreteExpressionClosure ConcreteScalarExpressions ConcreteGroundOperations.\n'+header
out+='''Ltac solve_joint_update_ready :=
 first [apply closure_scalar; solve [repeat first [eapply scalar_ready_ref; eassumption | apply scalar_ready_const | apply scalar_ready_unary | apply scalar_ready_binary | apply scalar_ready_cast]]
 | apply closure_mux; solve_joint_update_ready | apply closure_unary; solve_joint_update_ready | apply closure_binary; solve_joint_update_ready].
'''
def premises(n,refs):
 return ''.join(f' (exists ground bits, VM.find {r} old = Some (Gval '+('(Fuint ground)' if bodies.get(n)==r else 'ground')+' bits)) ->\n' for r in refs)
for n,e in sorted(nodes.items()):
 refs=e['dependencies']
 out+=f"Definition joint_update_expr_{n} : hfexpr VarOrder.T := {e['expression']}.\nLemma joint_update_ready_{n} old :\n"+premises(n,refs)+f' concrete_expression_ready old joint_update_expr_{n}.\nProof.\n'
 for r in refs:out+=f' intros [g{r} [b{r} H{r}]].\n'
 out+=f' unfold joint_update_expr_{n}.\n'
 if n in bodies:
  body=bodies[n]
  out+=f" eapply closure_validif with (width := g{body}); [solve_joint_update_ready|solve_joint_update_ready|].\n unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref]. rewrite H{body}. reflexivity.\n"
 elif 'Evalidif' in e['expression'] and not refs:out+=' eapply closure_validif with (width := 32%nat); [solve_joint_update_ready|solve_joint_update_ready|reflexivity].\n'
 else:
  assert 'Evalidif' not in e['expression'],n
  out+=' solve_joint_update_ready.\n'
 out+='Qed.\n'
write('JointUpdateExpressionCertificates.v',out)
model=(root/'formal/flat-low/CoreSocModel.v').read_text();positions=[]
for n in nodes:
 m=re.search(r'\(@Snode VarOrder.T '+str(n)+r' ',model);assert m
 positions.append((len(re.findall(r'\(@Qcons VarOrder.T ',model[:m.start()]))-1,n))
positions.sort();last=-1;offsets=[]
for pos,n in positions:offsets.append(pos-last-1);last=pos
out='Require Import CoreSocModel ComparisonNodes X0ConcretePositionCertificate X0ConcreteSafetyCertificate JointUpdateExpressionCertificates.\n'+header
out+='Definition joint_update_node_offsets : seq nat := [::'+';'.join(f'{v}%nat' for v in offsets)+'].\n'
out+='Definition joint_update_expected_nodes : seq (VarOrder.T * hfexpr VarOrder.T) := [::'+';'.join(f'({n},joint_update_expr_{n})' for _,n in positions)+'].\n'
out+='''Lemma joint_update_node_positions : select_node_offsets joint_update_node_offsets flat_statements = Some joint_update_expected_nodes.
Proof. vm_compute. reflexivity. Qed.
Lemma joint_update_node_safety : selected_node_safety flat_memories flat_statements joint_update_node_offsets flat_statements = true.
Proof. vm_compute. reflexivity. Qed.
'''
write('JointUpdateNodePositions.v',out)
indices={n:i for i,(_,n) in enumerate(positions)}
out='Require Import CoreSocModel ComparisonNodes SelectedNodeConcreteGroundOutput JointUpdateNodePositions JointUpdateExpressionCertificates.\n'+header+'Local Opaque flat_statements flat_memories generated_modules generated_top.\n'
for n,e in sorted(nodes.items()):
 refs=e['dependencies']
 out+=f'Lemma joint_update_node_output_{n} inputs path old current result :\n'+premises(n,refs)
 out+=' formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->\n'
 out+=f' exists ground bits, VM.find {n} result = Some (Gval ground bits).\nProof.\n intros '+' '.join(f'H{r}' for r in refs)+' Step.\n'
 out+=f''' eapply (selected_node_concrete_ground_output joint_update_node_offsets flat_statements joint_update_expected_nodes {n} joint_update_expr_{n} inputs path flat_memories old current result).
 - exact joint_update_node_positions.
 - exact joint_update_node_safety.
 - apply (@List.nth_error_In _ joint_update_expected_nodes {indices[n]} ({n},joint_update_expr_{n})). vm_compute. reflexivity.
 - apply joint_update_ready_{n}; assumption.
 - exact Step.
Qed.
'''
out+=f'Print Assumptions joint_update_node_output_{max(nodes)}.\n'
write('JointUpdateOutputCertificates.v',out)
print(f'Generated {len(nodes)} new scalar joint-update node certificates.')
