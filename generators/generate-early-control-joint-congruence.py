"""Reuse existing joint-update certificates for early-control node congruence."""
from pathlib import Path
import json,re
root=Path(__file__).resolve().parents[2];base=root/'formal/flat-low';proof=base/'staged-integration'
plan=json.loads((base/'early-bubble-stability-plan.json').read_text())
rows={r['id']:r for r in plan['nodes']}
ids=list(map(int,re.findall(r'\((\d+),joint_update_expr_', (proof/'JointUpdateNodePositions.v').read_text())))
out='''Require Import CoreSocModel ComparisonNodes SelectedGroundNodeCongruence SelectedNodeSafety JointUpdateExpressionCertificates JointUpdateNodePositions ConcreteExpressionClosure.
From Coq Require Import ZArith List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
'''
for n in plan['certificate_coverage']['joint']:
 deps=rows[n]['dependencies'];expr=f'joint_update_expr_{n}'
 out+=f'Lemma early_control_joint_member_{n} : List.In ({n},{expr}) joint_update_expected_nodes.\nProof. apply (List.nth_error_In joint_update_expected_nodes {ids.index(n)}%nat). vm_compute. reflexivity. Qed.\n'
 out+=f'Theorem early_control_node_{n}_congruent inputs path left right next_left next_right :\n'
 for d in deps:out+=f' (exists ground bits, VM.find {d} left = Some (Gval ground bits)) ->\n'
 for d in deps:out+=f' VM.find {d} left = VM.find {d} right ->\n'
 out+=''' formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
'''+f' VM.find {n} next_left = VM.find {n} next_right.\nProof.\n intros '+' '.join(f'H{d}' for d in deps)+' '+' '.join(f'E{d}' for d in deps)+' L R.\n'
 out+=f''' destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes {n} {expr} joint_update_node_positions joint_update_node_safety early_control_joint_member_{n})
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_ground_node_congruent count tail {n} {expr} (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [{expr} eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
'''
 for d in deps:out+=f'   rewrite E{d}.\n'
 out+='   reflexivity.\n - intros site value Eval.\n'
 out+=f'   destruct (concrete_expression_closure inputs path flat_memories left {expr} (joint_update_ready_{n} left '+' '.join(f'H{d}' for d in deps)+') site value Eval) as [ground [bits Value]].\n'
 out+='   subst value. exists ground. reflexivity.\n - exact L.\n - exact R.\nQed.\n'
out+='Print Assumptions early_control_node_7944_congruent.\n' if 7944 in plan['certificate_coverage']['joint'] else ''
p=proof/'EarlyControlJointCongruence.v'
if not p.exists() or p.read_text()!=out:p.write_text(out)
print('Generated',len(plan['certificate_coverage']['joint']),'joint-update congruence lemmas')
