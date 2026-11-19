"""Reuse existing data-address certificates for early-control node congruence."""
from pathlib import Path
import json,re
root=Path(__file__).resolve().parents[2];base=root/'formal/flat-low';proof=base/'staged-integration'
plan=json.loads((base/'early-bubble-stability-plan.json').read_text())
rows={r['id']:r for r in plan['nodes']}
ids=list(map(int,re.findall(r'\(N.of_nat (\d+), address_expr_', (proof/'DataAddressPositionCertificate.v').read_text())))
out='''Require Import CoreSocModel ComparisonNodes SelectedUIntNodeCongruenceGeneral SelectedNodeSafety DataAddressExpressionCertificates DataAddressUIntCertificates DataAddressPositionCertificate DataAddressSafetyCertificate.
From Coq Require Import ZArith List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
'''
for n in plan['certificate_coverage']['data']:
 deps=rows[n]['dependencies'];expr=f'address_expr_{n}'
 out+=f'Lemma early_control_data_member_{n} : List.In ({n},{expr}) data_address_expected_nodes.\nProof. apply (List.nth_error_In data_address_expected_nodes {ids.index(n)}%nat). vm_compute. reflexivity. Qed.\n'
 out+=f'Theorem early_control_node_{n}_congruent inputs path left right next_left next_right :\n'
 for d in deps:out+=f' (exists width bits, VM.find {d} left = Some (Gval (Fuint width) bits)) ->\n'
 for d in deps:out+=f' VM.find {d} left = VM.find {d} right ->\n'
 out+=''' formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
'''+f' VM.find {n} next_left = VM.find {n} next_right.\nProof.\n intros '+' '.join(f'H{d}' for d in deps)+' '+' '.join(f'E{d}' for d in deps)+' L R.\n'
 out+=f''' destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes {n} {expr} data_address_actual_node_expressions data_address_actual_nodes_safe early_control_data_member_{n})
 as [count [tail [Position [Safe Nonreg]]]].
 apply (selected_uint_node_congruent count tail {n} {expr} (formal_invalid_policy inputs path) left right next_left next_right Position Safe Nonreg).
 - intro site. cbn [{expr} eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
'''
 for d in deps:out+=f'   rewrite E{d}.\n'
 out+='   reflexivity.\n - intros site value Eval.\n'
 out+=f'   destruct (address_uint_result_{n} inputs path site flat_memories left value '+' '.join(f'H{d}' for d in deps)+' Eval) as [width [bits Value]].\n'
 out+='   subst value. exists width. reflexivity.\n - exact L.\n - exact R.\nQed.\n'
out+='Print Assumptions early_control_node_884_congruent.\nPrint Assumptions early_control_node_919_congruent.\n'
p=proof/'EarlyControlDataCongruence.v'
if not p.exists() or p.read_text()!=out:p.write_text(out)
print('Generated',len(plan['certificate_coverage']['data']),'data-address congruence lemmas')
