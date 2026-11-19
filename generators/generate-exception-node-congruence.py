"""Reuse x0 expression/type/position certificates for source128 stability."""
import json,re
from pathlib import Path
root=Path(__file__).resolve().parents[2];base=root/'formal/flat-low'
entries=json.loads((base/'exception-stability-cone.json').read_text())['nodes']
s=(base/'staged-integration/X0ConcretePositionCertificate.v').read_text()
ids=list(map(int,re.findall(r'\(N.of_nat (\d+), x0_concrete_expr_',s)))
out='''Require Import CoreSocModel ComparisonNodes SelectedUIntNodeCongruence X0ConcreteExpressionCertificates X0UIntExpressionCertificates X0ConcretePositionCertificate.
From Coq Require Import ZArith List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
'''
for e in entries:
 if e['kind']!='Snode':continue
 n=e['id'];deps=e['dependencies']
 out+=f'Theorem exception_node_{n}_congruent invalid left right next_left next_right :\n'
 for d in deps:out+=f' (exists width bits, VM.find {d} left = Some (Gval (Fuint width) bits)) ->\n'
 for d in deps:out+=f' VM.find {d} left = VM.find {d} right ->\n'
 out+=f''' formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find {n} next_left = VM.find {n} next_right.
Proof.
 intros '''+' '.join(f'H{d}' for d in deps)+' '+' '.join(f'E{d}' for d in deps)+f''' L R.
 apply (x0_selected_uint_node_congruent {n} x0_concrete_expr_{n} invalid left right next_left next_right).
 - apply (List.nth_error_In x0_expected_nodes {ids.index(n)}). vm_compute. reflexivity.
 - intro site. cbn [x0_concrete_expr_{n} eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
'''
 out+="   try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].\n"
 for d in deps:out+=f'   rewrite E{d}.\n'
 out+='   reflexivity.\n - intros site value Eval.\n'
 out+=f'   destruct (x0_uint_result_{n} invalid site flat_memories left value '+' '.join(f'H{d}' for d in deps)+' Eval) as [width [bits Value]].\n'
 out+='   subst value. exists width. reflexivity.\n - exact L.\n - exact R.\nQed.\n'
out+='Print Assumptions exception_node_442_congruent.\n'
p=base/'staged-integration/ExceptionNodeCongruence.v'
if not p.exists() or p.read_text()!=out:p.write_text(out)
