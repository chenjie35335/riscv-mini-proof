"""Stronger UInt outputs needed by validif bodies and final writer ports."""
from pathlib import Path
import contextlib,io,runpy,re
root=Path(__file__).resolve().parents[2];p=root/'formal/flat-low/staged-integration'
with contextlib.redirect_stdout(io.StringIO()):a=runpy.run_path(str(root/'scripts/audit-x0-concrete-cone.py'))
nodes=[9214,9224,9225,9227,9228,9229,9230,9232,9233,9234]
bodies={9225:9224,9229:9214,9230:9225,9233:9228,9234:9229}
positions=[int(n) for n in re.findall(r'\((\d+),writer_expr_', (p/'DataWriterNodePositions.v').read_text())]
out='''Require Import CoreSocModel ComparisonNodes DataWriterExpressionCertificates DataWriterNodePositions SelectedNodeConcreteOutput ConcreteGroundOrUInt ConcreteExtractNode ConcreteGroundConditionValidIf ConcreteUIntOperations ConcreteUIntScalarExpressions ConcreteScalarExpressions.
From Coq Require Import ZArith List.
From mathcomp Require Import ssreflect ssrbool ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From nbits Require Import NBits.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
'''
def pre(n,refs):return ''.join(f' (exists ground bits, VM.find {r} old = Some (Gval '+('(Fuint ground)' if bodies.get(n)==r else 'ground')+' bits)) ->\n' for r in refs)
for n in nodes:
 refs=a['drivers'][n][0]['dependencies']
 out+=f'Lemma writer_uint_result_{n} inputs path site mm old result :\n'+pre(n,refs)
 out+=f' eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm writer_expr_{n} old old = Some result -> concrete_uint_value result.\nProof.\n'
 for r in refs:out+=f' intros [g{r} [b{r} H{r}]].\n'
 if n in bodies or n==9228:
  body=bodies.get(n);width=f'g{body}' if body else '1%nat'
  out+=f' unfold writer_expr_{n}. eapply formal_ground_condition_uint_validif with (width := {width}).\n'
  out+=' - eapply scalar_ready_ref; eassumption.\n'
  out+=' - '+('eapply uint_ready_ref; eassumption.' if body else 'apply uint_ready_const.')+'\n'
  out+=f" - unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref]. "+(f'rewrite H{body}. ' if body else '')+'reflexivity.\n'
 else:
  out+=f' intro Eval. unfold writer_expr_{n} in Eval. cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.\n rewrite '+' '.join(f'?H{r}' for r in refs)+' in Eval.\n'
  if n==9214:out+=' eapply ground_or_uint; exact Eval.\n'
  elif n==9224:out+=' destruct g9182; cbn [eval_unop] in Eval; try discriminate Eval;\n repeat match type of Eval with context [if ?c then _ else _] => destruct c end;\n try discriminate Eval; inversion Eval; subst; do 2 eexists; reflexivity.\n'
  else:
   out+=" unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.\n rewrite "+' '.join(f'?H{r}' for r in refs)+' in Eval.\n'
   out+=' '+ '; '.join(f'destruct g{r}' for r in refs)+';\n cbn [validif_policy_result type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;\n repeat match type of Eval with context [if ?c then _ else _] => destruct c; cbn in Eval end;\n try discriminate Eval; inversion Eval; subst; do 2 eexists; reflexivity.\n'
 out+='Qed.\n'
 out+=f'Theorem data_writer_uint_output_{n} inputs path old current result :\n'+pre(n,refs)
 out+=' formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->\n'
 out+=f' exists width bits, VM.find {n} result = Some (Gval (Fuint width) bits).\nProof.\n intros '+' '.join(f'H{r}' for r in refs)+' Step.\n'
 out+=f''' eapply (selected_node_concrete_output data_writer_node_offsets flat_statements data_writer_expected_nodes {n} writer_expr_{n} inputs path flat_memories old current result).
 - exact data_writer_node_positions.
 - exact data_writer_node_safety.
 - apply (@List.nth_error_In _ data_writer_expected_nodes {positions.index(n)} ({n},writer_expr_{n})). vm_compute. reflexivity.
 - apply writer_ready_{n}; assumption.
 - intros location value Eval.
'''
 out+=f'   destruct (writer_uint_result_{n} inputs path location flat_memories old value '+' '.join(f'H{r}' for r in refs)+' Eval) as [w [b Value]].\n   subst value. exists w. reflexivity.\n - exact Step.\nQed.\n'
out+='Print Assumptions data_writer_uint_output_9234.\n'
f=p/'DataWriterUIntOutputs.v'
if not f.exists() or f.read_text()!=out:f.write_text(out)
