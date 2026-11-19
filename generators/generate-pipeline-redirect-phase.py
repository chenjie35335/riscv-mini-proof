"""Refresh the 49-row kill table using actual flattened nodes and Scala control rows."""
from pathlib import Path
import re
root=Path(__file__).resolve().parents[2];d=root/'formal/flat-low/staged-integration';model=(root/'formal/flat-low/CoreSocModel.v').read_text();cert=(d/'JointUpdateNodePositions.v').read_text();ids=list(map(int,re.findall(r'\((\d+),joint_update_expr_',cert)));values=[]
for n in range(8655,8704):
 a=model.index(f'(@Snode VarOrder.T {n} ');v=re.search(r'\(@Econst VarOrder.T \(Fuint 1\) \[::(true|false)\]\)',model[a:]).group(1);values.append(v)
rows=[line.split('List(',1)[1].split(')',1)[0].split(',') for line in (root/'src/main/scala/mini/Control.scala').read_text().splitlines() if '-> List(' in line]
assert len(rows)==49
assert list(reversed(values))==['true' if r[6].strip()=='Y' else 'false' for r in rows]
path=d/'PipelineRedirectPhase.v';marker='(* Parametric kill/redirect phase proofs. *)';old=path.read_text() if path.exists() else '';tail=old[old.index(marker):] if marker in old else marker+'\n'
header='''Require Import CoreSocModel ComparisonNodes DUTRedirectDecode ReferenceRedirectSpine
 JointUpdateNodePositions JointUpdateExpressionCertificates JointUpdateConnectionCertificates FormalDeclaredConnection.
From Coq Require Import NArith ZArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
'''
header+='Definition pipeline_kill_rows : seq bool := [::'+';'.join(reversed(values))+'].\n'
header+='Definition pipeline_kill_indices : seq nat := [::'+';'.join(str(ids.index(n))+'%nat' for n in range(8655,8704))+'].\n'
header+='Definition pipeline_kill_extract_index : nat := '+str(ids.index(8998))+'%nat.\n'
path.write_text(header+tail)
print('49 kill rows match Scala Control.scala and flattened model')
