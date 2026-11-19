"""Expression readiness for 68 scalar register updates, not commit-position proof."""
import contextlib,io,json,re,runpy
from pathlib import Path
root=Path(__file__).resolve().parents[2];p=root/'formal/flat-low/staged-integration'
with contextlib.redirect_stdout(io.StringIO()):a=runpy.run_path(str(root/'scripts/audit-x0-concrete-cone.py'))
ids=a['report']['joint_register_candidates']
s='''Require Import ConcreteExpressionClosure ConcreteScalarExpressions ConcreteGroundOperations.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Firrtl_with_implicit_widths Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Ltac solve_joint_register_ready :=
 first [apply closure_scalar; solve [repeat first [eapply scalar_ready_ref; eassumption | apply scalar_ready_const | apply scalar_ready_unary | apply scalar_ready_binary | apply scalar_ready_cast]]
 | apply closure_mux; solve_joint_register_ready | apply closure_unary; solve_joint_register_ready | apply closure_binary; solve_joint_register_ready].
'''
count=0
for n in ids:
 if n in (9220,9222):continue
 es=a['drivers'][n];assert len(es)==1
 e=es[0];assert not e['aggregate_reference'] and 'Evalidif' not in e['expression']
 s+=f"Definition joint_register_update_{n} : hfexpr VarOrder.T := {e['expression']}.\nLemma joint_register_ready_{n} old :\n"
 for d in e['dependencies']:s+=f' (exists ground bits, VM.find {d} old = Some (Gval ground bits)) ->\n'
 s+=f' concrete_expression_ready old joint_register_update_{n}.\nProof.\n'
 for d in e['dependencies']:s+=f' intros [g{d} [b{d} H{d}]].\n'
 s+=f' unfold joint_register_update_{n}. solve_joint_register_ready.\nQed.\n';count+=1
s+='Print Assumptions joint_register_ready_7768.\n'
f=p/'JointRegisterExpressionCertificates.v'
if not f.exists() or f.read_text()!=s:f.write_text(s)
print('Generated',count,'scalar register expression readiness certificates.')
