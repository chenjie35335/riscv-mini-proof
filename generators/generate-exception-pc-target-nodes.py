"""Actual reference-PC update nodes, with reusable successful-evaluation certificates."""
from pathlib import Path
import re

root=Path(__file__).resolve().parents[2];base=root/'formal/flat-low'
model=(base/'CoreSocModel.v').read_text()
out='''Require Import CoreSocModel ComparisonNodes RegisterInvariants ScalarNodeFrames FormalTypedNodeFrames FormalTypedNodeEquation FormalSuccessfulNodeEvaluation.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Firrtl_with_implicit_widths Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
'''
for n in [6788,6796,6969,6970,6971,6972,6973,6974,6975,6976,6977,6987,7029,7030,7031,7032,7033,7034,7035,7036,7037,7046,7060]:
 m=re.search(r'\(@Snode VarOrder.T '+str(n)+r' ',model);depth=0
 for end in range(m.start(),len(model)):
  depth+=(model[end]=='(')-(model[end]==')')
  if depth==0:break
 expr=model[m.end():end];pos=len(re.findall(r'\(@Qcons VarOrder.T ',model[:m.start()]))-1
 name=f'exception_pc_target_{n}'
 out+=f'''Definition {name}_expr := {expr}.
Definition {name}_tail := match straight_drop {pos+1} flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma {name}_position : straight_drop {pos} flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T {n} {name}_expr) {name}_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma {name}_safe : formal_typed_suffix_safe flat_memories {n} {name}_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma {name}_nonregister : has_register {n} flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem {name}_value invalid old current result width bits :
 eval_hfexpr_with_memory flat_memories {name}_expr old old = Some (Gval (Fuint width) bits) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find {n} result = Some (Gval (Fuint width) bits).
Proof.
 intros Eval Step. eapply formal_combinational_known_node;
 [exact {name}_position|exact {name}_safe|exact {name}_nonregister|exact Eval|reflexivity|exact Step].
Qed.
Theorem {name}_evaluation invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value, eval_hfexpr_with_memory flat_memories {name}_expr old old = Some value.
Proof.
 intro Step.
 exact (formal_successful_node_evaluation {pos} flat_statements {name}_tail {n} {name}_expr invalid flat_memories old false current result {name}_position Step).
Qed.
'''
out+='Print Assumptions exception_pc_target_7060_value.\n'
p=base/'staged-integration'/'ExceptionPCTargetNodes.v'
if not p.exists() or p.read_text()!=out:p.write_text(out)
