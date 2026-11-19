"""Actual expression and position certificates for exception instruction selection."""
import re
import argparse
from pathlib import Path
parser=argparse.ArgumentParser()
parser.add_argument('--pc-shifts', action='store_true')
parser.add_argument('--pc-select', action='store_true')
args=parser.parse_args()
assert not (args.pc_shifts and args.pc_select)
root=Path(__file__).resolve().parents[2]
base=root/'formal/flat-low'
model=(base/'CoreSocModel.v').read_text()
out='''Require Import CoreSocModel ComparisonNodes RegisterInvariants ScalarNodeFrames FormalTypedNodeFrames FormalTypedNodeEquation.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Firrtl_with_implicit_widths Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
'''
for n in ([771,772] if args.pc_shifts else ([7086,7087,7119] if args.pc_select else [1883,6811,7088,7089,7120])):
 width = 30 if n == 771 else 32
 m=re.search(r'\(@Snode VarOrder.T '+str(n)+r' ',model)
 depth=0
 for end in range(m.start(),len(model)):
  depth+=(model[end]=='(')-(model[end]==')')
  if depth==0:break
 expr=model[m.end():end]
 pos=len(re.findall(r'\(@Qcons VarOrder.T ',model[:m.start()]))-1
 name=f'exception_pc_shift_{n}' if args.pc_shifts else (f'exception_pc_selection_{n}' if args.pc_select else f'exception_selection_{n}')
 out+=f'''Definition {name}_expr : hfexpr VarOrder.T := {expr}.
Definition {name}_tail := match straight_drop {pos+1} flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma {name}_position : straight_drop {pos} flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T {n} {name}_expr) {name}_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma {name}_safe : formal_typed_suffix_safe flat_memories {n} {name}_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma {name}_nonregister : has_register {n} flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem {name}_value invalid old current result bits :
 eval_hfexpr_with_memory flat_memories {name}_expr old old = Some (Gval (Fuint {width}) bits) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find {n} result = Some (Gval (Fuint {width}) bits).
Proof.
 intros Eval Step. eapply formal_combinational_known_node;
 [exact {name}_position|exact {name}_safe|exact {name}_nonregister|exact Eval|reflexivity|exact Step].
Qed.
'''
out+=('Print Assumptions exception_pc_shift_772_value.\n' if args.pc_shifts else ('Print Assumptions exception_pc_selection_7119_value.\n' if args.pc_select else 'Print Assumptions exception_selection_7120_value.\n'))
p=base/'staged-integration'/('ExceptionPCShiftNodes.v' if args.pc_shifts else ('ExceptionPCSelectionNodes.v' if args.pc_select else 'ExceptionSelectionNodes.v'))
if not p.exists() or p.read_text()!=out:p.write_text(out)
