"""Check the actual flattened DUT shifter cone without changing its model."""
from pathlib import Path
import re,bisect
root=Path(__file__).resolve().parents[2]
base=root/'formal/flat-low'
s=(base/'CoreSocModel.v').read_text()
positions=[m.start() for m in re.finditer(r'\(@Qcons VarOrder.T ',s)]
exprs=[]; offsets=[]
for n in range(1171,1279):
 a=s.index(f'(@Snode VarOrder.T {n} ')+len(f'(@Snode VarOrder.T {n} ')
 depth=0
 for b in range(a,len(s)):
  depth+=(s[b]=='(')-(s[b]==')')
  if depth==0:break
 exprs.append((n,s[a:b+1]));offsets.append(bisect.bisect_right(positions,a)-1)
out='''Require Import CoreSocModel ComparisonNodes SelectedNodeSafety X0ConcretePositionCertificate X0ConcreteSafetyCertificate.
From Coq Require Import NArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
'''
for n,e in exprs:out+=f'Definition rf_shift_expr_{n} := {e}.\n'
out+='Definition rf_shift_nodes := [::'+';'.join(f'({n},rf_shift_expr_{n})' for n,_ in exprs)+'].\n'
out+='Definition rf_shift_offsets := [::'+';'.join(str(x)+'%nat' for x in [offsets[0]]+[b-a-1 for a,b in zip(offsets,offsets[1:])])+'].\n'
out+='''Lemma rf_shift_positions : select_node_offsets rf_shift_offsets flat_statements=Some rf_shift_nodes.
Proof. vm_compute;reflexivity. Qed.
Lemma rf_shift_safety : selected_node_safety flat_memories flat_statements rf_shift_offsets flat_statements=true.
Proof. vm_compute;reflexivity. Qed.
'''
(base/'staged-integration/RFShiftNodes.v').write_text(out)
