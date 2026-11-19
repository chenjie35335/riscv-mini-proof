from pathlib import Path
import re
from bisect import bisect_right
root=Path(__file__).resolve().parents[2]
s=(root/'formal/flat-low/CoreSocModel.v').read_text()
ids=[3457,3458,3459,3460,3461]
q=[m.start()for m in re.finditer(r'\(@Qcons VarOrder.T ',s)]
expr={};pos={}
for m in re.finditer(r'\(@Snode VarOrder.T (\d+) ',s):
 n=int(m[1])
 if n not in ids:continue
 d=1;j=m.end()
 while d:d+=(s[j]=='(')-(s[j]==')');j+=1
 expr[n]=s[m.end():j-1];pos[n]=bisect_right(q,m.start())-1
out='''Require Import DUTRedirectSemantics FormalLocalHistory ObservedJointRegisterConcrete CoreSocModel ComparisonNodes ReferenceRedirectSpine SelectedNodeSafety X0ConcretePositionCertificate X0ConcreteSafetyCertificate ReferenceLoadSemantics.
From Coq Require Import NArith ZArith List Lia PeanoNat.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
'''
for n in ids:out+=f'Definition rf_subtract_ref_expr_{n} := {expr[n]}.\n'
out+='Definition rf_subtract_ref_nodes := [::'+';'.join(f'({n},rf_subtract_ref_expr_{n})'for n in ids)+'].\n'
prev=-1;offs=[]
for n in ids:offs.append(pos[n]-prev-1);prev=pos[n]
out+='Definition rf_subtract_ref_offsets := [::'+';'.join(str(i)+'%nat'for i in offs)+'].\nLemma rf_subtract_ref_positions :select_node_offsets rf_subtract_ref_offsets flat_statements=Some rf_subtract_ref_nodes.\nProof. vm_compute;reflexivity. Qed.\nLemma rf_subtract_ref_safety :selected_node_safety flat_memories flat_statements rf_subtract_ref_offsets flat_statements=true.\nProof. vm_compute;reflexivity. Qed.\nLocal Opaque flat_statements flat_memories generated_modules generated_top.\n'
p=root/'formal/flat-low/staged-integration/RFSubtractReferenceData.v'
marker='(* Handwritten semantic composition. *)'
tail=p.read_text().split(marker,1)[1] if p.exists() and marker in p.read_text() else '\n'
p.write_text(out+'\n'+marker+tail)
