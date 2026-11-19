from pathlib import Path
import re,bisect
root=Path(__file__).resolve().parents[2];base=root/'formal/flat-low';s=(base/'CoreSocModel.v').read_text()
q=[m.start() for m in re.finditer(r'\(@Qcons VarOrder.T ',s)]
rows=[];positions=[]
for n in list(range(1156,1162))+list(range(7820,7824)):
 start=s.index(f'(@Snode VarOrder.T {n} ')+len(f'(@Snode VarOrder.T {n} ');depth=0
 for end in range(start,len(s)):
  depth+=(s[end]=='(')-(s[end]==')')
  if depth==0:break
 rows.append((n,s[start:end+1]));positions.append(bisect.bisect_right(q,start)-1)
offsets=[positions[0]]+[b-a-1 for a,b in zip(positions,positions[1:])]
out='''Require Import CoreSocModel ComparisonNodes ReferenceRedirectSpine SelectedNodeSafety X0ConcretePositionCertificate X0ConcreteSafetyCertificate ReferenceLoadSemantics.
From Coq Require Import ZArith Lia List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
'''
for n,e in rows:out+=f'Definition alu_address_expr_{n} : hfexpr VarOrder.T := {e}.\n'
out+='Definition alu_address_nodes := [::'+';'.join(f'({n},alu_address_expr_{n})' for n,e in rows)+'].\n'
out+='Definition alu_address_offsets := [::'+';'.join(f'{n}%nat' for n in offsets)+'].\n'
out+='''Lemma alu_address_positions : select_node_offsets alu_address_offsets flat_statements = Some alu_address_nodes.
Proof. vm_compute. reflexivity. Qed.
Lemma alu_address_safety : selected_node_safety flat_memories flat_statements alu_address_offsets flat_statements = true.
Proof. vm_compute. reflexivity. Qed.
Local Opaque flat_statements flat_memories generated_modules generated_top.
'''
p=base/'staged-integration/ALUAddressSemantics.v';marker='(* Actual ALU address proofs. *)';tail=p.read_text().split(marker,1)[1] if p.exists() and marker in p.read_text() else '\n';p.write_text(out+marker+tail)
