"""Single schema for all 31 reference RF NOP mux chains."""
from pathlib import Path
import re
root=Path(__file__).resolve().parents[2];out=root/'formal/flat-low/staged-integration';s=(root/'formal/flat-low/CoreSocModel.v').read_text();ex={};pos={}
for m in re.finditer(r'\(@Snode VarOrder.T (\d+) ',s):
 p=m.end();d=1;j=p
 while d:d+=(s[j]=='(')-(s[j]==')');j+=1
 n=int(m[1]);ex[n]=s[p:j-1];pos[n]=s[:m.start()].count('(@Qcons VarOrder.T ')-1
refs=lambda n:list(map(int,re.findall(r'\(@Eid VarOrder.T (\d+)\)',ex[n])))
chain=[];n=3614
while n!=2176:chain.append(n);n=refs(n)[-1]
chain=chain[::-1]
# Verify each actual expression against the shared node/branch displacement schema.
for i in range(1,32):
 for n in chain:
  actual=ex[n+80*(i-1)];r=refs(n);expected=[r[0],3223+i if n==3538 else r[1]+80*(i-1),2177-i if n==3538 else r[2]+80*(i-1)]
  assert refs(n+80*(i-1))==expected,(i,n)
text='''Require Import CoreSocModel ComparisonNodes X0ConcretePositionCertificate X0ConcreteSafetyCertificate.
From Coq Require Import ZArith List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import HiFirrtl_with_implicit_widths.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Definition rf_reference_chain_specs : seq (nat * nat * nat) := [::'''
text+=';'.join(f'({n}%nat,{refs(n)[0]}%nat,{refs(n)[1]}%nat)' for n in chain)+'].\n'
text+='''Definition rf_reference_chain_node (index stage : nat) : VarOrder.T :=
 N.of_nat (let '(node,_,_) := nth (0%nat,0%nat,0%nat) rf_reference_chain_specs stage in node + 80 * (index - 1)).
Definition rf_reference_chain_expr (index stage : nat) : hfexpr VarOrder.T :=
 let '(_,guard,yes) := nth (0%nat,0%nat,0%nat) rf_reference_chain_specs stage in
 @Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T (N.of_nat guard)))
 (@Eref VarOrder.T (@Eid VarOrder.T (N.of_nat (if stage == 0%nat then (3223 + index)%nat else (yes + 80 * (index - 1))%nat))))
 (@Eref VarOrder.T (@Eid VarOrder.T (if stage == 0%nat then N.of_nat (2177-index)%nat else rf_reference_chain_node index (stage-1)))).
Definition rf_reference_chain_nodes : seq (VarOrder.T * hfexpr VarOrder.T) := [::'''
items=sorted([(pos[n+80*(i-1)],i,j) for i in range(1,32) for j,n in enumerate(chain)])
text=text[:-4]+'''\n List.flat_map (fun index => List.map (fun stage => (rf_reference_chain_node index stage,rf_reference_chain_expr index stage)) (List.seq 0 36)) (List.seq 1 31).\n'''
prev=-1;offset=[]
for p,_,_ in items:offset.append(p-prev-1);prev=p
text+='Definition rf_reference_chain_offsets : seq nat := [::'+';'.join(str(x)+'%nat' for x in offset)+'].\n'
text+='''Lemma rf_reference_chain_positions : select_node_offsets rf_reference_chain_offsets flat_statements = Some rf_reference_chain_nodes.
Proof. vm_compute. reflexivity. Qed.
Lemma rf_reference_chain_safety : selected_node_safety flat_memories flat_statements rf_reference_chain_offsets flat_statements = true.
Proof. vm_compute. reflexivity. Qed.
'''
(out/'RFReferenceNopStorageCertificates.v').write_text(text)
print(len(items),'actual mux nodes verified')
