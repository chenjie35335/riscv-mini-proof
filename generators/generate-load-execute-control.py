"""Cross-check four execute-control tables with Scala and existing actual nodes."""
from pathlib import Path
import re,bisect
root=Path(__file__).resolve().parents[2];base=root/'formal/flat-low';model=(base/'CoreSocModel.v').read_text();nodes={}
for m in re.finditer(r'\(@Snode VarOrder.T (\d+) ',model):
 a=m.end();depth=0
 for b in range(a,len(model)):
  depth+=(model[b]=='(')-(model[b]==')')
  if depth==0:break
 nodes[int(m[1])]=model[a:b+1]
def constants(n):
 return [sum((bit.strip()=='true')<<i for i,bit in enumerate(bits.split(';'))) for bits in re.findall(r'\[::([^]]*)\]',nodes[n])]
control=(root/'src/main/scala/mini/Control.scala').read_text();alu=(root/'src/main/scala/mini/Alu.scala').read_text()
values_by_name={name:int(value) for name,value in re.findall(r'val (\w+) = (\d+)\.U',control+'\n'+alu)}
scala_rows=[fields.split(',') for name,fields in re.findall(r'(\w+)\s*-> List\(([^\n]+)\)',control)]
ids=list(map(int,re.findall(r'\(N.of_nat (\d+),',(base/'staged-integration/DataAddressPositionCertificate.v').read_text())))
values=[];indices=[];defaults=[]
for which in range(4):
 end=8458+49*which
 row=[constants(end-i)[0] for i in range(49)]
 assert row==[values_by_name[fields[which+1].strip()] for fields in scala_rows]
 values.append(row);indices.append([ids.index(end-i) for i in range(49)]);defaults.append(constants(end-48)[-1])
assert defaults==[0,0,0,15]
q=[m.start() for m in re.finditer(r'\(@Qcons VarOrder.T ',model)]
pos=lambda t:bisect.bisect_right(q,model.index(t))-1
wire_positions=[];wire_distances=[]
for which in range(4):
 for target,source in [(8252+which,8458+49*which),(86+which,8252+which)]:
  d=pos(f'(@Swire VarOrder.T {target} ');c=pos(f'(@Sfcnct VarOrder.T (@Eid VarOrder.T {target}) (@Eref VarOrder.T (@Eid VarOrder.T {source})))')
  wire_positions.append(d);wire_distances.append(c-d-1)
seq=lambda xs,nat=False:'[::'+';'.join(str(x)+('%nat' if nat else '') for x in xs)+']'
out='''Require Import LoadTypeCorrespondence DUTRedirectDecode CoreSocModel ComparisonNodes DataAddressPositionCertificate DataAddressSafetyCertificate FormalDeclaredWireCheck ReferenceRedirectSpine JointBoundaryRegisters JointUpdateBoundaryHistory FormalPCDecodeInputConnections ObservedJointRegisterConcrete FormalObservedHistory FormalLocalHistory.
From Coq Require Import NArith ZArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
'''
out+='Definition load_execute_values : seq (seq N) := [::'+';'.join(seq(row) for row in values)+'].\n'
out+='Definition load_execute_indices : seq (seq nat) := [::'+';'.join(seq(row,True) for row in indices)+'].\n'
out+='Definition load_execute_wire_positions : seq nat := '+seq(wire_positions,True)+'.\n'
out+='Definition load_execute_wire_distances : seq nat := '+seq(wire_distances,True)+'.\n'
out+='''Definition load_execute_width which := nth 0%nat [::1%nat;1%nat;3%nat;4%nat] which.
Definition load_execute_default which : N := if Nat.eqb which 3 then 15 else 0.
Definition load_execute_expected which : N := nth 0 [::1;0;1;0] which.
Definition load_execute_wire_target which outer : VarOrder.T := (if outer then 86 else 8252) + N.of_nat which.
Definition load_execute_wire_source which outer : VarOrder.T := if outer then 8252 + N.of_nat which else 8458 + 49 * N.of_nat which.
Definition load_execute_wire_index which outer := Nat.add (Nat.mul 2 which) (if outer then 1%nat else 0%nat).
Lemma load_execute_wire_certificate which outer : (which < 4)%coq_nat ->
 declared_wire_check flat_memories flat_statements (nth 0%nat load_execute_wire_positions (load_execute_wire_index which outer))
 (nth 0%nat load_execute_wire_distances (load_execute_wire_index which outer))
 (load_execute_wire_target which outer) (load_execute_wire_source which outer) (load_execute_width which) = true.
Proof. intro Bound. destruct outer;do 4 (destruct which as [|which];[vm_compute;reflexivity|]);lia. Qed.
Local Opaque flat_statements flat_memories generated_modules generated_top.
'''
p=base/'staged-integration/LoadExecuteControl.v';mark='(* Parametric execute-control semantics. *)';tail=p.read_text().split(mark,1)[1] if p.exists() and mark in p.read_text() else '\n';p.write_text(out+mark+tail)
print('Verified four Scala tables, 196 existing mux certificates and eight actual aliases.')
