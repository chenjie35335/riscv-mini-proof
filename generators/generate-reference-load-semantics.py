"""Batch actual reference load lanes; preserve the shared semantic proof tail."""
from pathlib import Path
import re,bisect
root=Path(__file__).resolve().parents[2];base=root/'formal/flat-low';s=(base/'CoreSocModel.v').read_text()
q=[m.start() for m in re.finditer(r'\(@Qcons VarOrder.T ',s)]
starts=[3351,3369,3387,3405,3426];ends=[3365,3383,3401,3422,3443]
rows=[];address_rows=[];poses=[];pairs=[]
for start,end in zip(starts,ends):
 row=[];address_row=[]
 for n in range(start-3,end+1):
  a=s.index(f'(@Snode VarOrder.T {n} ');a+=len(f'(@Snode VarOrder.T {n} ');depth=0
  for b in range(a,len(s)):
   depth+=(s[b]=='(')-(s[b]==')')
   if depth==0:break
  e=s[a:b+1];(row if n>=start else address_row).append(e);pairs.append(f'({n},{e})');poses.append(bisect.bisect_right(q,a)-1)
 rows.append('[::'+';'.join(row)+']');address_rows.append('[::'+';'.join(address_row)+']')
seq=lambda xs:'[::'+';'.join(str(x)+'%nat' for x in xs)+']'
out='''Require Import CoreSocModel ComparisonNodes SelectedNodeSafety X0ConcretePositionCertificate X0ConcreteSafetyCertificate FormalTypedNodeEquation FormalGroundNodeEquation ReferenceLoadArithmetic.
From Coq Require Import ZArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
'''
out+='Definition reference_load_nodes : seq (VarOrder.T * hfexpr VarOrder.T) := [::'+';'.join(pairs)+'].\n'
out+='Definition reference_load_offsets := '+seq([poses[0]]+[b-a-1 for a,b in zip(poses,poses[1:])])+'.\n'
out+='Definition reference_load_rows : seq (seq (hfexpr VarOrder.T)) := [::'+';'.join(rows)+'].\n'
out+='Definition reference_load_address_rows : seq (seq (hfexpr VarOrder.T)) := [::'+';'.join(address_rows)+'].\n'
out+='''Definition reference_load_base lane : VarOrder.T := nth 0 [::3351;3369;3387;3405;3426] lane.
Definition reference_load_width lane : nat := nth 0%nat [::16%nat;8%nat;32%nat;16%nat;8%nat] lane.
Definition reference_load_length lane : nat := nth 0%nat [::15%nat;15%nat;15%nat;18%nat;18%nat] lane.
Definition reference_load_node lane stage := reference_load_base lane + N.of_nat stage.
Definition reference_load_expression lane stage := nth (@Econst VarOrder.T (Fuint 1) [::false]) (nth [::] reference_load_rows lane) stage.
Definition reference_load_address_node lane stage := reference_load_base lane - 3 + N.of_nat stage.
Definition reference_load_address_expression lane stage := nth (@Econst VarOrder.T (Fuint 1) [::false]) (nth [::] reference_load_address_rows lane) stage.
Definition reference_load_mask lane := from_N 64 (nth 0 [::65535;255;4294967295;65535;255] lane).
Lemma reference_load_positions : select_node_offsets reference_load_offsets flat_statements = Some reference_load_nodes.
Proof. vm_compute. reflexivity. Qed.
Lemma reference_load_safety : selected_node_safety flat_memories flat_statements reference_load_offsets flat_statements = true.
Proof. vm_compute. reflexivity. Qed.
Lemma reference_load_member lane stage : (lane < 5)%coq_nat -> (stage < reference_load_length lane)%coq_nat ->
 List.In (reference_load_node lane stage,reference_load_expression lane stage) reference_load_nodes.
Proof.
 intros Lane Stage.
 apply (List.nth_error_In reference_load_nodes ((nth 0%nat [::3%nat;21%nat;39%nat;57%nat;78%nat] lane) + stage)%nat).
 do 5 (destruct lane as [|lane]; [cbn [reference_load_length nth] in Stage;
 do 18 (destruct stage as [|stage]; [try (vm_compute;reflexivity);try lia|]);lia|]). lia.
Qed.
Lemma reference_load_address_member lane stage : (lane < 5)%coq_nat -> (stage < 3)%coq_nat ->
 List.In (reference_load_address_node lane stage,reference_load_address_expression lane stage) reference_load_nodes.
Proof.
 intros Lane Stage.
 apply (List.nth_error_In reference_load_nodes ((nth 0%nat [::0%nat;18%nat;36%nat;54%nat;75%nat] lane) + stage)%nat).
 do 5 (destruct lane as [|lane]; [do 3 (destruct stage as [|stage]; [vm_compute;reflexivity|]);lia|]). lia.
Qed.
Local Opaque flat_statements flat_memories generated_modules generated_top.
'''
p=base/'staged-integration/ReferenceLoadSemantics.v';mark='(* Shared load-lane semantics. *)';tail=p.read_text().split(mark,1)[1] if p.exists() and mark in p.read_text() else '\n';p.write_text(out+mark+tail)
print('Generated',len(pairs),'actual load nodes in five lanes.')
