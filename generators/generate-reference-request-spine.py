"""Paired valid/width request spine with shared guard interface."""
from pathlib import Path
import re,bisect
root=Path(__file__).resolve().parents[2];base=root/'formal/flat-low';s=(base/'CoreSocModel.v').read_text();q=[m.start() for m in re.finditer(r'\(@Qcons VarOrder.T ',s)]
reads=[(6517,6520,None,None,None),(6518,6521,2679,8,0),(6528,6531,1970,1,0),(6544,6546,2664,16,2),(6553,6555,1966,3,2),(6569,6571,2649,32,4),(6578,6580,1962,5,4),(6596,6598,1958,8,6),(6610,6612,2565,16,7),(6619,6621,1886,8,7),(7111,7112,1707,9,0)]
writes=[(6641,6645,None,None,None),(6642,6646,1951,8,0),(6659,6661,2723,16,1),(6668,6670,1946,2,1),(6683,6685,2708,32,3),(6692,6694,1941,4,3),(7113,7114,1707,5,0)]
# constant true branches for these stage indices
consts={False:{1,3,5,7,8},True:{1,2,4}}
ids=sorted([n for rows in [reads,writes] for row in rows for n in row[:2]]+[7186,7187,7188,7189]);ex={};pos=[]
for n in ids:
 a=s.index(f'(@Snode VarOrder.T {n} ')+len(f'(@Snode VarOrder.T {n} ');d=0
 for b in range(a,len(s)):
  d+=(s[b]=='(')-(s[b]==')')
  if d==0:break
 ex[n]=s[a:b+1];pos.append(bisect.bisect_right(q,a)-1)
seq=lambda xs:'[::'+';'.join(map(str,xs))+']'
out='''Require Import CoreSocModel ComparisonNodes SelectedNodeSafety X0ConcretePositionCertificate X0ConcreteSafetyCertificate ReferenceRedirectSpine DUTRedirectDecode FormalDeclaredWireCheck.
From Coq Require Import NArith ZArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
'''
out+='Definition reference_request_nodes : seq (VarOrder.T * hfexpr VarOrder.T) := '+seq(f'({n},{ex[n]})' for n in ids)+'.\n'
out+='Definition reference_request_offsets := '+seq(str(n)+'%nat' for n in [pos[0]]+[b-a-1 for a,b in zip(pos,pos[1:])])+'.\n'
wireposes=[];wiredist=[]
for field in range(4):
 for outer in [False,True]:
  target=(1519 if outer else 1709)+2*field;source=(1709+2*field if outer else 7186+field)
  d=bisect.bisect_right(q,s.index(f'(@Swire VarOrder.T {target} '))-1
  c=bisect.bisect_right(q,s.index(f'(@Sfcnct VarOrder.T (@Eid VarOrder.T {target}) (@Eref VarOrder.T (@Eid VarOrder.T {source})))'))-1
  wireposes.append(d);wiredist.append(c-d-1)
out+='Definition reference_request_wire_positions := '+seq(str(x)+'%nat' for x in wireposes)+'.\n'
out+='Definition reference_request_wire_distances := '+seq(str(x)+'%nat' for x in wiredist)+'.\n'
out+='''Definition reference_request_field_width field := if Nat.even field then 1%nat else 6%nat.
Definition reference_request_wire_target field outer : VarOrder.T := (if outer then 1519 else 1709)+2*N.of_nat field.
Definition reference_request_wire_source field outer : VarOrder.T := if outer then 1709+2*N.of_nat field else 7186+N.of_nat field.
Lemma reference_request_wire_certificate field outer : (field < 4)%coq_nat ->
 declared_wire_check flat_memories flat_statements
 (nth 0%nat reference_request_wire_positions (Nat.add (Nat.mul 2 field) (if outer then 1 else 0)))
 (nth 0%nat reference_request_wire_distances (Nat.add (Nat.mul 2 field) (if outer then 1 else 0)))
 (reference_request_wire_target field outer) (reference_request_wire_source field outer) (reference_request_field_width field) = true.
Proof. intro Field. destruct outer;do 4 (destruct field as [|field];[vm_compute;reflexivity|]);lia. Qed.
'''
out+='''Lemma reference_request_positions : select_node_offsets reference_request_offsets flat_statements = Some reference_request_nodes.
Proof. vm_compute;reflexivity. Qed.
Lemma reference_request_safety : selected_node_safety flat_memories flat_statements reference_request_offsets flat_statements = true.
Proof. vm_compute;reflexivity. Qed.
Local Opaque flat_statements flat_memories generated_modules generated_top.
'''
for field in [0,1]:
 name='valid' if field==0 else 'width';typ='bool' if field==0 else 'N'
 out+=f'Definition reference_request_{name} (writing:bool) (guards:VarOrder.T -> bool) : {typ} :=\n if writing then\n'
 for writing,rows in [(True,writes),(False,reads)]:
  for stage,row in enumerate(rows):
   _,_,g,y,n=row
   val=('false' if field==0 else '0') if stage==0 else f'if guards {g} then '+(('true' if field==0 else str(y)) if stage in consts[writing] else f'v{y}')+f' else v{n}'
   out+=f' let v{stage} := {val} in\n'
  out+=f' v{len(rows)-1}'+(' else\n' if writing else '.\n')
out+='''Definition reference_request_guard_nodes : seq VarOrder.T := [::1707;1886;1941;1946;1951;1958;1962;1966;1970;2565;2649;2664;2679;2708;2723].
Theorem reference_request_spine_history writing guards invalid history limit start :
 (forall i, (i < limit)%coq_nat -> formal_value_iter invalid flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 (forall node i, List.In node reference_request_guard_nodes -> (start <= i)%coq_nat -> (i <= limit)%coq_nat -> VM.find node (history i) = Some (Gval (Fuint 1) [::guards node])) ->
 forall time, (Nat.add start 11 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 VM.find (if writing then 7113 else 7111) (history time) = Some (Gval (Fuint 1) [::reference_request_valid writing guards]) /\\
 VM.find (if writing then 7114 else 7112) (history time) = Some (Gval (Fuint 6) (from_N 6 (reference_request_width writing guards))).
Proof.
 intros Steps Guards. destruct writing.
'''
for writing,rows in [(True,writes),(False,reads)]:
 out+=' -\n'
 for stage,row in enumerate(rows):
  for field in [0,1]:
   node=row[field];g,y,n=row[2:];width=1 if field==0 else 6;vn=('b' if field==0 else 'w')+str(stage)
   val=('false' if field==0 else '0') if stage==0 else f'if guards {g} then '+(('true' if field==0 else str(y)) if stage in consts[writing] else ('b' if field==0 else 'w')+str(y))+' else '+('b' if field==0 else 'w')+str(n)
   out+=f' set {vn} := ({val}).\n'
   bits=f'[::{vn}]' if field==0 else f'from_N 6 {vn}'
   out+=f''' assert (V{node} : forall time, (Nat.add start {stage+1} <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find {node} (history time) = Some (Gval (Fuint {width}) ({bits}))).
 {{ intros [|time] Lower Upper;try lia.
 eapply (reference_redirect_ground_step reference_request_offsets reference_request_nodes {node} ({ex[node]}));
 [exact reference_request_positions|exact reference_request_safety|apply (List.nth_error_In reference_request_nodes {ids.index(node)}%nat);vm_compute;reflexivity| |apply Steps;lia].
 intros site. cbn [eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
'''
   if stage:
    look=[f'(Guards {g} time ltac:(vm_compute;tauto) ltac:(lia) ltac:(lia))']
    if stage not in consts[writing]:look.append(f'(V{rows[y][field]} time ltac:(lia) ltac:(lia))')
    look.append(f'(V{rows[n][field]} time ltac:(lia) ltac:(lia))')
    out+=' rewrite '+' '.join(look)+'. unfold eval_type_of_expr;cbn [type_of_expr\' eval_type_of_ref];rewrite '+' '.join('?'+x for x in look)+'.\n'
    out+=f' unfold {vn}. destruct (guards {g});cbn;try reflexivity;apply dut_decode_adapt;'+('reflexivity.' if field==0 else 'apply size_from_N.')+' }\n'
   else:out+=' reflexivity. }\n'
 out+=f' intros time Lower Upper. split;[exact (V{rows[-1][0]} time ltac:(lia) Upper)|exact (V{rows[-1][1]} time ltac:(lia) Upper)].\n'
out+='Qed.\n'
p=base/'staged-integration/ReferenceRequestSpine.v';mark='(* Request output aliases. *)';tail=p.read_text().split(mark,1)[1] if p.exists() and mark in p.read_text() else '\n';p.write_text(out+mark+tail)
