"""Actual reference store data mux and output certificates; preserve semantic tail."""
from pathlib import Path
import re,bisect
root=Path(__file__).resolve().parents[2];base=root/'formal/flat-low';s=(base/'CoreSocModel.v').read_text();q=[m.start()for m in re.finditer(r'\(@Qcons VarOrder.T ',s)]
ids=[6647,6648,6662,6671,6686,6695,7115,7190];pairs=[];pos=[]
for n in ids:
 a=s.index(f'(@Snode VarOrder.T {n} ')+len(f'(@Snode VarOrder.T {n} ');d=0
 for b in range(a,len(s)):
  d+=(s[b]=='(')-(s[b]==')')
  if d==0:break
 pairs.append(f'({n},{s[a:b+1]})');pos.append(bisect.bisect_right(q,a)-1)
seq=lambda xs:'[::'+';'.join(map(str,xs))+']'
out='''Require Import CoreSocModel ComparisonNodes SelectedNodeSafety X0ConcretePositionCertificate X0ConcreteSafetyCertificate ReferenceRedirectSpine DUTRedirectDecode FormalDeclaredWireCheck ReferenceStoreData.
From Coq Require Import NArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
'''
out+='Definition reference_store_request_data_nodes : seq(VarOrder.T*hfexpr VarOrder.T) := '+seq(pairs)+'.\n'
out+='Definition reference_store_request_data_offsets := '+seq(str(x)+'%nat'for x in[pos[0]]+[b-a-1 for a,b in zip(pos,pos[1:])])+'.\n'
out+='''Lemma reference_store_request_data_positions : select_node_offsets reference_store_request_data_offsets flat_statements=Some reference_store_request_data_nodes.
Proof. vm_compute;reflexivity. Qed.
Lemma reference_store_request_data_safety : selected_node_safety flat_memories flat_statements reference_store_request_data_offsets flat_statements=true.
Proof. vm_compute;reflexivity. Qed.
'''
for target,source in [(1716,7190),(1526,1716)]:
 d=bisect.bisect_right(q,s.index(f'(@Swire VarOrder.T {target} '))-1
 c=bisect.bisect_right(q,s.index(f'(@Sfcnct VarOrder.T (@Eid VarOrder.T {target}) (@Eref VarOrder.T (@Eid VarOrder.T {source})))'))-1
 out+=f'''Lemma reference_store_request_wire_{target} : declared_wire_check flat_memories flat_statements {d} {c-d-1} {target} {source} 32=true.
Proof. vm_compute;reflexivity. Qed.
'''
out+='Local Opaque flat_statements flat_memories generated_modules generated_top.\n'
p=base/'staged-integration/ReferenceStoreRequestData.v';mark='(* Shared store request data semantics. *)';tail=p.read_text().split(mark,1)[1]if p.exists()and mark in p.read_text()else'\n';p.write_text(out+mark+tail)
s=p.read_text().split('(* Store data batch history. *)')[0]
s+='''(* Store data batch history. *)
Definition reference_store_request_data_guards : seq VarOrder.T := [::1951;2723;1946;2708;1941;1707].
Theorem reference_store_request_data_history invalid history limit start guards word :
 (forall t,(t<limit)%coq_nat ->formal_value_iter invalid flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 (forall t,(start<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 2804(history t)=Some(Gval(Fuint 32)word)) ->
 (forall node t,List.In node reference_store_request_data_guards ->(start<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find node(history t)=Some(Gval(Fuint 1)[::guards node])) ->
 forall t,(Nat.add start 8<=t)%coq_nat ->(t<=limit)%coq_nat ->
 VM.find 7115(history t)=Some(Gval(Fuint 32)(reference_store_request_word guards word)).
Proof.
 intros Steps Source Guards.
 assert(Pieces:forall lane t,(lane<3)%coq_nat ->(Nat.add start 2<=t)%coq_nat ->(t<=limit)%coq_nat ->
 VM.find(reference_store_data_base lane+1)(history t)=Some(Gval(Fuint(reference_store_data_width lane))(take(reference_store_data_width lane)word))).
 { intros lane [|[|t]] Lane Lower Upper;try lia.
 exact(reference_store_data_steps lane invalid(history t)(history(S t))(history(S(S t)))word Lane(Source t ltac:(lia)ltac:(lia))(Steps t ltac:(lia))(Steps(S t)ltac:(lia))). }
'''
rows=[(6647,None,None,None),(6648,1951,('piece',2,8),0),(6662,2723,('piece',1,16),1),(6671,1946,('prior',2,32),1),(6686,2708,('piece',0,32),3),(6695,1941,('prior',4,32),3),(7115,1707,('prior',5,32),0)]
for i,(node,g,yes,no) in enumerate(rows):
 val='zeros 32' if i==0 else f'if guards {g} then '+(f'reference_store_request_piece {yes[2]} word'if yes[0]=='piece'else f'v{yes[1]}')+f' else v{no}'
 s+=f' set v{i} := ({val}).\n assert(Size{i}:size v{i}=32%nat).\n {{ '+('reflexivity.'if not i else f'unfold v{i}. destruct(guards {g});'+('[apply reference_store_request_piece_size|' if yes[0]=='piece'else f'[exact Size{yes[1]}|')+f'exact Size{no}].')+' }\n'
 s+=f''' assert(V{i}:forall t,(Nat.add start {i+2}<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find {node}(history t)=Some(Gval(Fuint 32)v{i})).
 {{ intros [|t] Lower Upper;try lia.
 eapply(reference_redirect_ground_step reference_store_request_data_offsets reference_store_request_data_nodes {node} (snd(nth (0,@Econst VarOrder.T(Fuint 1)[::false])reference_store_request_data_nodes {i})));[exact reference_store_request_data_positions|exact reference_store_request_data_safety|apply(List.nth_error_In reference_store_request_data_nodes {i}%nat);vm_compute;reflexivity| |apply Steps;lia].
'''
 if not i:s+=' intros site;reflexivity. }\n';continue
 ynode=[6679,6655,6635][yes[1]]if yes[0]=='piece'else rows[yes[1]][0]
 s+=f''' intros site. unfold v{i}. eapply(store_data_mux_eval _ _ _ {g} {ynode} {rows[no][0]} {yes[2]});
 [reflexivity|exact Size{no}|apply Guards;[vm_compute;tauto|lia|lia]| |apply V{no};lia|].
'''
 if yes[0]=='piece':s+=f' - exact(Pieces {yes[1]} t ltac:(vm_compute;lia)ltac:(lia)ltac:(lia)).\n - reflexivity. }}\n'
 else:s+=f' - apply V{yes[1]};lia.\n - apply dut_decode_adapt;exact Size{yes[1]}. }}\n'
s+=' intros t Lower Upper. exact(V6 t Lower Upper).\nQed.\n'
p.write_text(s)
