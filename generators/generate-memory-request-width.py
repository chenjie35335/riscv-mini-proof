"""One batched actual read/write width decoder; shared semantic proof tail."""
from pathlib import Path
import re,bisect
root=Path(__file__).resolve().parents[2];base=root/'formal/flat-low';model=(base/'CoreSocModel.v').read_text();q=[m.start() for m in re.finditer(r'\(@Qcons VarOrder.T ',model)]
ids=list(range(7984,7996))+list(range(7997,8003))+[8077,8078,8085,8086,8200,8204];expr=[];pos=[]
for n in ids:
 a=model.index(f'(@Snode VarOrder.T {n} ')+len(f'(@Snode VarOrder.T {n} ');depth=0
 for b in range(a,len(model)):
  depth+=(model[b]=='(')-(model[b]==')')
  if depth==0:break
 expr.append(model[a:b+1]);pos.append(bisect.bisect_right(q,a)-1)
seq=lambda xs:'[::'+';'.join(map(str,xs))+']'
out='''Require Import CoreSocModel ComparisonNodes SelectedNodeSafety X0ConcretePositionCertificate X0ConcreteSafetyCertificate ReferenceRedirectSpine LoadTypeCorrespondence DUTRedirectDecode FormalDeclaredWireCheck JointUpdateBoundaryHistory FormalObservedHistory FormalLocalHistory JointBoundaryRegisters.
From Coq Require Import NArith ZArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
'''
out+='Definition memory_width_nodes : seq (VarOrder.T * hfexpr VarOrder.T) := '+seq([f'({n},{e})' for n,e in zip(ids,expr)])+'.\n'
out+='Definition memory_width_offsets := '+seq([str(x)+'%nat' for x in [pos[0]]+[b-a-1 for a,b in zip(pos,pos[1:])]])+'.\n'
wireposes=[];wiredist=[]
for target,source in [(1476,8200),(1480,8204)]:
 d=bisect.bisect_right(q,model.index(f'(@Swire VarOrder.T {target} '))-1
 c=bisect.bisect_right(q,model.index(f'(@Sfcnct VarOrder.T (@Eid VarOrder.T {target}) (@Eref VarOrder.T (@Eid VarOrder.T {source})))'))-1
 wireposes.append(d);wiredist.append(c-d-1)
out+=f'''Lemma memory_width_wire writing : declared_wire_check flat_memories flat_statements
 (if writing then {wireposes[1]} else {wireposes[0]}) (if writing then {wiredist[1]} else {wiredist[0]})
 (if writing then 1480 else 1476) (if writing then 8204 else 8200) 6 = true.
Proof. destruct writing;vm_compute;reflexivity. Qed.
'''
out+='''Lemma memory_width_positions : select_node_offsets memory_width_offsets flat_statements = Some memory_width_nodes.
Proof. vm_compute; reflexivity. Qed.
Lemma memory_width_safety : selected_node_safety flat_memories flat_statements memory_width_offsets flat_statements = true.
Proof. vm_compute; reflexivity. Qed.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Definition memory_request_width (writing:bool) (kind:nat) : N :=
 if writing then nth 0 [::0;32;16;8] kind else nth 0 [::0;32;16;8;16;8;0;0] kind.
Definition memory_request_active writing kind := negb (N.eqb (memory_request_width writing kind) 0).
'''
# Separate cases inside a single theorem, no per-node wrappers.
out+='''Theorem memory_width_decoder_history writing kind invalid history limit :
 (kind < (if writing then 4 else 8))%coq_nat ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter invalid flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 (forall i, (i <= limit)%coq_nat -> VM.find (if writing then 7996 else 7755) (history i) = Some (Gval (Fuint (if writing then 2 else 3)) (from_N (if writing then 2 else 3) (N.of_nat kind)))) ->
 forall time, (12 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 VM.find (if writing then 8002 else 7995) (history time) = Some (Gval (Fuint 6) (from_N 6 (memory_request_width writing kind))).
Proof.
 intros Kind Steps Source. destruct writing;cbn in Kind.
'''
for writing in [True,False]:
 codes=[3,2,1] if writing else [0,3,2,1,5,4];widths=[8,16,32] if writing else [0,8,16,32,8,16];baseid=7997 if writing else 7984;offset=12 if writing else 0;values=[0]*(4 if writing else 8)
 out+=' - '\
 + '\n'
 for j,(code,width) in enumerate(zip(codes,widths)):
  for is_mux in [False,True]:
   n=baseid+2*j+int(is_mux);idx=offset+2*j+int(is_mux);depth=j+2 if is_mux else 1
   if is_mux:values[code]=width;bits=[f'from_N 6 {v}' for v in values];w=6
   else:bits=['[::true]' if k==code else '[::false]' for k in range(len(values))];w=1
   term=f'nth [::] {seq(bits)} kind'
   out+=f''' assert (V{n} : forall time, ({depth} <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find {n} (history time) = Some (Gval (Fuint {w}) ({term}))).
 {{ intros [|time] Lower Upper;try lia.
   eapply (reference_redirect_ground_step memory_width_offsets memory_width_nodes {n} ({expr[idx]}));
   [exact memory_width_positions|exact memory_width_safety|apply (List.nth_error_In memory_width_nodes {idx}%nat);vm_compute;reflexivity| |apply Steps;lia].
   intros site. cbn [eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
'''
   lookups=[f'(Source time ltac:(lia))'] if not is_mux else [f'(V{n-1} time ltac:(lia) ltac:(lia))']+([f'(V{n-2} time ltac:(lia) ltac:(lia))'] if j else [])
   out+='   rewrite '+' '.join(lookups)+'. unfold eval_type_of_expr; cbn [type_of_expr\' eval_type_of_ref]; rewrite '+' '.join('?'+x for x in lookups)+'.\n'
   out+=f'   do {len(values)} (destruct kind as [|kind];[reflexivity|]);lia. }}\n'
 out+=f' intros time Lower Upper. specialize (V{baseid+2*len(codes)-1} time ltac:(lia) Upper).\n'
 out+=f' do {len(values)} (destruct kind as [|kind];[exact V{baseid+2*len(codes)-1}|]);lia.\n'
out+='Qed.\n'
p=base/'staged-integration/MemoryRequestWidth.v';mark='(* Shared request semantics. *)';tail=p.read_text().split(mark,1)[1] if p.exists() and mark in p.read_text() else '\n';p.write_text(out+mark+tail)
