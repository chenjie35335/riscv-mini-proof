from pathlib import Path
import re,bisect
root=Path(__file__).resolve().parents[2];p=root/'formal/flat-low/staged-integration';s=(root/'formal/flat-low/CoreSocModel.v').read_text();q=[m.start() for m in re.finditer(r'\(@Qcons VarOrder.T ',s)]
def get(n,kind='Snode'):
 pat=rf'\(@{kind} VarOrder.T '+(rf'\(@Eid VarOrder.T {n}\) ' if kind=='Sfcnct' else rf'{n} ');m=re.search(pat,s);a=m.end();d=0
 for z in range(a,len(s)):
  d+=(s[z]=='(')-(s[z]==')')
  if not d:return s[a:z+1],bisect.bisect_right(q,m.start())-1
nodes={};guards=set()
def visit(n):
 if n in [2209,2552]:return
 if n in nodes:return
 e,pos=get(n);deps=list(map(int,re.findall(r'\(@Eid VarOrder.T (\d+)\)',e)))
 if e.startswith('(@Emux'):guards.add(deps[0]);deps=deps[1:]
 for d in deps:visit(d)
 nodes[n]=(e,pos,deps)
visit(6963);visit(6960)
ids=sorted(nodes);ranks={2209:0,2552:0};width={2209:32,2552:32};words={2209:'rs1',2552:'immediate'}
for n in ids:
 e,pos,ds=nodes[n];ranks[n]=1+max([ranks[d] for d in ds],default=0)
 if e.startswith('(@Emux'):
  g=int(re.findall(r'\(@Eid VarOrder.T (\d+)\)',e)[0]);w=f'(if guards {g} then {words[ds[0]]} else {words[ds[1]]})';width[n]=32
 elif 'Badd' in e:w=f'(from_N 33(to_N {words[ds[0]]}+to_N {words[ds[1]]}))';width[n]=33
 elif 'Utail' in e:w=f'(take 32 {words[ds[0]]})';width[n]=32
 elif ds:w=words[ds[0]];width[n]=width[ds[0]]
 else:w='(zeros 32)';width[n]=32
 words[n]=f'(memory_address_word_{n} guards rs1 immediate)';nodes[n]+=(w,)
h='''Require Import CoreSocModel ComparisonNodes ReferenceRedirectSpine SelectedNodeSafety X0ConcretePositionCertificate X0ConcreteSafetyCertificate ReferenceStoreRequestData ReferenceLoadSemantics DUTRedirectDecode FormalDeclaredWireCheck.
From Coq Require Import NArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Firrtl_with_implicit_widths Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque generated_modules generated_top.
'''
r=h
for n in ids:r+=f'Definition memory_address_expr_{n} := {nodes[n][0]}.\n'
dut=[8075,8076,8083,8084,8199,8203]
for n in dut:r+=f'Definition memory_address_expr_{n} := {get(n)[0]}.\n'
allids=sorted(ids+dut);pos=[get(n)[1] for n in allids];offset=[pos[0]]+[b-a-1 for a,b in zip(pos,pos[1:])]
r+='Definition memory_address_nodes := [::'+';'.join(f'({n},memory_address_expr_{n})'for n in allids)+'].\n'
r+='Definition memory_address_offsets := [::'+';'.join(str(x)+'%nat'for x in offset)+'].\n'
r+='''Lemma memory_address_positions :select_node_offsets memory_address_offsets flat_statements=Some memory_address_nodes.
Proof. vm_compute;reflexivity. Qed.
Lemma memory_address_safety :selected_node_safety flat_memories flat_statements memory_address_offsets flat_statements=true.
Proof. vm_compute;reflexivity. Qed.
'''
wiremap={1710:6960,1520:1710,1714:6963,1524:1714,1475:8199,1479:8203}
for n,source in wiremap.items():
 m=re.search(rf'\(@Swire VarOrder.T {n} ',s);start=bisect.bisect_right(q,m.start())-1;end=get(n,'Sfcnct')[1]
 r+=f'''Lemma memory_address_wire_{n} :declared_wire_check flat_memories flat_statements {start} {end-start-1} {n} {source} 32=true.
Proof. vm_compute;reflexivity. Qed.
'''
r+='Local Opaque flat_statements flat_memories.\n'
r+='Definition memory_address_guards := [::'+';'.join(map(str,sorted(guards)))+'].\n'
for n in ids:
 e,pos,ds,w=nodes[n];r+=f'Definition memory_address_word_{n} (guards:VarOrder.T->bool)(rs1 immediate:bits) := {w}.\n'
 r+=f'''Lemma memory_address_size_{n} guards rs1 immediate :size rs1=32%nat ->size immediate=32%nat ->size {words[n]}={width[n]}%nat.
Proof. intros RS IS. unfold memory_address_word_{n}.
'''
 if e.startswith('(@Emux'):
  g=int(re.findall(r"\(@Eid VarOrder.T (\d+)\)",e)[0]);r+=f' destruct(guards {g});'+'[apply memory_address_size_'+str(ds[0])+'|apply memory_address_size_'+str(ds[1])+'];assumption.\n'
 elif 'Badd' in e:r+=' apply size_from_N.\n'
 elif 'Utail' in e:r+=f' rewrite size_take(memory_address_size_{ds[0]} guards rs1 immediate RS IS);reflexivity.\n'
 elif ds:r+=(' exact RS.\n' if ds[0]==2209 else ' exact IS.\n' if ds[0]==2552 else f' apply memory_address_size_{ds[0]};assumption.\n')
 else:r+=' reflexivity.\n'
 r+='Qed.\n'
r+='''Theorem memory_address_reference_history invalid history limit start guards rs1 immediate :
 size rs1=32%nat ->size immediate=32%nat ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter invalid flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 (forall t,(start<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 2209(history t)=Some(Gval(Fuint 32)rs1)) ->
 (forall t,(start<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 2552(history t)=Some(Gval(Fuint 32)immediate)) ->
 (forall node t,List.In node memory_address_guards ->(start<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find node(history t)=Some(Gval(Fuint 1)[::guards node])) ->
 forall t,(Nat.add start 30<=t)%coq_nat ->(t<=limit)%coq_nat ->
 VM.find 6960(history t)=Some(Gval(Fuint 32)(memory_address_word_6960 guards rs1 immediate)) /\\
 VM.find 6963(history t)=Some(Gval(Fuint 32)(memory_address_word_6963 guards rs1 immediate)).
Proof.
 intros RS IS Steps Src Imm Guards.
'''
for n in ids:
 e,pos,ds,w=nodes[n];r+=f''' assert(V{n}:forall t,(Nat.add start {ranks[n]}<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find {n}(history t)=Some(Gval(Fuint {width[n]}){words[n]})).
 {{ intros[|t] Lower Upper;try lia.
 eapply(reference_redirect_ground_step memory_address_offsets memory_address_nodes {n} memory_address_expr_{n});
 [exact memory_address_positions|exact memory_address_safety|apply(List.nth_error_In memory_address_nodes {allids.index(n)}%nat);vm_compute;reflexivity| |apply Steps;lia].
 intros site. unfold memory_address_word_{n}.
'''
 if e.startswith('(@Emux'):
  g=int(re.findall(r'\(@Eid VarOrder.T (\d+)\)',e)[0]);yes,no=ds
  r+=f''' eapply(store_data_mux_eval _ _ _ {g} {yes} {no} 32);[reflexivity|apply memory_address_size_{no};assumption|apply Guards;[vm_compute;tauto|lia|lia]|apply V{yes};lia|apply V{no};lia|apply dut_decode_adapt;apply memory_address_size_{yes};assumption]. }}
'''
 else:
  r+=f' cbn[memory_address_expr_{n} eval_hfexpr_validif_policy eval_href_validif_policy].\n'
  if ds:
   for d in ds:r+=f' rewrite({"Src" if d==2209 else "Imm" if d==2552 else "V"+str(d)} t ltac:(lia)ltac:(lia)).\n'
  r+=' reflexivity. }\n'
r+=' intros t Lower Upper;split;[apply V6960|apply V6963];lia.\nQed.\n'
# alias outputs
r+='''Theorem memory_address_outputs_history invalid history limit start guards rs1 immediate address :
 size rs1=32%nat ->size immediate=32%nat ->size address=32%nat ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter invalid flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 (forall t,(start<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 2209(history t)=Some(Gval(Fuint 32)rs1)) ->
 (forall t,(start<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 2552(history t)=Some(Gval(Fuint 32)immediate)) ->
 (forall node t,List.In node memory_address_guards ->(start<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find node(history t)=Some(Gval(Fuint 1)[::guards node])) ->
 (forall t,(t<=limit)%coq_nat ->VM.find 8004(history t)=Some(Gval(Fuint 32)address)) ->
 forall t,(Nat.add start 34<=t)%coq_nat ->(t<=limit)%coq_nat ->
 VM.find 1475(history t)=Some(Gval(Fuint 32)address) /\\VM.find 1479(history t)=Some(Gval(Fuint 32)address) /\\
 VM.find 1520(history t)=Some(Gval(Fuint 32)(memory_address_word_6960 guards rs1 immediate)) /\\
 VM.find 1524(history t)=Some(Gval(Fuint 32)(memory_address_word_6963 guards rs1 immediate)).
Proof.
 intros RS IS AS Steps Src Imm Guards Address.
 pose proof(memory_address_reference_history invalid history limit start guards rs1 immediate RS IS Steps Src Imm Guards)as Ref.
'''
for n,dep,rank in [(8075,8004,1),(8076,8075,2),(8199,8076,3),(8083,8004,1),(8084,8083,2),(8203,8084,3)]:
 r+=f''' assert(V{n}:forall t,({rank}<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find {n}(history t)=Some(Gval(Fuint 32)address)).
 {{ intros[|t] Lower Upper;try lia. eapply(reference_redirect_ground_step memory_address_offsets memory_address_nodes {n} memory_address_expr_{n} _ _ invalid(history t)(history t)(history(S t)));[exact memory_address_positions|exact memory_address_safety|apply(List.nth_error_In memory_address_nodes {allids.index(n)}%nat);vm_compute;reflexivity|intros site;apply {"Address" if dep==8004 else "V"+str(dep)};lia|apply Steps;lia]. }}
'''
r+=' intros[|[|[|[|t]]]] Lower Upper;try lia. repeat split.\n'
for n,source in [(1475,8199),(1479,8203)]:r+=f' - eapply declared_wire_checked_value with (old:=history(S(S(S t)))) (current:=history(S(S(S t))));[exact memory_address_wire_{n}|apply V{source};lia|apply dut_decode_adapt;exact AS|apply Steps;lia].\n'
for n,mid,source,proj in [(1520,1710,6960,'proj1'),(1524,1714,6963,'proj2')]:r+=f''' - eapply declared_wire_checked_value with (old:=history(S(S(S t)))) (current:=history(S(S(S t))));[exact memory_address_wire_{n}| |apply dut_decode_adapt;apply memory_address_size_{source};assumption|apply Steps;lia].
 eapply declared_wire_checked_value with (old:=history(S(S t))) (current:=history(S(S t)));[exact memory_address_wire_{mid}|exact({proj}(Ref (S(S t)) ltac:(lia)ltac:(lia)))|apply dut_decode_adapt;apply memory_address_size_{source};assumption|apply Steps;lia].
'''
r+='Qed.\n'
(p/'MemoryAddressOutputs.v').write_text(r)
print(len(ids),max(ranks.values()),sorted(guards))
