"""Generate one history theorem for the immutable reference exception mux cone."""
from pathlib import Path
import json,re,bisect
root=Path(__file__).resolve().parents[2];base=root/'formal/flat-low'
model=(base/'CoreSocModel.v').read_text()
entries=json.loads((base/'event-proof-frontier.json').read_text())['reference_event_flag_spine']
expr={e['node']:e['expression'] for e in entries};ids=sorted(expr)
positions=[m.start() for m in re.finditer(r'\(@Qcons VarOrder.T ',model)]
pos=[]
for n in ids:
 needle=f'(@Snode VarOrder.T {n} {expr[n]})'
 assert needle in model,n
 pos.append(bisect.bisect_right(positions,model.index(needle))-1)
seq=lambda x:'[::'+';'.join(map(str,x))+']'
guards=sorted({d for e in entries for d in e['dependencies'] if d not in ids})
rank={};value={}
for n in ids:
 e=next(e for e in entries if e['node']==n)
 deps=[d for d in e['dependencies'] if d in ids]
 rank[n]=1+max([rank[d] for d in deps]+[0])
 refs=lambda m: f'(v{m[1]})' if int(m[1]) in ids else f'(guards {m[1]})'
 v=re.sub(r'\(@Eref VarOrder.T \(@Eid VarOrder.T (\d+)\)\)',refs,expr[n])
 v=re.sub(r'\(@Econst VarOrder.T \(Fuint 1\) \[::(true|false)\]\)',r'\1',v)
 if v.startswith('(@Emux VarOrder.T '):
  a=v[len('(@Emux VarOrder.T '):-1]
  parts=re.findall(r'\([^()]+\)|true|false',a);assert len(parts)==3,(n,a)
  v=f'if {parts[0]} then {parts[1]} else {parts[2]}'
 value[n]=v
out='''Require Import CoreSocModel ComparisonNodes SelectedNodeSafety X0ConcretePositionCertificate X0ConcreteSafetyCertificate ReferenceRedirectSpine DUTRedirectDecode.
From Coq Require Import NArith ZArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
'''
out+='Definition reference_event_nodes := '+seq(f'({n},{expr[n]})' for n in ids)+'.\n'
out+='Definition reference_event_offsets := '+seq(str(x)+'%nat' for x in [pos[0]]+[b-a-1 for a,b in zip(pos,pos[1:])])+'.\n'
out+='''Lemma reference_event_positions : select_node_offsets reference_event_offsets flat_statements = Some reference_event_nodes.
Proof. vm_compute;reflexivity. Qed.
Lemma reference_event_safety : selected_node_safety flat_memories flat_statements reference_event_offsets flat_statements = true.
Proof. vm_compute;reflexivity. Qed.
Local Opaque flat_statements flat_memories generated_modules generated_top.
'''
out+='Definition reference_event_guards : seq VarOrder.T := '+seq(guards)+'.\n'
out+='Definition reference_event_value (guards:VarOrder.T -> bool) :=\n'+''.join(f' let v{n} := {value[n]} in\n' for n in ids)+' v6780.\n'
out+=f'''Theorem reference_event_spine_history guards invalid history limit start :
 (forall i, (i < limit)%coq_nat -> formal_value_iter invalid flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 (forall node i, List.In node reference_event_guards -> (start <= i)%coq_nat -> (i <= limit)%coq_nat -> VM.find node (history i) = Some (Gval (Fuint 1) [::guards node])) ->
 forall time, (Nat.add start {rank[6780]} <= time)%coq_nat -> (time <= limit)%coq_nat ->
 VM.find 6780 (history time) = Some (Gval (Fuint 1) [::reference_event_value guards]).
Proof.
 intros Steps Guards.
'''
for n in ids:
 e=next(e for e in entries if e['node']==n)
 out+=f' set v{n} := ({value[n]}).\n'
 out+=f''' assert (V{n} : forall time, (Nat.add start {rank[n]} <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find {n} (history time) = Some (Gval (Fuint 1) [::v{n}])).
 {{ intros [|time] Lower Upper;try lia.
 eapply (reference_redirect_ground_step reference_event_offsets reference_event_nodes {n} ({expr[n]}));
 [exact reference_event_positions|exact reference_event_safety|apply (List.nth_error_In reference_event_nodes {ids.index(n)}%nat);vm_compute;reflexivity| |apply Steps;lia].
 intros site. cbn [eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
'''
 look=[f'(V{d} time ltac:(lia) ltac:(lia))' if d in ids else f'(Guards {d} time ltac:(vm_compute;tauto) ltac:(lia) ltac:(lia))' for d in e['dependencies']]
 out+=' rewrite '+' '.join(look)+'.\n'
 if 'condition' in e:
  out+=' unfold eval_type_of_expr;cbn [type_of_expr\' eval_type_of_ref];rewrite '+' '.join('?'+x for x in look)+'.\n'
  out+=f' unfold v{n}. destruct (guards {e["condition"]});cbn;try reflexivity;apply dut_decode_adapt;reflexivity. }}\n'
 else:out+=' reflexivity. }\n'
out+=f' intros time Lower Upper. exact (V6780 time Lower Upper).\nQed.\n'
(base/'staged-integration/ReferenceEventSpine.v').write_text(out)
print(f'{len(ids)} nodes, {len(guards)} guards, depth {rank[6780]}')
