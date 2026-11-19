from pathlib import Path
import json,re
root=Path(__file__).resolve().parents[2];base=root/'formal/flat-low'
es=sorted(json.loads((base/'event-proof-frontier.json').read_text())['reference_event_flag_spine'],key=lambda e:e['node'])
active={6323:'g 2357=true',6354:'g 2010=true',6704:'False',6705:'False',6706:'False'}
for a,b,d,c in [(6376,6380,2004,2912),(6400,6404,1998,2892),(6424,6428,1992,2872),(6448,6452,1986,2850),(6472,6476,1980,2830),(6496,6500,1974,2806)]:
 active[a]=f'g {d}=true /\\g {c}=true';active[b]=f'g {d}=true'
for n,d in [(6523,1970),(6548,1966),(6573,1962),(6589,1958),(6614,1886),(6630,1951),(6663,1946),(6687,1941)]:active[n]=f'g {d}=true'
s='''Require Import ReferenceEventSpine ReferenceEventConditions ReferenceEventSpineTypes SelectedZeroMux ReferenceRedirectSpine CoreSocModel ComparisonNodes.
From Coq Require Import NArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque generated_modules generated_top flat_statements flat_memories.
Definition reference_event_node_needed (g:VarOrder.T->bool)(node:VarOrder.T):Prop :=
 match node with
'''
for n,a in active.items():s+=f' | {n} => {a}\n'
s+=' | _ => True\n end.\nDefinition reference_event_selected_guard i :VarOrder.T := nth 1707 [::'+ ';'.join(str(e.get('condition',1707)) for e in es)+'] i.\n'
s+='''Theorem reference_event_selected_zero_history g invalid history limit start :
 (forall t,(t<limit)%coq_nat ->formal_value_iter invalid flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 reference_event_safe g ->
 (forall i t,(i<45)%coq_nat ->(start<=t)%coq_nat ->(t<=limit)%coq_nat ->
 reference_event_node_needed g(reference_event_spine_node i) ->
 VM.find(reference_event_selected_guard i)(history t)=Some(Gval(Fuint 1)[::g(reference_event_selected_guard i)])) ->
 forall t,(Nat.add start 46<=t)%coq_nat ->(t<=limit)%coq_nat ->
 VM.find 6780(history t)=Some(Gval(Fuint 1)[::false]).
Proof.
 intros Steps Safe Guards.
 unfold reference_event_safe in Safe.
'''
for idx,e in enumerate(es):
 n=e['node'];a=active.get(n,'True')
 s+=f' assert(Z{n}:forall t,(Nat.add start {idx+1}<=t)%coq_nat ->(t<=limit)%coq_nat ->({a}) ->exists width,VM.find {n}(history t)=Some(Gval(Fuint width)(zeros width))).\n {{ intros[|t] Lower Upper Active;try lia.\n'
 if a=='False':s+=' }\n';continue
 if n==6780:
  s+=' destruct(Z6779 t ltac:(lia)ltac:(lia) I)as[width Zero]. exists width.\n'
  s+=f' eapply(reference_redirect_ground_step reference_event_offsets reference_event_nodes {n} {e["expression"]});[exact reference_event_positions|exact reference_event_safety|apply(List.nth_error_In reference_event_nodes {idx}%nat);vm_compute;reflexivity|intros site;exact Zero|apply Steps;lia]. }}\n';continue
 c=e['condition']
 s+=f' pose proof(Guards {idx}%nat t ltac:(lia)ltac:(lia)ltac:(lia) Active)as Guard.\n change(VM.find {c}(history t)=Some(Gval(Fuint 1)[::g {c}]))in Guard.\n destruct(g {c})eqn:G.\n'
 # parse expression atomic pieces condition, then,else
 parts=re.findall(r'\(@Eref VarOrder.T \(@Eid VarOrder.T (\d+)\)\)|\(@Econst VarOrder.T \(Fuint 1\) \[::(true|false)\]\)',e['expression'])
 assert len(parts)==3,(n,parts)
 for bit,(ref,const) in zip(['true','false'],parts[1:]):
  s+=' - '
  if const=='true':s+='exfalso;intuition congruence.\n';continue
  if ref:s+=f'destruct(Z{ref} t ltac:(lia)ltac:(lia)ltac:(intuition congruence))as[width Zero].\n'
  else:s+='assert(Zero:Some(Gval(Fuint 1)[::false])=Some(Gval(Fuint 1)(zeros 1)))by reflexivity.\n'
  s+=f'   eapply(selected_zero_mux reference_event_offsets reference_event_nodes {n} _ _ _ invalid(history t)(history(S t)){bit} '+('width' if ref else '1')+');\n'
  s+=f'   [exact reference_event_positions|exact reference_event_safety|apply(List.nth_error_In reference_event_nodes {idx}%nat);vm_compute;reflexivity|intros site;exact Guard|intros site;exact Zero|apply Steps;lia].\n'
 s+=' }\n'
s+=''' intros t Lower Upper.
 destruct(Z6780 t Lower Upper I)as[width Zero].
 destruct(reference_event_spine_types_history invalid history limit start Steps 45%nat ltac:(lia)t Lower Upper)as[value[Value Typed]].
 change(VM.find 6780(history t)=Some value)in Value.
 rewrite Zero in Value;inversion Value;subst value.
 change(Gtyp(Fuint width)=Gtyp(Fuint 1))in Typed.
 inversion Typed;subst width;exact Zero.
Qed.
'''
(base/'staged-integration/ReferenceEventSelectedHistory.v').write_text(s)
