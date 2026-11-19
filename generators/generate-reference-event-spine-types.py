from pathlib import Path
import re
root=Path(__file__).resolve().parents[2];base=root/'formal/flat-low/staged-integration';src=(base/'ReferenceEventSpine.v').read_text();line=src.split('Definition reference_event_nodes := ')[1].split('\n')[0];ids=list(map(int,re.findall(r'\((\d+),',line)));assert len(ids)==46
model=(root/'formal/flat-low/CoreSocModel.v').read_text();deps=[]
for n in ids:
 m=re.search(rf'\(@Snode VarOrder.T {n} ',model);a=m.end();d=0
 for z in range(a,len(model)):
  d+=(model[z]=='(')-(model[z]==')')
  if not d:e=model[a:z+1];break
 ds=list(map(int,re.findall(r'\(@Eid VarOrder.T (\d+)\)',e)))
 if e.startswith('(@Emux'):ds=ds[1:]
 assert all(x in ids[:ids.index(n)] for x in ds)
 deps.append(ds)
r='''Require Import ReferenceImmediateTypes ReferenceEventSpine FormalSuccessfulNodeEvaluation SelectedNodeSafety FormalTypedNodeEquation ScalarSinkTypes DUTRedirectDecode FormalObservedHistory FormalLocalHistory CoreSocModel ComparisonNodes X0ConcretePositionCertificate X0ConcreteSafetyCertificate.
From Coq Require Import NArith List Lia Arith.Wf_nat.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Definition reference_event_spine_node i :=fst(nth (0,(@Econst VarOrder.T(Fuint 1)[::false]))reference_event_nodes i).
Definition reference_event_spine_expression i :=snd(nth (0,(@Econst VarOrder.T(Fuint 1)[::false]))reference_event_nodes i).
Definition reference_event_spine_rank i :=S i.
'''
r+='Definition reference_event_spine_dependencies := [::'+';'.join('[::'+';'.join(map(str,ds))+']' for ds in deps)+'].\n'
r+='''Definition reference_event_spine_refs i :=nth [::]reference_event_spine_dependencies i.
Lemma reference_event_spine_type_plan i :(i<46)%coq_nat ->
 immediate_expression_check(fun _=>1%nat)(reference_event_spine_expression i)=Some(1%nat,reference_event_spine_refs i).
Proof. intro Bound. do 46(destruct i as[|i];[vm_compute;reflexivity|]);lia. Qed.
Lemma reference_event_spine_type_member i :(i<46)%coq_nat ->
 List.In(reference_event_spine_node i,reference_event_spine_expression i)reference_event_nodes.
Proof.
 intro Bound. apply(List.nth_error_In reference_event_nodes i).
 do 46(destruct i as[|i];[vm_compute;reflexivity|]);lia.
Qed.
Lemma reference_event_spine_type_predecessors i node :(i<46)%coq_nat ->List.In node(reference_event_spine_refs i) ->
 exists j,(j<i)%coq_nat /\\(j<46)%coq_nat /\\reference_event_spine_node j=node.
Proof.
 intro Bound.
'''
for i,ds in enumerate(deps):
 r+=' destruct i as[|i].\n { cbn [reference_event_spine_refs reference_event_spine_dependencies nth List.In]. intro Member.\n'
 for dep in ds:r+=f' destruct Member as[<-|Member].\n - exists {ids.index(dep)}%nat;vm_compute;repeat split;try reflexivity;lia.\n'
 r+=' '+('- ' if ds else '')+'contradiction. }\n'
r+=''' lia.
Qed.
Theorem reference_event_spine_type_step i invalid old result :(i<46)%coq_nat ->
 (forall node,List.In node(reference_event_spine_refs i) ->exists value,VM.find node old=Some value /\\type_of_val value=Gtyp(Fuint 1)) ->
 formal_value_iter invalid flat_memories old false old flat_statements=Some result ->
 exists value,VM.find(reference_event_spine_node i)result=Some value /\\type_of_val value=Gtyp(Fuint 1).
Proof.
 intros Bound Dependencies Step.
 destruct(selected_node_safe_position flat_memories flat_statements reference_event_offsets flat_statements reference_event_nodes _ _ reference_event_positions reference_event_safety(reference_event_spine_type_member i Bound))as[count[tail[Position[Safe Nonreg]]]].
 destruct(formal_successful_node_evaluation count flat_statements tail _ _ invalid flat_memories old false old result Position Step)as[value Eval]. rewrite add0n in Eval.
 assert(Typed:type_of_val value=Gtyp(Fuint 1)).
 { eapply immediate_expression_check_sound;[exact(reference_event_spine_type_plan i Bound)|exact Dependencies|exact Eval]. }
 exists value;split;[|exact Typed].
 eapply formal_combinational_known_node;[exact Position|exact Safe|exact Nonreg|exact Eval|exact Typed|exact Step].
Qed.
Theorem reference_event_spine_types_history invalid history limit start :
 (forall t,(t<limit)%coq_nat ->formal_value_iter invalid flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 forall i,(i<46)%coq_nat ->forall t,(Nat.add start(reference_event_spine_rank i)<=t)%coq_nat ->(t<=limit)%coq_nat ->
 exists value,VM.find(reference_event_spine_node i)(history t)=Some value /\\type_of_val value=Gtyp(Fuint 1).
Proof.
 intros Steps i. induction i using lt_wf_ind. intros Bound[|t]Lower Upper.
 - unfold reference_event_spine_rank in Lower;lia.
 - eapply reference_event_spine_type_step;[exact Bound| |apply Steps;lia].
   intros node Member. destruct(reference_event_spine_type_predecessors i node Bound Member)as[j[Before[J Node]]].
   rewrite<-Node. apply(H j Before J t);unfold reference_event_spine_rank in *;lia.
Qed.
Theorem reference_event_spine_types_observed memory inputs k observed i :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->(i<46)%coq_nat ->
 exists value,VM.find(reference_event_spine_node i)(top_environment observed)=Some value /\\type_of_val value=Gtyp(Fuint 1).
Proof.
 intros Observe Legal Bound.
 destruct(observed_history memory inputs k observed Observe Legal)as[reset[history[Last[Steps Resets]]]].
 rewrite<-Last. assert(Big:(46<=9259)%coq_nat)by(vm_compute;lia). apply(reference_event_spine_types_history _ history 9259 0 Steps i Bound 9259);unfold reference_event_spine_rank;cbn[Nat.add];lia.
Qed.
'''
for i,n in enumerate(ids):
 r+=f'''Corollary reference_event_spine_{n}_type_history invalid history limit start t :
 (forall j,(j<limit)%coq_nat ->formal_value_iter invalid flat_memories(history j)false(history j)flat_statements=Some(history(S j))) ->
 (Nat.add start {i+1}<=t)%coq_nat ->(t<=limit)%coq_nat ->
 exists value,VM.find {n}(history t)=Some value /\\type_of_val value=Gtyp(Fuint 1).
Proof. intros Steps Lower Upper;exact(reference_event_spine_types_history invalid history limit start Steps {i}%nat ltac:(lia)t Lower Upper). Qed.
'''
(base/'ReferenceEventSpineTypes.v').write_text(r)
