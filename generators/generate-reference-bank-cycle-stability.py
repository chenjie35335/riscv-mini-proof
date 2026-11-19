"""Batched new RF reference data DAG, stopping at audited control/load cuts."""
from pathlib import Path
import re,bisect,json
root=Path(__file__).resolve().parents[2];base=root/'formal/flat-low';proof=base/'staged-integration';s=(base/'CoreSocModel.v').read_text();q=[m.start()for m in re.finditer(r'\(@Qcons VarOrder.T ',s)];es={};pos={}
for m in re.finditer(r'\(@Snode VarOrder.T (\d+) ',s):
 a=m.end();d=0
 for b in range(a,len(s)):
  d+=(s[b]=='(')-(s[b]==')')
  if d==0:break
 n=int(m[1]);es[n]=s[a:b+1];pos[n]=bisect.bisect_right(q,a)-1
v=(proof/'RFReferenceWriteEffect.v').read_text();rows=re.search(r'Definition rf_reference_write_rows.*?:= \[::(.*?)\]\.',v)[1];targets=[int(x)for x in re.findall(r'\(\d+%nat,(\d+)%nat,',rows)]+[3221]
stable=set(map(int,re.findall(r'Theorem reference_control_stable_(\d+)_history',(proof/'ReferenceControlStabilityHistory.v').read_text())))|{3347}
seen=set();cuts=set();ranks={}
def deps(n):return sorted(set(map(int,re.findall(r'\(@Eid VarOrder.T (\d+)\)',es[n]))))
def visit(n):
 if n in ranks:return ranks[n]
 if n in stable:cuts.add(n);ranks[n]=0;return 0
 seen.add(n);ranks[n]=1+max([visit(d)for d in deps(n)]or[0]);return ranks[n]
for n in targets:visit(n)
ids=sorted(seen,key=lambda n:pos[n]);cuts=sorted(cuts);count=len(ids)
assert all(d in cuts or ids.index(d)<i for i,n in enumerate(ids)for d in deps(n))
seq=lambda xs:'[::'+';'.join(map(str,xs))+']'
nats=lambda xs:seq(str(x)+'%nat'for x in xs)
out='''Require Import CoreSocModel ComparisonNodes SelectedNodeSafety X0ConcretePositionCertificate X0ConcreteSafetyCertificate ReferenceControlGroundOperations ReferenceControlGroundExpressions ReferenceControlNodeGeneric ReferenceControlStabilityHistory.
From Coq Require Import NArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
'''
out+='Definition ref_bank_cycle_nodes : seq(VarOrder.T*hfexpr VarOrder.T) := '+seq(f'({n},{es[n]})'for n in ids)+'.\n'
poses=[pos[n]for n in ids];out+='Definition ref_bank_cycle_offsets := '+nats([poses[0]]+[b-a-1 for a,b in zip(poses,poses[1:])])+'.\n'
out+='Definition ref_bank_cycle_cuts : seq VarOrder.T := '+seq(cuts)+'.\n'
out+='Definition ref_bank_cycle_ranks := '+nats(ranks[n]for n in ids)+'.\n'
out+='Definition ref_bank_cycle_dependencies : seq(seq VarOrder.T) := '+seq(seq(deps(n))for n in ids)+'.\n'
out+='''Definition ref_bank_cycle_node i :=fst(nth(0,@Econst VarOrder.T(Fuint 1)[::false])ref_bank_cycle_nodes i).
Definition ref_bank_cycle_expression i :=snd(nth(0,@Econst VarOrder.T(Fuint 1)[::false])ref_bank_cycle_nodes i).
Definition ref_bank_cycle_rank i :=nth 0%nat ref_bank_cycle_ranks i.
Definition ref_bank_cycle_refs i :=nth [::]ref_bank_cycle_dependencies i.
Lemma ref_bank_cycle_positions :select_node_offsets ref_bank_cycle_offsets flat_statements=Some ref_bank_cycle_nodes.
Proof. vm_compute;reflexivity. Qed.
Lemma ref_bank_cycle_safety :selected_node_safety flat_memories flat_statements ref_bank_cycle_offsets flat_statements=true.
Proof. vm_compute;reflexivity. Qed.
Local Opaque flat_statements flat_memories generated_modules generated_top.
'''
out+=f'''Lemma ref_bank_cycle_ready i old :(i<{count})%coq_nat ->
 (forall node,List.In node(ref_bank_cycle_refs i) ->exists value ground,VM.find node old=Some value /\\type_of_val value=Gtyp ground) ->
 reference_control_ready old(ref_bank_cycle_expression i).
Proof. intro Bound.
'''
# Ready only descends into branch expressions. All actual branches are references/constants.
def ready(e):
 if e.startswith('(@Eref'):
  d=int(re.search(r'\(@Eid VarOrder.T (\d+)\)',e)[1]);return f'destruct(Values {d} ltac:(vm_compute;tauto))as[value[ground[Value Typed]]]. eapply rc_ref;[exact Value|exists ground;exact Typed].'
 if e.startswith('(@Emux'):
  children=[];depth=0
  for i,c in enumerate(e):
   if c=='(':
    if depth==1:a=i
    depth+=1
   elif c==')':
    depth-=1
    if depth==1:children.append(e[a:i+1])
  return 'apply rc_mux. { '+ready(children[1])+' } { '+ready(children[2])+' }'
 if e.startswith('(@Evalidif'):raise ValueError(e)
 return 'apply '+{'@Econst':'rc_const','@Eprim_unop':'rc_unary','@Eprim_binop':'rc_binary','@Ecast':'rc_cast'}[e.split()[0][1:]]+'.'
for i,n in enumerate(ids):out+=f' destruct i as[|i]. {{ intro Values. change(reference_control_ready old {es[n]}). '+ready(es[n])+' }\n'
out+=' lia. Qed.\n'
out+=f'''Lemma ref_bank_cycle_eval_equal i inputs path left right :(i<{count})%coq_nat ->
 (forall node,List.In node(ref_bank_cycle_refs i) ->VM.find node left=VM.find node right) ->
 forall site,eval_hfexpr_validif_policy(isolated_validif_policy(formal_invalid_policy inputs path))site flat_memories(ref_bank_cycle_expression i)left left=
 eval_hfexpr_validif_policy(isolated_validif_policy(formal_invalid_policy inputs path))site flat_memories(ref_bank_cycle_expression i)right right.
Proof. intro Bound.
'''
for n in ids:
 out+=' destruct i as[|i]. { intros Equal site. cbn[ref_bank_cycle_expression ref_bank_cycle_nodes nth snd eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr\' eval_type_of_ref].\n'
 if deps(n):
  eqs=[f'(Equal {d} ltac:(vm_compute;tauto))'for d in deps(n)]
  out+=' rewrite '+' '.join(eqs)+'. unfold eval_type_of_expr;cbn[type_of_expr\' eval_type_of_ref];rewrite '+' '.join('?'+x for x in eqs)+'.\n'
 out+=' reflexivity. }\n'
out+=' lia. Qed.\n'
# Table dependency and rank certificate.
out+=f'''Lemma ref_bank_cycle_predecessors i node :(i<{count})%coq_nat ->List.In node(ref_bank_cycle_refs i) ->
 List.In node ref_bank_cycle_cuts \/ exists j,(j<i)%coq_nat /\\(j<{count})%coq_nat /\\ref_bank_cycle_node j=node /\\(ref_bank_cycle_rank j<ref_bank_cycle_rank i)%coq_nat.
Proof. intro Bound.
'''
for n in ids:
 out+=' destruct i as[|i]. { cbn[ref_bank_cycle_refs ref_bank_cycle_dependencies nth List.In]. intro Member.\n'
 for d in deps(n):
  out+=' destruct Member as[<-|Member].\n'
  if d in cuts:out+=' - left;vm_compute;tauto.\n'
  else:out+=f' - right;exists {ids.index(d)}%nat;vm_compute;repeat split;try reflexivity;lia.\n'
 out+=' contradiction. }\n'
out+=' lia. Qed.\n'
p=proof/'ReferenceBankCycleStability.v';mark='(* Shared batched history. *)';tail=p.read_text().split(mark,1)[1]if p.exists()and mark in p.read_text()else'\n';p.write_text(out+mark+tail)
(base/'reference-bank-cycle-stability-plan.json').write_text(json.dumps(dict(count=count,maximum_rank=max(ranks[n]for n in ids),targets=targets,cuts=cuts),indent=2)+'\n')
print(count,'nodes; max rank',max(ranks[n]for n in ids),'cuts',len(cuts))
p=proof/'ReferenceBankCycleCuts.v'
if p.exists():
 text=p.read_text().split('(* Shared existing cuts. *)')[0]
 text+='''(* Shared existing cuts. *)
Theorem ref_bank_cycle_cut_facts inputs path history limit bit raw :size raw=32%nat ->
 VM.find 9222(history 0%nat)=Some(Gval(Fuint 32)raw) ->
 (forall t,(t<=limit)%coq_nat ->VM.find 1(history t)=Some(Gval(Fuint 1)[::bit])) ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter(formal_invalid_policy inputs path)flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 forall node,List.In node ref_bank_cycle_cuts ->
 (forall t,(200<=t)%coq_nat ->(t<=limit)%coq_nat ->exists value ground,VM.find node(history t)=Some value /\\type_of_val value=Gtyp ground) /\\
 (forall t u,(200<=t)%coq_nat ->(200<=u)%coq_nat ->(t<=limit)%coq_nat ->(u<=limit)%coq_nat ->VM.find node(history t)=VM.find node(history u)).
Proof. intros Size Initial Resets Steps node Member.
 cbn[ref_bank_cycle_cuts List.In]in Member. repeat destruct Member as[<-|Member];try contradiction.
'''
 for n in cuts:
  if n==3347:
   text+=''' - split.
 + intros t Lower Upper. exists(Gval(Fuint 32)raw),(Fuint 32). split;[apply(ref_bank_raw_history _ history limit raw Size Initial Steps);lia|reflexivity].
 + intros t u Lower Other Upper OtherUpper. rewrite(ref_bank_raw_history _ history limit raw Size Initial Steps t ltac:(lia)Upper)(ref_bank_raw_history _ history limit raw Size Initial Steps u ltac:(lia)OtherUpper);reflexivity.
'''
  else:
   text+=f''' - split.
 + intros t Lower Upper. apply(reference_control_ground_{n}_history inputs path history limit bit Resets Steps t);lia.
 + intros t u Lower Other Upper OtherUpper. apply(reference_control_stable_{n}_history inputs path history limit bit Resets Steps t u);lia.
'''
 text+='Qed.\n';p.write_text(text)
