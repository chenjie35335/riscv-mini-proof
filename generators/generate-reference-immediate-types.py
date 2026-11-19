"""A single typed DAG certificate for both unselected immediate mux prefixes."""
from pathlib import Path
import re
root=Path(__file__).resolve().parents[2];base=root/'formal/flat-low/staged-integration';model=(root/'formal/flat-low/CoreSocModel.v').read_text();es={}
for m in re.finditer(r'\(@Snode VarOrder.T (\d+) ',model):
 a=m.end();d=0
 for b in range(a,len(model)):
  d+=(model[b]=='(')-(model[b]==')')
  if d==0:break
 es[int(m[1])]=model[a:b+1]
def children(e):
 d=0;out=[]
 for i,c in enumerate(e):
  if c=='(':
   if d==1:a=i
   d+=1
  elif c==')':
   d-=1
   if d==1 and e[a:a+2]=='(@':out.append(e[a:i+1])
 return out
def leaves(e):
 ch=children(e)
 if e.startswith('(@Emux'):return ch[1:]
 if e.startswith('(@Eref') or e.startswith('(@Econst'):return [e]
 return ch
def deps(e):return [int(re.search(r'\(@Eid VarOrder.T (\d+)\)',x)[1]) for x in leaves(e) if x.startswith('(@Eref')]
seen=set()
def walk(n):
 if n==1884 or n in seen:return
 seen.add(n)
 for d in deps(es[n]):walk(d)
for n in [2552]:walk(n)
ids=sorted(seen);widths={1884:32};ranks={1884:0}
def leafwidth(e):
 if e.startswith('(@Eref'):return widths[int(re.search(r'\(@Eid VarOrder.T (\d+)\)',e)[1])]
 return int(re.search(r'\(Fuint (\d+)\)',e)[1])
for n in ids:
 e=es[n];ls=leaves(e)
 if '(Uextr ' in e:
  hi,lo=map(int,re.search(r'\(Uextr (\d+) (\d+)\)',e).groups());widths[n]=max(hi+1-lo,0)
 elif e.startswith('(@Eprim_binop'):widths[n]=sum(map(leafwidth,ls))
 elif e.startswith('(@Emux'):widths[n]=max(map(leafwidth,ls))
 else:widths[n]=leafwidth(e)
 ranks[n]=1+max([ranks[d] for d in deps(e)] or [0])
groups={}
for g in range(3):
 for n in re.findall(r'Lemma reference_control_member_(\d+)',(base/f'ReferenceControlNodeCongruence{g}.v').read_text()):groups[int(n)]=g
seq=lambda xs:'[::'+';'.join(map(str,xs))+']'
natseq=lambda xs:seq(str(n)+'%nat' for n in xs)
s='Definition reference_immediate_ids : seq VarOrder.T := '+seq(ids)+'.\n'
s+='Definition reference_immediate_widths : seq nat := '+natseq(widths[n] for n in ids)+'.\n'
s+='Definition reference_immediate_ranks : seq nat := '+natseq(ranks[n] for n in ids)+'.\n'
s+='Definition reference_immediate_groups : seq nat := '+natseq(groups[n] for n in ids)+'.\n'
s+='Definition reference_immediate_expressions : seq (hfexpr VarOrder.T) := '+seq('reference_control_expr_'+str(n) for n in ids)+'.\n'
s+='Definition reference_immediate_dependencies : seq (seq VarOrder.T) := '+seq(seq(deps(es[n])) for n in ids)+'.\n'
s+='''Definition reference_immediate_node i := nth 0 reference_immediate_ids i.
Definition reference_immediate_width i := nth 0%nat reference_immediate_widths i.
Definition reference_immediate_rank i := nth 0%nat reference_immediate_ranks i.
Definition reference_immediate_expression i := nth (@Econst VarOrder.T (Fuint 1) [::false]) reference_immediate_expressions i.
Definition reference_immediate_refs i := nth [::] reference_immediate_dependencies i.
Definition reference_immediate_width_of node := if node == 1884 then 32%nat else reference_immediate_width (index node reference_immediate_ids).
Definition reference_immediate_nodes i := match nth 2%nat reference_immediate_groups i with O => reference_control_0_nodes | S O => reference_control_1_nodes | _ => reference_control_2_nodes end.
Definition reference_immediate_offsets i := match nth 2%nat reference_immediate_groups i with O => reference_control_0_offsets | S O => reference_control_1_offsets | _ => reference_control_2_offsets end.
'''
count=len(ids)
s+=f'''Lemma reference_immediate_plan i : (i < {count})%coq_nat ->
 immediate_expression_check reference_immediate_width_of (reference_immediate_expression i) = Some (reference_immediate_width i,reference_immediate_refs i) /\\ (0 < reference_immediate_rank i)%coq_nat.
Proof. intro Bound. do {count} (destruct i as [|i];[split;[vm_compute;reflexivity|vm_compute;lia]|]);lia. Qed.
Lemma reference_immediate_member i : (i < {count})%coq_nat ->
 List.In (reference_immediate_node i,reference_immediate_expression i) (reference_immediate_nodes i).
Proof. intro Bound.
'''
for n in ids:s+=f' destruct i as [|i];[exact reference_control_member_{n}|].\n'
s+=' lia.\nQed.\n'
s+=f'''Lemma reference_immediate_predecessors i node : (i < {count})%coq_nat -> List.In node (reference_immediate_refs i) ->
 node = 1884 \/ exists j, (j < i)%coq_nat /\\ (j < {count})%coq_nat /\\ reference_immediate_node j = node /\\ reference_immediate_width_of node = reference_immediate_width j /\\ (reference_immediate_rank j < reference_immediate_rank i)%coq_nat.
Proof.
 intro Bound.
'''
for n in ids:
 ds=deps(es[n]);s+=' destruct i as [|i].\n { cbn [reference_immediate_refs reference_immediate_dependencies nth List.In].\n'
 if not ds:s+=' contradiction. }\n';continue
 s+=' intro Member.\n'
 for d in ds:
  s+=' destruct Member as [<-|Member].\n'
  if d==1884:s+=' - left;reflexivity.\n'
  else:s+=f' - right;exists {ids.index(d)}%nat;vm_compute;repeat split;try reflexivity;lia.\n'
 s+=' - contradiction. }\n'
s+=' lia.\nQed.\n'
s+=f'''Theorem reference_immediate_node_type_step i invalid old result : (i < {count})%coq_nat ->
 (forall site value, eval_hfexpr_validif_policy (isolated_validif_policy invalid) site flat_memories (reference_immediate_expression i) old old = Some value -> type_of_val value = Gtyp (Fuint (reference_immediate_width i))) ->
 formal_value_iter invalid flat_memories old false old flat_statements = Some result ->
 exists value, VM.find (reference_immediate_node i) result = Some value /\\ type_of_val value = Gtyp (Fuint (reference_immediate_width i)).
Proof.
 intros Bound Shape Step.
 assert (Position : select_node_offsets (reference_immediate_offsets i) flat_statements = Some (reference_immediate_nodes i)).
 {{ unfold reference_immediate_offsets,reference_immediate_nodes;destruct (nth 2%nat reference_immediate_groups i) as [|[|g]];[exact reference_control_0_positions|exact reference_control_1_positions|exact reference_control_2_positions]. }}
 assert (Safety : selected_node_safety flat_memories flat_statements (reference_immediate_offsets i) flat_statements = true).
 {{ unfold reference_immediate_offsets;destruct (nth 2%nat reference_immediate_groups i) as [|[|g]];[exact reference_control_0_safety|exact reference_control_1_safety|exact reference_control_2_safety]. }}
 destruct (selected_node_safe_position flat_memories flat_statements (reference_immediate_offsets i) flat_statements (reference_immediate_nodes i) _ _ Position Safety (reference_immediate_member i Bound)) as [count [tail [Pos [Safe Nonreg]]]].
 destruct (formal_successful_node_evaluation count flat_statements tail _ _ invalid flat_memories old false old result Pos Step) as [value Eval]. rewrite add0n in Eval.
 exists value. split;[eapply formal_combinational_known_node;[exact Pos|exact Safe|exact Nonreg|exact Eval|eapply Shape;exact Eval|exact Step]|eapply Shape;exact Eval].
Qed.
Theorem reference_immediate_types_history invalid history limit start :
 (forall t, (t < limit)%coq_nat -> formal_value_iter invalid flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 (forall t, (start <= t)%coq_nat -> (t <= limit)%coq_nat -> exists value, VM.find 1884 (history t) = Some value /\\ type_of_val value = Gtyp (Fuint 32)) ->
 forall i, (i < {count})%coq_nat -> forall t, (Nat.add start (reference_immediate_rank i) <= t)%coq_nat -> (t <= limit)%coq_nat ->
 exists value, VM.find (reference_immediate_node i) (history t) = Some value /\\ type_of_val value = Gtyp (Fuint (reference_immediate_width i)).
Proof.
 intros Steps Source i. induction i using lt_wf_ind. intros Bound [|t] Lower Upper.
 - pose proof (proj2 (reference_immediate_plan i Bound));lia.
 - eapply reference_immediate_node_type_step;[exact Bound| |apply Steps;lia].
   intros site value Eval. eapply immediate_expression_check_sound;[exact (proj1 (reference_immediate_plan i Bound))| |exact Eval].
   intros node Member. destruct (reference_immediate_predecessors i node Bound Member) as [->|[j [Before [J [Node [Width Rank]]]]]].
   + change (exists value, VM.find 1884 (history t) = Some value /\\ type_of_val value = Gtyp (Fuint 32)).
     apply Source;[pose proof (proj2 (reference_immediate_plan i Bound));lia|lia].
   + rewrite Width. rewrite <- Node. apply (H j Before J t);lia.
Qed.
'''
p=base/'ReferenceImmediateTypes.v';mark='(* Generated immediate type DAG. *)';prefix=p.read_text().split(mark,1)[0];p.write_text(prefix+mark+'\n'+s)
print('Generated',count,'typed nodes; depth',max(ranks.values()),'prefix indexes',ids.index(2238),ids.index(2539))
