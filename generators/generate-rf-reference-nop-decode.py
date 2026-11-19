"""Kernel-checked NOP constants for the reference RF decode cone."""
from pathlib import Path
import re,json
root=Path(__file__).resolve().parents[2];base=root/'formal/flat-low';proof=base/'staged-integration'
s=(base/'CoreSocModel.v').read_text(); ex={};positions={}
for index,m in enumerate(re.finditer(r'\(@S(?:node|reg|wire|fcnct|skip|mem|assert|assume)\b',s)):
 if not s.startswith('(@Snode VarOrder.T ',m.start()):continue
 h=re.match(r'\(@Snode VarOrder.T (\d+) ',s[m.start():]); n=int(h[1]);start=m.start()+h.end();d=1;j=start
 while d:d+=(s[j]=='(')-(s[j]==')');j+=1
 ex[n]=s[start:j-1];positions[n]=index
refs=lambda n:list(dict.fromkeys(map(int,re.findall(r'\(@Eid VarOrder.T (\d+)\)',ex[n]))))
guards=[];n=3614
while n!=2176:
 ds=refs(n);guards.append(ds[0]);n=ds[-1]
seen={1706,1707};order=[];rank={1706:0,1707:0}
def visit(n):
 if n in seen:return
 seen.add(n)
 for d in refs(n):visit(d)
 order.append(n);rank[n]=1+max([rank[d] for d in refs(n)]+[0])
for n in guards+[3221]:visit(n)
# Reuse the small constant evaluator, independently checked by each Coq evaluation.
src=(root/'formal/generators/generate-nop-kill-values.py').read_text()
exec(src[src.index('def parse(s):'):src.index('values={7748:')])
values={1706:(32,0x13),1707:(1,1)}
exec(src[src.index('def calc(a):'):src.index('for n in order:',src.index('def calc(a):'))])
for n in order:values[n]=calc(parse(ex[n]))
assert values[3221]==(5,0)
print(len(order),'nodes; rank',rank[3221],'guards',[(n,values[n]) for n in guards])
existing={}
for group in range(4):
 t=(proof/f'ReferenceControlNodeCertificates{group}.v').read_text()
 for i,n in enumerate(map(int,re.findall(r'\((\d+),reference_control_expr_',t))):existing[n]=(group,i)
missing=sorted(set(order)-set(existing),key=positions.get)
print('missing',len(missing))
# Actual statement positions: count all Qcons, not only statement constructors.
for n in missing:
 m=re.search(r'\(@Snode VarOrder.T '+str(n)+r' ',s);positions[n]=s[:m.start()].count('(@Qcons VarOrder.T ')
# Qcons surrounding current statement counts it; position is zero-based.
for n in missing:positions[n]-=1
bits=lambda w,v:'[::'+';'.join('true' if v>>i&1 else 'false' for i in range(w))+']'
val=lambda n:f'(Gval (Fuint {values[n][0]}) {bits(*values[n])})'
head='''Require Import CoreSocModel ComparisonNodes X0ConcretePositionCertificate X0ConcreteSafetyCertificate SelectedNodeSafety ReferenceControlExpressions ReferenceRedirectSpine ReferenceControlNodeCertificates0 ReferenceControlNodeCertificates1 ReferenceControlNodeCertificates2 ReferenceControlNodeCertificates3 FormalInstructionResetConstants.
From Coq Require Import ZArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
'''
out=head
for n in missing:out+=f'Definition rf_nop_expr_{n} : hfexpr VarOrder.T := {ex[n]}.\n'
prev=-1;offsets=[]
for n in missing:offsets.append(positions[n]-prev-1);prev=positions[n]
out+='Definition rf_nop_offsets : seq nat := [::'+';'.join(f'{x}%nat' for x in offsets)+'].\n'
out+='Definition rf_nop_nodes : seq (VarOrder.T * hfexpr VarOrder.T) := [::'+';'.join(f'({n},rf_nop_expr_{n})' for n in missing)+'].\n'
out+='''Lemma rf_nop_positions : select_node_offsets rf_nop_offsets flat_statements = Some rf_nop_nodes.
Proof. vm_compute. reflexivity. Qed.
Lemma rf_nop_safety : selected_node_safety flat_memories flat_statements rf_nop_offsets flat_statements = true.
Proof. vm_compute. reflexivity. Qed.
'''
# A single public history theorem; internal assertions remain local to its proof.
out+='Definition rf_reference_nop_guards : seq (VarOrder.T * bool) := [::'+';'.join(f'({n},{str(bool(values[n][1])).lower()})' for n in guards)+'].\n'
out+='''Theorem rf_reference_nop_decode_history invalid history (limit start : nat) :
 (forall time, ((start <= time)%coq_nat /\\ (time <= limit)%coq_nat) -> VM.find 1706 (history time) = Some (Gval (Fuint 32) instruction_nop)) ->
 (forall time, ((start <= time)%coq_nat /\\ (time <= limit)%coq_nat) -> VM.find 1707 (history time) = Some (Gval (Fuint 1) [::true])) ->
 (forall time, (time < limit)%coq_nat -> formal_value_iter invalid flat_memories (history time) false (history time) flat_statements = Some (history (S time))) ->
'''
out+=f''' forall time, ((Nat.add start {max(rank.values())} <= time)%coq_nat /\\ (time <= limit)%coq_nat) ->
 VM.find 3221 (history time) = Some (Gval (Fuint 5) [::false;false;false;false;false]) /\\
 forall node bit, List.In (node,bit) rf_reference_nop_guards -> VM.find node (history time) = Some (Gval (Fuint 1) [::bit]).
Proof.
 intros H1706 H1707 Steps.
'''
for n in order:
 ds=refs(n)
 out+=f' assert (H{n} : forall time, ((Nat.add start {rank[n]} <= time)%coq_nat /\\ (time <= limit)%coq_nat) -> VM.find {n} (history time) = Some {val(n)}).\n {{ intros time [Lower Upper]. destruct time as [|time]; [lia|].\n'
 if n in existing:
  group,idx=existing[n];prefix=f'reference_control_{group}';expr=f'reference_control_expr_{n}'
 else:prefix='rf_nop';idx=missing.index(n);expr=f'rf_nop_expr_{n}'
 out+=f'''  eapply (reference_redirect_ground_step {prefix}_offsets {prefix}_nodes {n} {expr});
  [exact {prefix}_positions|exact {prefix}_safety| | |apply Steps;lia].
  - apply (List.nth_error_In {prefix}_nodes {idx}%nat). vm_compute. reflexivity.
  - intros site. cbn [{expr} eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
'''
 for d in ds:out+=f'    rewrite (H{d} time ltac:(lia)).\n'
 out+='    vm_compute. reflexivity. }\n'
out+=' intros time Bounds. split.\n - apply H3221. lia.\n - intros node bit Member.\n'
out+='   cbn [rf_reference_nop_guards] in Member.\n'
for i,n in enumerate(guards):
 out+=f'   destruct Member as [M{i}|Member].\n   {{ inversion M{i}; subst. apply H{n}. lia. }}\n'
out+='   contradiction.\n'
out+='Qed.\n'
(proof/'RFReferenceNopDecode.v').write_text(out)
(base/'rf-reference-nop-decode.json').write_text(json.dumps({'nodes':order,'guards':guards,'rank':rank,'values':values,'missing':missing},indent=2))
