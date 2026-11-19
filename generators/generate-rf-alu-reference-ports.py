from pathlib import Path
import re
root=Path(__file__).resolve().parents[2];p=root/'formal/flat-low/staged-integration';model=(root/'formal/flat-low/CoreSocModel.v').read_text();expr={}
for m in re.finditer(r'\(@Snode VarOrder.T (\d+) ',model):
 n=int(m[1])
 if not 1883<=n<=2622:continue
 d=1;j=m.end()
 while d:d+=(model[j]=='(')-(model[j]==')');j+=1
 expr[n]=model[m.end():j-1]
def definition(s,name):return re.search(r'Definition '+name+r'[^\n]*:= \[::([^]]*)\]',s)[1]
decode=(p/'ReferenceInstructionDecode.v').read_text()
guards=list(map(int,definition(decode,'reference_instruction_guards').split(';')))
classes=[14,15,16,3,4,5]
out='''Require Import CoreSocModel ComparisonNodes RFALUData RFScalarControl ReferenceRs1Types ReferenceRs2Types ReferenceLoadRs1 ReferenceStoreRs2 ReferenceLoadImmediate ReferenceImmediateTypes ReferenceInstructionDecode ReferenceControlStabilityHistory ReferenceControlNodeCongruence0 ReferenceControlNodeCongruence2 ReferenceControlNodeCertificates0 ReferenceControlNodeCertificates2 ReferenceControlExpressions ReferenceRedirectSpine RFReadPorts DUTRedirectDecode.
From Coq Require Import NArith List Lia PeanoNat.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
'''
seq=lambda xs:'[::'+';'.join(map(str,xs))+']'
for port,start,end,group,lanes in [(1,2102,2143,0,6),(2,2597,2620,2,3)]:
 pre=f'rf_alu_rs{port}';tp=f'reference_rs{port}';text=(p/f'ReferenceRs{port}Types.v').read_text();typeids=list(map(int,definition(text,tp+'_ids').split(';')));ids=list(range(start,end+1));rows=[list(map(int,re.findall(r'@Eid VarOrder.T (\d+)',expr[n])))for n in ids];decoder=[guards.index(r[0])for r in rows];yes=[r[1]for r in rows];selected=[decoder.index(c)for c in classes[:lanes]];raw=[yes[i]for i in selected];aux=set()
 def visit(n):
  if n==1884 or n in aux:return
  aux.add(n)
  for d in re.findall(r'@Eid VarOrder.T (\d+)',expr[n]):visit(int(d))
 for n in raw:visit(n)
 aux=sorted(aux);aux+=([2144,2145]if port==1 else[2621,2622])
 out+=f'Definition {pre}_node n :VarOrder.T:=N.of_nat(Nat.add {start} n).\nDefinition {pre}_decoder n:=nth 0%nat '+seq([str(i)+'%nat'for i in decoder])+' n.\n'
 out+=f'Definition {pre}_guard n:=reference_instruction_guard({pre}_decoder n).\nDefinition {pre}_yes n :VarOrder.T:=nth 0 '+seq(yes)+' n.\n'
 out+=f'Definition {pre}_target lane:=nth 0%nat '+seq([str(i)+'%nat'for i in selected])+' lane.\n'
 out+=f'Definition {pre}_expression n:=@Emux VarOrder.T(@Eref VarOrder.T(@Eid VarOrder.T({pre}_guard n)))(@Eref VarOrder.T(@Eid VarOrder.T({pre}_yes n)))(@Eref VarOrder.T(@Eid VarOrder.T(match n with O=>{start-1}|S n=>{pre}_node n end))).\n'
 out+=f'Lemma {pre}_member n :(n<{len(ids)})%coq_nat ->List.In({pre}_node n,{pre}_expression n)reference_control_{group}_nodes.\nProof. intro Bound.\n'
 for n in ids:out+=f'destruct n as[|n];[exact reference_control_member_{n}|].\n'
 out+='lia. Qed.\n'
 out+=fr'''Lemma {pre}_step n invalid old result word :(n<{len(ids)})%coq_nat ->
 (forall site,eval_hfexpr_validif_policy(isolated_validif_policy invalid)site flat_memories({pre}_expression n)old old=Some(Gval(Fuint 5)word)) ->
 formal_value_iter invalid flat_memories old false old flat_statements=Some result ->VM.find({pre}_node n)result=Some(Gval(Fuint 5)word).
Proof. intros Bound Eval Step. eapply(reference_redirect_ground_step reference_control_{group}_offsets reference_control_{group}_nodes _ ({pre}_expression n));[exact reference_control_{group}_positions|exact reference_control_{group}_safety|apply {pre}_member;exact Bound|exact Eval|exact Step]. Qed.
Lemma {pre}_same n inputs path history limit reset time :(n<{len(ids)})%coq_nat ->
 (forall t,(t<=limit)%coq_nat ->VM.find 1(history t)=Some(Gval(Fuint 1)[::reset])) ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter(formal_invalid_policy inputs path)flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 (500<=time)%coq_nat ->(time<limit)%coq_nat ->VM.find({pre}_node n)(history time)=VM.find({pre}_node n)(history(S time)).
Proof. intros Bound Resets Steps Lower Upper.
'''
 for n in ids:out+=f'destruct n as[|n];[apply(reference_control_stable_{n}_history inputs path history limit reset Resets Steps time(S time));lia|].\n'
 out+='lia. Qed.\n'
 out+=fr'''Lemma {pre}_types n invalid history limit time :(n<{len(ids)})%coq_nat ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter invalid flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 (forall t,(200<=t)%coq_nat ->(t<=limit)%coq_nat ->exists v,VM.find 1884(history t)=Some v /\type_of_val v=Gtyp(Fuint 32)) ->
 (500<=time)%coq_nat ->(time<=limit)%coq_nat ->
 (exists v,VM.find({pre}_yes n)(history time)=Some v /\type_of_val v=Gtyp(Fuint 5)) /\
 (exists v,VM.find(match n with O=>{start-1}|S n=>{pre}_node n end)(history time)=Some v /\type_of_val v=Gtyp(Fuint 5)).
Proof. intros Bound Steps Source Lower Upper.
'''
 for n,row in zip(ids,rows):
  out+='destruct n as[|n]. { split.\n'
  for dep in row[1:]:
   i=typeids.index(dep);out+=f'- exact({tp}_types_history invalid history limit 200 Steps Source {i}%nat ltac:(vm_compute;lia)time ltac:(cbv[{tp}_rank {tp}_ranks nth];lia)Upper).\n'
  out+='}\n'
 out+='lia. Qed.\n'
 out+=f'Definition {pre}_aux_node i :VarOrder.T:=nth 0 '+seq(aux)+' i.\n'
 out+=f'Definition {pre}_aux_expr i:=nth(@Econst VarOrder.T(Fuint 1)[::false]) '+seq([f'reference_control_expr_{i}'for i in aux])+' i.\n'
 out+=fr'''Lemma {pre}_value i inputs path history limit reset time width word :(i<{len(aux)})%coq_nat ->
 (forall t,(t<=limit)%coq_nat ->VM.find 1(history t)=Some(Gval(Fuint 1)[::reset])) ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter(formal_invalid_policy inputs path)flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 (500<=time)%coq_nat ->(time<limit)%coq_nat ->
 (forall site,eval_hfexpr_validif_policy(isolated_validif_policy(formal_invalid_policy inputs path))site flat_memories({pre}_aux_expr i)(history time)(history time)=Some(Gval(Fuint width)word)) ->
 VM.find({pre}_aux_node i)(history time)=Some(Gval(Fuint width)word).
Proof. intros Bound Resets Steps Lower Upper Eval.
'''
 for n in aux:
  g=0 if n<=2182 else 2
  out+=f'destruct i as[|i]. {{ change(VM.find {n}(history time)=Some(Gval(Fuint width)word)).\nrewrite(reference_control_stable_{n}_history inputs path history limit reset Resets Steps time(S time)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)).\neapply(reference_redirect_ground_step reference_control_{g}_offsets reference_control_{g}_nodes {n} reference_control_expr_{n});[exact reference_control_{g}_positions|exact reference_control_{g}_safety|exact reference_control_member_{n}|exact Eval|apply Steps;lia]. }}\n'
 out+='lia. Qed.\n'
 out+=fr'''Lemma {pre}_raw inputs path history limit reset time instruction lane :(lane<{lanes})%coq_nat ->
 (forall t,(t<=limit)%coq_nat ->VM.find 1(history t)=Some(Gval(Fuint 1)[::reset])) ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter(formal_invalid_policy inputs path)flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 (500<=time)%coq_nat ->(time<limit)%coq_nat ->VM.find 1884(history time)=Some(Gval(Fuint 32)instruction) ->
 VM.find({pre}_yes({pre}_target lane))(history time)=Some(Gval(Fuint 5)(rf_instruction_address {'false' if port==1 else 'true'} instruction)).
Proof. intros Lane Resets Steps Lower Upper Source.
'''
 for target in raw:
  out+='destruct lane as[|lane]. {\n';vals={1884:('instruction',32)}
  def value(n):
   nonlocal_dummy=None
   global out
   if n in vals:return
   dep=int(re.findall(r'@Eid VarOrder.T (\d+)',expr[n])[0]);value(dep);hi,lo=map(int,re.search(r'\(Uextr (\d+) (\d+)\)',expr[n]).groups());word=f'(drop {lo}(take {hi+1} {vals[dep][0]}))';vals[n]=(word,hi-lo+1)
   out+=f'assert(V{n}:VM.find {n}(history time)=Some(Gval(Fuint {hi-lo+1}){word})).\n{{ eapply({pre}_value {aux.index(n)} inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site. cbn[{pre}_aux_expr nth reference_control_expr_{n} eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite '+('Source'if dep==1884 else f'V{dep}')+'. reflexivity. }\n'
  value(target)
  out+=f'cbn[rf_instruction_address {pre}_yes {pre}_target nth]. rewrite !drop0 !take_take in V{target};try reflexivity. exact V{target}. }}\n'
 out+='lia. Qed.\n'
f=p/'RFALUReferencePorts.v';marker='(* Semantic port composition. *)';old=f.read_text()if f.exists()else'';tail=old.split(marker,1)[1]if marker in old else'\n';f.write_text(out+marker+tail)
