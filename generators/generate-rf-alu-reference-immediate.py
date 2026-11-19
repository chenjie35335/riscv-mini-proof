from pathlib import Path
import re
root=Path(__file__).resolve().parents[2];p=root/'formal/flat-low/staged-integration';model=(root/'formal/flat-low/CoreSocModel.v').read_text();expr={}
for m in re.finditer(r'\(@Snode VarOrder.T (\d+) ',model):
 n=int(m[1])
 if not 2210<=n<=2552:continue
 d=1;j=m.end()
 while d:d+=(model[j]=='(')-(model[j]==')');j+=1
 expr[n]=model[m.end():j-1]
types=(p/'ReferenceImmediateTypes.v').read_text();ids=list(map(int,re.search(r'Definition reference_immediate_ids[^\n]*\[::([^]]*)\]',types)[1].split(';')))
decode=(p/'ReferenceInstructionDecode.v').read_text();guards=list(map(int,re.search(r'Definition reference_instruction_guards[^\n]*\[::([^]]*)\]',decode)[1].split(';')))
seq=lambda xs:'[::'+';'.join(map(str,xs))+']'
out='''Require Import ReferenceControlNodeCongruence2 ReferenceRedirectSpine DUTRedirectDecode CoreSocModel ComparisonNodes RFALUData RFScalarControl ReferenceBranchImmediate ReferenceImmediateTypes ReferenceLoadImmediate ReferenceControlExpressions ReferenceInstructionDecode LoadImmediateSemantics ReferenceLoadSemantics.
From Coq Require Import NArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
'''
for label,start,end,width in [('low',2232,2246,12),('high',2524,2550,32)]:
 pre='rf_i_'+label;nodes=list(range(start,end+1));rows=[list(map(int,re.findall(r'@Eid VarOrder.T (\d+)',expr[n])))for n in nodes]
 out+=f'Definition {pre}_node n :VarOrder.T:=N.of_nat(Nat.add {start} n).\nDefinition {pre}_decoder n :=nth 0%nat '+seq([str(guards.index(r[0]))+'%nat'for r in rows])+' n.\n'
 out+=f'Definition {pre}_guard n :=reference_instruction_guard({pre}_decoder n).\nDefinition {pre}_yes n :VarOrder.T:=nth 0 '+seq([r[1]for r in rows])+' n.\n'
 out+=f'Definition {pre}_expression n :=@Emux VarOrder.T(@Eref VarOrder.T(@Eid VarOrder.T({pre}_guard n)))(@Eref VarOrder.T(@Eid VarOrder.T({pre}_yes n)))(@Eref VarOrder.T(@Eid VarOrder.T(match n with O=>{start-1}|S n=>{pre}_node n end))).\n'
 out+=fr'''Lemma {pre}_value n inputs path history limit reset time word :(n<{len(nodes)})%coq_nat ->
 (forall t,(t<=limit)%coq_nat ->VM.find 1(history t)=Some(Gval(Fuint 1)[::reset])) ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter(formal_invalid_policy inputs path)flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 (500<=time)%coq_nat ->(time<limit)%coq_nat ->
 (forall site,eval_hfexpr_validif_policy(isolated_validif_policy(formal_invalid_policy inputs path))site flat_memories({pre}_expression n)(history time)(history time)=Some(Gval(Fuint {width})word)) ->
 VM.find({pre}_node n)(history time)=Some(Gval(Fuint {width})word).
Proof. intros Bound Resets Steps Lower Upper Eval.
'''
 for n in nodes:out+=f'destruct n as[|n];[exact(reference_immediate_value_history {ids.index(n)} inputs path history limit reset time {width} word ltac:(lia)Resets Steps Lower Upper Eval)|].\n'
 out+='lia. Qed.\n'
 out+=fr'''Lemma {pre}_types n invalid history limit time :(n<{len(nodes)})%coq_nat ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter invalid flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 (forall t,(200<=t)%coq_nat ->(t<=limit)%coq_nat ->exists v,VM.find 1884(history t)=Some v /\type_of_val v=Gtyp(Fuint 32)) ->
 (500<=time)%coq_nat ->(time<=limit)%coq_nat ->
 (exists v,VM.find({pre}_yes n)(history time)=Some v /\type_of_val v=Gtyp(Fuint {width})) /\
 (exists v,VM.find(match n with O=>{start-1}|S n=>{pre}_node n end)(history time)=Some v /\type_of_val v=Gtyp(Fuint {width})).
Proof. intros Bound Steps Source Lower Upper.
'''
 for row in rows:
  out+='destruct n as[|n]. { split.\n'
  for n in row[1:]:out+=f'- exact(reference_immediate_types_history invalid history limit 200 Steps Source {ids.index(n)}%nat ltac:(lia)time ltac:(cbv[reference_immediate_rank reference_immediate_ranks nth];lia)Upper).\n'
  out+='}\n'
 out+='lia. Qed.\n'
 out+=f'''Lemma {pre}_decode instruction lane n :(lane<3)%coq_nat ->(n<{len(nodes)})%coq_nat ->
 N.land(to_N instruction)(reference_instruction_mask(Nat.add 3 lane))=reference_instruction_code(Nat.add 3 lane) ->
 N.eqb(reference_instruction_code({pre}_decoder n))(N.land(to_N instruction)(reference_instruction_mask({pre}_decoder n)))=Nat.eqb n lane.
Proof. intros Lane Bound Match.
 rewrite(rf_reference_decode_onehot instruction(Nat.add 3 lane)({pre}_decoder n)ltac:(lia)ltac:(do {len(nodes)}(destruct n as[|n];[vm_compute;lia|]);lia)Match).
 do 3(destruct lane as[|lane];[do {len(nodes)}(destruct n as[|n];[reflexivity|]);lia|]);lia.
Qed.
'''
f=p/'RFALUReferenceImmediate.v';marker='(* Actual I-format semantics. *)';old=f.read_text()if f.exists()else'';tail=old.split(marker,1)[1]if marker in old else'\n';f.write_text(out+marker+tail)
