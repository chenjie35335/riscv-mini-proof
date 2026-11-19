from pathlib import Path
import re,bisect
root=Path(__file__).resolve().parents[2];p=root/'formal/flat-low/staged-integration';model=(p.parent/'CoreSocModel.v').read_text();positions=[m.start()for m in re.finditer(r'\(@Qcons VarOrder.T ',model)]
ids=list(range(3450,3457))+list(range(3462,3472))+list(range(3505,3519));expr={};pos=[]
for n in ids:
 a=model.index(f'(@Snode VarOrder.T {n} ')+len(f'(@Snode VarOrder.T {n} ');d=0
 for b in range(a,len(model)):
  d+=(model[b]=='(')-(model[b]==')')
  if d==0:break
 expr[n]=model[a:b+1];pos.append(bisect.bisect_right(positions,a)-1)
s='''Require Import RFShiftALUHistory RFShiftCycle RFShiftSemantics RFReferenceWriteEffect CoreSocModel ComparisonNodes ReferenceRedirectSpine SelectedNodeSafety X0ConcretePositionCertificate X0ConcreteSafetyCertificate.
From Coq Require Import NArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
'''
for n in ids:s+=f'Definition rf_ref_shift_expr_{n}:={expr[n]}.\n'
s+='Definition rf_ref_shift_nodes:=[::'+';'.join(f'({n},rf_ref_shift_expr_{n})'for n in ids)+'].\nDefinition rf_ref_shift_offsets:=[::'+';'.join(str(n)+'%nat'for n in [pos[0]]+[b-a-1 for a,b in zip(pos,pos[1:])])+'].\n'
s+='''Lemma rf_ref_shift_positions:select_node_offsets rf_ref_shift_offsets flat_statements=Some rf_ref_shift_nodes.
Proof. vm_compute;reflexivity. Qed.
Lemma rf_ref_shift_safety:selected_node_safety flat_memories flat_statements rf_ref_shift_offsets flat_statements=true.
Proof. vm_compute;reflexivity. Qed.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Definition rf_ref_shift_output immediate lane :VarOrder.T:=if immediate then nth 0[::3518;3514;3510]lane else nth 0[::3471;3466;3456]lane.
Definition rf_ref_shift_word lane left right :=
 let amount:=to_nat(take 5 right)in
 match lane with O=>take 32(zext_to 63(zeros amount++left))|S O=>zext_to 32(drop amount left)|_=>sext_to 32(drop(minn amount 31)left)end.
Lemma rf_ref_shift_word_correct lane left right :(lane<3)%coq_nat ->size left=32%nat ->size right=32%nat ->
 rf_ref_shift_word lane left right=rf_shift_word(negb(Nat.eqb lane 0))(Nat.eqb lane 2)left right.
Proof.
 intros Lane Left Right. rewrite(rf_shift_word_correct _ _ _ _ Left Right).
 pose proof(to_nat_bounded(take 5 right))as Bound. rewrite size_take Right in Bound.
 assert(Small:(to_nat(take 5 right)<=31)%nat)by exact Bound.
 destruct lane as[|[|[|lane]]];try lia;unfold rf_ref_shift_word,rf_shift_spec;cbn[Nat.eqb negb].
 - unfold zext_to. rewrite rf_reference_take_extension;[reflexivity|rewrite size_cat size_zeros Left;apply leq_addl].
 - reflexivity.
 - rewrite(minn_idPl Small);reflexivity.
Qed.
'''
# raw history two families separate to avoid assuming both rs2/immediate at once
for imm in [False,True]:
 family=list(range(3505,3519))if imm else list(range(3450,3457))+list(range(3462,3472));source=2552 if imm else 2804;tag='immediate'if imm else'register';words={2209:'left',source:'right'};width={2209:32,source:32};signed={2209:False,source:False};rank={2209:0,source:0};deps={}
 s+=f'''Theorem rf_ref_shift_{tag}_history invalid history limit left right :
 (forall t,(t<=limit)%coq_nat ->VM.find 2209(history t)=Some(Gval(Fuint 32)left)) ->
 (forall t,(t<=limit)%coq_nat ->VM.find {source}(history t)=Some(Gval(Fuint 32)right)) ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter invalid flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 forall lane t,(lane<3)%coq_nat ->(7<=t)%coq_nat ->(t<=limit)%coq_nat ->
 VM.find(rf_ref_shift_output {str(imm).lower()} lane)(history t)=Some(Gval(Fuint 32)(rf_ref_shift_word lane left right)).
Proof.
 intros Left Right Steps.
'''
 for n in family:
  e=expr[n];ds=list(map(int,re.findall(r'Eid VarOrder.T (\d+)',e)));deps[n]=ds;rank[n]=1+max(rank[d]for d in ds);sg=False
  if 'Uextr'in e:
   hi,lo=map(int,re.search(r'Uextr (\d+) (\d+)',e).groups());v=f'drop {lo}(take {hi+1} {words[ds[0]]})';w=hi+1-lo
  elif 'Bdshl'in e:v=f'zext_to 63(zeros(to_nat {words[ds[1]]})++{words[ds[0]]})';w=63
  elif 'Bdshr'in e:
   sg=signed[ds[0]];w=32;v=f'{"sext_to"if sg else"zext_to"} 32(drop({"minn(to_nat "+words[ds[1]]+")31"if sg else"to_nat "+words[ds[1]]}){words[ds[0]]})'
  elif 'AsSInt'in e:v=words[ds[0]];w=width[ds[0]];sg=True
  else:v=words[ds[0]];w=width[ds[0]]
  words[n]=f'w{n}';width[n]=w;signed[n]=sg;s+=f' set(w{n}:={v}).\n'
  s+=f''' assert(V{n}:forall t,({rank[n]}<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find {n}(history t)=Some(Gval({"Fsint"if sg else"Fuint"} {w})w{n})).
 {{ intros [|t] Lower Upper;[lia|]. eapply(reference_redirect_ground_step rf_ref_shift_offsets rf_ref_shift_nodes {n} rf_ref_shift_expr_{n});
 [exact rf_ref_shift_positions|exact rf_ref_shift_safety|apply(List.nth_error_In rf_ref_shift_nodes {ids.index(n)}%nat);reflexivity| |apply Steps;lia].
 intro site. cbn[rf_ref_shift_expr_{n} eval_hfexpr_validif_policy eval_href_validif_policy].
'''
  for d in ds:s+=f' rewrite({"Left"if d==2209 else"Right"if d==source else"V"+str(d)} t ltac:(lia)'+(''if d in [2209,source]else'ltac:(lia)')+').\n'
  s+=' reflexivity. }\n'
 s+=' intros lane t Lane Lower Upper. do 3(destruct lane as[|lane];[|]);try lia.\n' if False else ' intros lane t Lane Lower Upper.\n'
 for j,out in enumerate(([3518,3514,3510]if imm else[3471,3466,3456])):
  s+=f' destruct lane as[|lane]. {{ pose proof(V{out} t ltac:(lia)Upper)as V. unfold '+','.join('w'+str(n)for n in reversed(family)if n<=out)+' in V. rewrite ?drop0 in V. exact V. }\n'
 s+=' lia.\nQed.\n'
# observed wrapper
s+='''Require Import FormalObservedHistory FormalLocalHistory ReferenceControlStabilityHistory.
Theorem rf_reference_shift_observed memory inputs k observed immediate lane left right :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->(lane<3)%coq_nat ->
 VM.find 2209(top_environment observed)=Some(Gval(Fuint 32)left) ->
 VM.find(if immediate then 2552 else 2804)(top_environment observed)=Some(Gval(Fuint 32)right) ->
 VM.find(rf_ref_shift_output immediate lane)(top_environment observed)=Some(Gval(Fuint 32)(rf_ref_shift_word lane left right)).
Proof.
 intros Observe Legal Lane Left Right.
 destruct(observed_history memory inputs k observed Observe Legal)as[reset[history[Last[Steps Resets]]]].
 assert(L:forall t,(t<=7)%coq_nat ->VM.find 2209(history(Nat.add 9252 t))=Some(Gval(Fuint 32)left)).
 { intros t Bound. rewrite(reference_control_stable_2209_history (generated_observation_input inputs k)nil history 9259 reset Resets Steps (Nat.add 9252 t)9259 ltac:(do 8(destruct t as[|t];[vm_compute;lia|]);lia)ltac:(vm_compute;lia)ltac:(do 8(destruct t as[|t];[vm_compute;lia|]);lia)ltac:(vm_compute;lia))Last;exact Left. }
 assert(R:forall t,(t<=7)%coq_nat ->VM.find(if immediate then 2552 else 2804)(history(Nat.add 9252 t))=Some(Gval(Fuint 32)right)).
 { intros t Bound. destruct immediate.
 - rewrite(reference_control_stable_2552_history (generated_observation_input inputs k)nil history 9259 reset Resets Steps (Nat.add 9252 t)9259 ltac:(do 8(destruct t as[|t];[vm_compute;lia|]);lia)ltac:(vm_compute;lia)ltac:(do 8(destruct t as[|t];[vm_compute;lia|]);lia)ltac:(vm_compute;lia))Last;exact Right.
 - rewrite(reference_control_stable_2804_history (generated_observation_input inputs k)nil history 9259 reset Resets Steps (Nat.add 9252 t)9259 ltac:(do 8(destruct t as[|t];[vm_compute;lia|]);lia)ltac:(vm_compute;lia)ltac:(do 8(destruct t as[|t];[vm_compute;lia|]);lia)ltac:(vm_compute;lia))Last;exact Right. }
 assert(S:forall t,(t<7)%coq_nat ->formal_value_iter(formal_invalid_policy(generated_observation_input inputs k)nil)flat_memories(history(Nat.add 9252 t))false(history(Nat.add 9252 t))flat_statements=Some(history(Nat.add 9252(S t)))).
 { intros t Bound. replace(Nat.add 9252(S t))with(S(Nat.add 9252 t))by lia. apply Steps. do 7(destruct t as[|t];[vm_compute;lia|]);lia. }
 rewrite<-Last. destruct immediate.
 - exact(rf_ref_shift_immediate_history _ (fun i=>history(Nat.add 9252 i))7 left right L R S lane 7 Lane ltac:(lia)ltac:(lia)).
 - exact(rf_ref_shift_register_history _ (fun i=>history(Nat.add 9252 i))7 left right L R S lane 7 Lane ltac:(lia)ltac:(lia)).
Qed.
'''
(p/'RFShiftReferenceData.v').write_text(s)
