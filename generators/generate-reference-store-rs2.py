"""Batch the real 11-node store rs2 selector suffix, reusing typed mux proofs."""
from pathlib import Path
import re
root=Path(__file__).resolve().parents[2];base=root/'formal/flat-low/staged-integration'
expr=(base/'ReferenceControlExpressions.v').read_text();types=(base/'ReferenceRs2Types.v').read_text();ids=list(map(int,re.search(r'Definition reference_rs2_ids[^\n]*\[::([^]]*)\]',types)[1].split(';')))
yes=[int(re.findall(r'Eid VarOrder.T (\d+)',re.search(fr'Definition reference_control_expr_{n} := (.*)',expr)[1])[1]) for n in range(2610,2621)]
seq=lambda xs:'[::'+';'.join(map(str,xs))+']'
s=r'''Require Import ReferenceSecondRegisterRead ReferenceRs2Types ReferenceLoadImmediate ReferenceImmediateTypes ReferenceInstructionDecode ReferenceControlStabilityHistory ReferenceControlNodeCongruence0 ReferenceControlNodeCertificates0 ReferenceControlNodeCongruence2 ReferenceControlNodeCertificates2 ReferenceControlExpressions ReferenceRedirectSpine CoreSocModel ComparisonNodes LoadTypeCorrespondence LoadImmediateSemantics RFReadPorts DUTRedirectDecode.
From Coq Require Import NArith List Lia PeanoNat.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Definition reference_store_rs2_node n : VarOrder.T := N.of_nat(Nat.add 2610 n).
Definition reference_store_rs2_decoder n := nth 0%nat [::34%nat;35%nat;36%nat;40%nat;41%nat;42%nat;43%nat;44%nat;45%nat;46%nat;47%nat] n.
Definition reference_store_rs2_guard n := reference_instruction_guard(reference_store_rs2_decoder n).
'''
s+='Definition reference_store_rs2_yes n : VarOrder.T := nth 0 '+seq(yes)+' n.\n'
s+=r'''Definition reference_store_rs2_expression n := @Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T (reference_store_rs2_guard n))) (@Eref VarOrder.T (@Eid VarOrder.T (reference_store_rs2_yes n))) (@Eref VarOrder.T (@Eid VarOrder.T (match n with O=>2609 | S p=>reference_store_rs2_node p end))).
Lemma reference_store_rs2_member n : (n<11)%coq_nat ->List.In(reference_store_rs2_node n,reference_store_rs2_expression n)reference_control_2_nodes.
Proof. intro Bound.
'''
for n in range(2610,2621):s+=f' destruct n as [|n];[exact reference_control_member_{n}|].\n'
s+=' lia. Qed.\n'
s+=r'''Theorem reference_store_rs2_step n invalid old result word : (n<11)%coq_nat ->
 (forall site,eval_hfexpr_validif_policy(isolated_validif_policy invalid)site flat_memories(reference_store_rs2_expression n)old old=Some(Gval(Fuint 5)word)) ->
 formal_value_iter invalid flat_memories old false old flat_statements=Some result ->
 VM.find(reference_store_rs2_node n)result=Some(Gval(Fuint 5)word).
Proof. intros Bound Eval Step. eapply(reference_redirect_ground_step reference_control_2_offsets reference_control_2_nodes _ (reference_store_rs2_expression n));[exact reference_control_2_positions|exact reference_control_2_safety|apply reference_store_rs2_member;exact Bound|exact Eval|exact Step]. Qed.
Lemma reference_store_rs2_same n inputs path history limit reset time : (n<11)%coq_nat ->
 (forall t,(t<=limit)%coq_nat ->VM.find 1(history t)=Some(Gval(Fuint 1)[::reset])) ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter(formal_invalid_policy inputs path)flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 (500<=time)%coq_nat ->(time<limit)%coq_nat ->
 VM.find(reference_store_rs2_node n)(history time)=VM.find(reference_store_rs2_node n)(history(S time)).
Proof. intros Bound Resets Steps Lower Upper.
'''
for n in range(2610,2621):s+=f' destruct n as [|n];[apply(reference_control_stable_{n}_history inputs path history limit reset Resets Steps time (S time));lia|].\n'
s+=' lia. Qed.\n'
s+=r'''Lemma reference_store_rs2_branch_types n invalid history limit time : (n<11)%coq_nat ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter invalid flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 (forall t,(200<=t)%coq_nat ->(t<=limit)%coq_nat ->exists v,VM.find 1884(history t)=Some v /\ type_of_val v=Gtyp(Fuint 32)) ->
 (500<=time)%coq_nat ->(time<=limit)%coq_nat ->
 (exists v,VM.find(reference_store_rs2_yes n)(history time)=Some v /\type_of_val v=Gtyp(Fuint 5)) /\
 (exists v,VM.find(match n with O=>2609 | S p=>reference_store_rs2_node p end)(history time)=Some v /\type_of_val v=Gtyp(Fuint 5)).
Proof. intros Bound Steps Source Lower Upper.
'''
for i in range(11):
 s+=' destruct n as [|n]. { split.\n'
 for n in [yes[i],2609+i]:s+=f' - exact(reference_rs2_types_history invalid history limit 200 Steps Source {ids.index(n)}%nat ltac:(vm_compute;lia) time ltac:(cbv [reference_rs2_rank reference_rs2_ranks nth];lia) Upper).\n'
 s+=' }\n'
s+=' lia. Qed.\n'
aux=[1942,2575,1947,2576,1952,2577,2621,2622]
s+='Definition reference_store_rs2_aux_ids : seq VarOrder.T := '+seq(aux)+'.\nDefinition reference_store_rs2_aux_node i := nth 0 reference_store_rs2_aux_ids i.\n'
s+='Definition reference_store_rs2_aux_expressions := '+seq('reference_control_expr_'+str(n) for n in aux)+'.\nDefinition reference_store_rs2_aux_expression i := nth (@Econst VarOrder.T (Fuint 1)[::false]) reference_store_rs2_aux_expressions i.\n'
s+=r'''Lemma reference_store_rs2_aux_value i inputs path history limit reset time width word : (i<8)%coq_nat ->
 (forall t,(t<=limit)%coq_nat ->VM.find 1(history t)=Some(Gval(Fuint 1)[::reset])) ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter(formal_invalid_policy inputs path)flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 (500<=time)%coq_nat ->(time<limit)%coq_nat ->
 (forall site,eval_hfexpr_validif_policy(isolated_validif_policy(formal_invalid_policy inputs path))site flat_memories(reference_store_rs2_aux_expression i)(history time)(history time)=Some(Gval(Fuint width)word)) ->
 VM.find(reference_store_rs2_aux_node i)(history time)=Some(Gval(Fuint width)word).
Proof. intros Bound Resets Steps Lower Upper Eval.
'''
for n in aux:
 g=0 if n<2183 else 2
 s+=f''' destruct i as [|i].
 {{ change (VM.find {n}(history time)=Some(Gval(Fuint width)word)).
 rewrite(reference_control_stable_{n}_history inputs path history limit reset Resets Steps time(S time)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)).
 eapply(reference_redirect_ground_step reference_control_{g}_offsets reference_control_{g}_nodes {n} reference_control_expr_{n});[exact reference_control_{g}_positions|exact reference_control_{g}_safety|exact reference_control_member_{n}|exact Eval|apply Steps;lia]. }}
'''
s+=' lia. Qed.\n'
source=(base/'ReferenceStoreRs1.v').read_text()
a=source.index('Lemma reference_store_rs1_raw');b=source.index('Theorem reference_store_rs1_history',a)
raw=source[a:b].replace('reference_store_rs1_raw','reference_store_rs2_raw').replace('reference_load_rs1_yes','reference_store_rs2_yes').replace('Nat.sub 7 lane','Nat.sub 2 lane').replace('rf_instruction_address false','rf_instruction_address true').replace('rf_instruction_address_size false','rf_instruction_address_size true')
# Generate six actual extraction steps directly; avoid the unnecessary rs1 middle slice.
raw=raw[:raw.index('Proof.')]+'Proof.\n intros Lane Resets Steps Lower Upper Source.\n'
for lane in range(3):
 raw+=' destruct lane as [|lane]. {\n'
 for j in range(2):
  n=aux[2*lane+j];word='take 25 instruction' if j==0 else 'rf_instruction_address true instruction';width=25 if j==0 else 5
  raw+=f''' assert(V{j}:VM.find {n}(history time)=Some(Gval(Fuint {width})({word}))).
 {{ eapply(reference_store_rs2_aux_value {2*lane+j} inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|].
 intro site. cbn [reference_store_rs2_aux_expression reference_store_rs2_aux_expressions nth reference_control_expr_{n} eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite {'Source' if j==0 else 'V0'}. cbn.
'''
  if j:raw+=' unfold rf_instruction_address.\n'
  raw+=' repeat rewrite drop0. repeat rewrite <- take_min. cbn. reflexivity. }\n'
 raw+=' exact V1. }\n'
raw+=' lia. Qed.\n';s+=raw
# Reuse established suffix/enable composition with the second-port certificate batch.
a=source.index('Theorem reference_store_rs1_history');b=source.index('Lemma reference_store_rs1_decode',a)
t=source[a:b].replace('reference_store_rs1','reference_store_rs2').replace('reference_load_rs1','reference_store_rs2').replace('rf_instruction_address false','rf_instruction_address true').replace('rf_instruction_address_size false','rf_instruction_address_size true').replace('Nat.sub 7 lane','Nat.sub 2 lane').replace('2143','2620').replace('2144','2621').replace('2145','2622').replace('2124','2609').replace('(n<19)','(n<11)').replace(' 19 ',' 11 ').replace('_node 18','_node 10').replace('_aux_value 10','_aux_value 6').replace('_aux_value 11','_aux_value 7')
s+=t
p=base/'ReferenceStoreRs2.v';mark='(* Store rs2 observed composition. *)';tail=p.read_text().split(mark,1)[1] if p.exists() and mark in p.read_text() else '\n';p.write_text(s+mark+tail)
