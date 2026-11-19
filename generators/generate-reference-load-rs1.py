"""Batch the real 19-node load rs1 selector suffix and twelve extraction/gating nodes."""
from pathlib import Path
import re
root=Path(__file__).resolve().parents[2];base=root/'formal/flat-low/staged-integration'
expr=(base/'ReferenceControlExpressions.v').read_text();types=(base/'ReferenceRs1Types.v').read_text();ids=list(map(int,re.search(r'Definition reference_rs1_ids[^\n]*\[::([^]]*)\]',types)[1].split(';')))
yes=[int(re.findall(r'Eid VarOrder.T (\d+)',re.search(fr'Definition reference_control_expr_{n} := (.*)',expr)[1])[1]) for n in range(2125,2144)]
seq=lambda xs:'[::'+';'.join(map(str,xs))+']'
s=r'''Require Import ReferenceRegisterRead ReferenceRs1Types ReferenceLoadImmediate ReferenceImmediateTypes ReferenceInstructionDecode ReferenceControlStabilityHistory ReferenceControlNodeCongruence0 ReferenceControlNodeCertificates0 ReferenceControlExpressions ReferenceRedirectSpine CoreSocModel ComparisonNodes LoadTypeCorrespondence LoadImmediateSemantics RFReadPorts DUTRedirectDecode.
From Coq Require Import NArith List Lia PeanoNat.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Definition reference_load_rs1_node n : VarOrder.T := N.of_nat(Nat.add 2125 n).
Definition reference_load_rs1_guard n := reference_instruction_guard(Nat.add 29 n).
'''
s+='Definition reference_load_rs1_yes n : VarOrder.T := nth 0 '+seq(yes)+' n.\n'
s+=r'''Definition reference_load_rs1_expression n := @Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T (reference_load_rs1_guard n))) (@Eref VarOrder.T (@Eid VarOrder.T (reference_load_rs1_yes n))) (@Eref VarOrder.T (@Eid VarOrder.T (match n with O=>2124 | S p=>reference_load_rs1_node p end))).
Lemma reference_load_rs1_member n : (n<19)%coq_nat ->List.In(reference_load_rs1_node n,reference_load_rs1_expression n)reference_control_0_nodes.
Proof. intro Bound.
'''
for n in range(2125,2144):s+=f' destruct n as [|n];[exact reference_control_member_{n}|].\n'
s+=' lia. Qed.\n'
s+=r'''Theorem reference_load_rs1_step n invalid old result word : (n<19)%coq_nat ->
 (forall site,eval_hfexpr_validif_policy(isolated_validif_policy invalid)site flat_memories(reference_load_rs1_expression n)old old=Some(Gval(Fuint 5)word)) ->
 formal_value_iter invalid flat_memories old false old flat_statements=Some result ->
 VM.find(reference_load_rs1_node n)result=Some(Gval(Fuint 5)word).
Proof. intros Bound Eval Step. eapply(reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes _ (reference_load_rs1_expression n));[exact reference_control_0_positions|exact reference_control_0_safety|apply reference_load_rs1_member;exact Bound|exact Eval|exact Step]. Qed.
Lemma reference_load_rs1_same n inputs path history limit reset time : (n<19)%coq_nat ->
 (forall t,(t<=limit)%coq_nat ->VM.find 1(history t)=Some(Gval(Fuint 1)[::reset])) ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter(formal_invalid_policy inputs path)flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 (500<=time)%coq_nat ->(time<limit)%coq_nat ->
 VM.find(reference_load_rs1_node n)(history time)=VM.find(reference_load_rs1_node n)(history(S time)).
Proof. intros Bound Resets Steps Lower Upper.
'''
for n in range(2125,2144):s+=f' destruct n as [|n];[apply(reference_control_stable_{n}_history inputs path history limit reset Resets Steps time (S time));lia|].\n'
s+=' lia. Qed.\n'
s+=r'''Lemma reference_load_rs1_branch_types n invalid history limit time : (n<19)%coq_nat ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter invalid flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 (forall t,(200<=t)%coq_nat ->(t<=limit)%coq_nat ->exists v,VM.find 1884(history t)=Some v /\ type_of_val v=Gtyp(Fuint 32)) ->
 (500<=time)%coq_nat ->(time<=limit)%coq_nat ->
 (exists v,VM.find(reference_load_rs1_yes n)(history time)=Some v /\type_of_val v=Gtyp(Fuint 5)) /\
 (exists v,VM.find(match n with O=>2124 | S p=>reference_load_rs1_node p end)(history time)=Some v /\type_of_val v=Gtyp(Fuint 5)).
Proof. intros Bound Steps Source Lower Upper.
'''
for i in range(19):
 s+=' destruct n as [|n]. { split.\n'
 for n in [yes[i],2124+i]:s+=f' - exact(reference_rs1_types_history invalid history limit 200 Steps Source {ids.index(n)}%nat ltac:(vm_compute;lia) time ltac:(cbv [reference_rs1_rank reference_rs1_ranks nth];lia) Upper).\n'
 s+=' }\n'
s+=' lia. Qed.\n'
aux=[n for pair in [(1955+4*i,1956+4*i)for i in range(5)] for n in pair]+[2144,2145]
s+='Definition reference_load_rs1_aux_ids : seq VarOrder.T := '+seq(aux)+'.\nDefinition reference_load_rs1_aux_node i := nth 0 reference_load_rs1_aux_ids i.\n'
s+='Definition reference_load_rs1_aux_expressions := '+seq('reference_control_expr_'+str(n) for n in aux)+'.\nDefinition reference_load_rs1_aux_expression i := nth (@Econst VarOrder.T (Fuint 1)[::false]) reference_load_rs1_aux_expressions i.\n'
s+=r'''Lemma reference_load_rs1_aux_member i : (i<12)%coq_nat ->List.In(reference_load_rs1_aux_node i,reference_load_rs1_aux_expression i)reference_control_0_nodes.
Proof. intro Bound.
'''
for n in aux:s+=f' destruct i as [|i];[exact reference_control_member_{n}|].\n'
s+=' lia. Qed.\n'
s+=r'''Lemma reference_load_rs1_aux_value i inputs path history limit reset time width word : (i<12)%coq_nat ->
 (forall t,(t<=limit)%coq_nat ->VM.find 1(history t)=Some(Gval(Fuint 1)[::reset])) ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter(formal_invalid_policy inputs path)flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 (500<=time)%coq_nat ->(time<limit)%coq_nat ->
 (forall site,eval_hfexpr_validif_policy(isolated_validif_policy(formal_invalid_policy inputs path))site flat_memories(reference_load_rs1_aux_expression i)(history time)(history time)=Some(Gval(Fuint width)word)) ->
 VM.find(reference_load_rs1_aux_node i)(history time)=Some(Gval(Fuint width)word).
Proof. intros Bound Resets Steps Lower Upper Eval.
 assert(Stable:VM.find(reference_load_rs1_aux_node i)(history time)=VM.find(reference_load_rs1_aux_node i)(history(S time))). {
'''
for n in aux:s+=f' destruct i as [|i];[apply(reference_control_stable_{n}_history inputs path history limit reset Resets Steps time (S time));lia|].\n'
s+=r''' lia. } rewrite Stable. eapply(reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes _ (reference_load_rs1_aux_expression i));[exact reference_control_0_positions|exact reference_control_0_safety|apply reference_load_rs1_aux_member;exact Bound|exact Eval|apply Steps;exact Upper]. Qed.
'''
p=base/'ReferenceLoadRs1.v';mark='(* Actual load rs1 semantics. *)';tail=p.read_text().split(mark,1)[1] if p.exists()and mark in p.read_text()else'\n';s=s.replace('/ (exists','/\\\n (exists');p.write_text(s+mark+tail)
