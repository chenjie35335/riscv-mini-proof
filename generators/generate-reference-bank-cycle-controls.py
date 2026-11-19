"""Batch already-proved reference RF Boolean controls into one interface."""
from pathlib import Path
import re
root=Path(__file__).resolve().parents[2];p=root/'formal/flat-low/staged-integration'
s=(p/'RFReferenceNopStorageCertificates.v').read_text().split('Definition rf_reference_chain_specs')[1].split('\n')[0]
guards=list(map(int,re.findall(r'\(\d+%nat,(\d+)%nat,',s)))
ids=guards+[2966,2949,2679,2664,2649,2565,1707]
out='''Require Import RFReferenceNopHistory ReferenceBankCycleInputs RFReferenceWriteEffect RFReferenceNopStorageCertificates ReferenceControlStabilityHistory CoreSocModel ComparisonNodes.
From Coq Require Import NArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
'''
out+='Definition ref_bank_control_nodes := [::'+';'.join(map(str,ids))+'].\n'
out+='''Definition ref_bank_controls_concrete env :=forall node,List.In node ref_bank_control_nodes ->VM.find node env=Some(Gval(Fuint 1)[::ref_write_bit env node]).
Lemma ref_bank_guard_member stage :(stage<36)%coq_nat ->List.In(rf_reference_chain_guard stage)ref_bank_control_nodes.
Proof. intro Bound. do 36(destruct stage as[|stage];[vm_compute;tauto|]);lia. Qed.
Lemma ref_bank_permission_member stage :(stage<36)%coq_nat ->rf_reference_write_depth stage=2%nat ->List.In(rf_reference_permission_node stage)ref_bank_control_nodes.
Proof. intro Bound. do 36(destruct stage as[|stage];[vm_compute;intuition discriminate|]);lia. Qed.
Theorem ref_bank_controls_stable inputs path history limit bit :
 (forall t,(t<=limit)%coq_nat ->VM.find 1(history t)=Some(Gval(Fuint 1)[::bit])) ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter(formal_invalid_policy inputs path)flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 forall node,List.In node ref_bank_control_nodes ->forall t u,(200<=t)%coq_nat ->(200<=u)%coq_nat ->(t<=limit)%coq_nat ->(u<=limit)%coq_nat ->VM.find node(history t)=VM.find node(history u).
Proof.
 intros Resets Steps node Member t u Lower Other Upper OtherUpper.
 cbn [ref_bank_control_nodes List.In]in Member.
 repeat destruct Member as[<-|Member];try contradiction.
'''
for n in ids:out+=f' - apply(reference_control_stable_{n}_history inputs path history limit bit Resets Steps t u);lia.\n'
out+='Qed.\n'
(p/'ReferenceBankCycleControls.v').write_text(out)
