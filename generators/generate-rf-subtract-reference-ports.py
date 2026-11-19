#!/usr/bin/env python3
from pathlib import Path
import re
root=Path(__file__).resolve().parents[2]
base=root/'formal/flat-low/staged-integration'
nodes=[2020,2021,2022,2585]
head='''Require Import RFReferenceNopHistory ReferenceBankObservation FormalLocalHistory ReferenceLoadImmediate DUTRedirectDecode RFAddReferencePorts RFAddCycle RFALUReferencePorts RFALUReferenceData ReferenceImmediatePrefix ReferenceRs1Types ReferenceRs2Types ReferenceControlExpressions ReferenceControlStabilityHistory ReferenceControlNodeCertificates0 ReferenceControlNodeCertificates2 ReferenceControlNodeCongruence0 ReferenceControlNodeCongruence2 ReferenceRedirectSpine ReferenceInstructionDecode RFReadPorts CoreSocModel ComparisonNodes.
From Coq Require Import NArith List Lia PeanoNat.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
'''
lines=[head,'Definition rf_subtract_port_nodes :seq VarOrder.T :=[::'+';'.join(map(str,nodes))+'].', 'Definition rf_subtract_port_expr n :=nth (@Econst VarOrder.T(Fuint 1)[::false])[::'+';'.join('reference_control_expr_'+str(n) for n in nodes)+']n.', '''Lemma rf_subtract_port_value n inputs path history limit reset time width word :(n<4)%coq_nat ->
 (forall t,(t<=limit)%coq_nat ->VM.find 1(history t)=Some(Gval(Fuint 1)[::reset])) ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter(formal_invalid_policy inputs path)flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 (500<=time)%coq_nat ->(time<limit)%coq_nat ->
 (forall site,eval_hfexpr_validif_policy(isolated_validif_policy(formal_invalid_policy inputs path))site flat_memories(rf_subtract_port_expr n)(history time)(history time)=Some(Gval(Fuint width)word)) ->
 VM.find(nth 0 rf_subtract_port_nodes n)(history time)=Some(Gval(Fuint width)word).
Proof. intros Bound Resets Steps Lower Upper Eval.''']
for node in nodes:
 group=0 if node<2500 else 2
 lines += [f'''destruct n as[|n]. {{ change(VM.find {node}(history time)=Some(Gval(Fuint width)word)).
rewrite(reference_control_stable_{node}_history inputs path history limit reset Resets Steps time(S time)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)).
eapply(reference_redirect_ground_step reference_control_{group}_offsets reference_control_{group}_nodes {node} reference_control_expr_{node});[exact reference_control_{group}_positions|exact reference_control_{group}_safety|exact reference_control_member_{node}|exact Eval|apply Steps;lia]. }}''']
lines+=['lia. Qed.']
# Three instruction slices, all independent of decoding.
lines+=['''Theorem rf_subtract_port_slices inputs path history limit reset time instruction :
 (forall t,(t<=limit)%coq_nat ->VM.find 1(history t)=Some(Gval(Fuint 1)[::reset])) ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter(formal_invalid_policy inputs path)flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 (500<=time)%coq_nat ->(time<limit)%coq_nat ->VM.find 1884(history time)=Some(Gval(Fuint 32)instruction) ->
 VM.find 2022(history time)=Some(Gval(Fuint 5)(rf_instruction_address false instruction)) /\\
 VM.find 2585(history time)=Some(Gval(Fuint 5)(rf_instruction_address true instruction)).
Proof.
 intros Resets Steps Lower Upper Source.''']
vals={1884:('instruction',32)}
for node,src,hi,lo in [(2020,1884,24,0),(2021,2020,19,0),(2022,2021,19,15),(2585,2020,24,20)]:
 val=f'drop {lo}(take {hi+1}({vals[src][0]}))';vals[node]=(val,hi-lo+1)
 lines += [f'''assert(V{node}:VM.find {node}(history time)=Some(Gval(Fuint {hi-lo+1})({val}))).
{{ eapply(rf_subtract_port_value {nodes.index(node)} inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site.
cbn[rf_subtract_port_expr nth reference_control_expr_{node} eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite {'Source' if src==1884 else 'V'+str(src)}. reflexivity. }}''']
lines += ['''unfold rf_instruction_address. rewrite !drop0 !take_take in V2022,V2585;try reflexivity.
split;assumption.
Qed.''']
p=base/'RFSubtractReferencePorts.v'
marker='(* Handwritten semantic composition. *)'
tail=p.read_text().split(marker,1)[1] if p.exists() and marker in p.read_text() else '\n'
p.write_text('\n'.join(lines)+'\n'+marker+tail)
