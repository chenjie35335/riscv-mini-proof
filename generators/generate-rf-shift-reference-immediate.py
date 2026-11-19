from pathlib import Path
import re
root=Path(__file__).resolve().parents[2];p=root/'formal/flat-low/staged-integration'
base=(p/'RFALUReferenceImmediate.v').read_text();s=base[:base.index('Definition rf_i_low_node')]
s='Require Import ReferenceControlStabilityHistory ReferenceControlNodeCertificates2 RFALUReferenceImmediate RFShiftCycle RFAddReferencePorts.\n'+s
part=base[base.index('Lemma rf_i_low_selected'):base.index('Require Import ReferenceIllegalObserved')]
for name in ['low_selected','high_selected','raw','sign','immediate_history']:part=part.replace('rf_i_'+name,'rf_shift_i_'+name)
part=part.replace('Nat.eqb n lane','Nat.eqb n (Nat.add 3 lane)').replace('rf_i_low_yes lane','rf_i_low_yes (Nat.add 3 lane)').replace('rf_i_high_yes lane','rf_i_high_yes (Nat.add 3 lane)').replace('time)15 lane','time)15 (Nat.add 3 lane)').replace('time)27 lane','time)27 (Nat.add 3 lane)')
a=part.index('Lemma rf_shift_i_raw');b=part.index('Theorem rf_shift_i_immediate_history');chunk=part[a:b]
# remap numeric node IDs and indices in the raw/sign proofs
chunk=re.sub(r'\b(222[3-5]|25(?:0[0-8])|249[7-9])\b',lambda m:str(int(m[0])-(3 if int(m[0])>=2223 and int(m[0])<=2225 else 12)),chunk)
# identifiers include node ids
chunk=re.sub(r'_(222[3-5]|250[0-8]|249[7-9])(?=[^0-9]|$)',lambda m:'_'+str(int(m[1])-(3 if int(m[1])<2300 else 12)),chunk)
chunk=re.sub(r'reference_immediate_value_history (\d+)',lambda m:'reference_immediate_value_history '+str(int(m[1])-(3 if int(m[1])<40 else 6)),chunk)
part=part[:a]+chunk+part[b:];s+=part
s+='''Require Import RFReferenceNopHistory FormalObservedHistory ObservedJointRegisterConcrete JointUpdateBoundaryHistory FormalLocalHistory LoadTypeCorrespondence.
Theorem rf_shift_immediate_observed memory inputs k observed instruction lane :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 VM.find 1707(top_environment observed)=Some(Gval(Fuint 1)[::true]) ->
 VM.find 7750(top_environment observed)=Some(Gval(Fuint 32)instruction) ->(lane<3)%coq_nat ->
 N.land(to_N instruction)(reference_instruction_mask(rf_shift_class true lane))=reference_instruction_code(rf_shift_class true lane) ->
 VM.find 2552(top_environment observed)=Some(Gval(Fuint 32)(load_i_immediate instruction)).
Proof.
 intros Observe Legal Enabled Instruction Lane Match.
 destruct(rf_reference_operand_context memory inputs k observed instruction(rf_shift_class true lane)Observe Legal Enabled Instruction(rf_shift_class_bound true lane Lane)Match)
 as[Size[reset[history[Last[Resets[Steps[Source[Enable Decode]]]]]]]].
 pose proof(rf_shift_i_immediate_history (generated_observation_input inputs k)nil history 9259 reset 9250 instruction lane Lane Size Resets Steps Source ltac:(vm_compute;lia)ltac:(vm_compute;lia)Enable)as Value.
 assert(Low:forall n,(n<15)%coq_nat ->VM.find(rf_i_low_guard n)(history 9250%nat)=Some(Gval(Fuint 1)[::Nat.eqb n(Nat.add 3 lane)])).
 { intros n Bound. unfold rf_i_low_guard. rewrite(Decode(rf_i_low_decoder n)ltac:(do 15(destruct n as[|n];[cbn[rf_i_low_decoder nth];lia|]);lia)). do 3(destruct lane as[|lane];[do 15(destruct n as[|n];[reflexivity|]);lia|]);lia. }
 assert(High:forall n,(n<27)%coq_nat ->VM.find(rf_i_high_guard n)(history 9250%nat)=Some(Gval(Fuint 1)[::Nat.eqb n(Nat.add 3 lane)])).
 { intros n Bound. unfold rf_i_high_guard. rewrite(Decode(rf_i_high_decoder n)ltac:(do 27(destruct n as[|n];[cbn[rf_i_high_decoder nth];lia|]);lia)). do 3(destruct lane as[|lane];[do 27(destruct n as[|n];[reflexivity|]);lia|]);lia. }
 specialize(Value Low High).
 rewrite(reference_control_stable_2552_history (generated_observation_input inputs k)nil history 9259 reset Resets Steps 9250 9259 ltac:(vm_compute;lia)ltac:(vm_compute;lia)ltac:(vm_compute;lia)ltac:(vm_compute;lia))Last in Value. exact Value.
Qed.
'''
(p/'RFShiftReferenceImmediate.v').write_text(s)
