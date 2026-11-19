#!/usr/bin/env python3
from pathlib import Path
root=Path(__file__).resolve().parents[2]
s=(root/'formal/flat-low/staged-integration/RFALUReferencePorts.v').read_text()
parts=[s[:s.index('Definition rf_alu_rs1_node')], 'Require Import RFALUReferencePorts ReferenceControlNodeCertificates0 ReferenceControlNodeCongruence0 ReferenceControlNodeCertificates2 ReferenceControlNodeCongruence2 RFReferenceNopHistory ReferenceSecondRegisterRead.\n']
parts.append('''Definition branch_operand_match instruction lane :=N.land(to_N instruction)(reference_instruction_mask(Nat.add 23 lane))=reference_instruction_code(Nat.add 23 lane).
Lemma branch_operands_raw inputs path history limit reset time instruction lane :(lane<6)%coq_nat ->
 (forall t,(t<=limit)%coq_nat ->VM.find 1(history t)=Some(Gval(Fuint 1)[::reset])) ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter(formal_invalid_policy inputs path)flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 (500<=time)%coq_nat ->(time<limit)%coq_nat ->VM.find 1884(history time)=Some(Gval(Fuint 32)instruction) ->
 VM.find(rf_alu_rs1_yes(Nat.add 17 lane))(history time)=Some(Gval(Fuint 5)(rf_instruction_address false instruction)) /\\
 VM.find(rf_alu_rs2_yes(Nat.add 7 lane))(history time)=Some(Gval(Fuint 5)(rf_instruction_address true instruction)).
Proof. intros Lane Resets Steps Lower Upper Source.
''')
for lane in range(6):
 base=2005-6*lane;rs2=2583-lane
 parts.append('destruct lane as[|lane]. {\n')
 words=[]
 for i,(node,src,hi,lo,width,group) in enumerate([(base,1884,30,0,31,0),(base+1,base,24,0,25,0),(base+2,base+1,19,0,20,0),(base+3,base+2,19,15,5,0),(rs2,base+1,24,20,5,2)]):
  prev='instruction' if i==0 else words[1] if i==4 else words[i-1]
  word=f'(drop {lo}(take {hi+1} {prev}))';words.append(word)
  fact='Source' if i==0 else 'V1' if i==4 else f'V{i-1}'
  parts.append(f'''assert(V{i}:VM.find {node}(history time)=Some(Gval(Fuint {width}){word})).
 {{ rewrite(reference_control_stable_{node}_history inputs path history limit reset Resets Steps time(S time)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)).
 eapply(reference_redirect_ground_step reference_control_{group}_offsets reference_control_{group}_nodes {node} reference_control_expr_{node});[exact reference_control_{group}_positions|exact reference_control_{group}_safety|exact reference_control_member_{node}| |apply Steps;lia].
 intro site. cbn[reference_control_expr_{node} eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite {fact};reflexivity. }}
''')
 parts.append('cbn[rf_instruction_address rf_alu_rs1_yes rf_alu_rs2_yes nth]. rewrite !drop0 !take_take in V3,V4;try reflexivity. split;assumption. }\n')
parts.append('lia. Qed.\n')
for port,num,offset,stop in [('rs1',42,17,'Lemma rf_alu_rs1_decode'),('rs2',24,7,'Lemma rf_alu_rs2_decode')]:
 hist=s[s.index('Theorem rf_alu_'+port+'_history'):s.index(stop)]
 hist=hist.replace('rf_alu_'+port+'_history','branch_'+port+'_history').replace('(lane<3)%coq_nat','(lane<6)%coq_nat')
 start=hist.index(' pose proof(rf_alu_'+port+'_raw');end=hist.index(' assert(Target:',start)
 selected='proj1' if port=='rs1' else 'proj2'
 hist=hist[:start]+f' pose proof({selected}(branch_operands_raw inputs path history limit reset time instruction lane Lane Resets Steps Lower Upper(Source time ltac:(lia)ltac:(lia))))as Raw.\n'+hist[end:]
 hist=hist.replace('rf_alu_'+port+'_target lane',f'Nat.add {offset} lane')
 start=hist.index(' { do ',hist.index(' assert(Target:'));end=hist.index(' assert(Selected:',start)
 hist=hist[:start]+' { lia. }\n'+hist[end:]
 parts.append(hist)
 parts.append(f'''Lemma branch_{port}_decode instruction lane n :(lane<6)%coq_nat ->(n<{num})%coq_nat ->branch_operand_match instruction lane ->
 N.eqb(reference_instruction_code(rf_alu_{port}_decoder n))(N.land(to_N instruction)(reference_instruction_mask(rf_alu_{port}_decoder n)))=Nat.eqb n(Nat.add {offset} lane).
Proof. intros Lane Bound Match.
 rewrite(rf_reference_decode_onehot instruction(Nat.add 23 lane)(rf_alu_{port}_decoder n)ltac:(lia)ltac:(do {num}(destruct n as[|n];[cbn[rf_alu_{port}_decoder nth];lia|]);lia)Match).
 do 6(destruct lane as[|lane];[do {num}(destruct n as[|n];[reflexivity|]);lia|]);lia.
Qed.
''')
parts.append('Require Import ObservedJointRegisterConcrete JointUpdateBoundaryHistory FormalObservedHistory FormalLocalHistory MemoryRequestObservedSemantics LoadTypeCorrespondence.\n')
for port,offset in [('rs1',17),('rs2',7)]:
 start=s.index('Theorem rf_alu_'+port+'_observed')
 end=s.index('Theorem rf_alu_rs2_observed') if port=='rs1' else len(s)
 obs=s[start:end]
 obs=obs.replace('rf_alu_'+port+'_observed','branch_'+port+'_observed').replace('rf_alu_'+port+'_bank_observed','reference_branch_'+port+'_bank_active_observed')
 obs=obs.replace('(lane < 3)%coq_nat','(lane < 6)%coq_nat').replace('(lane<3)%coq_nat','(lane<6)%coq_nat')
 obs=obs.replace('N.land(to_N instruction)(reference_instruction_mask(rf_bitwise_class lane))=reference_instruction_code(rf_bitwise_class lane)','branch_operand_match instruction lane')
 obs=obs.replace('(rf_alu_'+port+'_target lane)',f'(Nat.add {offset} lane)').replace('rf_alu_'+port+'_decode instruction','branch_'+port+'_decode instruction').replace('rf_alu_'+port+'_history','branch_'+port+'_history')
 parts.append(obs)
parts.append('''Require Import ReferenceIllegalObserved LoadPipelineClassification FormalInstructionResetConstants.
Theorem reference_branch_operands_observed memory inputs k observed instruction lane bank :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 VM.find 1(formal_external_inputs(generated_observation_input inputs k))=Some(Gval(Fuint 1)[::false]) ->
 (lane<6)%coq_nat ->VM.find 7750(top_environment observed)=Some(Gval(Fuint 32)instruction) ->branch_operand_match instruction lane ->
 rf_reference_bank_at(top_environment observed)bank ->
 VM.find 2209(top_environment observed)=Some(Gval(Fuint 32)(bank(to_nat(rf_instruction_address false instruction)))) /\\
 VM.find 2804(top_environment observed)=Some(Gval(Fuint 32)(bank(to_nat(rf_instruction_address true instruction)))).
Proof.
 intros Observe Legal Reset Lane Instruction Match Bank.
 assert(Enabled:VM.find 1707(top_environment observed)=Some(Gval(Fuint 1)[::true])).
 { destruct(load_pipeline_late_observed memory inputs k observed Observe Legal)as[bit[Late Nop]].
 destruct bit.
 - specialize(Nop(Logic.eq_refl _)). rewrite Nop in Instruction;inversion Instruction;subst instruction.
 do 6(destruct lane as[|lane];[vm_compute in Match;discriminate|]);lia.
 - exact(reference_enable_observed_bubble memory inputs k observed false Observe Legal Reset Late). }
 split.
 - exact(reference_branch_rs1_bank_active_observed memory inputs k observed instruction lane bank Observe Legal Enabled Lane Instruction Match Bank).
 - exact(reference_branch_rs2_bank_active_observed memory inputs k observed instruction lane bank Observe Legal Enabled Lane Instruction Match Bank).
Qed.
''')
(root/'formal/flat-low/staged-integration/ReferenceBranchOperands.v').write_text('\n'.join(parts))
