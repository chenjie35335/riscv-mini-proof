#!/usr/bin/env python3
"""Instantiate the shared immediate suffix proof for the actual JALR row."""
from pathlib import Path
import re
root=Path(__file__).resolve().parents[2]
s=(root/'formal/flat-low/staged-integration/RFALUReferenceImmediate.v').read_text()
ids_text=(root/'formal/flat-low/staged-integration/ReferenceImmediateTypes.v').read_text()
ids=list(map(int,re.search(r'Definition reference_immediate_ids.*?\[::(.*?)\]\.',ids_text).group(1).split(';')))
parts=[s[:s.index('Definition rf_i_low_node')], 'Require Import RFALUReferenceImmediate JALRAddressCycle ReferenceControlStabilityHistory ReferenceControlNodeCertificates2 ReferenceControlNodeCongruence1 ReferenceControlNodeCertificates1.\n']
for kind,count in [('low',15),('high',27)]:
 chunk=s[s.index(f'Lemma rf_i_{kind}_selected'):]
 chunk=chunk[:chunk.index('Qed.')+4]
 chunk=chunk.replace(f'rf_i_{kind}_selected',f'jalr_i_{kind}_selected').replace('(lane<3)%coq_nat',f'(lane<{count})%coq_nat')
 parts.append(chunk+'\n')
raw=s[s.index('Lemma rf_i_raw'):s.index('Lemma rf_i_sign')]
raw=raw[:raw.index('destruct lane as[|lane].')]+raw[raw.index('destruct lane as[|lane].'):].split('destruct lane as[|lane].')[1]
raw=raw[:raw.rfind('}')].replace('rf_i_raw','jalr_i_raw').replace('instruction lane :(lane<3)%coq_nat ->','instruction :').replace('intros Lane Resets','intros Resets').replace('(rf_i_low_yes lane)',' 2219')
raw=raw.replace('reference_immediate_value_history 38','reference_immediate_value_history 32').replace('reference_control_expr_2225','reference_control_expr_2219')
# Remove the branch-opening brace from the copied first case.
raw=raw.replace('Source.\n {','Source.\n ')+ 'Qed.\n'
parts.append(raw)
sign=s[s.index('Lemma rf_i_sign'):s.index('Theorem rf_i_immediate_history')]
pre,rest=sign.split('destruct lane as[|lane]. {',1)
body=rest.split('exact V3. }',1)[0]+'exact V3.\nQed.\n'
pre=pre.replace('rf_i_sign','jalr_i_sign').replace('word lane :(lane<3)%coq_nat ->','word :').replace('intros Lane Size','intros Size').replace('(rf_i_high_yes lane)',' 2449')
for old,new in [(2505,2446),(2506,2447),(2507,2448),(2508,2449)]:body=body.replace(str(old),str(new))
body=body.replace('value_history 264','value_history '+str(ids.index(2448))).replace('value_history 265','value_history '+str(ids.index(2449)))
body=body.replace('reference_control_2_', 'reference_control_1_')
parts.append(pre+body)
hist=s[s.index('Theorem rf_i_immediate_history'):s.index('Require Import ReferenceIllegalObserved')]
hist=hist.replace('rf_i_immediate_history','jalr_i_immediate_history').replace('instruction lane :\n (lane<3)%coq_nat ->','instruction :\n ')
hist=hist.replace('intros Lane Size','intros Size').replace('Nat.eqb n lane','Nat.eqb n 6',1).replace('Nat.eqb n lane','Nat.eqb n 9',1)
hist=hist.replace('rf_i_raw','jalr_i_raw').replace('instruction lane Lane Resets','instruction Resets')
hist=hist.replace('rf_i_low_selected','jalr_i_low_selected').replace('))lane Lane RawSize', '))6 ltac:(lia)RawSize',1)
hist=hist.replace('rf_i_sign','jalr_i_sign').replace('))lane Lane RawSize', '))RawSize',1)
hist=hist.replace('rf_i_high_selected','jalr_i_high_selected').replace('instruction)lane Lane(', 'instruction)9 ltac:(lia)(')
parts.append(hist)
parts.append(s[s.index('Require Import ReferenceIllegalObserved'):s.index('Lemma rf_bitwise_reference_enabled')])
for kind,count,selected in [('low',15,6),('high',27,9)]:
 parts.append(f"""Lemma jalr_i_{kind}_decode instruction n :(n<{count})%coq_nat ->jalr_match instruction ->
 N.eqb(reference_instruction_code(rf_i_{kind}_decoder n))(N.land(to_N instruction)(reference_instruction_mask(rf_i_{kind}_decoder n)))=Nat.eqb n {selected}.
Proof. intros Bound Match.
 rewrite(rf_reference_decode_onehot instruction 22 (rf_i_{kind}_decoder n)ltac:(lia)ltac:(do {count}(destruct n as[|n];[vm_compute;lia|]);lia)Match).
 do {count}(destruct n as[|n];[reflexivity|]);lia.
Qed.
""")
obs=s[s.index('Theorem rf_bitwise_immediate_observed'):]
obs=obs.replace('rf_bitwise_immediate_observed','reference_jalr_immediate_observed').replace('instruction lane :','instruction :').replace(' (lane<3)%coq_nat ->',' ')
obs=obs.replace('N.land(to_N instruction)(reference_instruction_mask(Nat.add 3 lane))=reference_instruction_code(Nat.add 3 lane)','jalr_match instruction')
obs=obs.replace('intros Observe Legal Reset Lane Instruction Match.','intros Observe Legal Reset Instruction Match.')
a=obs.index(' { apply(rf_bitwise_reference_enabled');b=obs.index(' destruct(observed_joint_register_concrete',a)
obs=obs[:a]+""" { destruct(load_pipeline_late_observed memory inputs k observed Observe Legal)as[bit[Late Nop]].
 destruct bit.
 - specialize(Nop(Logic.eq_refl _)). rewrite Nop in Instruction;inversion Instruction;subst instruction. vm_compute in Match;discriminate.
 - exact(reference_enable_observed_bubble memory inputs k observed false Observe Legal Reset Late). }
"""+obs[b:]
obs=obs.replace('Nat.eqb n lane','Nat.eqb n 6',1).replace('Nat.eqb n lane','Nat.eqb n 9',1)
obs=obs.replace('rf_i_low_decode instruction lane n Lane Bound Match','jalr_i_low_decode instruction n Bound Match').replace('rf_i_high_decode instruction lane n Lane Bound Match','jalr_i_high_decode instruction n Bound Match')
obs=obs.replace('rf_i_immediate_history','jalr_i_immediate_history').replace('9250 instruction lane Lane Size','9250 instruction Size')
parts.append(obs)
(root/'formal/flat-low/staged-integration/ReferenceJALRImmediate.v').write_text('\n'.join(parts))
