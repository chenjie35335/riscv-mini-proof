#!/usr/bin/env python3
from pathlib import Path
root=Path(__file__).resolve().parents[2]
s=(root/'formal/flat-low/staged-integration/RFALUReferencePorts.v').read_text()
parts=[s[:s.index('Definition rf_alu_rs1_node')], 'Require Import RFALUReferencePorts ReferenceJALRImmediate JALRAddressCycle ReferenceControlNodeCertificates0 ReferenceControlNodeCongruence0 RFReferenceNopHistory.\n']
parts.append('''Lemma jalr_rs1_raw inputs path history limit reset time instruction :
 (forall t,(t<=limit)%coq_nat ->VM.find 1(history t)=Some(Gval(Fuint 1)[::reset])) ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter(formal_invalid_policy inputs path)flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 (500<=time)%coq_nat ->(time<limit)%coq_nat ->VM.find 1884(history time)=Some(Gval(Fuint 32)instruction) ->
 VM.find 2012(history time)=Some(Gval(Fuint 5)(rf_instruction_address false instruction)).
Proof.
 intros Resets Steps Lower Upper Source.
 assert(V:VM.find 2011(history time)=Some(Gval(Fuint 20)(take 20 instruction))).
 { rewrite(reference_control_stable_2011_history inputs path history limit reset Resets Steps time(S time)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)).
 eapply(reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 2011 reference_control_expr_2011);[exact reference_control_0_positions|exact reference_control_0_safety|exact reference_control_member_2011| |apply Steps;lia].
 intro site. cbn[reference_control_expr_2011 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Source. change(Some(Gval(Fuint 20)(drop 0(take 20 instruction)))=Some(Gval(Fuint 20)(take 20 instruction))). rewrite drop0;reflexivity. }
 rewrite(reference_control_stable_2012_history inputs path history limit reset Resets Steps time(S time)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)).
 eapply(reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 2012 reference_control_expr_2012);[exact reference_control_0_positions|exact reference_control_0_safety|exact reference_control_member_2012| |apply Steps;lia].
 intro site. cbn[reference_control_expr_2012 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite V. change(Some(Gval(Fuint 5)(drop 15(take 20(take 20 instruction))))=Some(Gval(Fuint 5)(rf_instruction_address false instruction))). unfold rf_instruction_address. rewrite <-take_min;reflexivity.
Qed.
''')
hist=s[s.index('Theorem rf_alu_rs1_history'):s.index('Lemma rf_alu_rs1_decode')]
hist=hist.replace('rf_alu_rs1_history','jalr_rs1_history').replace('instruction lane :(lane<6)%coq_nat ->','instruction :').replace('intros Lane Size','intros Size').replace('(rf_alu_rs1_target lane)',' 16%nat')
hist=hist.replace('rf_alu_rs1_raw','jalr_rs1_raw').replace('instruction lane Lane Resets','instruction Resets')
a=hist.index(' assert(Target:');b=hist.index(' assert(Selected:',a);hist=hist[:a]+hist[b:]
hist=hist.replace('16%nat5','16%nat 5').replace('[exact Target|','[lia|')
parts.append(hist)
parts.append('''Lemma jalr_rs1_decode instruction n :(n<42)%coq_nat ->jalr_match instruction ->
 N.eqb(reference_instruction_code(rf_alu_rs1_decoder n))(N.land(to_N instruction)(reference_instruction_mask(rf_alu_rs1_decoder n)))=Nat.eqb n 16.
Proof. intros Bound Match.
 rewrite(rf_reference_decode_onehot instruction 22(rf_alu_rs1_decoder n)ltac:(lia)ltac:(do 42(destruct n as[|n];[cbn[rf_alu_rs1_decoder nth];lia|]);lia)Match).
 do 42(destruct n as[|n];[reflexivity|]);lia.
Qed.
Require Import ObservedJointRegisterConcrete JointUpdateBoundaryHistory FormalObservedHistory FormalLocalHistory MemoryRequestObservedSemantics LoadTypeCorrespondence.
''')
obs=s[s.index('Theorem rf_alu_rs1_observed'):s.index('Theorem rf_alu_rs2_observed')]
obs=obs.replace('rf_alu_rs1_observed','jalr_rs1_observed').replace('rf_alu_rs1_bank_observed','reference_jalr_rs1_bank_active_observed').replace('instruction lane','instruction')
obs=obs.replace(' (lane < 6)%coq_nat ->',' ').replace(' (lane<6)%coq_nat ->',' ')
obs=obs.replace('N.land(to_N instruction)(reference_instruction_mask(rf_bitwise_class lane))=reference_instruction_code(rf_bitwise_class lane)','jalr_match instruction')
obs=obs.replace('Enabled Lane','Enabled').replace('(rf_alu_rs1_target lane)',' 16%nat').replace('rf_alu_rs1_decode instruction n Lane Bound','jalr_rs1_decode instruction n Bound')
obs=obs.replace('rf_alu_rs1_history','jalr_rs1_history').replace('instruction Lane Size','instruction Size')
parts.append(obs)
parts.append("""Require Import ReferenceIllegalObserved LoadPipelineClassification FormalInstructionResetConstants.
Theorem reference_jalr_rs1_bank_observed memory inputs k observed instruction bank :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 VM.find 1(formal_external_inputs(generated_observation_input inputs k))=Some(Gval(Fuint 1)[::false]) ->
 VM.find 7750(top_environment observed)=Some(Gval(Fuint 32)instruction) ->jalr_match instruction ->
 rf_reference_bank_at(top_environment observed)bank ->
 VM.find 2209(top_environment observed)=Some(Gval(Fuint 32)(bank(to_nat(rf_instruction_address false instruction)))).
Proof.
 intros Observe Legal Reset Instruction Match Bank.
 assert(Enabled:VM.find 1707(top_environment observed)=Some(Gval(Fuint 1)[::true])).
 { destruct(load_pipeline_late_observed memory inputs k observed Observe Legal)as[bit[Late Nop]].
 destruct bit.
 - specialize(Nop(Logic.eq_refl _)). rewrite Nop in Instruction;inversion Instruction;subst instruction. vm_compute in Match;discriminate.
 - exact(reference_enable_observed_bubble memory inputs k observed false Observe Legal Reset Late). }
 exact(reference_jalr_rs1_bank_active_observed memory inputs k observed instruction bank Observe Legal Enabled Instruction Match Bank).
Qed.
""")
(root/'formal/flat-low/staged-integration/ReferenceJALRRead.v').write_text('\n'.join(parts))
