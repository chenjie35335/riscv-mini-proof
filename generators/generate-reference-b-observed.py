"""Lift the branch immediate history through actual observed decode and enable."""
from pathlib import Path
p=Path(__file__).resolve().parents[2]/'formal/flat-low/staged-integration'
s=(p/'ReferenceBranchImmediate.v').read_text()
start=s.index('Require Import ReferenceIllegalObserved JointUpdateBoundaryHistory RFScalarControl')
imports=s[start:s.index('Lemma jal_reference_enabled_observed',start)]
enabled='''Definition reference_branch_match (instruction:bits) lane :=N.land(to_N instruction)(reference_instruction_mask(Nat.sub 28 lane))=reference_instruction_code(Nat.sub 28 lane).
Lemma branch_reference_enabled_observed lane memory inputs k observed instruction :
 (lane<6)%coq_nat ->generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 VM.find 1(formal_external_inputs(generated_observation_input inputs k))=Some(Gval(Fuint 1)[::false]) ->
 VM.find 7750(top_environment observed)=Some(Gval(Fuint 32)instruction) ->reference_branch_match instruction lane ->
 VM.find 1707(top_environment observed)=Some(Gval(Fuint 1)[::true]).
Proof.
 intros Lane Observe Legal Reset Instruction Match.
 destruct(load_pipeline_late_observed memory inputs k observed Observe Legal)as[bit[Late Nop]]. destruct bit.
 - specialize(Nop(Logic.eq_refl _)). rewrite Nop in Instruction. inversion Instruction;subst instruction.
 do 6(destruct lane as[|lane];[vm_compute in Match;discriminate|]);lia.
 - exact(reference_enable_observed_bubble memory inputs k observed false Observe Legal Reset Late).
Qed.
Lemma branch_field_guard_decoder n : (n<6)%coq_nat ->branch_field_guard n=reference_instruction_guard(Nat.add 23 n).
Proof. do 6(destruct n as[|n];[reflexivity|]);lia. Qed.
Lemma branch_upper_guard_decoder n : (n<11)%coq_nat ->load_imm_mux_guard true n=reference_instruction_guard(Nat.add 29 n).
Proof. do 11(destruct n as[|n];[reflexivity|]);lia. Qed.
Lemma branch_decode_lane lane n : (lane<6)%coq_nat ->(n<6)%coq_nat ->Nat.eqb(Nat.add 23 n)(Nat.sub 28 lane)=Nat.eqb n(Nat.sub 5 lane).
Proof. do 6(destruct lane as[|lane];[do 6(destruct n as[|n];[reflexivity|]);lia|]);lia. Qed.
'''
body=s[s.index('Theorem reference_jal_immediate_observed'):]
body=body.replace('reference_jal_immediate_observed memory','reference_branch_immediate_observed lane memory').replace(' generated_observe memory inputs k=Some observed ->',' (lane<6)%coq_nat ->generated_observe memory inputs k=Some observed ->',1).replace('N.land(to_N instruction)127=111','reference_branch_match instruction lane').replace('dut_j_immediate','dut_b_immediate').replace('intros Observe Legal Reset Instruction Jal.','intros Lane Observe Legal Reset Instruction Match.').replace('jal_reference_enabled_observed memory inputs k observed instruction Observe Legal Reset Instruction Jal','branch_reference_enabled_observed lane memory inputs k observed instruction Lane Observe Legal Reset Instruction Match').replace('[::Nat.eqb row 21]','[::Nat.eqb row(Nat.sub 28 lane)]').replace('rf_reference_decode_onehot instruction 21 row ltac:(lia) Row Jal','rf_reference_decode_onehot instruction (Nat.sub 28 lane) row ltac:(lia) Row Match')
a=body.index(' assert(Guards:');b=body.index(' pose proof(reference_jal_immediate_history',a)
body=body[:a]+''' assert(Guards:forall n,(n<6)%coq_nat ->VM.find(branch_field_guard n)(history 9250%nat)=Some(Gval(Fuint 1)[::Nat.eqb n(Nat.sub 5 lane)])).
 { intros n Bound. rewrite(branch_field_guard_decoder n Bound)(Decode(Nat.add 23 n)ltac:(lia))(branch_decode_lane lane n Lane Bound);reflexivity. }
 assert(UpperGuards:forall n,(n<11)%coq_nat ->VM.find(load_imm_mux_guard true n)(history 9250%nat)=Some(Gval(Fuint 1)[::false])).
 { intros n Bound. rewrite(branch_upper_guard_decoder n Bound)(Decode(Nat.add 29 n)ltac:(lia)). rewrite(proj2(Nat.eqb_neq(Nat.add 29 n)(Nat.sub 28 lane))ltac:(lia));reflexivity. }
'''+body[b:]
body=body.replace('reference_jal_immediate_history (generated_observation_input inputs k)','reference_branch_immediate_history lane (generated_observation_input inputs k)').replace('9250 instruction Size Resets','9250 instruction Lane Size Resets').replace('(Decode 21%nat ltac:(lia))Guards','Guards UpperGuards')
target=p/'ReferenceConditionalBranchImmediate.v';old=target.read_text();marker='(* Branch observed interface. *)';target.write_text(old.split(marker)[0]+marker+'\n'+imports+enabled+body)
