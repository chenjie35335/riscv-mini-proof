from pathlib import Path
b=Path(__file__).resolve().parents[2]/'formal/flat-low/staged-integration'
s=(b/'RFShiftReferenceImmediate.v').read_text()
head=s[:s.index('Lemma rf_shift_i_low_selected')]
a=s.index('Lemma rf_shift_i_high_selected');z=s.index('Lemma rf_shift_i_raw',a)
h=s[a:z].replace('rf_shift_i_high_selected','rf_upper_reference_high_selected').replace('word lane :(lane<3)%coq_nat ->','word auipc :').replace('(Nat.add 3 lane)','(if auipc then 7%nat else 6%nat)').replace('intros Lane Size','intros Size').replace('[lia|exact Size|','[destruct auipc;lia|exact Size|')
h=h.replace('|exact Raw|lia|lia]', '|exact Raw|destruct auipc;lia|destruct auipc;lia]')
r='Require Import RFUpperSemantics.\n'+head+h
r+='''Theorem rf_upper_reference_immediate_history inputs path history limit reset time instruction auipc :
 size instruction=32%nat ->
 (forall t,(t<=limit)%coq_nat ->VM.find 1(history t)=Some(Gval(Fuint 1)[::reset])) ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter(formal_invalid_policy inputs path)flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 (forall t,(200<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1884(history t)=Some(Gval(Fuint 32)instruction)) ->
 (500<=time)%coq_nat ->(time<limit)%coq_nat ->VM.find 1707(history time)=Some(Gval(Fuint 1)[::true]) ->
 VM.find 2475(history time)=Some(Gval(Fuint 1)[::negb auipc]) ->
 VM.find 2472(history time)=Some(Gval(Fuint 1)[::auipc]) ->
 (forall n,(n<27)%coq_nat ->VM.find(rf_i_high_guard n)(history time)=Some(Gval(Fuint 1)[::Nat.eqb n (if auipc then 7%nat else 6%nat)])) ->
 VM.find 2552(history time)=Some(Gval(Fuint 32)(rf_upper_immediate instruction)).
Proof.
 intros Size Resets Steps Source Lower Upper Enabled Lui Auipc Guards.
 assert(RawSize:size(drop 12(take 32 instruction))=20%nat)by(rewrite size_drop size_take Size;reflexivity).
 assert(ImmSize:size(rf_upper_immediate instruction)=32%nat)by(apply rf_upper_immediate_size;exact Size).
'''
for node,index,width,word,deps in [
 (2473,244,20,'drop 12(take 32 instruction)','rewrite(Source time ltac:(lia)ltac:(lia));reflexivity.'),
 (2476,245,20,'drop 12(take 32 instruction)','rewrite(Source time ltac:(lia)ltac:(lia));reflexivity.'),
 (2477,246,20,'if auipc then zeros 20 else drop 12(take 32 instruction)',"rewrite Lui. destruct auipc;cbn;unfold eval_type_of_expr;cbn[type_of_expr' eval_type_of_ref];rewrite ?V2476;[reflexivity|apply dut_decode_adapt;exact RawSize]."),
 (2478,247,20,'drop 12(take 32 instruction)',"rewrite Auipc. destruct auipc;cbn;unfold eval_type_of_expr;cbn[type_of_expr' eval_type_of_ref];rewrite ?V2473 ?V2477;apply dut_decode_adapt;exact RawSize."),
 (2479,248,20,'drop 12(take 32 instruction)','rewrite Enabled;cbn;rewrite V2478;apply dut_decode_adapt;exact RawSize.'),
 (2480,249,20,'drop 12(take 32 instruction)','exact V2479.'),
 (2481,250,32,'rf_upper_immediate instruction','rewrite V2480. reflexivity.'),
 (2482,251,32,'rf_upper_immediate instruction','rewrite V2481. change(Some(Gval(Fuint 32)(take 32(rf_upper_immediate instruction)))=Some(Gval(Fuint 32)(rf_upper_immediate instruction))). rewrite <-ImmSize. rewrite take_size;reflexivity.'),
 (2483,252,32,'rf_upper_immediate instruction','rewrite V2480. reflexivity.'),
 (2484,253,32,'rf_upper_immediate instruction','rewrite V2483. change(Some(Gval(Fuint 32)(take 32(rf_upper_immediate instruction)))=Some(Gval(Fuint 32)(rf_upper_immediate instruction))). rewrite <-ImmSize. rewrite take_size;reflexivity.')]:
 r+=f''' assert(V{node}:VM.find {node}(history time)=Some(Gval(Fuint {width})({word}))).
 {{ eapply(reference_immediate_value_history {index} inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site.
 cbn[reference_immediate_expression reference_immediate_expressions nth reference_control_expr_{node} eval_hfexpr_validif_policy eval_href_validif_policy].
 {deps} }}
'''
r+=''' apply(rf_upper_reference_high_selected inputs path history limit reset time(rf_upper_immediate instruction)auipc ImmSize Resets Steps).
 - intros t L U. exists(Gval(Fuint 32)instruction);split;[apply Source;assumption|reflexivity].
 - exact Lower.
 - exact Upper.
 - exact Enabled.
 - exact Guards.
 - destruct auipc;[exact V2482|exact V2484].
Qed.
Require Import RFReferenceNopHistory FormalObservedHistory ObservedJointRegisterConcrete JointUpdateBoundaryHistory FormalLocalHistory LoadTypeCorrespondence.
Theorem rf_upper_reference_immediate_observed memory inputs k observed instruction auipc :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 VM.find 1707(top_environment observed)=Some(Gval(Fuint 1)[::true]) ->
 VM.find 7750(top_environment observed)=Some(Gval(Fuint 32)instruction) ->
 N.land(to_N instruction)(reference_instruction_mask(rf_upper_class auipc))=reference_instruction_code(rf_upper_class auipc) ->
 VM.find 2552(top_environment observed)=Some(Gval(Fuint 32)(rf_upper_immediate instruction)).
Proof.
 intros Observe Legal Enabled Instruction Match.
 destruct(rf_reference_operand_context memory inputs k observed instruction(rf_upper_class auipc)Observe Legal Enabled Instruction(rf_upper_class_bound auipc)Match)
 as[Size[reset[history[Last[Resets[Steps[Source[Enable Decode]]]]]]]].
 assert(Lui:VM.find 2475(history 9250%nat)=Some(Gval(Fuint 1)[::negb auipc])).
 { pose proof(Decode 9%nat ltac:(lia))as D. destruct auipc;exact D. }
 assert(Auipc:VM.find 2472(history 9250%nat)=Some(Gval(Fuint 1)[::auipc])).
 { pose proof(Decode 10%nat ltac:(lia))as D. destruct auipc;exact D. }
 assert(High:forall n,(n<27)%coq_nat ->VM.find(rf_i_high_guard n)(history 9250%nat)=Some(Gval(Fuint 1)[::Nat.eqb n(if auipc then 7%nat else 6%nat)])).
 { intros n Bound. unfold rf_i_high_guard. rewrite(Decode(rf_i_high_decoder n)ltac:(do 27(destruct n as[|n];[cbn[rf_i_high_decoder nth];lia|]);lia)). destruct auipc;do 27(destruct n as[|n];[reflexivity|]);lia. }
 pose proof(rf_upper_reference_immediate_history (generated_observation_input inputs k)nil history 9259 reset 9250 instruction auipc Size Resets Steps Source ltac:(vm_compute;lia)ltac:(vm_compute;lia)Enable Lui Auipc High)as Value.
 rewrite(reference_control_stable_2552_history (generated_observation_input inputs k)nil history 9259 reset Resets Steps 9250 9259 ltac:(vm_compute;lia)ltac:(vm_compute;lia)ltac:(vm_compute;lia)ltac:(vm_compute;lia))Last in Value. exact Value.
Qed.
'''
(b/'RFUpperReferenceImmediate.v').write_text(r)
