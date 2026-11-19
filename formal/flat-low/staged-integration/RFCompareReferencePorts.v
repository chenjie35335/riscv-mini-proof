Require Import RFCompareCycle RFReferenceNopHistory ReferenceBankObservation FormalLocalHistory ReferenceLoadImmediate DUTRedirectDecode RFAddReferencePorts RFAddCycle RFALUReferencePorts RFALUReferenceData ReferenceImmediatePrefix ReferenceRs1Types ReferenceRs2Types ReferenceControlExpressions ReferenceControlStabilityHistory ReferenceControlNodeCertificates0 ReferenceControlNodeCertificates2 ReferenceControlNodeCongruence0 ReferenceControlNodeCongruence2 ReferenceRedirectSpine ReferenceInstructionDecode RFReadPorts CoreSocModel ComparisonNodes.
From Coq Require Import NArith List Lia PeanoNat.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.

Definition rf_compare_port_nodes :seq VarOrder.T :=[::2050;2051;2052;2055;2056;2057;2591;2592].
Definition rf_compare_port_expr n :=nth (@Econst VarOrder.T(Fuint 1)[::false])[::reference_control_expr_2050;reference_control_expr_2051;reference_control_expr_2052;reference_control_expr_2055;reference_control_expr_2056;reference_control_expr_2057;reference_control_expr_2591;reference_control_expr_2592]n.
Lemma rf_compare_port_value n inputs path history limit reset time width word :(n<8)%coq_nat ->
 (forall t,(t<=limit)%coq_nat ->VM.find 1(history t)=Some(Gval(Fuint 1)[::reset])) ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter(formal_invalid_policy inputs path)flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 (500<=time)%coq_nat ->(time<limit)%coq_nat ->
 (forall site,eval_hfexpr_validif_policy(isolated_validif_policy(formal_invalid_policy inputs path))site flat_memories(rf_compare_port_expr n)(history time)(history time)=Some(Gval(Fuint width)word)) ->
 VM.find(nth 0 rf_compare_port_nodes n)(history time)=Some(Gval(Fuint width)word).
Proof. intros Bound Resets Steps Lower Upper Eval.
destruct n as[|n]. { change(VM.find 2050(history time)=Some(Gval(Fuint width)word)).
rewrite(reference_control_stable_2050_history inputs path history limit reset Resets Steps time(S time)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)).
eapply(reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 2050 reference_control_expr_2050);[exact reference_control_0_positions|exact reference_control_0_safety|exact reference_control_member_2050|exact Eval|apply Steps;lia]. }
destruct n as[|n]. { change(VM.find 2051(history time)=Some(Gval(Fuint width)word)).
rewrite(reference_control_stable_2051_history inputs path history limit reset Resets Steps time(S time)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)).
eapply(reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 2051 reference_control_expr_2051);[exact reference_control_0_positions|exact reference_control_0_safety|exact reference_control_member_2051|exact Eval|apply Steps;lia]. }
destruct n as[|n]. { change(VM.find 2052(history time)=Some(Gval(Fuint width)word)).
rewrite(reference_control_stable_2052_history inputs path history limit reset Resets Steps time(S time)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)).
eapply(reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 2052 reference_control_expr_2052);[exact reference_control_0_positions|exact reference_control_0_safety|exact reference_control_member_2052|exact Eval|apply Steps;lia]. }
destruct n as[|n]. { change(VM.find 2055(history time)=Some(Gval(Fuint width)word)).
rewrite(reference_control_stable_2055_history inputs path history limit reset Resets Steps time(S time)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)).
eapply(reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 2055 reference_control_expr_2055);[exact reference_control_0_positions|exact reference_control_0_safety|exact reference_control_member_2055|exact Eval|apply Steps;lia]. }
destruct n as[|n]. { change(VM.find 2056(history time)=Some(Gval(Fuint width)word)).
rewrite(reference_control_stable_2056_history inputs path history limit reset Resets Steps time(S time)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)).
eapply(reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 2056 reference_control_expr_2056);[exact reference_control_0_positions|exact reference_control_0_safety|exact reference_control_member_2056|exact Eval|apply Steps;lia]. }
destruct n as[|n]. { change(VM.find 2057(history time)=Some(Gval(Fuint width)word)).
rewrite(reference_control_stable_2057_history inputs path history limit reset Resets Steps time(S time)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)).
eapply(reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 2057 reference_control_expr_2057);[exact reference_control_0_positions|exact reference_control_0_safety|exact reference_control_member_2057|exact Eval|apply Steps;lia]. }
destruct n as[|n]. { change(VM.find 2591(history time)=Some(Gval(Fuint width)word)).
rewrite(reference_control_stable_2591_history inputs path history limit reset Resets Steps time(S time)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)).
eapply(reference_redirect_ground_step reference_control_2_offsets reference_control_2_nodes 2591 reference_control_expr_2591);[exact reference_control_2_positions|exact reference_control_2_safety|exact reference_control_member_2591|exact Eval|apply Steps;lia]. }
destruct n as[|n]. { change(VM.find 2592(history time)=Some(Gval(Fuint width)word)).
rewrite(reference_control_stable_2592_history inputs path history limit reset Resets Steps time(S time)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)).
eapply(reference_redirect_ground_step reference_control_2_offsets reference_control_2_nodes 2592 reference_control_expr_2592);[exact reference_control_2_positions|exact reference_control_2_safety|exact reference_control_member_2592|exact Eval|apply Steps;lia]. }
lia. Qed.
Theorem rf_compare_port_slices inputs path history limit reset time instruction unsigned :
 (forall t,(t<=limit)%coq_nat ->VM.find 1(history t)=Some(Gval(Fuint 1)[::reset])) ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter(formal_invalid_policy inputs path)flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 (500<=time)%coq_nat ->(time<limit)%coq_nat ->VM.find 1884(history time)=Some(Gval(Fuint 32)instruction) ->
 VM.find(if unsigned then 2052 else 2057)(history time)=Some(Gval(Fuint 5)(rf_instruction_address false instruction)) /\
 VM.find(if unsigned then 2591 else 2592)(history time)=Some(Gval(Fuint 5)(rf_instruction_address true instruction)).
Proof.
 intros Resets Steps Lower Upper Source.
assert(V2050:VM.find 2050(history time)=Some(Gval(Fuint 25)(drop 0(take 25(instruction))))).
{ eapply(rf_compare_port_value 0 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site.
cbn[rf_compare_port_expr nth reference_control_expr_2050 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Source. reflexivity. }
assert(V2051:VM.find 2051(history time)=Some(Gval(Fuint 20)(drop 0(take 20(drop 0(take 25(instruction))))))).
{ eapply(rf_compare_port_value 1 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site.
cbn[rf_compare_port_expr nth reference_control_expr_2051 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite V2050. reflexivity. }
assert(V2052:VM.find 2052(history time)=Some(Gval(Fuint 5)(drop 15(take 20(drop 0(take 20(drop 0(take 25(instruction))))))))).
{ eapply(rf_compare_port_value 2 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site.
cbn[rf_compare_port_expr nth reference_control_expr_2052 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite V2051. reflexivity. }
assert(V2055:VM.find 2055(history time)=Some(Gval(Fuint 25)(drop 0(take 25(instruction))))).
{ eapply(rf_compare_port_value 3 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site.
cbn[rf_compare_port_expr nth reference_control_expr_2055 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Source. reflexivity. }
assert(V2056:VM.find 2056(history time)=Some(Gval(Fuint 20)(drop 0(take 20(drop 0(take 25(instruction))))))).
{ eapply(rf_compare_port_value 4 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site.
cbn[rf_compare_port_expr nth reference_control_expr_2056 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite V2055. reflexivity. }
assert(V2057:VM.find 2057(history time)=Some(Gval(Fuint 5)(drop 15(take 20(drop 0(take 20(drop 0(take 25(instruction))))))))).
{ eapply(rf_compare_port_value 5 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site.
cbn[rf_compare_port_expr nth reference_control_expr_2057 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite V2056. reflexivity. }
assert(V2591:VM.find 2591(history time)=Some(Gval(Fuint 5)(drop 20(take 25(drop 0(take 25(instruction))))))).
{ eapply(rf_compare_port_value 6 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site.
cbn[rf_compare_port_expr nth reference_control_expr_2591 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite V2050. reflexivity. }
assert(V2592:VM.find 2592(history time)=Some(Gval(Fuint 5)(drop 20(take 25(drop 0(take 25(instruction))))))).
{ eapply(rf_compare_port_value 7 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site.
cbn[rf_compare_port_expr nth reference_control_expr_2592 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite V2055. reflexivity. }
unfold rf_instruction_address. rewrite !drop0 !take_take in V2052,V2057,V2591,V2592;try reflexivity.
destruct unsigned;split;assumption.
Qed.
(* Handwritten semantic composition. *)
Theorem rf_compare_rs1_history inputs path history limit reset time instruction unsigned :size instruction=32%nat ->
 (forall t,(t<=limit)%coq_nat ->VM.find 1(history t)=Some(Gval(Fuint 1)[::reset])) ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter(formal_invalid_policy inputs path)flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 (forall t,(200<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1884(history t)=Some(Gval(Fuint 32)instruction)) ->
 (500<=time)%coq_nat ->(time<limit)%coq_nat ->VM.find 1707(history time)=Some(Gval(Fuint 1)[::true]) ->
 (forall n,(n<42)%coq_nat ->VM.find(rf_alu_rs1_guard n)(history time)=Some(Gval(Fuint 1)[::Nat.eqb n (if unsigned then 8%nat else 7%nat)])) ->
 VM.find 2145(history time)=Some(Gval(Fuint 5)(rf_instruction_address false instruction)).
Proof.
 intros Size Resets Steps Source Lower Upper Enabled Guards.
 assert(Typed:forall t,(200<=t)%coq_nat ->(t<=limit)%coq_nat ->exists v,VM.find 1884(history t)=Some v /\type_of_val v=Gtyp(Fuint 32)).
 { intros t L U. exists(Gval(Fuint 32)instruction);split;[apply Source;assumption|reflexivity]. }
 pose proof(proj1(rf_compare_port_slices inputs path history limit reset time instruction unsigned Resets Steps Lower Upper(Source time ltac:(lia)ltac:(lia))))as Raw.
 assert(Target:((if unsigned then 8 else 7)<42)%coq_nat)by(destruct unsigned;vm_compute;lia).
 assert(Selected:VM.find 2143(history time)=Some(Gval(Fuint 5)(rf_instruction_address false instruction))).
 { change(VM.find(rf_alu_rs1_node 41)(history time)=Some(Gval(Fuint 5)(rf_instruction_address false instruction))).
 eapply(immediate_stable_mux_suffix (formal_invalid_policy inputs path)(history time)(history(S time))42 (if unsigned then 8%nat else 7%nat) 5(rf_instruction_address false instruction)2101 rf_alu_rs1_node rf_alu_rs1_guard rf_alu_rs1_yes);[ltac:(destruct unsigned;vm_compute;lia)|exact(rf_instruction_address_size false instruction Size)| | |exact Guards| | |ltac:(destruct unsigned;exact Raw)|ltac:(destruct unsigned;vm_compute;lia)|lia].
 - intros n Bound. exact(rf_alu_rs1_same n inputs path history limit reset time Bound Resets Steps Lower Upper).
 - intros n Bound value Eval. apply(rf_alu_rs1_step n _ _ _ value Bound Eval);apply Steps;exact Upper.
 - intros n Bound. exact(proj1(rf_alu_rs1_types n _ history limit time Bound Steps Typed Lower ltac:(lia))).
 - intros n Bound. exact(proj2(rf_alu_rs1_types n _ history limit time Bound Steps Typed Lower ltac:(lia))). }
 assert(Gate:VM.find 2144(history time)=Some(Gval(Fuint 5)(rf_instruction_address false instruction))).
 { eapply(rf_alu_rs1_value 15 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site.
 cbn[rf_alu_rs1_aux_expr nth reference_control_expr_2144 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Enabled;cbn;rewrite Selected. apply dut_decode_adapt;exact(rf_instruction_address_size false instruction Size). }
 eapply(rf_alu_rs1_value 16 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site;exact Gate.
Qed.

Theorem rf_compare_rs2_history inputs path history limit reset time instruction unsigned :
 size instruction=32%nat ->
 (forall t,(t<=limit)%coq_nat ->VM.find 1(history t)=Some(Gval(Fuint 1)[::reset])) ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter(formal_invalid_policy inputs path)flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 (forall t,(200<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1884(history t)=Some(Gval(Fuint 32)instruction)) ->
 (500<=time)%coq_nat ->(time<limit)%coq_nat ->VM.find 1707(history time)=Some(Gval(Fuint 1)[::true]) ->
 (forall row,(row<48)%coq_nat ->VM.find(reference_instruction_guard row)(history time)=Some(Gval(Fuint 1)[::Nat.eqb row(rf_compare_class unsigned)])) ->
 VM.find 2622(history time)=Some(Gval(Fuint 5)(rf_instruction_address true instruction)).
Proof.
 intros Size Resets Steps Source Lower Upper Enabled Decode.
 assert(Typed:forall t,(200<=t)%coq_nat ->(t<=limit)%coq_nat ->exists v,VM.find 1884(history t)=Some v /\type_of_val v=Gtyp(Fuint 32)).
 { intros t L U. exists(Gval(Fuint 32)instruction);split;[apply Source;assumption|reflexivity]. }
 pose proof(proj2(rf_compare_port_slices inputs path history limit reset time instruction unsigned Resets Steps Lower Upper(Source time ltac:(lia)ltac:(lia))))as Raw.
 assert(Guards:forall n,(n<24)%coq_nat ->VM.find(rf_alu_rs2_guard n)(history time)=Some(Gval(Fuint 1)[::false])).
 { intros n Bound. unfold rf_alu_rs2_guard. rewrite(Decode(rf_alu_rs2_decoder n)ltac:(do 24(destruct n as[|n];[cbn[rf_alu_rs2_decoder nth];lia|]);lia)). destruct unsigned;do 24(destruct n as[|n];[reflexivity|]);lia. }
 assert(Prefix:VM.find 2596(history time)=Some(Gval(Fuint 5)(rf_instruction_address true instruction))).
 { destruct unsigned.
 - destruct(reference_rs2_types_history _ history limit 200 Steps Typed 61%nat ltac:(lia)time ltac:(cbv[reference_rs2_rank reference_rs2_ranks nth];lia)ltac:(lia))as[other[Other OtherType]].
 eapply(rf_add_port_value 11 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site. cbn[rf_add_port_expr nth]. unfold reference_control_expr_2596.
 exact(immediate_selected_mux _ site _ _ _ _ 5 _ other true(rf_instruction_address_size true instruction Size)(Decode 13%nat ltac:(lia))Raw Other OtherType).
 - destruct(reference_rs2_types_history _ history limit 200 Steps Typed 60%nat ltac:(lia)time ltac:(cbv[reference_rs2_rank reference_rs2_ranks nth];lia)ltac:(lia))as[other[Other OtherType]].
 assert(V2595:VM.find 2595(history time)=Some(Gval(Fuint 5)(rf_instruction_address true instruction))).
 { eapply(rf_add_port_value 10 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site. cbn[rf_add_port_expr nth]. unfold reference_control_expr_2595.
 exact(immediate_selected_mux _ site _ _ _ _ 5 _ other true(rf_instruction_address_size true instruction Size)(Decode 12%nat ltac:(lia))Raw Other OtherType). }
 destruct(reference_rs2_types_history _ history limit 200 Steps Typed 57%nat ltac:(lia)time ltac:(cbv[reference_rs2_rank reference_rs2_ranks nth];lia)ltac:(lia))as[other1[Other1 Type1]].
 eapply(rf_add_port_value 11 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site. cbn[rf_add_port_expr nth]. unfold reference_control_expr_2596.
 exact(immediate_selected_mux _ site _ _ _ _ 5 _ other1 false(rf_instruction_address_size true instruction Size)(Decode 13%nat ltac:(lia))V2595 Other1 Type1). }
 assert(Selected:VM.find 2620(history time)=Some(Gval(Fuint 5)(rf_instruction_address true instruction))).
 { change(VM.find(rf_alu_rs2_node 23)(history time)=Some(Gval(Fuint 5)(rf_instruction_address true instruction))).
 apply(immediate_stable_mux_prefix (formal_invalid_policy inputs path)(history time)24 5(rf_instruction_address true instruction)2596 rf_alu_rs2_node rf_alu_rs2_guard rf_alu_rs2_yes(rf_instruction_address_size true instruction Size));[|exact Guards| |exact Prefix|lia].
 - intros n Bound value Eval. rewrite(rf_alu_rs2_same n inputs path history limit reset time Bound Resets Steps Lower Upper). apply(rf_alu_rs2_step n _ _ _ value Bound Eval);apply Steps;exact Upper.
 - intros n Bound. exact(proj1(rf_alu_rs2_types n _ history limit time Bound Steps Typed Lower ltac:(lia))). }
 assert(Gate:VM.find 2621(history time)=Some(Gval(Fuint 5)(rf_instruction_address true instruction))).
 { eapply(rf_alu_rs2_value 6 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site.
 cbn[rf_alu_rs2_aux_expr nth reference_control_expr_2621 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Enabled;cbn;rewrite Selected. apply dut_decode_adapt;exact(rf_instruction_address_size true instruction Size). }
 eapply(rf_alu_rs2_value 7 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site;exact Gate.
Qed.

Require Import ObservedJointRegisterConcrete LoadTypeCorrespondence ReferenceSecondRegisterRead ReferenceLoadRs1 ReferenceRegisterRead.
Theorem rf_compare_index_observed second memory inputs k observed instruction unsigned :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 VM.find 1707(top_environment observed)=Some(Gval(Fuint 1)[::true]) ->
 VM.find 7750(top_environment observed)=Some(Gval(Fuint 32)instruction) ->
 N.land(to_N instruction)(reference_instruction_mask((rf_compare_class unsigned)))=reference_instruction_code((rf_compare_class unsigned)) ->
 VM.find(if second then 2622 else 2145)(top_environment observed)=Some(Gval(Fuint 5)(rf_instruction_address second instruction)).
Proof.
 intros Observe Legal Enabled Instruction Match.
 destruct(rf_reference_operand_context memory inputs k observed instruction((rf_compare_class unsigned))Observe Legal Enabled Instruction ltac:(destruct unsigned;vm_compute;lia)Match)
 as[Size[reset[history[Last[Resets[Steps[Source[Enable Decode]]]]]]]].
 destruct second.
 -
 pose proof(rf_compare_rs2_history (generated_observation_input inputs k)nil history 9259 reset 9250 instruction unsigned Size Resets Steps Source ltac:(vm_compute;lia)ltac:(vm_compute;lia)Enable Decode)as Value.
 rewrite(reference_control_stable_2622_history (generated_observation_input inputs k)nil history 9259 reset Resets Steps 9250 9259 ltac:(vm_compute;lia)ltac:(vm_compute;lia)ltac:(vm_compute;lia)ltac:(vm_compute;lia))Last in Value. exact Value.
 - pose proof(rf_compare_rs1_history (generated_observation_input inputs k)nil history 9259 reset 9250 instruction unsigned Size Resets Steps Source ltac:(vm_compute;lia)ltac:(vm_compute;lia)Enable ltac:(intros n Bound; unfold rf_alu_rs1_guard; rewrite(Decode(rf_alu_rs1_decoder n)ltac:(do 42(destruct n as[|n];[cbn[rf_alu_rs1_decoder nth];lia|]);lia)); destruct unsigned;do 42(destruct n as[|n];[reflexivity|]);lia))as Value.
 rewrite(reference_control_stable_2145_history (generated_observation_input inputs k)nil history 9259 reset Resets Steps 9250 9259 ltac:(vm_compute;lia)ltac:(vm_compute;lia)ltac:(vm_compute;lia)ltac:(vm_compute;lia))Last in Value. exact Value.
Qed.
Theorem rf_compare_bank_observed second memory inputs k observed instruction unsigned bank :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 VM.find 1707(top_environment observed)=Some(Gval(Fuint 1)[::true]) ->
 VM.find 7750(top_environment observed)=Some(Gval(Fuint 32)instruction) ->
 N.land(to_N instruction)(reference_instruction_mask((rf_compare_class unsigned)))=reference_instruction_code((rf_compare_class unsigned)) ->
 rf_reference_bank_at(top_environment observed)bank ->
 VM.find(if second then 2804 else 2209)(top_environment observed)=Some(Gval(Fuint 32)(bank(to_nat(rf_instruction_address second instruction)))).
Proof.
 intros Observe Legal Enabled Instruction Match Bank.
 destruct(observed_joint_register_concrete memory inputs k observed 7750%nat 32%nat Observe Legal load_type_instruction_member)as[word[Size Word]].
 rewrite Instruction in Word;inversion Word;subst word.
 pose proof(rf_compare_index_observed second memory inputs k observed instruction unsigned Observe Legal Enabled Instruction Match)as Index.
 destruct second.
 - exact(reference_second_register_read_observed memory inputs k observed bank _ Observe Legal Bank(rf_instruction_address_size true instruction Size)Index).
 - exact(reference_register_read_observed memory inputs k observed bank _ Observe Legal Bank(rf_instruction_address_size false instruction Size)Index).
Qed.
