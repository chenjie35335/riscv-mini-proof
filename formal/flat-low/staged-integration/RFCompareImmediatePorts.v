Require Import RFCompareImmediateCycle RFCompareCycle RFReferenceNopHistory ReferenceBankObservation FormalLocalHistory ReferenceLoadImmediate DUTRedirectDecode RFAddReferencePorts RFAddCycle RFALUReferencePorts RFALUReferenceData ReferenceImmediatePrefix ReferenceRs1Types ReferenceRs2Types ReferenceControlExpressions ReferenceControlStabilityHistory ReferenceControlNodeCertificates0 ReferenceControlNodeCertificates2 ReferenceControlNodeCongruence0 ReferenceControlNodeCongruence2 ReferenceRedirectSpine ReferenceInstructionDecode RFReadPorts CoreSocModel ComparisonNodes.
From Coq Require Import NArith List Lia PeanoNat.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.

Definition rf_compare_immediate_port_nodes :seq VarOrder.T :=[::2089;2090;2093;2094].
Definition rf_compare_immediate_port_expr n :=nth (@Econst VarOrder.T(Fuint 1)[::false])[::reference_control_expr_2089;reference_control_expr_2090;reference_control_expr_2093;reference_control_expr_2094]n.
Lemma rf_compare_immediate_port_value n inputs path history limit reset time width word :(n<4)%coq_nat ->
 (forall t,(t<=limit)%coq_nat ->VM.find 1(history t)=Some(Gval(Fuint 1)[::reset])) ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter(formal_invalid_policy inputs path)flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 (500<=time)%coq_nat ->(time<limit)%coq_nat ->
 (forall site,eval_hfexpr_validif_policy(isolated_validif_policy(formal_invalid_policy inputs path))site flat_memories(rf_compare_immediate_port_expr n)(history time)(history time)=Some(Gval(Fuint width)word)) ->
 VM.find(nth 0 rf_compare_immediate_port_nodes n)(history time)=Some(Gval(Fuint width)word).
Proof. intros Bound Resets Steps Lower Upper Eval.
destruct n as[|n]. { change(VM.find 2089(history time)=Some(Gval(Fuint width)word)).
rewrite(reference_control_stable_2089_history inputs path history limit reset Resets Steps time(S time)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)).
eapply(reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 2089 reference_control_expr_2089);[exact reference_control_0_positions|exact reference_control_0_safety|exact reference_control_member_2089|exact Eval|apply Steps;lia]. }
destruct n as[|n]. { change(VM.find 2090(history time)=Some(Gval(Fuint width)word)).
rewrite(reference_control_stable_2090_history inputs path history limit reset Resets Steps time(S time)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)).
eapply(reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 2090 reference_control_expr_2090);[exact reference_control_0_positions|exact reference_control_0_safety|exact reference_control_member_2090|exact Eval|apply Steps;lia]. }
destruct n as[|n]. { change(VM.find 2093(history time)=Some(Gval(Fuint width)word)).
rewrite(reference_control_stable_2093_history inputs path history limit reset Resets Steps time(S time)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)).
eapply(reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 2093 reference_control_expr_2093);[exact reference_control_0_positions|exact reference_control_0_safety|exact reference_control_member_2093|exact Eval|apply Steps;lia]. }
destruct n as[|n]. { change(VM.find 2094(history time)=Some(Gval(Fuint width)word)).
rewrite(reference_control_stable_2094_history inputs path history limit reset Resets Steps time(S time)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)).
eapply(reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 2094 reference_control_expr_2094);[exact reference_control_0_positions|exact reference_control_0_safety|exact reference_control_member_2094|exact Eval|apply Steps;lia]. }
lia. Qed.
Theorem rf_compare_immediate_port_slices inputs path history limit reset time instruction unsigned :
 (forall t,(t<=limit)%coq_nat ->VM.find 1(history t)=Some(Gval(Fuint 1)[::reset])) ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter(formal_invalid_policy inputs path)flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 (500<=time)%coq_nat ->(time<limit)%coq_nat ->VM.find 1884(history time)=Some(Gval(Fuint 32)instruction) ->
 VM.find(if unsigned then 2090 else 2094)(history time)=Some(Gval(Fuint 5)(rf_instruction_address false instruction)).
Proof.
 intros Resets Steps Lower Upper Source.
assert(V2089:VM.find 2089(history time)=Some(Gval(Fuint 20)(drop 0(take 20(instruction))))).
{ eapply(rf_compare_immediate_port_value 0 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site.
cbn[rf_compare_immediate_port_expr nth reference_control_expr_2089 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Source. reflexivity. }
assert(V2090:VM.find 2090(history time)=Some(Gval(Fuint 5)(drop 15(take 20(drop 0(take 20(instruction))))))).
{ eapply(rf_compare_immediate_port_value 1 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site.
cbn[rf_compare_immediate_port_expr nth reference_control_expr_2090 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite V2089. reflexivity. }
assert(V2093:VM.find 2093(history time)=Some(Gval(Fuint 20)(drop 0(take 20(instruction))))).
{ eapply(rf_compare_immediate_port_value 2 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site.
cbn[rf_compare_immediate_port_expr nth reference_control_expr_2093 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Source. reflexivity. }
assert(V2094:VM.find 2094(history time)=Some(Gval(Fuint 5)(drop 15(take 20(drop 0(take 20(instruction))))))).
{ eapply(rf_compare_immediate_port_value 3 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site.
cbn[rf_compare_immediate_port_expr nth reference_control_expr_2094 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite V2093. reflexivity. }
unfold rf_instruction_address. rewrite !drop0 !take_take in V2090,V2094;try reflexivity.
destruct unsigned;assumption.
Qed.
(* Handwritten semantic composition. *)
Theorem rf_compare_immediate_rs1_history inputs path history limit reset time instruction unsigned :
 size instruction=32%nat ->
 (forall t,(t<=limit)%coq_nat ->VM.find 1(history t)=Some(Gval(Fuint 1)[::reset])) ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter(formal_invalid_policy inputs path)flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 (forall t,(200<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1884(history t)=Some(Gval(Fuint 32)instruction)) ->
 (500<=time)%coq_nat ->(time<limit)%coq_nat ->VM.find 1707(history time)=Some(Gval(Fuint 1)[::true]) ->
 (forall row,(row<48)%coq_nat ->VM.find(reference_instruction_guard row)(history time)=Some(Gval(Fuint 1)[::Nat.eqb row(rf_compare_immediate_class unsigned)])) ->
 VM.find 2145(history time)=Some(Gval(Fuint 5)(rf_instruction_address false instruction)).
Proof.
 intros Size Resets Steps Source Lower Upper Enabled Decode.
 assert(Typed:forall t,(200<=t)%coq_nat ->(t<=limit)%coq_nat ->exists v,VM.find 1884(history t)=Some v /\type_of_val v=Gtyp(Fuint 32)).
 { intros t L U. exists(Gval(Fuint 32)instruction);split;[apply Source;assumption|reflexivity]. }
 pose proof(rf_compare_immediate_port_slices inputs path history limit reset time instruction unsigned Resets Steps Lower Upper(Source time ltac:(lia)ltac:(lia)))as Raw.
 assert(Guards:forall n,(n<42)%coq_nat ->VM.find(rf_alu_rs1_guard n)(history time)=Some(Gval(Fuint 1)[::false])).
 { intros n Bound. unfold rf_alu_rs1_guard. rewrite(Decode(rf_alu_rs1_decoder n)ltac:(do 42(destruct n as[|n];[cbn[rf_alu_rs1_decoder nth];lia|]);lia)). destruct unsigned;do 42(destruct n as[|n];[reflexivity|]);lia. }
 assert(Prefix:VM.find 2101(history time)=Some(Gval(Fuint 5)(rf_instruction_address false instruction))).
 { destruct unsigned.
 - destruct(reference_rs1_types_history _ history limit 200 Steps Typed 124%nat ltac:(lia)time ltac:(cbv[reference_rs1_rank reference_rs1_ranks nth];lia)ltac:(lia))as[other[Other OtherType]].
 eapply(rf_add_port_value 7 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site. cbn[rf_add_port_expr nth]. unfold reference_control_expr_2101.
 exact(immediate_selected_mux _ site _ _ _ _ 5 _ other true(rf_instruction_address_size false instruction Size)(Decode 2%nat ltac:(lia))Raw Other OtherType).
 - destruct(reference_rs1_types_history _ history limit 200 Steps Typed 123%nat ltac:(lia)time ltac:(cbv[reference_rs1_rank reference_rs1_ranks nth];lia)ltac:(lia))as[other[Other OtherType]].
 assert(V2100:VM.find 2100(history time)=Some(Gval(Fuint 5)(rf_instruction_address false instruction))).
 { eapply(rf_add_port_value 6 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site. cbn[rf_add_port_expr nth]. unfold reference_control_expr_2100.
 exact(immediate_selected_mux _ site _ _ _ _ 5 _ other true(rf_instruction_address_size false instruction Size)(Decode 1%nat ltac:(lia))Raw Other OtherType). }
 destruct(reference_rs1_types_history _ history limit 200 Steps Typed 118%nat ltac:(lia)time ltac:(cbv[reference_rs1_rank reference_rs1_ranks nth];lia)ltac:(lia))as[other1[Other1 Type1]].
 eapply(rf_add_port_value 7 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site. cbn[rf_add_port_expr nth]. unfold reference_control_expr_2101.
 exact(immediate_selected_mux _ site _ _ _ _ 5 _ other1 false(rf_instruction_address_size false instruction Size)(Decode 2%nat ltac:(lia))V2100 Other1 Type1). }
 assert(Selected:VM.find 2143(history time)=Some(Gval(Fuint 5)(rf_instruction_address false instruction))).
 { change(VM.find(rf_alu_rs1_node 41)(history time)=Some(Gval(Fuint 5)(rf_instruction_address false instruction))).
 apply(immediate_stable_mux_prefix (formal_invalid_policy inputs path)(history time)42 5(rf_instruction_address false instruction)2101 rf_alu_rs1_node rf_alu_rs1_guard rf_alu_rs1_yes(rf_instruction_address_size false instruction Size));[|exact Guards| |exact Prefix|lia].
 - intros n Bound value Eval. rewrite(rf_alu_rs1_same n inputs path history limit reset time Bound Resets Steps Lower Upper). apply(rf_alu_rs1_step n _ _ _ value Bound Eval);apply Steps;exact Upper.
 - intros n Bound. exact(proj1(rf_alu_rs1_types n _ history limit time Bound Steps Typed Lower ltac:(lia))). }
 assert(Gate:VM.find 2144(history time)=Some(Gval(Fuint 5)(rf_instruction_address false instruction))).
 { eapply(rf_alu_rs1_value 15 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site.
 cbn[rf_alu_rs1_aux_expr nth reference_control_expr_2144 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Enabled;cbn;rewrite Selected. apply dut_decode_adapt;exact(rf_instruction_address_size false instruction Size). }
 eapply(rf_alu_rs1_value 16 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site;exact Gate.
Qed.

Require Import ObservedJointRegisterConcrete LoadTypeCorrespondence ReferenceLoadRs1 ReferenceRegisterRead.
Theorem rf_compare_immediate_index_observed memory inputs k observed instruction unsigned :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 VM.find 1707(top_environment observed)=Some(Gval(Fuint 1)[::true]) ->
 VM.find 7750(top_environment observed)=Some(Gval(Fuint 32)instruction) ->
 N.land(to_N instruction)(reference_instruction_mask(rf_compare_immediate_class unsigned))=reference_instruction_code(rf_compare_immediate_class unsigned) ->
 VM.find 2145(top_environment observed)=Some(Gval(Fuint 5)(rf_instruction_address false instruction)).
Proof.
 intros Observe Legal Enabled Instruction Match.
 destruct(rf_reference_operand_context memory inputs k observed instruction(rf_compare_immediate_class unsigned)Observe Legal Enabled Instruction ltac:(destruct unsigned;vm_compute;lia)Match)
 as[Size[reset[history[Last[Resets[Steps[Source[Enable Decode]]]]]]]].
 pose proof(rf_compare_immediate_rs1_history (generated_observation_input inputs k)nil history 9259 reset 9250 instruction unsigned Size Resets Steps Source ltac:(vm_compute;lia)ltac:(vm_compute;lia)Enable Decode)as Value.
 rewrite(reference_control_stable_2145_history (generated_observation_input inputs k)nil history 9259 reset Resets Steps 9250 9259 ltac:(vm_compute;lia)ltac:(vm_compute;lia)ltac:(vm_compute;lia)ltac:(vm_compute;lia))Last in Value. exact Value.
Qed.
Theorem rf_compare_immediate_bank_observed memory inputs k observed instruction unsigned bank :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 VM.find 1707(top_environment observed)=Some(Gval(Fuint 1)[::true]) ->
 VM.find 7750(top_environment observed)=Some(Gval(Fuint 32)instruction) ->
 N.land(to_N instruction)(reference_instruction_mask(rf_compare_immediate_class unsigned))=reference_instruction_code(rf_compare_immediate_class unsigned) ->
 rf_reference_bank_at(top_environment observed)bank ->
 VM.find 2209(top_environment observed)=Some(Gval(Fuint 32)(bank(to_nat(rf_instruction_address false instruction)))).
Proof.
 intros Observe Legal Enabled Instruction Match Bank.
 destruct(observed_joint_register_concrete memory inputs k observed 7750%nat 32%nat Observe Legal load_type_instruction_member)as[word[Size Word]].
 rewrite Instruction in Word;inversion Word;subst word.
 exact(reference_register_read_observed memory inputs k observed bank _ Observe Legal Bank(rf_instruction_address_size false instruction Size)(rf_compare_immediate_index_observed memory inputs k observed instruction unsigned Observe Legal Enabled Instruction Match)).
Qed.
