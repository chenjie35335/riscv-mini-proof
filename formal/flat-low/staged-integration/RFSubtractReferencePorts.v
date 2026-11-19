Require Import RFReferenceNopHistory ReferenceBankObservation FormalLocalHistory ReferenceLoadImmediate DUTRedirectDecode RFAddReferencePorts RFAddCycle RFALUReferencePorts RFALUReferenceData ReferenceImmediatePrefix ReferenceRs1Types ReferenceRs2Types ReferenceControlExpressions ReferenceControlStabilityHistory ReferenceControlNodeCertificates0 ReferenceControlNodeCertificates2 ReferenceControlNodeCongruence0 ReferenceControlNodeCongruence2 ReferenceRedirectSpine ReferenceInstructionDecode RFReadPorts CoreSocModel ComparisonNodes.
From Coq Require Import NArith List Lia PeanoNat.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.

Definition rf_subtract_port_nodes :seq VarOrder.T :=[::2020;2021;2022;2585].
Definition rf_subtract_port_expr n :=nth (@Econst VarOrder.T(Fuint 1)[::false])[::reference_control_expr_2020;reference_control_expr_2021;reference_control_expr_2022;reference_control_expr_2585]n.
Lemma rf_subtract_port_value n inputs path history limit reset time width word :(n<4)%coq_nat ->
 (forall t,(t<=limit)%coq_nat ->VM.find 1(history t)=Some(Gval(Fuint 1)[::reset])) ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter(formal_invalid_policy inputs path)flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 (500<=time)%coq_nat ->(time<limit)%coq_nat ->
 (forall site,eval_hfexpr_validif_policy(isolated_validif_policy(formal_invalid_policy inputs path))site flat_memories(rf_subtract_port_expr n)(history time)(history time)=Some(Gval(Fuint width)word)) ->
 VM.find(nth 0 rf_subtract_port_nodes n)(history time)=Some(Gval(Fuint width)word).
Proof. intros Bound Resets Steps Lower Upper Eval.
destruct n as[|n]. { change(VM.find 2020(history time)=Some(Gval(Fuint width)word)).
rewrite(reference_control_stable_2020_history inputs path history limit reset Resets Steps time(S time)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)).
eapply(reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 2020 reference_control_expr_2020);[exact reference_control_0_positions|exact reference_control_0_safety|exact reference_control_member_2020|exact Eval|apply Steps;lia]. }
destruct n as[|n]. { change(VM.find 2021(history time)=Some(Gval(Fuint width)word)).
rewrite(reference_control_stable_2021_history inputs path history limit reset Resets Steps time(S time)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)).
eapply(reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 2021 reference_control_expr_2021);[exact reference_control_0_positions|exact reference_control_0_safety|exact reference_control_member_2021|exact Eval|apply Steps;lia]. }
destruct n as[|n]. { change(VM.find 2022(history time)=Some(Gval(Fuint width)word)).
rewrite(reference_control_stable_2022_history inputs path history limit reset Resets Steps time(S time)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)).
eapply(reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 2022 reference_control_expr_2022);[exact reference_control_0_positions|exact reference_control_0_safety|exact reference_control_member_2022|exact Eval|apply Steps;lia]. }
destruct n as[|n]. { change(VM.find 2585(history time)=Some(Gval(Fuint width)word)).
rewrite(reference_control_stable_2585_history inputs path history limit reset Resets Steps time(S time)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)).
eapply(reference_redirect_ground_step reference_control_2_offsets reference_control_2_nodes 2585 reference_control_expr_2585);[exact reference_control_2_positions|exact reference_control_2_safety|exact reference_control_member_2585|exact Eval|apply Steps;lia]. }
lia. Qed.
Theorem rf_subtract_port_slices inputs path history limit reset time instruction :
 (forall t,(t<=limit)%coq_nat ->VM.find 1(history t)=Some(Gval(Fuint 1)[::reset])) ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter(formal_invalid_policy inputs path)flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 (500<=time)%coq_nat ->(time<limit)%coq_nat ->VM.find 1884(history time)=Some(Gval(Fuint 32)instruction) ->
 VM.find 2022(history time)=Some(Gval(Fuint 5)(rf_instruction_address false instruction)) /\
 VM.find 2585(history time)=Some(Gval(Fuint 5)(rf_instruction_address true instruction)).
Proof.
 intros Resets Steps Lower Upper Source.
assert(V2020:VM.find 2020(history time)=Some(Gval(Fuint 25)(drop 0(take 25(instruction))))).
{ eapply(rf_subtract_port_value 0 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site.
cbn[rf_subtract_port_expr nth reference_control_expr_2020 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Source. reflexivity. }
assert(V2021:VM.find 2021(history time)=Some(Gval(Fuint 20)(drop 0(take 20(drop 0(take 25(instruction))))))).
{ eapply(rf_subtract_port_value 1 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site.
cbn[rf_subtract_port_expr nth reference_control_expr_2021 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite V2020. reflexivity. }
assert(V2022:VM.find 2022(history time)=Some(Gval(Fuint 5)(drop 15(take 20(drop 0(take 20(drop 0(take 25(instruction))))))))).
{ eapply(rf_subtract_port_value 2 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site.
cbn[rf_subtract_port_expr nth reference_control_expr_2022 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite V2021. reflexivity. }
assert(V2585:VM.find 2585(history time)=Some(Gval(Fuint 5)(drop 20(take 25(drop 0(take 25(instruction))))))).
{ eapply(rf_subtract_port_value 3 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site.
cbn[rf_subtract_port_expr nth reference_control_expr_2585 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite V2020. reflexivity. }
unfold rf_instruction_address. rewrite !drop0 !take_take in V2022,V2585;try reflexivity.
split;assumption.
Qed.
(* Handwritten semantic composition. *)
Theorem rf_subtract_rs1_history inputs path history limit reset time instruction :size instruction=32%nat ->
 (forall t,(t<=limit)%coq_nat ->VM.find 1(history t)=Some(Gval(Fuint 1)[::reset])) ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter(formal_invalid_policy inputs path)flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 (forall t,(200<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1884(history t)=Some(Gval(Fuint 32)instruction)) ->
 (500<=time)%coq_nat ->(time<limit)%coq_nat ->VM.find 1707(history time)=Some(Gval(Fuint 1)[::true]) ->
 (forall n,(n<42)%coq_nat ->VM.find(rf_alu_rs1_guard n)(history time)=Some(Gval(Fuint 1)[::Nat.eqb n 14%nat])) ->
 VM.find 2145(history time)=Some(Gval(Fuint 5)(rf_instruction_address false instruction)).
Proof.
 intros Size Resets Steps Source Lower Upper Enabled Guards.
 assert(Typed:forall t,(200<=t)%coq_nat ->(t<=limit)%coq_nat ->exists v,VM.find 1884(history t)=Some v /\type_of_val v=Gtyp(Fuint 32)).
 { intros t L U. exists(Gval(Fuint 32)instruction);split;[apply Source;assumption|reflexivity]. }
 pose proof(proj1(rf_subtract_port_slices inputs path history limit reset time instruction Resets Steps Lower Upper(Source time ltac:(lia)ltac:(lia))))as Raw.
 assert(Target:(14<42)%coq_nat)by lia.
 assert(Selected:VM.find 2143(history time)=Some(Gval(Fuint 5)(rf_instruction_address false instruction))).
 { change(VM.find(rf_alu_rs1_node 41)(history time)=Some(Gval(Fuint 5)(rf_instruction_address false instruction))).
 eapply(immediate_stable_mux_suffix (formal_invalid_policy inputs path)(history time)(history(S time))42 14%nat 5(rf_instruction_address false instruction)2101 rf_alu_rs1_node rf_alu_rs1_guard rf_alu_rs1_yes);[exact Target|exact(rf_instruction_address_size false instruction Size)| | |exact Guards| | |exact Raw|lia|lia].
 - intros n Bound. exact(rf_alu_rs1_same n inputs path history limit reset time Bound Resets Steps Lower Upper).
 - intros n Bound value Eval. apply(rf_alu_rs1_step n _ _ _ value Bound Eval);apply Steps;exact Upper.
 - intros n Bound. exact(proj1(rf_alu_rs1_types n _ history limit time Bound Steps Typed Lower ltac:(lia))).
 - intros n Bound. exact(proj2(rf_alu_rs1_types n _ history limit time Bound Steps Typed Lower ltac:(lia))). }
 assert(Gate:VM.find 2144(history time)=Some(Gval(Fuint 5)(rf_instruction_address false instruction))).
 { eapply(rf_alu_rs1_value 15 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site.
 cbn[rf_alu_rs1_aux_expr nth reference_control_expr_2144 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Enabled;cbn;rewrite Selected. apply dut_decode_adapt;exact(rf_instruction_address_size false instruction Size). }
 eapply(rf_alu_rs1_value 16 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site;exact Gate.
Qed.

Theorem rf_subtract_rs2_history inputs path history limit reset time instruction :size instruction=32%nat ->
 (forall t,(t<=limit)%coq_nat ->VM.find 1(history t)=Some(Gval(Fuint 1)[::reset])) ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter(formal_invalid_policy inputs path)flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 (forall t,(200<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1884(history t)=Some(Gval(Fuint 32)instruction)) ->
 (500<=time)%coq_nat ->(time<limit)%coq_nat ->VM.find 1707(history time)=Some(Gval(Fuint 1)[::true]) ->
 (forall n,(n<24)%coq_nat ->VM.find(rf_alu_rs2_guard n)(history time)=Some(Gval(Fuint 1)[::Nat.eqb n 5%nat])) ->
 VM.find 2622(history time)=Some(Gval(Fuint 5)(rf_instruction_address true instruction)).
Proof.
 intros Size Resets Steps Source Lower Upper Enabled Guards.
 assert(Typed:forall t,(200<=t)%coq_nat ->(t<=limit)%coq_nat ->exists v,VM.find 1884(history t)=Some v /\type_of_val v=Gtyp(Fuint 32)).
 { intros t L U. exists(Gval(Fuint 32)instruction);split;[apply Source;assumption|reflexivity]. }
 pose proof(proj2(rf_subtract_port_slices inputs path history limit reset time instruction Resets Steps Lower Upper(Source time ltac:(lia)ltac:(lia))))as Raw.
 assert(Target:(5<24)%coq_nat)by lia.
 assert(Selected:VM.find 2620(history time)=Some(Gval(Fuint 5)(rf_instruction_address true instruction))).
 { change(VM.find(rf_alu_rs2_node 23)(history time)=Some(Gval(Fuint 5)(rf_instruction_address true instruction))).
 eapply(immediate_stable_mux_suffix (formal_invalid_policy inputs path)(history time)(history(S time))24 5%nat 5(rf_instruction_address true instruction)2596 rf_alu_rs2_node rf_alu_rs2_guard rf_alu_rs2_yes);[exact Target|exact(rf_instruction_address_size true instruction Size)| | |exact Guards| | |exact Raw|lia|lia].
 - intros n Bound. exact(rf_alu_rs2_same n inputs path history limit reset time Bound Resets Steps Lower Upper).
 - intros n Bound value Eval. apply(rf_alu_rs2_step n _ _ _ value Bound Eval);apply Steps;exact Upper.
 - intros n Bound. exact(proj1(rf_alu_rs2_types n _ history limit time Bound Steps Typed Lower ltac:(lia))).
 - intros n Bound. exact(proj2(rf_alu_rs2_types n _ history limit time Bound Steps Typed Lower ltac:(lia))). }
 assert(Gate:VM.find 2621(history time)=Some(Gval(Fuint 5)(rf_instruction_address true instruction))).
 { eapply(rf_alu_rs2_value 6 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site.
 cbn[rf_alu_rs2_aux_expr nth reference_control_expr_2621 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Enabled;cbn;rewrite Selected. apply dut_decode_adapt;exact(rf_instruction_address_size true instruction Size). }
 eapply(rf_alu_rs2_value 7 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site;exact Gate.
Qed.
Require Import ObservedJointRegisterConcrete LoadTypeCorrespondence ReferenceSecondRegisterRead ReferenceLoadRs1 ReferenceRegisterRead.
Theorem rf_subtract_index_observed second memory inputs k observed instruction :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 VM.find 1707(top_environment observed)=Some(Gval(Fuint 1)[::true]) ->
 VM.find 7750(top_environment observed)=Some(Gval(Fuint 32)instruction) ->
 N.land(to_N instruction)(reference_instruction_mask(19%nat))=reference_instruction_code(19%nat) ->
 VM.find(if second then 2622 else 2145)(top_environment observed)=Some(Gval(Fuint 5)(rf_instruction_address second instruction)).
Proof.
 intros Observe Legal Enabled Instruction Match.
 destruct(rf_reference_operand_context memory inputs k observed instruction(19%nat)Observe Legal Enabled Instruction ltac:(lia)Match)
 as[Size[reset[history[Last[Resets[Steps[Source[Enable Decode]]]]]]]].
 destruct second.
 -
 pose proof(rf_subtract_rs2_history (generated_observation_input inputs k)nil history 9259 reset 9250 instruction Size Resets Steps Source ltac:(vm_compute;lia)ltac:(vm_compute;lia)Enable ltac:(intros n Bound; unfold rf_alu_rs2_guard; rewrite(Decode(rf_alu_rs2_decoder n)ltac:(do 24(destruct n as[|n];[cbn[rf_alu_rs2_decoder nth];lia|]);lia)); do 24(destruct n as[|n];[reflexivity|]);lia))as Value.
 rewrite(reference_control_stable_2622_history (generated_observation_input inputs k)nil history 9259 reset Resets Steps 9250 9259 ltac:(vm_compute;lia)ltac:(vm_compute;lia)ltac:(vm_compute;lia)ltac:(vm_compute;lia))Last in Value. exact Value.
 - pose proof(rf_subtract_rs1_history (generated_observation_input inputs k)nil history 9259 reset 9250 instruction Size Resets Steps Source ltac:(vm_compute;lia)ltac:(vm_compute;lia)Enable ltac:(intros n Bound; unfold rf_alu_rs1_guard; rewrite(Decode(rf_alu_rs1_decoder n)ltac:(do 42(destruct n as[|n];[cbn[rf_alu_rs1_decoder nth];lia|]);lia)); do 42(destruct n as[|n];[reflexivity|]);lia))as Value.
 rewrite(reference_control_stable_2145_history (generated_observation_input inputs k)nil history 9259 reset Resets Steps 9250 9259 ltac:(vm_compute;lia)ltac:(vm_compute;lia)ltac:(vm_compute;lia)ltac:(vm_compute;lia))Last in Value. exact Value.
Qed.
Theorem rf_subtract_bank_observed second memory inputs k observed instruction bank :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 VM.find 1707(top_environment observed)=Some(Gval(Fuint 1)[::true]) ->
 VM.find 7750(top_environment observed)=Some(Gval(Fuint 32)instruction) ->
 N.land(to_N instruction)(reference_instruction_mask(19%nat))=reference_instruction_code(19%nat) ->
 rf_reference_bank_at(top_environment observed)bank ->
 VM.find(if second then 2804 else 2209)(top_environment observed)=Some(Gval(Fuint 32)(bank(to_nat(rf_instruction_address second instruction)))).
Proof.
 intros Observe Legal Enabled Instruction Match Bank.
 destruct(observed_joint_register_concrete memory inputs k observed 7750%nat 32%nat Observe Legal load_type_instruction_member)as[word[Size Word]].
 rewrite Instruction in Word;inversion Word;subst word.
 pose proof(rf_subtract_index_observed second memory inputs k observed instruction Observe Legal Enabled Instruction Match)as Index.
 destruct second.
 - exact(reference_second_register_read_observed memory inputs k observed bank _ Observe Legal Bank(rf_instruction_address_size true instruction Size)Index).
 - exact(reference_register_read_observed memory inputs k observed bank _ Observe Legal Bank(rf_instruction_address_size false instruction Size)Index).
Qed.
