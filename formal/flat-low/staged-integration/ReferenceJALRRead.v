Require Import CoreSocModel ComparisonNodes RFALUData RFScalarControl ReferenceRs1Types ReferenceRs2Types ReferenceLoadRs1 ReferenceStoreRs2 ReferenceLoadImmediate ReferenceImmediateTypes ReferenceInstructionDecode ReferenceControlStabilityHistory ReferenceControlNodeCongruence0 ReferenceControlNodeCongruence2 ReferenceControlNodeCertificates0 ReferenceControlNodeCertificates2 ReferenceControlExpressions ReferenceRedirectSpine RFReadPorts DUTRedirectDecode.
From Coq Require Import NArith List Lia PeanoNat.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.

Require Import RFALUReferencePorts ReferenceJALRImmediate JALRAddressCycle ReferenceControlNodeCertificates0 ReferenceControlNodeCongruence0 RFReferenceNopHistory.

Lemma jalr_rs1_raw inputs path history limit reset time instruction :
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

Theorem jalr_rs1_history inputs path history limit reset time instruction :size instruction=32%nat ->
 (forall t,(t<=limit)%coq_nat ->VM.find 1(history t)=Some(Gval(Fuint 1)[::reset])) ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter(formal_invalid_policy inputs path)flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 (forall t,(200<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1884(history t)=Some(Gval(Fuint 32)instruction)) ->
 (500<=time)%coq_nat ->(time<limit)%coq_nat ->VM.find 1707(history time)=Some(Gval(Fuint 1)[::true]) ->
 (forall n,(n<42)%coq_nat ->VM.find(rf_alu_rs1_guard n)(history time)=Some(Gval(Fuint 1)[::Nat.eqb n 16%nat])) ->
 VM.find 2145(history time)=Some(Gval(Fuint 5)(rf_instruction_address false instruction)).
Proof.
 intros Size Resets Steps Source Lower Upper Enabled Guards.
 assert(Typed:forall t,(200<=t)%coq_nat ->(t<=limit)%coq_nat ->exists v,VM.find 1884(history t)=Some v /\type_of_val v=Gtyp(Fuint 32)).
 { intros t L U. exists(Gval(Fuint 32)instruction);split;[apply Source;assumption|reflexivity]. }
 pose proof(jalr_rs1_raw inputs path history limit reset time instruction Resets Steps Lower Upper(Source time ltac:(lia)ltac:(lia)))as Raw.
 assert(Selected:VM.find 2143(history time)=Some(Gval(Fuint 5)(rf_instruction_address false instruction))).
 { change(VM.find(rf_alu_rs1_node 41)(history time)=Some(Gval(Fuint 5)(rf_instruction_address false instruction))).
 eapply(immediate_stable_mux_suffix (formal_invalid_policy inputs path)(history time)(history(S time))42  16%nat 5(rf_instruction_address false instruction)2101 rf_alu_rs1_node rf_alu_rs1_guard rf_alu_rs1_yes);[lia|exact(rf_instruction_address_size false instruction Size)| | |exact Guards| | |exact Raw|lia|lia].
 - intros n Bound. exact(rf_alu_rs1_same n inputs path history limit reset time Bound Resets Steps Lower Upper).
 - intros n Bound value Eval. apply(rf_alu_rs1_step n _ _ _ value Bound Eval);apply Steps;exact Upper.
 - intros n Bound. exact(proj1(rf_alu_rs1_types n _ history limit time Bound Steps Typed Lower ltac:(lia))).
 - intros n Bound. exact(proj2(rf_alu_rs1_types n _ history limit time Bound Steps Typed Lower ltac:(lia))). }
 assert(Gate:VM.find 2144(history time)=Some(Gval(Fuint 5)(rf_instruction_address false instruction))).
 { eapply(rf_alu_rs1_value 15 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site.
 cbn[rf_alu_rs1_aux_expr nth reference_control_expr_2144 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Enabled;cbn;rewrite Selected. apply dut_decode_adapt;exact(rf_instruction_address_size false instruction Size). }
 eapply(rf_alu_rs1_value 16 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site;exact Gate.
Qed.

Lemma jalr_rs1_decode instruction n :(n<42)%coq_nat ->jalr_match instruction ->
 N.eqb(reference_instruction_code(rf_alu_rs1_decoder n))(N.land(to_N instruction)(reference_instruction_mask(rf_alu_rs1_decoder n)))=Nat.eqb n 16.
Proof. intros Bound Match.
 rewrite(rf_reference_decode_onehot instruction 22(rf_alu_rs1_decoder n)ltac:(lia)ltac:(do 42(destruct n as[|n];[cbn[rf_alu_rs1_decoder nth];lia|]);lia)Match).
 do 42(destruct n as[|n];[reflexivity|]);lia.
Qed.
Require Import ObservedJointRegisterConcrete JointUpdateBoundaryHistory FormalObservedHistory FormalLocalHistory MemoryRequestObservedSemantics LoadTypeCorrespondence.

Theorem jalr_rs1_observed memory inputs k observed instruction :
 generated_observe memory inputs k = Some observed -> generated_legal_trace memory inputs k ->
 VM.find 1707(top_environment observed)=Some(Gval(Fuint 1)[::true]) ->
  VM.find 7750 (top_environment observed) = Some (Gval (Fuint 32) instruction) ->
 jalr_match instruction ->
 VM.find 2145 (top_environment observed) = Some (Gval (Fuint 5) (rf_instruction_address false instruction)).
Proof.
 intros Observe Legal Enabled Instruction Load.
 destruct (observed_joint_register_concrete memory inputs k observed 7750%nat 32%nat Observe Legal load_type_instruction_member) as [word [Size Word]].
 rewrite Instruction in Word. inversion Word;subst word.
 destruct (observed_history memory inputs k observed Observe Legal) as [reset [history [Last [Steps Resets]]]].
 assert (Inst : forall t, (t <= 9259)%coq_nat -> VM.find 7750 (history t) = Some (Gval (Fuint 32) instruction)).
 { intros t Upper. pose proof (joint_update_register_history_same _ history 9259 7750 32 load_type_instruction_member Steps) as Hold.
   rewrite (Hold t Upper). rewrite <- (Hold 9259%nat ltac:(lia)). rewrite Last. exact Instruction. }
 assert (Enable : forall t, (195 <= t)%coq_nat -> (t <= 9259)%coq_nat -> VM.find 1707 (history t) = Some (Gval (Fuint 1) [::true])).
 { intros t Lower Upper. rewrite (reference_control_stable_1707_history (generated_observation_input inputs k) nil history 9259 reset Resets Steps t 9259%nat ltac:(lia) ltac:(lia) Upper ltac:(lia)) Last. exact Enabled. }
 assert (Source : forall t, (200 <= t)%coq_nat -> (t <= 9259)%coq_nat -> VM.find 1884 (history t) = Some (Gval (Fuint 32) instruction)).
 { intros t Lower Upper. exact (memory_reference_instruction_history _ history 9259 195 instruction true Size Steps Inst Enable t Lower Upper). }
 assert (Guards : forall n,(n<42)%coq_nat ->VM.find(rf_alu_rs1_guard n)(history 9250%nat)=Some(Gval(Fuint 1)[::Nat.eqb n 16%nat])).
 { intros n Bound.
   set (h := fun t:nat => history (match t with O=>9248%nat | S O=>9249%nat | _=>9250%nat end)).
   assert (HS : forall t,(t<2)%coq_nat ->formal_value_iter(formal_invalid_policy(generated_observation_input inputs k)nil)flat_memories(h t)false(h t)flat_statements=Some(h(S t))).
   { intros [|[|t]] T;[apply Steps;vm_compute;lia|apply Steps;vm_compute;lia|lia]. }
   assert (HI : forall t,(t<=2)%coq_nat ->VM.find 1884(h t)=Some(Gval(Fuint 32)instruction)).
   { intros [|[|t]] T;unfold h;apply Source;vm_compute;lia. }
   pose proof(reference_instruction_decode_history _ h 2 instruction (rf_alu_rs1_decoder n) ltac:(do 42 (destruct n as [|n];[cbn [rf_alu_rs1_decoder nth];lia|]);lia) HS HI 2 ltac:(lia) ltac:(lia))as Decode.
   rewrite(jalr_rs1_decode instruction n Bound Load)in Decode. exact Decode. }
 pose proof(jalr_rs1_history (generated_observation_input inputs k)nil history 9259 reset 9250 instruction Size Resets Steps Source ltac:(vm_compute;lia)ltac:(vm_compute;lia)(Enable 9250%nat ltac:(vm_compute;lia)ltac:(vm_compute;lia))Guards)as Value.
 rewrite(reference_control_stable_2145_history (generated_observation_input inputs k)nil history 9259 reset Resets Steps 9250 9259 ltac:(vm_compute;lia)ltac:(vm_compute;lia)ltac:(vm_compute;lia)ltac:(vm_compute;lia))Last in Value. exact Value.
Qed.
Theorem reference_jalr_rs1_bank_active_observed memory inputs k observed instruction bank :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 VM.find 1707(top_environment observed)=Some(Gval(Fuint 1)[::true]) ->
 VM.find 7750(top_environment observed)=Some(Gval(Fuint 32)instruction) ->
 jalr_match instruction ->
 rf_reference_bank_at(top_environment observed)bank ->
 VM.find 2209(top_environment observed)=Some(Gval(Fuint 32)(bank(to_nat(rf_instruction_address false instruction)))).
Proof.
 intros Observe Legal Enabled Instruction Match Bank.
 assert(Size:size instruction=32%nat).
 { destruct(observed_joint_register_concrete memory inputs k observed 7750%nat 32%nat Observe Legal load_type_instruction_member)as[word[W V]]. rewrite Instruction in V;inversion V;subst;exact W. }
 eapply(reference_register_read_observed memory inputs k observed bank (rf_instruction_address false instruction));[exact Observe|exact Legal|exact Bank|exact(rf_instruction_address_size false instruction Size)|].
 exact(jalr_rs1_observed memory inputs k observed instruction Observe Legal Enabled Instruction Match).
Qed.

Require Import ReferenceIllegalObserved LoadPipelineClassification FormalInstructionResetConstants.
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
