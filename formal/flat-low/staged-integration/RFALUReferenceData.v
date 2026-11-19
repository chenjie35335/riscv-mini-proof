Require Import RFWriteEffect.
Require Import CoreSocModel ComparisonNodes RFALUData RFALUReferencePorts RFALUReferenceImmediate CycleRFExecute RFEffectState RFReferenceWriteEffect RFReferenceNopHistory ReferenceInstructionDecode RFReadPorts ReferenceControlStabilityHistory FormalObservedHistory FormalLocalHistory ObservedJointRegisterConcrete LoadTypeCorrespondence.
From Coq Require Import NArith List Lia PeanoNat.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Theorem rf_bitwise_reference_data_observed memory inputs k observed instruction lane bank :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 VM.find 1(formal_external_inputs(generated_observation_input inputs k))=Some(Gval(Fuint 1)[::false]) ->
 (lane<6)%coq_nat ->VM.find 7750(top_environment observed)=Some(Gval(Fuint 32)instruction) ->
 N.land(to_N instruction)(reference_instruction_mask(rf_bitwise_class lane))=reference_instruction_code(rf_bitwise_class lane) ->
 rf_reference_bank_at(top_environment observed)bank ->
 VM.find(rf_bitwise_output lane)(top_environment observed)=Some(Gval(Fuint 32)(cycle_bitwise_semantics lane bank instruction)).
Proof.
 intros Observe Legal Reset Lane Instruction Match Bank.
 pose proof(rf_bitwise_reference_enabled memory inputs k observed instruction lane Observe Legal Reset Lane Instruction Match)as Enabled.
 pose proof(rf_alu_rs1_bank_observed memory inputs k observed instruction lane bank Observe Legal Enabled Lane Instruction Match Bank)as Left.
 assert(Right:VM.find(rf_bitwise_source lane)(top_environment observed)=Some(Gval(Fuint 32)(rf_bitwise_right lane instruction(bank(to_nat(rf_instruction_address true instruction)))))).
 { unfold rf_bitwise_source,rf_bitwise_right. destruct(Nat.ltb lane 3)eqn:Reg.
 - apply Nat.ltb_lt in Reg. exact(rf_alu_rs2_bank_observed memory inputs k observed instruction lane bank Observe Legal Enabled Reg Instruction Match Bank).
 - do 3(destruct lane as[|lane];[discriminate Reg|]).
 destruct lane as[|lane];[exact(rf_bitwise_immediate_observed memory inputs k observed instruction 0%nat Observe Legal Reset ltac:(lia)Instruction Match)|].
 destruct lane as[|lane];[exact(rf_bitwise_immediate_observed memory inputs k observed instruction 1%nat Observe Legal Reset ltac:(lia)Instruction Match)|].
 destruct lane as[|lane];[exact(rf_bitwise_immediate_observed memory inputs k observed instruction 2%nat Observe Legal Reset ltac:(lia)Instruction Match)|]. lia. }
 destruct(observed_history memory inputs k observed Observe Legal)as[reset[history[Last[Steps Resets]]]].
 assert(L:VM.find 2209(history 9256%nat)=Some(Gval(Fuint 32)(bank(to_nat(rf_instruction_address false instruction))))).
 { rewrite(reference_control_stable_2209_history (generated_observation_input inputs k)nil history 9259 reset Resets Steps 9256 9259 ltac:(vm_compute;lia)ltac:(vm_compute;lia)ltac:(vm_compute;lia)ltac:(vm_compute;lia))Last;exact Left. }
 assert(R:forall time,(500<=time)%coq_nat ->(time<=9259)%coq_nat ->VM.find(rf_bitwise_source lane)(history time)=Some(Gval(Fuint 32)(rf_bitwise_right lane instruction(bank(to_nat(rf_instruction_address true instruction)))))).
 { intros time Lower Upper. unfold rf_bitwise_source in *. destruct(Nat.ltb lane 3).
 - rewrite(reference_control_stable_2804_history (generated_observation_input inputs k)nil history 9259 reset Resets Steps time 9259 ltac:(lia)ltac:(vm_compute;lia)Upper ltac:(vm_compute;lia))Last;exact Right.
 - rewrite(reference_control_stable_2552_history (generated_observation_input inputs k)nil history 9259 reset Resets Steps time 9259 ltac:(lia)ltac:(vm_compute;lia)Upper ltac:(vm_compute;lia))Last;exact Right. }
 rewrite<-Last. unfold cycle_bitwise_semantics.
 apply(rf_reference_bitwise_three lane(formal_invalid_policy(generated_observation_input inputs k)nil)(history 9256%nat)(history 9257%nat)(history 9258%nat)(history 9259%nat)_ _ Lane L).
 - intros old[Same|Same];subst old;apply R;vm_compute;lia.
 - apply Steps;vm_compute;lia.
 - apply Steps;vm_compute;lia.
 - apply Steps;vm_compute;lia.
Qed.
Require Import LoadImmediateSemantics ReferenceBankCycleInputs RFScalarControl MemoryRequestObservedSemantics JointUpdateBoundaryHistory.
Lemma rf_bitwise_semantics_size bank instruction lane :
 size instruction=32%nat ->
 (forall index,(index<32)%coq_nat ->size(bank index)=32%nat) ->
 size(cycle_bitwise_semantics lane bank instruction)=32%nat.
Proof.
 intros Size Bank.
 assert(Address:forall second,(to_nat(rf_instruction_address second instruction)<32)%coq_nat).
 { intro second. pose proof(to_nat_bounded(rf_instruction_address second instruction))as Bound.
 rewrite(rf_instruction_address_size second instruction Size)in Bound. exact(elimT ltP Bound). }
 unfold cycle_bitwise_semantics. apply rf_bitwise_word_size;[apply Bank,Address|].
 unfold rf_bitwise_right. destruct(Nat.ltb lane 3);[apply Bank,Address|exact(load_i_immediate_size instruction Size)].
Qed.
Lemma rf_bitwise_write_node lane :(lane<6)%coq_nat ->
 rf_reference_write_data(rf_isa_write_stage(rf_bitwise_class lane))=rf_bitwise_output lane.
Proof. intro Lane. do 6(destruct lane as[|lane];[reflexivity|]);lia. Qed.
Theorem rf_bitwise_reference_word_observed memory inputs k observed instruction lane bank :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 VM.find 1(formal_external_inputs(generated_observation_input inputs k))=Some(Gval(Fuint 1)[::false]) ->
 (lane<6)%coq_nat ->VM.find 7750(top_environment observed)=Some(Gval(Fuint 32)instruction) ->
 N.land(to_N instruction)(reference_instruction_mask(rf_bitwise_class lane))=reference_instruction_code(rf_bitwise_class lane) ->
 rf_reference_bank_at(top_environment observed)bank ->
 ref_write_word(top_environment observed)(rf_isa_write_stage(rf_bitwise_class lane))=cycle_bitwise_semantics lane bank instruction.
Proof.
 intros Observe Legal Reset Lane Instruction Match Bank.
 pose proof(rf_bitwise_reference_data_observed memory inputs k observed instruction lane bank Observe Legal Reset Lane Instruction Match Bank)as Data.
 unfold ref_write_word. rewrite(rf_bitwise_write_node lane Lane)Data.
 destruct(observed_joint_register_concrete memory inputs k observed 7750%nat 32%nat Observe Legal load_type_instruction_member)as[word[Size Word]]. rewrite Instruction in Word;inversion Word;subst word.
 pose proof(rf_bitwise_semantics_size bank instruction lane Size(fun index Bound=>proj1(Bank index Bound)))as Width.
 cbn. rewrite<-Width. apply take_size.
Qed.
Theorem rf_reference_decoder_observed memory inputs k observed instruction row :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 VM.find 7750(top_environment observed)=Some(Gval(Fuint 32)instruction) ->
 VM.find 1707(top_environment observed)=Some(Gval(Fuint 1)[::true]) ->(row<48)%coq_nat ->
 VM.find(reference_instruction_guard row)(top_environment observed)=Some(Gval(Fuint 1)[::N.eqb(reference_instruction_code row)(N.land(to_N instruction)(reference_instruction_mask row))]).
Proof.
 intros Observe Legal Instruction Enabled Row.
 destruct(observed_joint_register_concrete memory inputs k observed 7750%nat 32%nat Observe Legal load_type_instruction_member)as[word[Size Word]]. rewrite Instruction in Word;inversion Word;subst word.
 destruct(observed_history memory inputs k observed Observe Legal)as[reset[history[Last[Steps Resets]]]].
 assert(Inst:forall t,(t<=9259)%coq_nat ->VM.find 7750(history t)=Some(Gval(Fuint 32)instruction)).
 { intros t Upper. pose proof(joint_update_register_history_same _ history 9259 7750 32 load_type_instruction_member Steps)as Hold.
 rewrite(Hold t Upper). rewrite<-(Hold 9259%nat ltac:(lia)). rewrite Last;exact Instruction. }
 assert(Enable:forall t,(195<=t)%coq_nat ->(t<=9259)%coq_nat ->VM.find 1707(history t)=Some(Gval(Fuint 1)[::true])).
 { intros t Lower Upper. rewrite(reference_control_stable_1707_history (generated_observation_input inputs k)nil history 9259 reset Resets Steps t 9259%nat ltac:(lia)ltac:(lia)Upper ltac:(lia))Last;exact Enabled. }
 assert(Source:forall t,(200<=t)%coq_nat ->(t<=9259)%coq_nat ->VM.find 1884(history t)=Some(Gval(Fuint 32)instruction)).
 { intros t Lower Upper. exact(memory_reference_instruction_history _ history 9259 195 instruction true Size Steps Inst Enable t Lower Upper). }
 set(h:=fun t:nat=>history(match t with O=>9257%nat|S O=>9258%nat|_=>9259%nat end)).
 assert(HS:forall t,(t<2)%coq_nat ->formal_value_iter(formal_invalid_policy(generated_observation_input inputs k)nil)flat_memories(h t)false(h t)flat_statements=Some(h(S t))).
 { intros[|[|t]] T;[apply Steps;vm_compute;lia|apply Steps;vm_compute;lia|lia]. }
 assert(HI:forall t,(t<=2)%coq_nat ->VM.find 1884(h t)=Some(Gval(Fuint 32)instruction)).
 { intros[|[|t]] T;unfold h;apply Source;vm_compute;lia. }
 rewrite<-Last. exact(reference_instruction_decode_history _ h 2 instruction row Row HS HI 2 ltac:(lia)ltac:(lia)).
Qed.
Lemma rf_reference_effect_guards_ext left right permissions words destination count :
 (forall stage,(stage<count)%coq_nat ->left stage=right stage) ->
 rf_reference_effect left permissions words destination count=rf_reference_effect right permissions words destination count.
Proof.
 induction count as[|count IH];intro Guards;[reflexivity|].
 cbn[rf_reference_effect]. rewrite(Guards count ltac:(lia))(IH ltac:(intros stage Bound;apply Guards;lia));reflexivity.
Qed.
Theorem rf_bitwise_reference_effect_observed memory inputs k observed instruction lane bank :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 VM.find 1(formal_external_inputs(generated_observation_input inputs k))=Some(Gval(Fuint 1)[::false]) ->
 (lane<6)%coq_nat ->VM.find 7750(top_environment observed)=Some(Gval(Fuint 32)instruction) ->
 N.land(to_N instruction)(reference_instruction_mask(rf_bitwise_class lane))=reference_instruction_code(rf_bitwise_class lane) ->
 rf_reference_bank_at(top_environment observed)bank ->
 ref_write_effect(top_environment observed)=RFWrite(to_nat(rf_instruction_rd instruction))(cycle_bitwise_semantics lane bank instruction).
Proof.
 intros Observe Legal Reset Lane Instruction Match Bank.
 pose proof(rf_bitwise_reference_enabled memory inputs k observed instruction lane Observe Legal Reset Lane Instruction Match)as Enabled.
 assert(Row:(rf_bitwise_class lane<37)%coq_nat).
 { do 6(destruct lane as[|lane];[vm_compute;lia|]);lia. }
 assert(Writes:rf_isa_writes(rf_bitwise_class lane)=true).
 { do 6(destruct lane as[|lane];[reflexivity|]);lia. }
 destruct(rf_destination_class_observed memory inputs k observed instruction(rf_bitwise_class lane)Observe Legal Instruction Enabled Row Match)as[DutRd RefRd].
 rewrite Writes in RefRd.
 unfold ref_write_effect. rewrite(ref_write_bit_actual _ _ _ Enabled).
 unfold ref_write_destination. rewrite RefRd.
 rewrite(rf_reference_effect_guards_ext (ref_write_guard(top_environment observed))(rf_write_opcode_bit instruction)).
 2:{ intros stage Stage. destruct(rf_write_decoder_certificate stage Stage)as[Bound Node].
 unfold ref_write_guard. rewrite Node. rewrite(ref_write_bit_actual _ _ _ (rf_reference_decoder_observed memory inputs k observed instruction(rf_write_decoder_index stage)Observe Legal Instruction Enabled Bound)). reflexivity. }
 rewrite(rf_reference_class_write_effect instruction(rf_bitwise_class lane)_ _ _ Row Match Writes).
 assert(Permission:rf_reference_permission_value(rf_isa_write_stage(rf_bitwise_class lane))(ref_write_permission(top_environment observed)(rf_isa_write_stage(rf_bitwise_class lane)))=true).
 { do 6(destruct lane as[|lane];[reflexivity|]);lia. }
 rewrite Permission(rf_bitwise_reference_word_observed memory inputs k observed instruction lane bank Observe Legal Reset Lane Instruction Match Bank). reflexivity.
Qed.
