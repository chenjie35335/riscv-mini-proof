Require Import RFAddCycle RFAddReferencePorts RFALUArithmeticData ReferenceALUIImmediate RFALUReferenceData ReferenceBankCycleInputs RFEffectState RFScalarControl RFReferenceWriteEffect RFReferenceNopHistory RFWriteEffect RFReadPorts ReferenceInstructionDecode ReferenceLoadSemantics FormalLocalHistory CoreSocModel.
From Coq Require Import NArith List Lia PeanoNat.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Definition cycle_add_semantics lane(bank:rf_bank)instruction :=
 reference_load_address(bank(to_nat(rf_instruction_address false instruction)))
 (rf_add_operand_right lane instruction(bank(to_nat(rf_instruction_address true instruction)))).
Lemma cycle_add_semantics_size lane bank instruction :size(cycle_add_semantics lane bank instruction)=32%nat.
Proof. unfold cycle_add_semantics,reference_load_address. rewrite size_take size_from_N;reflexivity. Qed.
Theorem rf_add_reference_data_active memory inputs k observed instruction lane bank :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 VM.find 1(formal_external_inputs(generated_observation_input inputs k))=Some(Gval(Fuint 1)[::false]) ->
 VM.find 1707(top_environment observed)=Some(Gval(Fuint 1)[::true]) ->
 (lane<2)%coq_nat ->VM.find 7750(top_environment observed)=Some(Gval(Fuint 32)instruction) ->
 N.land(to_N instruction)(reference_instruction_mask(rf_add_class lane))=reference_instruction_code(rf_add_class lane) ->
 rf_reference_bank_at(top_environment observed)bank ->
 VM.find(rf_add_output lane)(top_environment observed)=Some(Gval(Fuint 32)(cycle_add_semantics lane bank instruction)).
Proof.
 intros Observe Legal Reset Enabled Lane Instruction Match Bank.
 pose proof(rf_add_bank_observed false memory inputs k observed instruction lane bank Observe Legal Enabled Lane ltac:(discriminate)Instruction Match Bank)as Left.
 unfold cycle_add_semantics. apply(rf_reference_add_observed memory inputs k observed lane _ _ Observe Legal ltac:(lia)).
 - destruct lane as[|[|lane]];[exact Left|exact Left|lia].
 - destruct lane as[|[|lane]];[| |lia].
   + exact(rf_add_bank_observed true memory inputs k observed instruction 0%nat bank Observe Legal Enabled ltac:(lia)ltac:(reflexivity)Instruction Match Bank).
   + exact(reference_alu_i_immediate_active_observed memory inputs k observed instruction 0%nat Observe Legal Reset Enabled ltac:(lia)Instruction Match).
Qed.
Lemma rf_add_write_node lane :(lane<2)%coq_nat ->rf_reference_write_data(rf_isa_write_stage(rf_add_class lane))=rf_add_output lane.
Proof. intro Lane. do 2(destruct lane as[|lane];[reflexivity|]);lia. Qed.
Theorem rf_add_reference_word_active memory inputs k observed instruction lane bank :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 VM.find 1(formal_external_inputs(generated_observation_input inputs k))=Some(Gval(Fuint 1)[::false]) ->
 VM.find 1707(top_environment observed)=Some(Gval(Fuint 1)[::true]) ->
 (lane<2)%coq_nat ->VM.find 7750(top_environment observed)=Some(Gval(Fuint 32)instruction) ->
 N.land(to_N instruction)(reference_instruction_mask(rf_add_class lane))=reference_instruction_code(rf_add_class lane) ->
 rf_reference_bank_at(top_environment observed)bank ->
 ref_write_word(top_environment observed)(rf_isa_write_stage(rf_add_class lane))=cycle_add_semantics lane bank instruction.
Proof.
 intros Observe Legal Reset Enabled Lane Instruction Match Bank.
 pose proof(rf_add_reference_data_active memory inputs k observed instruction lane bank Observe Legal Reset Enabled Lane Instruction Match Bank)as Data.
 unfold ref_write_word. rewrite(rf_add_write_node lane Lane)Data.
 change(take 32(cycle_add_semantics lane bank instruction)=cycle_add_semantics lane bank instruction).
 rewrite<-(cycle_add_semantics_size lane bank instruction). apply take_size.
Qed.
Theorem rf_add_reference_effect_active memory inputs k observed instruction lane bank :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 VM.find 1(formal_external_inputs(generated_observation_input inputs k))=Some(Gval(Fuint 1)[::false]) ->
 VM.find 1707(top_environment observed)=Some(Gval(Fuint 1)[::true]) ->
 (lane<2)%coq_nat ->VM.find 7750(top_environment observed)=Some(Gval(Fuint 32)instruction) ->
 N.land(to_N instruction)(reference_instruction_mask(rf_add_class lane))=reference_instruction_code(rf_add_class lane) ->
 rf_reference_bank_at(top_environment observed)bank ->
 ref_write_effect(top_environment observed)=RFWrite(to_nat(rf_instruction_rd instruction))(cycle_add_semantics lane bank instruction).
Proof.
 intros Observe Legal Reset Enabled Lane Instruction Match Bank.
 assert(Row:(rf_add_class lane<37)%coq_nat)by(do 2(destruct lane as[|lane];[vm_compute;lia|]);lia).
 assert(Writes:rf_isa_writes(rf_add_class lane)=true)by(do 2(destruct lane as[|lane];[reflexivity|]);lia).
 destruct(rf_destination_class_observed memory inputs k observed instruction(rf_add_class lane)Observe Legal Instruction Enabled Row Match)as[DutRd RefRd].
 rewrite Writes in RefRd. unfold ref_write_effect. rewrite(ref_write_bit_actual _ _ _ Enabled).
 unfold ref_write_destination. rewrite RefRd.
 rewrite(rf_reference_effect_guards_ext (ref_write_guard(top_environment observed))(rf_write_opcode_bit instruction)).
 2:{ intros stage Stage. destruct(rf_write_decoder_certificate stage Stage)as[Bound Node].
 unfold ref_write_guard. rewrite Node. rewrite(ref_write_bit_actual _ _ _ (rf_reference_decoder_observed memory inputs k observed instruction(rf_write_decoder_index stage)Observe Legal Instruction Enabled Bound)). reflexivity. }
 rewrite(rf_reference_class_write_effect instruction(rf_add_class lane)_ _ _ Row Match Writes).
 assert(Permission:rf_reference_permission_value(rf_isa_write_stage(rf_add_class lane))(ref_write_permission(top_environment observed)(rf_isa_write_stage(rf_add_class lane)))=true).
 { do 2(destruct lane as[|lane];[reflexivity|]);lia. }
 rewrite Permission(rf_add_reference_word_active memory inputs k observed instruction lane bank Observe Legal Reset Enabled Lane Instruction Match Bank). reflexivity.
Qed.
Require Import LoadPipelineClassification ReferenceIllegalObserved.
Lemma rf_nonzero_reference_active memory inputs k observed instruction :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 VM.find 1(formal_external_inputs(generated_observation_input inputs k))=Some(Gval(Fuint 1)[::false]) ->
 VM.find 7750(top_environment observed)=Some(Gval(Fuint 32)instruction) ->
 to_nat(rf_instruction_rd instruction)<>0%nat ->
 VM.find 1707(top_environment observed)=Some(Gval(Fuint 1)[::true]).
Proof.
 intros Observe Legal Reset Instruction Nonzero.
 destruct(load_pipeline_late_observed memory inputs k observed Observe Legal)as[bubble[Bubble Nop]].
 destruct bubble.
 - specialize(Nop(Logic.eq_refl true)). rewrite Instruction in Nop. inversion Nop;subst instruction.
   exfalso;apply Nonzero;reflexivity.
 - exact(reference_enable_observed_bubble memory inputs k observed false Observe Legal Reset Bubble).
Qed.
Theorem rf_add_reference_effect_nonzero memory inputs k observed instruction lane bank :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 VM.find 1(formal_external_inputs(generated_observation_input inputs k))=Some(Gval(Fuint 1)[::false]) ->
 (lane<2)%coq_nat ->VM.find 7750(top_environment observed)=Some(Gval(Fuint 32)instruction) ->
 N.land(to_N instruction)(reference_instruction_mask(rf_add_class lane))=reference_instruction_code(rf_add_class lane) ->
 to_nat(rf_instruction_rd instruction)<>0%nat ->rf_reference_bank_at(top_environment observed)bank ->
 ref_write_effect(top_environment observed)=RFWrite(to_nat(rf_instruction_rd instruction))(cycle_add_semantics lane bank instruction).
Proof.
 intros Observe Legal Reset Lane Instruction Match Nonzero Bank.
 exact(rf_add_reference_effect_active memory inputs k observed instruction lane bank Observe Legal Reset
 (rf_nonzero_reference_active memory inputs k observed instruction Observe Legal Reset Instruction Nonzero)Lane Instruction Match Bank).
Qed.
