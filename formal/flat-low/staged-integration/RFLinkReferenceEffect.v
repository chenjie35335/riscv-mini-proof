Require Import RFLinkReferenceData ReferencePCSequentialValues.
Require Import RFAddCycle RFAddReferencePorts RFALUArithmeticData ReferenceALUIImmediate RFALUReferenceData ReferenceBankCycleInputs RFEffectState RFScalarControl RFReferenceWriteEffect RFReferenceNopHistory RFWriteEffect RFReadPorts ReferenceInstructionDecode ReferenceLoadSemantics FormalLocalHistory CoreSocModel.
From Coq Require Import NArith List Lia PeanoNat.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Definition rf_link_class lane :=Nat.add 21 lane.
Definition rf_link_alignment lane :=if Nat.eqb lane 0 then 2966 else 2949.
Lemma rf_link_write_node lane :(lane<2)%coq_nat ->rf_reference_write_data(rf_isa_write_stage(rf_link_class lane))=rf_link_output lane.
Proof. intro Lane. do 2(destruct lane as[|lane];[reflexivity|]);lia. Qed.
Theorem rf_link_reference_word memory inputs k observed lane pc :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 (lane<2)%coq_nat ->size pc=32%nat ->
 VM.find 7331(top_environment observed)=Some(Gval(Fuint 32)pc) ->
 ref_write_word(top_environment observed)(rf_isa_write_stage(rf_link_class lane))=reference_pc_plus_four pc.
Proof.
 intros Observe Legal Lane Size PC. unfold ref_write_word.
 rewrite(rf_link_write_node lane Lane)(rf_link_data_observed memory inputs k observed lane pc Observe Legal Lane Size PC).
 change(take 32(reference_pc_plus_four pc)=reference_pc_plus_four pc).
 rewrite<-(reference_pc_plus_four_size pc). apply take_size.
Qed.
Theorem rf_link_reference_effect_active memory inputs k observed instruction lane pc :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 VM.find 1(formal_external_inputs(generated_observation_input inputs k))=Some(Gval(Fuint 1)[::false]) ->
 VM.find 1707(top_environment observed)=Some(Gval(Fuint 1)[::true]) ->
 (lane<2)%coq_nat ->VM.find 7750(top_environment observed)=Some(Gval(Fuint 32)instruction) ->
 N.land(to_N instruction)(reference_instruction_mask(rf_link_class lane))=reference_instruction_code(rf_link_class lane) ->
 size pc=32%nat ->
 VM.find 7331(top_environment observed)=Some(Gval(Fuint 32)pc) ->
 VM.find(rf_link_alignment lane)(top_environment observed)=Some(Gval(Fuint 1)[::true]) ->
 ref_write_effect(top_environment observed)=RFWrite(to_nat(rf_instruction_rd instruction))(reference_pc_plus_four pc).
Proof.
 intros Observe Legal Reset Enabled Lane Instruction Match Size PC Alignment.
 assert(Row:(rf_link_class lane<37)%coq_nat)by(do 2(destruct lane as[|lane];[vm_compute;lia|]);lia).
 assert(Writes:rf_isa_writes(rf_link_class lane)=true)by(do 2(destruct lane as[|lane];[reflexivity|]);lia).
 destruct(rf_destination_class_observed memory inputs k observed instruction(rf_link_class lane)Observe Legal Instruction Enabled Row Match)as[DutRd RefRd].
 rewrite Writes in RefRd. unfold ref_write_effect. rewrite(ref_write_bit_actual _ _ _ Enabled).
 unfold ref_write_destination. rewrite RefRd.
 rewrite(rf_reference_effect_guards_ext (ref_write_guard(top_environment observed))(rf_write_opcode_bit instruction)).
 2:{ intros stage Stage. destruct(rf_write_decoder_certificate stage Stage)as[Bound Node].
 unfold ref_write_guard. rewrite Node. rewrite(ref_write_bit_actual _ _ _ (rf_reference_decoder_observed memory inputs k observed instruction(rf_write_decoder_index stage)Observe Legal Instruction Enabled Bound)). reflexivity. }
 rewrite(rf_reference_class_write_effect instruction(rf_link_class lane)_ _ _ Row Match Writes).
 assert(Permission:rf_reference_permission_value(rf_isa_write_stage(rf_link_class lane))(ref_write_permission(top_environment observed)(rf_isa_write_stage(rf_link_class lane)))=true).
 { destruct lane as[|[|lane]];[change(ref_write_bit(top_environment observed)2966=true)|change(ref_write_bit(top_environment observed)2949=true)|lia];apply ref_write_bit_actual;exact Alignment. }
 rewrite Permission(rf_link_reference_word memory inputs k observed lane pc Observe Legal Lane Size PC). reflexivity.
Qed.
