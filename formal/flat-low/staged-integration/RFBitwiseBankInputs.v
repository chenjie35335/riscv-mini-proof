Require Import ReferenceBankGuardedObserved ReferenceBankSelectedData ReferenceBankCycleInputs RFBitwiseSelectedData RFALUReferenceData RFALUReferenceImmediate RFALUData RFEffectState RFScalarControl RFReferenceWriteEffect RFReferenceNopHistory ReferenceInstructionDecode FormalLocalHistory CoreSocModel.
From Coq Require Import NArith List Lia PeanoNat.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Theorem rf_reference_guard_values_observed memory inputs k observed instruction :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 VM.find 7750(top_environment observed)=Some(Gval(Fuint 32)instruction) ->
 VM.find 1707(top_environment observed)=Some(Gval(Fuint 1)[::true]) ->
 forall stage,(stage<36)%coq_nat ->
 VM.find(rf_reference_chain_guard stage)(top_environment observed)=Some(Gval(Fuint 1)[::ref_write_guard(top_environment observed)stage]).
Proof.
 intros Observe Legal Instruction Enabled stage Stage.
 destruct(rf_write_decoder_certificate stage Stage)as[Bound Node].
 pose proof(rf_reference_decoder_observed memory inputs k observed instruction(rf_write_decoder_index stage)Observe Legal Instruction Enabled Bound)as Value.
 unfold ref_write_guard. rewrite Node(ref_write_bit_actual _ _ _ Value). exact Value.
Qed.
Theorem rf_bitwise_bank_inputs memory inputs k observed instruction lane bank :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 VM.find 1(formal_external_inputs(generated_observation_input inputs k))=Some(Gval(Fuint 1)[::false]) ->
 (lane<6)%coq_nat ->VM.find 7750(top_environment observed)=Some(Gval(Fuint 32)instruction) ->
 N.land(to_N instruction)(reference_instruction_mask(rf_bitwise_class lane))=reference_instruction_code(rf_bitwise_class lane) ->
 rf_reference_bank_at(top_environment observed)bank ->
 ref_bank_guarded_controls(top_environment observed) /\
 ref_write_selected_data_concrete(top_environment observed) /\
 VM.find 3221(top_environment observed)=Some(Gval(Fuint 5)(ref_write_destination(top_environment observed))).
Proof.
 intros Observe Legal Reset Lane Instruction Match Bank.
 pose proof(rf_bitwise_reference_enabled memory inputs k observed instruction lane Observe Legal Reset Lane Instruction Match)as Enabled.
 assert(Row:(rf_bitwise_class lane<37)%coq_nat)by(do 6(destruct lane as[|lane];[vm_compute;lia|]);lia).
 assert(Writes:rf_isa_writes(rf_bitwise_class lane)=true)by(do 6(destruct lane as[|lane];[reflexivity|]);lia).
 split.
 - split;[rewrite(ref_write_bit_actual _ _ _ Enabled);exact Enabled|]. split.
   + exact(rf_reference_guard_values_observed memory inputs k observed instruction Observe Legal Instruction Enabled).
   + intros stage Stage Selected Depth.
     destruct(rf_write_decoder_certificate stage Stage)as[Bound Node].
     unfold ref_write_guard in Selected. rewrite Node in Selected.
     rewrite(ref_write_bit_actual _ _ _ (rf_reference_decoder_observed memory inputs k observed instruction(rf_write_decoder_index stage)Observe Legal Instruction Enabled Bound))in Selected.
     rewrite(rf_reference_decode_onehot instruction(rf_bitwise_class lane)(rf_write_decoder_index stage)Row Bound Match)in Selected.
     rewrite(rf_write_stage_match(rf_bitwise_class lane)stage Row Stage Writes)in Selected.
     apply Nat.eqb_eq in Selected;subst stage.
     do 6(destruct lane as[|lane];[discriminate Depth|]);lia.
 - split;[exact(rf_bitwise_selected_data_concrete memory inputs k observed instruction lane bank Observe Legal Reset Lane Instruction Match Bank)|].
   destruct(rf_destination_class_observed memory inputs k observed instruction(rf_bitwise_class lane)Observe Legal Instruction Enabled Row Match)as[Dut Reference].
   unfold ref_write_destination. rewrite Reference. reflexivity.
Qed.
