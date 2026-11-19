Require Import ReferenceBankSelectedData ReferenceBankCycleInputs RFALUReferenceData RFALUReferenceImmediate RFALUData RFEffectState RFScalarControl RFReferenceWriteEffect RFReferenceNopHistory ReferenceInstructionDecode CycleRFExecute FormalLocalHistory ObservedJointRegisterConcrete LoadTypeCorrespondence CoreSocModel.
From Coq Require Import NArith List Lia PeanoNat.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Theorem rf_bitwise_selected_data_concrete memory inputs k observed instruction lane bank :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 VM.find 1(formal_external_inputs(generated_observation_input inputs k))=Some(Gval(Fuint 1)[::false]) ->
 (lane<6)%coq_nat ->VM.find 7750(top_environment observed)=Some(Gval(Fuint 32)instruction) ->
 N.land(to_N instruction)(reference_instruction_mask(rf_bitwise_class lane))=reference_instruction_code(rf_bitwise_class lane) ->
 rf_reference_bank_at(top_environment observed)bank ->
 ref_write_selected_data_concrete(top_environment observed).
Proof.
 intros Observe Legal Reset Lane Instruction Match Bank stage Stage Selected.
 pose proof(rf_bitwise_reference_enabled memory inputs k observed instruction lane Observe Legal Reset Lane Instruction Match)as Enabled.
 assert(Row:(rf_bitwise_class lane<37)%coq_nat)by(do 6(destruct lane as[|lane];[vm_compute;lia|]);lia).
 assert(Writes:rf_isa_writes(rf_bitwise_class lane)=true)by(do 6(destruct lane as[|lane];[reflexivity|]);lia).
 destruct(rf_write_decoder_certificate stage Stage)as[Bound Node].
 unfold ref_write_guard in Selected. rewrite Node in Selected.
 rewrite(ref_write_bit_actual _ _ _ (rf_reference_decoder_observed memory inputs k observed instruction(rf_write_decoder_index stage)Observe Legal Instruction Enabled Bound))in Selected.
 rewrite(rf_reference_decode_onehot instruction(rf_bitwise_class lane)(rf_write_decoder_index stage)Row Bound Match)in Selected.
 rewrite(rf_write_stage_match(rf_bitwise_class lane)stage Row Stage Writes)in Selected.
 apply Nat.eqb_eq in Selected. subst stage.
 pose proof(rf_bitwise_reference_data_observed memory inputs k observed instruction lane bank Observe Legal Reset Lane Instruction Match Bank)as Value.
 rewrite<-(rf_bitwise_write_node lane Lane)in Value.
 exists(Gval(Fuint 32)(cycle_bitwise_semantics lane bank instruction)). split;[exact Value|].
 apply(ref_write_selected_data_word _ _ _ _ Value);[|reflexivity].
 destruct(observed_joint_register_concrete memory inputs k observed 7750%nat 32%nat Observe Legal load_type_instruction_member)as[word[Size Word]].
 rewrite Instruction in Word;inversion Word;subst word.
 exact(rf_bitwise_semantics_size bank instruction lane Size(fun index Bound=>proj1(Bank index Bound))).
Qed.
