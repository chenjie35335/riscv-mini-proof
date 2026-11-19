Require Import RFBitwiseBankInputs ReferenceBankGuardedObserved ReferenceBankSelectedData ReferenceBankCycleInputs RFALUReferenceData RFEffectState RFScalarControl RFReferenceWriteEffect ReferenceInstructionDecode FormalLocalHistory CoreSocModel.
From Coq Require Import NArith List Lia PeanoNat.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Theorem rf_single_write_bank_inputs memory inputs k observed instruction row word :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 VM.find 1707(top_environment observed)=Some(Gval(Fuint 1)[::true]) ->
 VM.find 7750(top_environment observed)=Some(Gval(Fuint 32)instruction) ->
 (row<37)%coq_nat ->N.land(to_N instruction)(reference_instruction_mask row)=reference_instruction_code row ->rf_isa_writes row=true ->
 VM.find(rf_reference_write_data(rf_isa_write_stage row))(top_environment observed)=Some(Gval(Fuint 32)word) ->size word=32%nat ->
 (rf_reference_write_depth(rf_isa_write_stage row)=2%nat ->
 VM.find(rf_reference_permission_node(rf_isa_write_stage row))(top_environment observed)=Some(Gval(Fuint 1)[::ref_write_permission(top_environment observed)(rf_isa_write_stage row)])) ->
 ref_bank_guarded_controls(top_environment observed) /\ref_write_selected_data_concrete(top_environment observed) /\
 VM.find 3221(top_environment observed)=Some(Gval(Fuint 5)(ref_write_destination(top_environment observed))).
Proof.
 intros Observe Legal Enabled Instruction Row Match Writes Data Size Permission.
 assert(SelectedStage:forall stage,(stage<36)%coq_nat ->ref_write_guard(top_environment observed)stage=true ->stage=rf_isa_write_stage row).
 { intros stage Stage Selected.
 destruct(rf_write_decoder_certificate stage Stage)as[Bound Node].
 unfold ref_write_guard in Selected. rewrite Node in Selected.
 rewrite(ref_write_bit_actual _ _ _ (rf_reference_decoder_observed memory inputs k observed instruction(rf_write_decoder_index stage)Observe Legal Instruction Enabled Bound))in Selected.
 rewrite(rf_reference_decode_onehot instruction row(rf_write_decoder_index stage)Row Bound Match)in Selected.
 rewrite(rf_write_stage_match row stage Row Stage Writes)in Selected. exact(proj1(Nat.eqb_eq _ _)Selected). }
 split.
 - split;[rewrite(ref_write_bit_actual _ _ _ Enabled);exact Enabled|]. split.
   + exact(rf_reference_guard_values_observed memory inputs k observed instruction Observe Legal Instruction Enabled).
   + intros stage Stage Selected Depth. pose proof(SelectedStage stage Stage Selected)as Same. subst stage. exact(Permission Depth).
 - split.
   + intros stage Stage Selected. rewrite(SelectedStage stage Stage Selected).
     exists(Gval(Fuint 32)word). split;[exact Data|]. exact(ref_write_selected_data_word _ _ _ _ Data Size (Logic.eq_refl true)).
   + destruct(rf_destination_class_observed memory inputs k observed instruction row Observe Legal Instruction Enabled Row Match)as[Dut Reference].
     unfold ref_write_destination. rewrite Reference. reflexivity.
Qed.
