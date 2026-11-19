Require Import RFNonwriteEffectAgreement RFBitwiseBankInputs RFALUReferenceData RFScalarControl ReferenceBankCycleInputs ReferenceBankGuardedObserved ReferenceBankSelectedData RFReferenceNopHistory ReferenceInstructionDecode ReferenceIllegalObserved LoadPipelineClassification FormalInstructionResetConstants FormalLocalHistory CoreSocModel.
From Coq Require Import NArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Theorem rf_nonwrite_bank_inputs memory inputs k observed instruction row :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 VM.find 1(formal_external_inputs(generated_observation_input inputs k))=Some(Gval(Fuint 1)[::false]) ->
 VM.find 7750(top_environment observed)=Some(Gval(Fuint 32)instruction) ->
 (row<37)%coq_nat ->N.land(to_N instruction)(reference_instruction_mask row)=reference_instruction_code row ->rf_isa_writes row=false ->
 ref_bank_guarded_controls(top_environment observed) /\ref_write_selected_data_concrete(top_environment observed) /\
 VM.find 3221(top_environment observed)=Some(Gval(Fuint 5)(ref_write_destination(top_environment observed))).
Proof.
 intros Observe Legal Reset Instruction Row Match NoWrite.
 destruct(load_pipeline_late_observed memory inputs k observed Observe Legal)as[bubble[Bubble Nop]].
 assert(Late:bubble=false).
 { destruct bubble;[|reflexivity]. specialize(Nop(Logic.eq_refl true)). rewrite Instruction in Nop.
   assert(Same:instruction=instruction_nop)by(inversion Nop;reflexivity).
   pose proof(rf_no_write_opcode instruction row 0 Row ltac:(lia)Match NoWrite)as FalseOpcode.
   rewrite Same in FalseOpcode;vm_compute in FalseOpcode;discriminate. }
 subst bubble.
 pose proof(reference_enable_observed_bubble memory inputs k observed false Observe Legal Reset Bubble)as Enabled.
 assert(Guards:forall stage,(stage<36)%coq_nat ->ref_write_guard(top_environment observed)stage=false).
 { intros stage Stage. destruct(rf_write_decoder_certificate stage Stage)as[Bound Node].
   unfold ref_write_guard;rewrite Node.
   rewrite(ref_write_bit_actual _ _ _ (rf_reference_decoder_observed memory inputs k observed instruction(rf_write_decoder_index stage)Observe Legal Instruction Enabled Bound)).
   exact(rf_no_write_opcode instruction row stage Row Stage Match NoWrite). }
 split.
 - split;[rewrite(ref_write_bit_actual _ _ _ Enabled);exact Enabled|]. split.
   + exact(rf_reference_guard_values_observed memory inputs k observed instruction Observe Legal Instruction Enabled).
   + intros stage Stage Selected Depth. rewrite(Guards stage Stage)in Selected;discriminate.
 - split.
   + intros stage Stage Selected. rewrite(Guards stage Stage)in Selected;discriminate.
   + destruct(rf_destination_class_observed memory inputs k observed instruction row Observe Legal Instruction Enabled Row Match)as[Dut Reference].
     unfold ref_write_destination;rewrite Reference;reflexivity.
Qed.
