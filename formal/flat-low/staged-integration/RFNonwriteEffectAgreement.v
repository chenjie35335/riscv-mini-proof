Require Import RFWriteEffect RFBitwiseEffectAgreement RFALUReferenceData RFAluWritebackObserved RFArchitecturalWriteEffect RFEffectState RFPipelineEnable RFScalarControl CycleView ReferenceBankCycleInputs ReferenceInstructionDecode ReferenceIllegalObserved LoadPipelineClassification FormalLocalHistory CoreSocModel.
From Coq Require Import NArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Theorem reference_nonwrite_effect_observed memory inputs k observed instruction row :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 cycle_reset inputs k false ->VM.find 7750(top_environment observed)=Some(Gval(Fuint 32)instruction) ->
 (row<37)%coq_nat ->N.land(to_N instruction)(reference_instruction_mask row)=reference_instruction_code row ->
 rf_isa_writes row=false ->ref_write_effect(top_environment observed)=RFNoWrite.
Proof.
 intros Observe Legal Reset Instruction Row Match NoWrite.
 destruct(load_pipeline_late_observed memory inputs k observed Observe Legal)as[bubble[Bubble Nop]].
 pose proof(reference_enable_observed_bubble memory inputs k observed bubble Observe Legal Reset Bubble)as Enabled.
 unfold ref_write_effect. rewrite(ref_write_bit_actual _ _ _ Enabled).
 destruct bubble;[reflexivity|]. cbn[negb].
 apply rf_reference_effect_disabled. intros stage Stage.
 destruct(rf_write_decoder_certificate stage Stage)as[Bound Node].
 unfold ref_write_guard. rewrite Node.
 rewrite(ref_write_bit_actual _ _ _ (rf_reference_decoder_observed memory inputs k observed instruction(rf_write_decoder_index stage)Observe Legal Instruction Enabled Bound)).
 exact(rf_no_write_opcode instruction row stage Row Stage Match NoWrite).
Qed.
Theorem cycle_nonwrite_effect_agreement memory inputs k observed v row :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 cycle_reset inputs k false ->cycle_view_at(top_environment observed)v ->
 (row<37)%coq_nat ->N.land(to_N(cv_commit_instruction v))(reference_instruction_mask row)=reference_instruction_code row ->
 rf_isa_writes row=false ->
 rf_effect_normalize(cycle_pending_effect v)=rf_effect_normalize(ref_write_effect(top_environment observed)).
Proof.
 intros Observe Legal Reset View Row Match NoWrite.
 rewrite(reference_nonwrite_effect_observed memory inputs k observed(cv_commit_instruction v)row Observe Legal Reset(cva_commit_instruction _ _ View)Row Match NoWrite).
 unfold cycle_pending_effect.
 rewrite(cycle_destination_observed memory inputs k observed v Observe Legal View).
 change(rf_effect_normalize(if cv_write_enabled v then RFWrite(to_nat(rf_instruction_rd(cv_commit_instruction v)))(cv_write_data v)else RFNoWrite)=
 rf_effect_normalize(if false then RFWrite(to_nat(rf_instruction_rd(cv_commit_instruction v)))(cv_write_data v)else RFNoWrite)).
 apply rf_scalar_effect_agreement;[|intros;reflexivity].
 pose proof(rf_pipeline_isa_write_enable_observed memory inputs k observed(cv_commit_instruction v)(cv_write_enabled v)row Observe Legal(cva_commit_instruction _ _ View)(cva_write_enabled _ _ View)Row Match)as Enable.
 rewrite NoWrite rf_instruction_nonzero_correct in Enable. exact Enable.
Qed.
