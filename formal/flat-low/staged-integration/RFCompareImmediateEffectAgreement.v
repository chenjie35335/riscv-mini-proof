Require Import RFAddReferenceData RFModeInvariant RFCompareImmediatePendingInvariant RFCompareImmediateData RFCompareImmediateCycle RFZeroDestinationEffect RFBitwiseEffectAgreement RFWritebackModeCycle RFAluWritebackObserved RFArchitecturalWriteEffect RFEffectState RFPipelineEnable RFScalarControl RFWriteEffect ControlWritebackKill CycleView ReferenceBankCycleInputs ReferenceInstructionDecode FormalInstructionResetConstants FormalLocalHistory CoreSocModel.
From Coq Require Import NArith List Lia PeanoNat.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
Local Open Scope N_scope.
Lemma rf_compare_immediate_decoded_mode instruction unsigned :
 N.land(to_N instruction)(reference_instruction_mask (rf_compare_immediate_class unsigned) )=reference_instruction_code (rf_compare_immediate_class unsigned)  ->
 wbkill_low(wbkill_decode 49 instruction)=false /\wbkill_high(wbkill_decode 49 instruction)=false.
Proof.
 intros Match. rewrite(rf_wb_legal_mode instruction (rf_compare_immediate_class unsigned) ltac:(destruct unsigned;vm_compute;lia)Match).
 destruct unsigned;split;reflexivity.
Qed.
Theorem cycle_compare_immediate_effect_agreement memory inputs k observed v unsigned :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 cycle_reset inputs k false ->cycle_view_at(top_environment observed)v ->
 cycle_writeback_mode v ->cycle_rf_compare_immediate_pending v ->
 N.land(to_N(cv_commit_instruction v))(reference_instruction_mask (rf_compare_immediate_class unsigned) )=reference_instruction_code (rf_compare_immediate_class unsigned)  ->
 rf_effect_normalize(cycle_pending_effect v)=rf_effect_normalize(ref_write_effect(top_environment observed)).
Proof.
 intros Observe Legal Reset View Mode Pending Match.
 destruct(Nat.eq_dec(to_nat(rf_instruction_rd(cv_commit_instruction v)))0)as[Zero|Nonzero].
 - exact(cycle_zero_destination_effect_agreement memory inputs k observed v Observe Legal Reset View Zero).
 - assert(NonNop:cv_commit_instruction v<>instruction_nop).
   { intro Nop. apply Nonzero. rewrite Nop;reflexivity. }
   destruct(Mode NonNop)as[Low High].
   destruct(rf_compare_immediate_decoded_mode(cv_commit_instruction v)unsigned Match)as[DecodedLow DecodedHigh].
   rewrite DecodedLow in Low. rewrite DecodedHigh in High.
   assert(Data:cv_write_data v=cycle_compare_immediate_semantics unsigned(cv_reference_bank v)(cv_commit_instruction v)).
   { rewrite -(cycle_alu_writeback memory inputs k observed v Observe Legal View Low High). exact(Pending unsigned Match Nonzero). }
   rewrite(rf_compare_immediate_effect_active memory inputs k observed(cv_commit_instruction v)unsigned(cv_reference_bank v)Observe Legal Reset (rf_nonzero_reference_active memory inputs k observed(cv_commit_instruction v)Observe Legal Reset(cva_commit_instruction _ _ View)Nonzero)(cva_commit_instruction _ _ View)Match(cva_reference_bank _ _ View)).
   unfold cycle_pending_effect. rewrite(cycle_destination_observed memory inputs k observed v Observe Legal View).
   change(rf_effect_normalize(if cv_write_enabled v then RFWrite(to_nat(rf_instruction_rd(cv_commit_instruction v)))(cv_write_data v)else RFNoWrite)=
   rf_effect_normalize(if true then RFWrite(to_nat(rf_instruction_rd(cv_commit_instruction v)))(cycle_compare_immediate_semantics unsigned(cv_reference_bank v)(cv_commit_instruction v))else RFNoWrite)).
   apply rf_scalar_effect_agreement;[|intros;exact Data].
   pose proof(rf_pipeline_isa_write_enable_observed memory inputs k observed(cv_commit_instruction v)(cv_write_enabled v) (rf_compare_immediate_class unsigned) Observe Legal(cva_commit_instruction _ _ View)(cva_write_enabled _ _ View)ltac:(destruct unsigned;vm_compute;lia)Match)as Enable.
   assert(Writes:rf_isa_writes (rf_compare_immediate_class unsigned) =true)by(destruct unsigned;reflexivity).
   rewrite Writes rf_instruction_nonzero_correct in Enable. exact Enable.
Qed.
