Require Import RFAddReferenceData RFModeInvariant RFShiftPendingInvariant RFShiftReferenceEffect RFShiftSemanticBank RFShiftCycle RFZeroDestinationEffect RFBitwiseEffectAgreement RFWritebackModeCycle RFAluWritebackObserved RFArchitecturalWriteEffect RFEffectState RFPipelineEnable RFScalarControl RFWriteEffect ControlWritebackKill CycleView ReferenceBankCycleInputs ReferenceInstructionDecode FormalInstructionResetConstants FormalLocalHistory CoreSocModel.
From Coq Require Import NArith List Lia PeanoNat.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
Local Open Scope N_scope.
Lemma rf_shift_decoded_mode instruction immediate lane :(lane<3)%coq_nat ->
 N.land(to_N instruction)(reference_instruction_mask (rf_shift_class immediate lane) )=reference_instruction_code (rf_shift_class immediate lane)  ->
 wbkill_low(wbkill_decode 49 instruction)=false /\wbkill_high(wbkill_decode 49 instruction)=false.
Proof.
 intros Lane Match. rewrite(rf_wb_legal_mode instruction (rf_shift_class immediate lane) (rf_shift_class_bound immediate lane Lane)Match).
 destruct immediate;do 3(destruct lane as[|lane];[split;reflexivity|]);lia.
Qed.
Theorem cycle_shift_effect_agreement memory inputs k observed v immediate lane :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 cycle_reset inputs k false ->cycle_view_at(top_environment observed)v ->
 cycle_writeback_mode v ->cycle_rf_shift_pending v ->(lane<3)%coq_nat ->
 N.land(to_N(cv_commit_instruction v))(reference_instruction_mask (rf_shift_class immediate lane) )=reference_instruction_code (rf_shift_class immediate lane)  ->
 rf_effect_normalize(cycle_pending_effect v)=rf_effect_normalize(ref_write_effect(top_environment observed)).
Proof.
 intros Observe Legal Reset View Mode Pending Lane Match.
 destruct(Nat.eq_dec(to_nat(rf_instruction_rd(cv_commit_instruction v)))0)as[Zero|Nonzero].
 - exact(cycle_zero_destination_effect_agreement memory inputs k observed v Observe Legal Reset View Zero).
 - assert(NonNop:cv_commit_instruction v<>instruction_nop).
   { intro Nop. apply Nonzero. rewrite Nop;reflexivity. }
   destruct(Mode NonNop)as[Low High].
   destruct(rf_shift_decoded_mode(cv_commit_instruction v)immediate lane Lane Match)as[DecodedLow DecodedHigh].
   rewrite DecodedLow in Low. rewrite DecodedHigh in High.
   assert(Data:cv_write_data v=cycle_shift_semantics immediate lane(cv_reference_bank v)(cv_commit_instruction v)).
   { rewrite -(cycle_alu_writeback memory inputs k observed v Observe Legal View Low High). exact(Pending immediate lane Lane Match Nonzero). }
   rewrite(rf_shift_reference_effect_active memory inputs k observed(cv_commit_instruction v)immediate lane(cv_reference_bank v)Observe Legal (rf_nonzero_reference_active memory inputs k observed(cv_commit_instruction v)Observe Legal Reset(cva_commit_instruction _ _ View)Nonzero)(cva_commit_instruction _ _ View)Lane Match(cva_reference_bank _ _ View)).
   unfold cycle_pending_effect. rewrite(cycle_destination_observed memory inputs k observed v Observe Legal View).
   change(rf_effect_normalize(if cv_write_enabled v then RFWrite(to_nat(rf_instruction_rd(cv_commit_instruction v)))(cv_write_data v)else RFNoWrite)=
   rf_effect_normalize(if true then RFWrite(to_nat(rf_instruction_rd(cv_commit_instruction v)))(cycle_shift_semantics immediate lane(cv_reference_bank v)(cv_commit_instruction v))else RFNoWrite)).
   apply rf_scalar_effect_agreement;[|intros;exact Data].
   pose proof(rf_pipeline_isa_write_enable_observed memory inputs k observed(cv_commit_instruction v)(cv_write_enabled v) (rf_shift_class immediate lane) Observe Legal(cva_commit_instruction _ _ View)(cva_write_enabled _ _ View)(rf_shift_class_bound immediate lane Lane)Match)as Enable.
   assert(Writes:rf_isa_writes (rf_shift_class immediate lane) =true)by(exact(rf_shift_writes immediate lane Lane)).
   rewrite Writes rf_instruction_nonzero_correct in Enable. exact Enable.
Qed.
