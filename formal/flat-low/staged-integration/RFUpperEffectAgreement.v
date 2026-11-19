Require Import RFAddReferenceData RFModeInvariant RFUpperPendingInvariant RFUpperReferenceEffect RFUpperSemantics RFZeroDestinationEffect
 RFBitwiseEffectAgreement RFWritebackModeCycle RFAluWritebackObserved RFArchitecturalWriteEffect RFEffectState RFPipelineEnable
 RFScalarControl RFWriteEffect ControlWritebackKill CycleView ReferenceBankCycleInputs ReferenceInstructionDecode
 FormalInstructionResetConstants FormalLocalHistory CoreSocModel LoadPipelineClassification.
From Coq Require Import NArith List Lia PeanoNat.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque generated_modules generated_top.
Lemma rf_upper_decoded_mode instruction auipc :
 N.land(to_N instruction)(reference_instruction_mask(rf_upper_class auipc))=reference_instruction_code(rf_upper_class auipc) ->
 wbkill_low(wbkill_decode 49 instruction)=false /\wbkill_high(wbkill_decode 49 instruction)=false.
Proof.
 intro Match. rewrite(rf_wb_legal_mode instruction(rf_upper_class auipc)(rf_upper_class_bound auipc)Match).
 destruct auipc;split;reflexivity.
Qed.
Lemma cycle_upper_active memory inputs k observed v auipc :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 cycle_view_at(top_environment observed)v ->
 N.land(to_N(cv_commit_instruction v))(reference_instruction_mask(rf_upper_class auipc))=reference_instruction_code(rf_upper_class auipc) ->
 cv_late_bubble v=false.
Proof.
 intros Observe Legal View Match.
 destruct(load_pipeline_late_observed memory inputs k observed Observe Legal)as[bubble[Bubble Nop]].
 rewrite(cva_late_bubble _ _ View)in Bubble. inversion Bubble;subst bubble.
 destruct(cv_late_bubble v)eqn:Late;[|reflexivity].
 specialize(Nop(Logic.eq_refl true)). rewrite(cva_commit_instruction _ _ View)in Nop.
 assert(Instruction:cv_commit_instruction v=instruction_nop)by(inversion Nop;reflexivity).
 rewrite Instruction in Match. exfalso;exact(rf_upper_not_nop auipc Match).
Qed.
Theorem cycle_upper_effect_agreement memory inputs k observed v auipc :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 cycle_reset inputs k false ->cycle_view_at(top_environment observed)v ->
 cycle_writeback_mode v ->cycle_pc_phase v ->cycle_rf_upper_pending v ->
 N.land(to_N(cv_commit_instruction v))(reference_instruction_mask(rf_upper_class auipc))=reference_instruction_code(rf_upper_class auipc) ->
 rf_effect_normalize(cycle_pending_effect v)=rf_effect_normalize(ref_write_effect(top_environment observed)).
Proof.
 intros Observe Legal Reset View Mode Phase Pending Match.
 destruct(Nat.eq_dec(to_nat(rf_instruction_rd(cv_commit_instruction v)))0)as[Zero|Nonzero].
 - exact(cycle_zero_destination_effect_agreement memory inputs k observed v Observe Legal Reset View Zero).
 - assert(NonNop:cv_commit_instruction v<>instruction_nop).
   { intro Nop. apply Nonzero. rewrite Nop;reflexivity. }
   pose proof(cycle_upper_active memory inputs k observed v auipc Observe Legal View Match)as Late.
   assert(PC:cv_commit_pc v=cv_reference_pc v).
   { destruct Phase as[[L P]|[[L P]|[L P]]];[exact P|rewrite Late in L;discriminate|rewrite Late in L;discriminate]. }
   destruct(Mode NonNop)as[Low High].
   destruct(rf_upper_decoded_mode(cv_commit_instruction v)auipc Match)as[DecodedLow DecodedHigh].
   rewrite DecodedLow in Low. rewrite DecodedHigh in High.
   assert(Data:cv_write_data v=cycle_upper_semantics auipc(cv_reference_pc v)(cv_commit_instruction v)).
   { rewrite -(cycle_alu_writeback memory inputs k observed v Observe Legal View Low High).
     rewrite <-PC. exact(Pending auipc Match). }
   rewrite(rf_upper_reference_effect_active memory inputs k observed(cv_commit_instruction v)auipc(cv_reference_pc v)
    Observe Legal(rf_nonzero_reference_active memory inputs k observed(cv_commit_instruction v)Observe Legal Reset(cva_commit_instruction _ _ View)Nonzero)
    (cva_commit_instruction _ _ View)Match(cva_reference_pc_width _ _ View)(cva_reference_pc _ _ View)).
   unfold cycle_pending_effect. rewrite(cycle_destination_observed memory inputs k observed v Observe Legal View).
   change(rf_effect_normalize(if cv_write_enabled v then RFWrite(to_nat(rf_instruction_rd(cv_commit_instruction v)))(cv_write_data v)else RFNoWrite)=
    rf_effect_normalize(if true then RFWrite(to_nat(rf_instruction_rd(cv_commit_instruction v)))(cycle_upper_semantics auipc(cv_reference_pc v)(cv_commit_instruction v))else RFNoWrite)).
   apply rf_scalar_effect_agreement;[|intros;exact Data].
   pose proof(rf_pipeline_isa_write_enable_observed memory inputs k observed(cv_commit_instruction v)(cv_write_enabled v)(rf_upper_class auipc)
    Observe Legal(cva_commit_instruction _ _ View)(cva_write_enabled _ _ View)(rf_upper_class_bound auipc)Match)as Enable.
   rewrite(rf_upper_reference_writes auipc) rf_instruction_nonzero_correct in Enable. exact Enable.
Qed.
