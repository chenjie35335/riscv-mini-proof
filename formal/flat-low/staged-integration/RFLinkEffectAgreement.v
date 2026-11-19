Require Import ReferencePCSequentialValues JALRPendingAlignment JALRAddressCycle.
Require Import RFLinkReferenceEffect RFPCWriteback RFModeInvariant RFZeroDestinationEffect RFBitwiseEffectAgreement RFWritebackModeCycle RFAluWritebackObserved RFArchitecturalWriteEffect RFEffectState RFPipelineEnable RFScalarControl RFWriteEffect ControlWritebackKill CycleView ReferenceBankCycleInputs ReferenceInstructionDecode FormalInstructionResetConstants FormalLocalHistory CoreSocModel RFAddReferenceData LoadPipelineClassification CycleJALAlignment JALRTakenInvariant PCRelativePendingInvariant CycleRedirectDecision.
From Coq Require Import NArith List Lia PeanoNat.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Lemma rf_link_decoded_mode instruction lane :(lane<2)%coq_nat ->
 N.land(to_N instruction)(reference_instruction_mask(rf_link_class lane))=reference_instruction_code(rf_link_class lane) ->
 wbkill_low(wbkill_decode 49 instruction)=false /\wbkill_high(wbkill_decode 49 instruction)=true.
Proof.
 intros Lane Match. rewrite(rf_wb_legal_mode instruction(rf_link_class lane)ltac:(unfold rf_link_class;lia)Match).
 do 2(destruct lane as[|lane];[split;reflexivity|]);lia.
Qed.
Lemma cycle_link_active memory inputs k observed v lane :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 cycle_view_at(top_environment observed)v ->(lane<2)%coq_nat ->
 N.land(to_N(cv_commit_instruction v))(reference_instruction_mask(rf_link_class lane))=reference_instruction_code(rf_link_class lane) ->
 cv_late_bubble v=false.
Proof.
 intros Observe Legal View Lane Match.
 destruct(load_pipeline_late_observed memory inputs k observed Observe Legal)as[bubble[Bubble Nop]].
 rewrite(cva_late_bubble _ _ View)in Bubble. inversion Bubble;subst bubble.
 destruct(cv_late_bubble v)eqn:Late;[|reflexivity].
 specialize(Nop(Logic.eq_refl true)). rewrite(cva_commit_instruction _ _ View)in Nop.
 assert(Instruction:cv_commit_instruction v=instruction_nop)by(inversion Nop;reflexivity).
 rewrite Instruction in Match. do 2(destruct lane as[|lane];[vm_compute in Match;discriminate|]);lia.
Qed.
Theorem cycle_link_effect_with_alignment memory inputs k observed v lane :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 cycle_reset inputs k false ->cycle_view_at(top_environment observed)v ->
 cycle_writeback_mode v ->cycle_pc_phase v ->(lane<2)%coq_nat ->
 N.land(to_N(cv_commit_instruction v))(reference_instruction_mask(rf_link_class lane))=reference_instruction_code(rf_link_class lane) ->
 VM.find(rf_link_alignment lane)(top_environment observed)=Some(Gval(Fuint 1)[::true]) ->
 rf_effect_normalize(cycle_pending_effect v)=rf_effect_normalize(ref_write_effect(top_environment observed)).
Proof.
 intros Observe Legal Reset View Mode Phase Lane Match Alignment.
 destruct(Nat.eq_dec(to_nat(rf_instruction_rd(cv_commit_instruction v)))0)as[Zero|Nonzero].
 - exact(cycle_zero_destination_effect_agreement memory inputs k observed v Observe Legal Reset View Zero).
 - assert(NonNop:cv_commit_instruction v<>instruction_nop).
   { intro Nop. apply Nonzero. rewrite Nop;reflexivity. }
   pose proof(cycle_link_active memory inputs k observed v lane Observe Legal View Lane Match)as Late.
   assert(PC:cv_commit_pc v=cv_reference_pc v).
   { destruct Phase as[[L P]|[[L P]|[L P]]];[exact P|rewrite Late in L;discriminate|rewrite Late in L;discriminate]. }
   destruct(Mode NonNop)as[Low High].
   destruct(rf_link_decoded_mode(cv_commit_instruction v)lane Lane Match)as[DecodedLow DecodedHigh].
   rewrite DecodedLow in Low. rewrite DecodedHigh in High.
   pose proof(cva_write_select _ _ View)as Select. rewrite Low High in Select.
   pose proof(rf_pc_writeback_observed memory inputs k observed(cv_commit_pc v)Observe Legal Select(cva_commit_pc _ _ View))as Output.
   rewrite PC(cva_write_data _ _ View)in Output.
   assert(Data:cv_write_data v=reference_pc_plus_four(cv_reference_pc v)).
   { exact(f_equal(fun value=>match value with Some(Gval _ word)=>word|_=>[::]end)Output). }
   pose proof(rf_nonzero_reference_active memory inputs k observed(cv_commit_instruction v)Observe Legal Reset(cva_commit_instruction _ _ View)Nonzero)as Enabled.
   rewrite(rf_link_reference_effect_active memory inputs k observed(cv_commit_instruction v)lane(cv_reference_pc v)Observe Legal Reset Enabled Lane(cva_commit_instruction _ _ View)Match(cva_reference_pc_width _ _ View)(cva_reference_pc _ _ View)Alignment).
   unfold cycle_pending_effect. rewrite(cycle_destination_observed memory inputs k observed v Observe Legal View).
   change(rf_effect_normalize(if cv_write_enabled v then RFWrite(to_nat(rf_instruction_rd(cv_commit_instruction v)))(cv_write_data v)else RFNoWrite)=
   rf_effect_normalize(if true then RFWrite(to_nat(rf_instruction_rd(cv_commit_instruction v)))(reference_pc_plus_four(cv_reference_pc v))else RFNoWrite)).
   apply rf_scalar_effect_agreement;[|intros;exact Data].
   pose proof(rf_pipeline_isa_write_enable_observed memory inputs k observed(cv_commit_instruction v)(cv_write_enabled v)(rf_link_class lane)Observe Legal(cva_commit_instruction _ _ View)(cva_write_enabled _ _ View)ltac:(unfold rf_link_class;lia)Match)as Enable.
   assert(Writes:rf_isa_writes(rf_link_class lane)=true)by(do 2(destruct lane as[|lane];[reflexivity|]);lia).
   rewrite Writes rf_instruction_nonzero_correct in Enable. exact Enable.
Qed.
Theorem cycle_link_effect_agreement memory inputs k observed v lane csr :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 cycle_reset inputs k false ->cycle_view_at(top_environment observed)v ->
 cycle_writeback_mode v ->cycle_pc_aligned v ->cycle_pc_relative_pending v ->cycle_redirect_decision v ->
 cycle_jalr_pending v ->cycle_jalr_taken v ->(lane<2)%coq_nat ->
 N.land(to_N(cv_commit_instruction v))(reference_instruction_mask(rf_link_class lane))=reference_instruction_code(rf_link_class lane) ->
 VM.find 7332(top_environment observed)=Some(Gval(Fuint 32)csr) ->size csr=32%nat ->
 rf_effect_normalize(cycle_pending_effect v)=rf_effect_normalize(ref_write_effect(top_environment observed)).
Proof.
 intros Observe Legal Reset View Mode PC Pending Decision JPending JTaken Lane Match Csr CsrSize.
 apply(cycle_link_effect_with_alignment memory inputs k observed v lane Observe Legal Reset View Mode(proj2 PC)Lane Match).
 destruct lane as[|[|lane]];[| |lia].
 - exact(cycle_jal_alignment_guard memory inputs k observed v csr Observe Legal Reset View Match
 (cycle_link_active memory inputs k observed v 0%nat Observe Legal View ltac:(lia)Match)PC Pending Decision Csr CsrSize).
 - exact(cycle_jalr_alignment_from_invariants memory inputs k observed v csr Observe Legal Reset View JPending JTaken Match Csr CsrSize).
Qed.
