Require Import RFReferenceWriteEffect RFWriteEffect RFBitwiseEffectAgreement RFAluWritebackObserved RFArchitecturalWriteEffect RFScalarControl CycleView ReferenceBankCycleInputs ReferenceIllegalObserved LoadPipelineClassification FormalLocalHistory CoreSocModel.
From Coq Require Import NArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Theorem cycle_zero_destination_effects memory inputs k observed v :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 cycle_reset inputs k false ->cycle_view_at(top_environment observed)v ->
 to_nat(rf_instruction_rd(cv_commit_instruction v))=0%nat ->
 rf_effect_normalize(cycle_pending_effect v)=RFNoWrite /\
 rf_effect_normalize(ref_write_effect(top_environment observed))=RFNoWrite.
Proof.
 intros Observe Legal Reset View Zero. split.
 - unfold cycle_pending_effect.
   rewrite(cycle_destination_observed memory inputs k observed v Observe Legal View)Zero.
   destruct(cv_write_enabled v);reflexivity.
 - destruct(load_pipeline_late_observed memory inputs k observed Observe Legal)as[bubble[Bubble Nop]].
   pose proof(reference_enable_observed_bubble memory inputs k observed bubble Observe Legal Reset Bubble)as Enabled.
   unfold ref_write_effect. rewrite(ref_write_bit_actual _ _ _ Enabled).
   destruct bubble;[reflexivity|]. cbn[negb].
   destruct(rf_legal_class_row _ (legal_observed_instruction_classified memory inputs k observed(cv_commit_instruction v)Observe Legal Reset(cva_commit_instruction _ _ View)))as[row[Row Match]].
   destruct(rf_destination_class_observed memory inputs k observed(cv_commit_instruction v)row Observe Legal(cva_commit_instruction _ _ View)Enabled Row Match)as[Dut Reference].
   unfold ref_write_destination. rewrite Reference.
   change(rf_effect_normalize(rf_reference_effect(ref_write_guard(top_environment observed))(ref_write_permission(top_environment observed))(ref_write_word(top_environment observed))
   (to_nat(if rf_isa_writes row then rf_instruction_rd(cv_commit_instruction v)else[::false;false;false;false;false]))36)=RFNoWrite).
   destruct(rf_isa_writes row);[rewrite Zero|];apply rf_reference_effect_zero.
Qed.
Theorem cycle_zero_destination_effect_agreement memory inputs k observed v :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 cycle_reset inputs k false ->cycle_view_at(top_environment observed)v ->
 to_nat(rf_instruction_rd(cv_commit_instruction v))=0%nat ->
 rf_effect_normalize(cycle_pending_effect v)=rf_effect_normalize(ref_write_effect(top_environment observed)).
Proof.
 intros Observe Legal Reset View Zero.
 destruct(cycle_zero_destination_effects memory inputs k observed v Observe Legal Reset View Zero)as[Dut Reference].
 rewrite Dut Reference;reflexivity.
Qed.
