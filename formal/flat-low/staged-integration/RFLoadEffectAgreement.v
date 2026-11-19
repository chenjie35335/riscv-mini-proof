Require Import RFLoadBankInputs RFLoadWritebackObserved RFReferenceSelectedEffect RFModeInvariant RFAddReferenceData RFZeroDestinationEffect RFBitwiseEffectAgreement RFAluWritebackObserved RFArchitecturalWriteEffect RFEffectState RFPipelineEnable RFScalarControl RFWriteEffect RFReferenceWriteEffect CycleView ReferenceBankCycleInputs ReferenceInstructionDecode FormalLocalHistory CoreSocModel MemoryPendingInvariant LoadTypeCorrespondence.
From Coq Require Import NArith List Lia PeanoNat.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
Local Open Scope N_scope.
Theorem cycle_load_effect_agreement memory inputs k observed v lane :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 cycle_reset inputs k false ->cycle_view_at(top_environment observed)v ->
 cycle_memory_pending v ->cycle_writeback_mode v ->(lane<5)%coq_nat ->load_type_is_load(cv_commit_instruction v)lane ->
 rf_effect_normalize(cycle_pending_effect v)=rf_effect_normalize(ref_write_effect(top_environment observed)).
Proof.
 intros Observe Legal Reset View Pending Mode Lane Load.
 destruct(Nat.eq_dec(to_nat(rf_instruction_rd(cv_commit_instruction v)))0)as[Zero|Nonzero].
 - exact(cycle_zero_destination_effect_agreement memory inputs k observed v Observe Legal Reset View Zero).
 - pose proof(rf_nonzero_reference_active memory inputs k observed _ Observe Legal Reset(cva_commit_instruction _ _ View)Nonzero)as Enabled.
   pose proof(cycle_load_writeback_correspondence memory inputs k observed v lane Observe Legal Reset View Pending Mode Lane Load)as Data.
   rewrite <-(rf_load_write_node lane Lane)in Data.
   assert(Permission:rf_reference_permission_value(rf_isa_write_stage(rf_load_class lane))(ref_write_permission(top_environment observed)(rf_isa_write_stage(rf_load_class lane)))=true).
   { pose proof(cycle_load_permission memory inputs k observed v lane Observe Legal Reset View Pending Lane Load)as Perm.
     destruct lane as[|[|[|[|[|lane]]]]];try lia;try reflexivity;
     specialize(Perm(Logic.eq_refl _));
     unfold rf_reference_permission_value;cbn [rf_load_class rf_isa_write_stage rf_reference_write_depth rf_reference_write_row rf_reference_write_rows nth Nat.sub Nat.ltb eqn];
     unfold ref_write_permission;rewrite(ref_write_bit_actual _ _ _ Perm);reflexivity. }
   assert(Word:ref_write_word(top_environment observed)(rf_isa_write_stage(rf_load_class lane))=cv_write_data v).
   { rewrite(ref_write_word_actual _ _ _ _ Data). rewrite <-(cva_write_width _ _ View). apply take_size. }
   rewrite(rf_reference_selected_effect memory inputs k observed(cv_commit_instruction v)(rf_load_class lane)(cv_write_data v)Observe Legal Enabled(cva_commit_instruction _ _ View)(rf_load_class_bound lane Lane)(rf_load_class_match _ lane Lane Load)(rf_load_class_writes lane Lane)Permission Word).
   unfold cycle_pending_effect. rewrite(cycle_destination_observed memory inputs k observed v Observe Legal View).
   change(rf_effect_normalize(if cv_write_enabled v then RFWrite(to_nat(rf_instruction_rd(cv_commit_instruction v)))(cv_write_data v)else RFNoWrite)=
   rf_effect_normalize(if true then RFWrite(to_nat(rf_instruction_rd(cv_commit_instruction v)))(cv_write_data v)else RFNoWrite)).
   apply rf_scalar_effect_agreement;[|intros;reflexivity].
   pose proof(rf_pipeline_isa_write_enable_observed memory inputs k observed(cv_commit_instruction v)(cv_write_enabled v)(rf_load_class lane)Observe Legal(cva_commit_instruction _ _ View)(cva_write_enabled _ _ View)(rf_load_class_bound lane Lane)(rf_load_class_match _ lane Lane Load))as Enable.
   rewrite(rf_load_class_writes lane Lane)rf_instruction_nonzero_correct in Enable. exact Enable.
Qed.
