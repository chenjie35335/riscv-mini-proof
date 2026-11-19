Require Import RFLinkReferenceEffect RFLinkReferenceData RFLinkEffectAgreement RFSingleWriteBankInputs RFScalarControl RFReferenceWriteEffect ReferenceBankGuardedObserved ReferenceBankSelectedData ReferenceBankCycleInputs ReferencePCSequentialValues ReferenceIllegalObserved CycleView FormalLocalHistory CoreSocModel ReferenceInstructionDecode.
From Coq Require Import NArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Theorem cycle_link_bank_inputs memory inputs k observed v lane :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 cycle_reset inputs k false ->cycle_view_at(top_environment observed)v ->(lane<2)%coq_nat ->
 N.land(to_N(cv_commit_instruction v))(reference_instruction_mask(rf_link_class lane))=reference_instruction_code(rf_link_class lane) ->
 VM.find(rf_link_alignment lane)(top_environment observed)=Some(Gval(Fuint 1)[::true]) ->
 ref_bank_guarded_controls(top_environment observed) /\ref_write_selected_data_concrete(top_environment observed) /\
 VM.find 3221(top_environment observed)=Some(Gval(Fuint 5)(ref_write_destination(top_environment observed))).
Proof.
 intros Observe Legal Reset View Lane Match Alignment.
 pose proof(cycle_link_active memory inputs k observed v lane Observe Legal View Lane Match)as Late.
 pose proof(cva_late_bubble _ _ View)as Bubble;rewrite Late in Bubble.
 pose proof(reference_enable_observed_bubble memory inputs k observed false Observe Legal Reset Bubble)as Enabled.
 pose proof(rf_link_data_observed memory inputs k observed lane(cv_reference_pc v)Observe Legal Lane(cva_reference_pc_width _ _ View)(cva_reference_pc _ _ View))as Data.
 rewrite<-(rf_link_write_node lane Lane)in Data.
 apply(rf_single_write_bank_inputs memory inputs k observed(cv_commit_instruction v)(rf_link_class lane)(reference_pc_plus_four(cv_reference_pc v)) Observe Legal Enabled(cva_commit_instruction _ _ View)ltac:(unfold rf_link_class;lia)Match).
 - do 2(destruct lane as[|lane];[reflexivity|]);lia.
 - exact Data.
 - apply reference_pc_plus_four_size.
 - intro Depth. destruct lane as[|[|lane]];[change(VM.find 2966(top_environment observed)=Some(Gval(Fuint 1)[::ref_write_bit(top_environment observed)2966]))|change(VM.find 2949(top_environment observed)=Some(Gval(Fuint 1)[::ref_write_bit(top_environment observed)2949]))|lia];rewrite(ref_write_bit_actual _ _ _ Alignment);exact Alignment.
Qed.
