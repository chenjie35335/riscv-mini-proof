Require Import RFNonNopActive FormalInstructionResetConstants RFLoadBankInputs.
Require Import RFLoadWritebackObserved RFModeInvariant RFSingleWriteBankInputs RFAddReferenceData CycleMemoryAlignment ReferenceByteAlignment ReferenceMemoryAlignment ReferenceBankGuardedObserved ReferenceBankSelectedData ReferenceBankCycleInputs RFEffectState RFScalarControl RFReferenceWriteEffect ReferenceInstructionDecode FormalLocalHistory CoreSocModel CycleView MemoryPendingInvariant LoadTypeCorrespondence ReferenceLoadSemantics.
From Coq Require Import NArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Theorem cycle_load_bank_inputs_all memory inputs k observed v lane :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 cycle_reset inputs k false ->cycle_view_at(top_environment observed)v ->
 cycle_memory_pending v ->cycle_writeback_mode v ->
 (lane<5)%coq_nat ->load_type_is_load(cv_commit_instruction v)lane ->
 ref_bank_guarded_controls(top_environment observed) /\ref_write_selected_data_concrete(top_environment observed) /\
 VM.find 3221(top_environment observed)=Some(Gval(Fuint 5)(ref_write_destination(top_environment observed))).
Proof.
 intros Observe Legal Reset View Pending Mode Lane Load.
 assert(NonNop:cv_commit_instruction v<>instruction_nop).
 { intro Nop;rewrite Nop in Load;exact(load_type_nop_not_load lane Lane Load). }
 pose proof(rf_nonnop_reference_active memory inputs k observed _ Observe Legal Reset(cva_commit_instruction _ _ View)NonNop)as Enabled.
 pose proof(cycle_load_writeback_correspondence memory inputs k observed v lane Observe Legal Reset View Pending Mode Lane Load)as Data.
 rewrite <-(rf_load_write_node lane Lane)in Data.
 apply(rf_single_write_bank_inputs memory inputs k observed(cv_commit_instruction v)(rf_load_class lane)(cv_write_data v)Observe Legal Enabled(cva_commit_instruction _ _ View)(rf_load_class_bound lane Lane)(rf_load_class_match _ lane Lane Load)(rf_load_class_writes lane Lane)Data).
 - exact(cva_write_width _ _ View).
 - intro Depth. pose proof(cycle_load_permission memory inputs k observed v lane Observe Legal Reset View Pending Lane Load Depth)as Permission.
 unfold ref_write_permission. rewrite(ref_write_bit_actual _ _ _ Permission). exact Permission.
Qed.
