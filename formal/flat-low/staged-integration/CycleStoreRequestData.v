Require Import ReferenceStoreRequestObserved ReferenceStoreRequestData ReferenceStoreData RFReadPorts MemoryPendingInvariant CycleView MemoryCycleStep StoreTypeCorrespondence FormalLocalHistory CoreSocModel.
From Coq Require Import NArith Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Theorem cycle_store_request_data memory inputs k observed v lane :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 cycle_reset inputs k false ->cycle_view_at(top_environment observed)v ->cycle_memory_pending v ->
 (lane<3)%coq_nat ->store_type_is_store(cv_commit_instruction v)lane ->
 VM.find 1526(top_environment observed)=Some(Gval(Fuint 32)
 (reference_store_request_piece(reference_store_data_width lane)
 (cv_reference_bank v(to_nat(rf_instruction_address true(cv_commit_instruction v)))))).
Proof.
 intros Observe Legal Reset View Pending Lane Store.
 eapply(reference_store_request_data_from_address memory inputs k observed(cv_commit_instruction v)lane
 (cv_reference_bank v)(cv_pending_alu v)Observe Legal Reset Lane(cva_commit_instruction _ _ View)Store
 (cva_reference_bank _ _ View)(cva_pending_width _ _ View)(cva_pending_alu _ _ View)).
 rewrite(Pending true lane Lane Store). reflexivity.
Qed.
