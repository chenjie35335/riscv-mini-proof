Require Import MemoryPendingInvariant CycleView MemoryCycleStep StoreReferenceAlignment ReferenceLoadRs1 ReferenceLoadImmediate MemoryLoadAddressWidth RFReadPorts ReferenceLoadSemantics LoadImmediateSemantics FormalLocalHistory CoreSocModel LoadTypeCorrespondence StoreTypeCorrespondence.
From Coq Require Import NArith Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Theorem cycle_store_alignment_from_pending memory inputs k observed v half :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 cycle_reset inputs k false ->cycle_view_at(top_environment observed)v ->cycle_memory_pending v ->
 store_type_is_store(cv_commit_instruction v)(if half then 1%nat else 0%nat) ->
 VM.find(if half then 2723 else 2708)(top_environment observed)=Some(Gval(Fuint 1)[::true]).
Proof.
 intros Observe Legal Reset View Pending Store.
 pose proof(Pending true (if half then 1%nat else 0%nat) ltac:(destruct half;cbn;lia) Store)as Address.
 eapply(store_reference_alignment_from_address memory inputs k observed(cv_commit_instruction v)half
 (cv_reference_bank v)(cv_pending_alu v) Observe Legal Reset(cva_commit_instruction _ _ View)Store
 (cva_reference_bank _ _ View)(cva_pending_width _ _ View)(cva_pending_alu _ _ View)).
 rewrite Address. reflexivity.
Qed.
Theorem cycle_load_width_from_pending memory inputs k observed v lane :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 cycle_reset inputs k false ->cycle_view_at(top_environment observed)v ->cycle_memory_pending v ->
 (lane<5)%coq_nat ->load_type_is_load(cv_commit_instruction v)lane ->
 VM.find 1476(top_environment observed)=VM.find 1521(top_environment observed) /\
 VM.find 1519(top_environment observed)=Some(Gval(Fuint 1)[::true]) /\
 VM.find 1523(top_environment observed)=Some(Gval(Fuint 1)[::false]).
Proof.
 intros Observe Legal Reset View Pending Lane Load.
 pose proof(reference_load_rs1_bank_observed memory inputs k observed(cv_commit_instruction v)lane
 (cv_reference_bank v)Observe Legal Reset Lane(cva_commit_instruction _ _ View)Load(cva_reference_bank _ _ View))as Rs1.
 pose proof(reference_load_immediate_observed memory inputs k observed(cv_commit_instruction v)lane
 Observe Legal Reset Lane(cva_commit_instruction _ _ View)Load)as Immediate.
 pose proof(Pending false lane Lane Load)as Address.
 cbn [cycle_memory_immediate] in Address.
 eapply(memory_load_width_from_actual_address memory inputs k observed(cv_commit_instruction v)lane
 _ _ Observe Legal Reset Lane(cva_commit_instruction _ _ View)Load Rs1 Immediate).
 rewrite <- Address. exact(cva_pending_alu _ _ View).
Qed.
