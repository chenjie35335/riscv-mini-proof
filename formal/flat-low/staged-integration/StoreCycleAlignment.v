Require Import ReferenceStoreRequestObserved StoreReferenceAlignment StoreMaskCorrespondence MemoryPendingInvariant CycleView MemoryCycleStep RFReadPorts StoreTypeCorrespondence CoreSocModel FormalLocalHistory.
From Coq Require Import NArith Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Lemma store_reference_alignment_bits lane address :
 (lane<3)%coq_nat ->reference_store_request_aligned lane address=true ->
 store_aligned_lane lane (nth false address 0%nat)(nth false address 1%nat).
Proof.
 intros Lane Aligned. destruct lane as[|[|[|lane]]];try lia;
 unfold reference_store_request_aligned in Aligned;
 destruct(nth false address 0%nat), (nth false address 1%nat);try discriminate;cbn[store_aligned_lane];tauto.
Qed.
Theorem cycle_store_reference_aligned memory inputs k observed v lane :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 cycle_reset inputs k false ->cycle_view_at(top_environment observed)v ->cycle_memory_pending v ->
 (lane<3)%coq_nat ->store_type_is_store(cv_commit_instruction v)lane ->
 store_aligned_lane lane
 (nth false(store_reference_address(cv_reference_bank v)(cv_commit_instruction v))0%nat)
 (nth false(store_reference_address(cv_reference_bank v)(cv_commit_instruction v))1%nat).
Proof.
 intros Observe Legal Reset View Pending Lane Store.
 apply store_reference_alignment_bits;[exact Lane|].
 assert(Address:take 2(cv_pending_alu v)=take 2(store_reference_address(cv_reference_bank v)(cv_commit_instruction v))).
 { rewrite(Pending true lane Lane Store). reflexivity. }
 destruct lane as[|[|[|lane]]];try lia;try reflexivity.
 - exact(reference_store_request_alignment_from_address memory inputs k observed(cv_commit_instruction v)false(cv_reference_bank v)(cv_pending_alu v)
 Observe Legal Reset(cva_commit_instruction _ _ View)Store(cva_reference_bank _ _ View)(cva_pending_width _ _ View)(cva_pending_alu _ _ View)Address).
 - exact(reference_store_request_alignment_from_address memory inputs k observed(cv_commit_instruction v)true(cv_reference_bank v)(cv_pending_alu v)
 Observe Legal Reset(cva_commit_instruction _ _ View)Store(cva_reference_bank _ _ View)(cva_pending_width _ _ View)(cva_pending_alu _ _ View)Address).
Qed.
