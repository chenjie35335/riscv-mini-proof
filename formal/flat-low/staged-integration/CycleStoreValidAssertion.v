Require Import ComparisonNodes.
Require Import CoreSocModel CycleView MemoryPendingInvariant MemoryCycleStep MemoryWriteValidAssertionWindow StoreActiveReachable ReferenceStoreRequestObserved ReferenceStoreRs1 ReferenceStoreObserved ReferenceStoreParts StoreReferenceAlignment MemoryRequestObservedSemantics ReferenceRequestSpine MemoryRequestCorrespondence ReferenceLoadSemantics ReferenceMemoryAlignment StoreTypeCorrespondence FormalLocalHistory.
From Coq Require Import NArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque generated_modules generated_top flat_statements flat_memories.
Lemma reference_store_valid_selected instruction lane address :
 (lane<3)%coq_nat ->store_type_is_store instruction lane ->reference_store_request_aligned lane address=true ->
 reference_request_valid true(memory_request_observed_guards instruction true address)=true.
Proof.
 intros Lane Store Aligned. unfold store_type_is_store in Store.
 unfold reference_request_valid,memory_request_observed_guards,memory_reference_instruction.
 rewrite Store. do 3(destruct lane as[|lane];[cbn[store_type_lane_code nth N.eqb Pos.eqb Nat.eqb orb reference_alignment_test reference_store_request_aligned]in *;rewrite ?Aligned;reflexivity|]). lia.
Qed.
Theorem cycle_store_valid_assertion memory inputs k observed v lane :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 cycle_reset inputs k false ->cycle_view_at(top_environment observed)v ->cycle_memory_pending v ->
 (lane<3)%coq_nat ->store_type_is_store(cv_commit_instruction v)lane ->generated_assert_m0_3_local(top_environment observed).
Proof.
 intros Observe Legal Reset View Pending Lane Store.
 pose proof(store_reference_enabled_observed memory inputs k observed(cv_commit_instruction v)lane Observe Legal Reset Lane(cva_commit_instruction _ _ View)Store)as Enabled.
 pose proof(reference_store_rs1_bank_observed memory inputs k observed(cv_commit_instruction v)lane(cv_reference_bank v)Observe Legal Reset Lane(cva_commit_instruction _ _ View)Store(cva_reference_bank _ _ View))as Rs1.
 pose proof(reference_store_immediate_observed memory inputs k observed(cv_commit_instruction v)lane Observe Legal Reset Lane(cva_commit_instruction _ _ View)Store)as Imm.
 pose proof(memory_request_all_guards_observed memory inputs k observed(cv_commit_instruction v)true _ _ Observe Legal(cva_commit_instruction _ _ View)Enabled Rs1 Imm)as Guards.
 assert(Aligned:reference_store_request_aligned lane(store_reference_address(cv_reference_bank v)(cv_commit_instruction v))=true).
 { assert(Address:take 2(cv_pending_alu v)=take 2(store_reference_address(cv_reference_bank v)(cv_commit_instruction v)))by(rewrite(Pending true lane Lane Store);reflexivity).
   destruct lane as[|[|[|lane]]];try lia;try reflexivity.
   - exact(reference_store_request_alignment_from_address memory inputs k observed(cv_commit_instruction v)false(cv_reference_bank v)(cv_pending_alu v)Observe Legal Reset(cva_commit_instruction _ _ View)Store(cva_reference_bank _ _ View)(cva_pending_width _ _ View)(cva_pending_alu _ _ View)Address).
   - exact(reference_store_request_alignment_from_address memory inputs k observed(cv_commit_instruction v)true(cv_reference_bank v)(cv_pending_alu v)Observe Legal Reset(cva_commit_instruction _ _ View)Store(cva_reference_bank _ _ View)(cva_pending_width _ _ View)(cva_pending_alu _ _ View)Address). }
 destruct(reference_request_observed memory inputs k observed _ true Observe Legal Guards)as[Ref Width].
 rewrite(reference_store_valid_selected _ lane _ Lane Store Aligned)in Ref.
 apply(memory_write_valid_assertion_window memory inputs k observed true _ Observe Legal Reset (store_active_write_valid_observed memory inputs k observed _ lane Observe Legal(cva_commit_instruction _ _ View)Lane Store)Guards).
 rewrite Ref(store_active_write_port_observed memory inputs k observed _ lane Observe Legal Reset(cva_commit_instruction _ _ View)Lane Store);reflexivity.
Qed.
