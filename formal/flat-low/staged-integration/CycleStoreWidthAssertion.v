Require Import StoreWidthAssertionWindow StoreActiveWidthReachable StoreActiveWidthCycle MemoryRequestWidth
 ReferenceStoreRequestObserved StoreCycleAlignment StoreMaskCorrespondence StoreReferenceAlignment
 ReferenceStoreRs1 ReferenceStoreObserved ReferenceStoreParts MemoryRequestObservedSemantics ReferenceRequestSpine ReferenceMemoryAlignment
 MemoryPendingInvariant CycleView RFReadPorts StoreTypeCorrespondence CoreSocModel FormalLocalHistory.
From Coq Require Import NArith Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque generated_modules generated_top.
Lemma store_request_width_selected instruction lane address :
 (lane<3)%coq_nat ->store_type_is_store instruction lane ->
 store_aligned_lane lane(nth false address 0%nat)(nth false address 1%nat) ->
 store_width_word lane=from_N 6(reference_request_width true(memory_request_observed_guards instruction true address)).
Proof.
 intros Lane Store Aligned. unfold store_type_is_store in Store.
 unfold reference_request_width,memory_request_observed_guards,memory_reference_instruction.
 rewrite Store.
 do 3(destruct lane as[|lane];[cbn[store_type_lane_code nth N.eqb Pos.eqb Nat.eqb reference_alignment_test store_width_word store_type_lane_kind memory_request_width store_aligned_lane]in *;
 destruct(nth false address 0%nat), (nth false address 1%nat);cbn in *;try solve[intuition discriminate];reflexivity|]);lia.
Qed.
Theorem cycle_store_width_assertion memory inputs k observed v lane :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 cycle_reset inputs k false ->cycle_view_at(top_environment observed)v ->cycle_memory_pending v ->
 (lane<3)%coq_nat ->store_type_is_store(cv_commit_instruction v)lane ->
 generated_assert_m0_6_local(top_environment observed).
Proof.
 intros Observe Legal Reset View Pending Lane Store.
 pose proof(cva_commit_instruction _ _ View)as Instruction.
 pose proof(cva_reference_bank _ _ View)as Bank.
 pose proof(store_reference_enabled_observed memory inputs k observed(cv_commit_instruction v)lane Observe Legal Reset Lane Instruction Store)as Enabled.
 pose proof(reference_store_rs1_bank_observed memory inputs k observed(cv_commit_instruction v)lane(cv_reference_bank v)Observe Legal Reset Lane Instruction Store Bank)as Rs1.
 pose proof(reference_store_immediate_observed memory inputs k observed(cv_commit_instruction v)lane Observe Legal Reset Lane Instruction Store)as Imm.
 pose proof(memory_request_all_guards_observed memory inputs k observed(cv_commit_instruction v)true _ _ Observe Legal Instruction Enabled Rs1 Imm)as Guards.
 apply(memory_write_width_assertion_window memory inputs k observed(store_width_word lane)(memory_request_observed_guards(cv_commit_instruction v)true(store_reference_address(cv_reference_bank v)(cv_commit_instruction v)))Observe Legal).
 - apply size_from_N.
 - exact(store_active_width_observed memory inputs k observed(cv_commit_instruction v)lane Observe Legal Instruction Lane Store).
 - exact Guards.
 - apply(store_request_width_selected _ lane _ Lane Store).
   exact(cycle_store_reference_aligned memory inputs k observed v lane Observe Legal Reset View Pending Lane Store).
Qed.
