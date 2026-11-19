Require Import StoreCycleDataAgreement StoreCheckerStateResult.
Require Import StoreStateResult StoreCycleState StoreCycleAlignment CycleStoreRequestData StoreInstructionCycleUpdate StoreReferenceAlignment ReferenceStoreRequestData ReferenceStoreData MemoryPendingInvariant CycleView RFReadPorts StoreTypeCorrespondence CoreSocModel FormalLocalHistory.
From Coq Require Import NArith Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Theorem cycle_store_checker_agreement memory inputs k observed v lane :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 cycle_reset inputs k false ->cycle_view_at(top_environment observed)v ->cycle_memory_pending v ->
 (lane<3)%coq_nat ->store_type_is_store(cv_commit_instruction v)lane ->
 size(cv_reference_bank v(to_nat(rf_instruction_address true(cv_commit_instruction v))))=32%nat ->
 cycle_store_state(top_environment observed)v lane ->
 VM.find 1481(top_environment observed)=VM.find 1526(top_environment observed).
Proof.
 intros Observe Legal Reset View Pending Lane Store Size State.
 pose proof(cycle_store_reference_aligned memory inputs k observed v lane Observe Legal Reset View Pending Lane Store)as Aligned.
 pose proof(store_checker_state_result memory inputs k observed(cv_commit_instruction v)lane
 (cv_reference_bank v(to_nat(rf_instruction_address false(cv_commit_instruction v))))
 (cv_reference_bank v(to_nat(rf_instruction_address true(cv_commit_instruction v))))
 Observe Legal Lane Size Aligned State)as DUT.
 pose proof(cycle_store_request_data memory inputs k observed v lane Observe Legal Reset View Pending Lane Store)as Reference.
 rewrite DUT Reference. unfold reference_store_request_piece.
 assert(Take:forall (word:bits),take 32(take(reference_store_data_width lane)word)=take(reference_store_data_width lane)word).
 { intro word. destruct lane as[|[|[|lane]]];try lia;
   cbn[reference_store_data_width nth];rewrite -take_min;reflexivity. }
 rewrite Take. reflexivity.
Qed.
Require Import RFReferenceNopHistory ObservedJointRegisterConcrete JointBoundaryRegisters.
Theorem cycle_store_checker_agreement_sized memory inputs k observed v lane :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 cycle_reset inputs k false ->cycle_view_at(top_environment observed)v ->cycle_memory_pending v ->
 (lane<3)%coq_nat ->store_type_is_store(cv_commit_instruction v)lane ->
 cycle_store_state(top_environment observed)v lane ->
 VM.find 1481(top_environment observed)=VM.find 1526(top_environment observed).
Proof.
 intros Observe Legal Reset View Pending Lane Store State.
 eapply cycle_store_checker_agreement;try eassumption.
 assert(IS:size(cv_commit_instruction v)=32%nat).
 { destruct(observed_joint_register_concrete memory inputs k observed 7750 32 Observe Legal
 ltac:(apply(List.nth_error_In joint_boundary_registers 55%nat);vm_compute;reflexivity))as[word[Size Value]].
 rewrite(cva_commit_instruction _ _ View)in Value. inversion Value;subst word;exact Size. }
 pose proof(to_nat_bounded(rf_instruction_address true(cv_commit_instruction v)))as Bound.
 rewrite(rf_instruction_address_size true _ IS)in Bound.
 exact(proj1(cva_reference_bank _ _ View _ (elimT ltP Bound))).
Qed.
