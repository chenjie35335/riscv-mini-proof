Require Import StoreAssertionObserved StoreAssertionReferenceContext StoreCycleCheckerAgreement StoreCycleDataAgreement StoreCycleState StorePendingInvariant StoreInstructionCycleUpdate StoreRequestMaskCycle StoreRequestMaskValues StoreRequestDataValue StoreOffsetValue MemoryPendingInvariant CycleView RFReadPorts RFReferenceNopHistory StoreTypeCorrespondence ObservedJointRegisterConcrete JointBoundaryRegisters CoreSocModel FormalLocalHistory.
From Coq Require Import NArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Theorem cycle_store_data_assertion memory inputs k observed v lane :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 cycle_reset inputs k false ->cycle_view_at(top_environment observed)v ->
 cycle_memory_pending v ->cycle_store_pending(top_environment observed)v ->
 (lane<3)%coq_nat ->store_type_is_store(cv_commit_instruction v)lane ->
 generated_assert_m0_5_local(top_environment observed).
Proof.
 intros Observe Legal Reset View Memory Pending Lane Store.
 pose proof(Pending lane Lane Store)as State.
 pose proof(cycle_store_checker_agreement_sized memory inputs k observed v lane Observe Legal Reset View Memory Lane Store State)as Agree.
 destruct(store_assertion_reference_context memory inputs k observed(cv_commit_instruction v)lane(cv_reference_bank v)
 Observe Legal Reset Lane(cva_commit_instruction _ _ View)Store(cva_reference_bank _ _ View))as[guards[source[Source Guards]]].
 assert(IS:size(cv_commit_instruction v)=32%nat).
 { destruct(observed_joint_register_concrete memory inputs k observed 7750 32 Observe Legal
 ltac:(apply(List.nth_error_In joint_boundary_registers 55%nat);vm_compute;reflexivity))as[word[Size Value]].
 rewrite(cva_commit_instruction _ _ View)in Value. inversion Value;subst word;exact Size. }
 set left:=cv_reference_bank v(to_nat(rf_instruction_address false(cv_commit_instruction v)) ).
 set right:=cv_reference_bank v(to_nat(rf_instruction_address true(cv_commit_instruction v)) ).
 assert(Size:size right=32%nat).
 { pose proof(to_nat_bounded(rf_instruction_address true(cv_commit_instruction v)))as Bound.
 rewrite(rf_instruction_address_size true _ IS)in Bound.
 exact(proj1(cva_reference_bank _ _ View _ (elimT ltP Bound))). }
 destruct State as[Address Mask Data].
 fold left in Address,Mask,Data. fold right in Data.
 pose proof(store_instruction_address_size left(cv_commit_instruction v))as AddressSize.
 unfold store_instruction_mask in Mask.
 unfold store_instruction_request,store_instruction_offset in Data.
 destruct(store_instruction_address left(cv_commit_instruction v))as[|a0[|a1 tail]]eqn:Bits;try discriminate AddressSize.
 cbn[nth]in Mask,Data.
 pose proof(store_request_mask4_size lane a0 a1 Lane)as MaskSize.
 destruct(store_request_mask4 lane a0 a1)as[|b0[|b1[|b2[|b3 rest]]]]eqn:MaskBits;try discriminate MaskSize.
 destruct rest;[|discriminate MaskSize].
 assert(RequestSize:size(take 32(zeros(to_nat(store_offset_word a0 a1))++right))=32%nat).
 { rewrite -(store_request_word8_low right(store_offset_word a0 a1)Size).
 apply store_request_word8_size;[exact Size|reflexivity]. }
 exact(store_assertion5_observed memory inputs k observed guards source a0 a1 tail b0 b1 b2 b3 _
 Observe Legal RequestSize Address Mask Data Source Guards Agree).
Qed.
