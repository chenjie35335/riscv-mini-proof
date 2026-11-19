Require Import MemoryAddressAssertionObserved MemoryAddressSemantics MemoryAddressOutputs MemoryRequestObservedSemantics ReferenceStoreRs1 ReferenceStoreObserved ReferenceStoreParts StoreReferenceAlignment ReferenceLoadSemantics ReferenceRequestSpine StoreCycleDataAgreement StoreCycleState StorePendingInvariant StoreInstructionCycleUpdate CycleView RFReadPorts RFReferenceNopHistory StoreTypeCorrespondence ObservedJointRegisterConcrete JointBoundaryRegisters CoreSocModel FormalLocalHistory.
From Coq Require Import NArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque generated_modules generated_top.
Theorem cycle_store_address_assertion memory inputs k observed v lane :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 cycle_reset inputs k false ->cycle_view_at(top_environment observed)v ->
 cycle_store_pending(top_environment observed)v ->
 (lane<3)%coq_nat ->store_type_is_store(cv_commit_instruction v)lane ->
 generated_assert_m0_4_local(top_environment observed).
Proof.
 intros Observe Legal Reset View Pending Lane Store.
 pose proof(Pending lane Lane Store)as State.
 pose proof(cva_commit_instruction _ _ View)as Instruction.
 pose proof(cva_reference_bank _ _ View)as Bank.
 pose proof(reference_store_rs1_bank_observed memory inputs k observed _ lane _ Observe Legal Reset Lane Instruction Store Bank)as Rs1.
 pose proof(reference_store_immediate_observed memory inputs k observed _ lane Observe Legal Reset Lane Instruction Store)as Imm.
 pose proof(store_reference_enabled_observed memory inputs k observed _ lane Observe Legal Reset Lane Instruction Store)as Enabled.
 pose proof(memory_request_all_guards_observed memory inputs k observed _ true _ _ Observe Legal Instruction Enabled Rs1 Imm)as Guards.
 assert(IS:size(cv_commit_instruction v)=32%nat).
 { destruct(observed_joint_register_concrete memory inputs k observed 7750 32 Observe Legal
 ltac:(apply(List.nth_error_In joint_boundary_registers 55%nat);vm_compute;reflexivity))as[word[Size Value]].
 rewrite Instruction in Value. inversion Value;subst word;exact Size. }
 set left:=cv_reference_bank v(to_nat(rf_instruction_address false(cv_commit_instruction v))).
 assert(LS:size left=32%nat).
 { pose proof(to_nat_bounded(rf_instruction_address false(cv_commit_instruction v)))as Bound.
 rewrite(rf_instruction_address_size false _ IS)in Bound.
 exact(proj1(Bank _ (elimT ltP Bound))). }
 destruct State as[Address Mask Data]. fold left in Address,Rs1.
 eapply(memory_store_address_assertion_observed memory inputs k observed (memory_request_observed_guards (cv_commit_instruction v) true (reference_load_address left(store_s_immediate(cv_commit_instruction v)))) left (store_s_immediate(cv_commit_instruction v)) (store_instruction_address left(cv_commit_instruction v)) Observe Legal LS (store_s_immediate_size _ IS) (store_instruction_address_size _ _) Rs1 Imm Address).
 - intros node Member. apply Guards. cbn[memory_address_guards List.In]in Member;repeat destruct Member as[<-|Member];try contradiction;vm_compute;tauto.
 - apply memory_store_address_semantics with(lane:=lane);assumption.
Qed.
