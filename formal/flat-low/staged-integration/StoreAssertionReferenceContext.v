Require Import ReferenceStoreRequestObserved ReferenceStoreRequestData ReferenceStoreRs2 ReferenceStoreRs1 ReferenceStoreObserved ReferenceStoreParts StoreReferenceAlignment MemoryRequestObservedSemantics ReferenceRequestSpine RFReadPorts RFReferenceNopHistory StoreTypeCorrespondence CoreSocModel FormalLocalHistory.
From Coq Require Import NArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Theorem store_assertion_reference_context memory inputs k observed instruction lane bank :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 VM.find 1(formal_external_inputs(generated_observation_input inputs k))=Some(Gval(Fuint 1)[::false]) ->
 (lane<3)%coq_nat ->VM.find 7750(top_environment observed)=Some(Gval(Fuint 32)instruction) ->store_type_is_store instruction lane ->
 rf_reference_bank_at(top_environment observed)bank ->
 exists guards source,
 VM.find 2804(top_environment observed)=Some(Gval(Fuint 32)source) /\
 (forall node,List.In node reference_store_request_data_guards ->VM.find node(top_environment observed)=Some(Gval(Fuint 1)[::guards node])).
Proof.
 intros Observe Legal Reset Lane Instruction Store Bank.
 pose proof(reference_store_rs2_bank_observed memory inputs k observed instruction lane bank Observe Legal Reset Lane Instruction Store Bank)as Data.
 pose proof(store_reference_enabled_observed memory inputs k observed instruction lane Observe Legal Reset Lane Instruction Store)as Enabled.
 pose proof(reference_store_rs1_bank_observed memory inputs k observed instruction lane bank Observe Legal Reset Lane Instruction Store Bank)as Rs1.
 pose proof(reference_store_immediate_observed memory inputs k observed instruction lane Observe Legal Reset Lane Instruction Store)as Imm.
 pose proof(memory_request_all_guards_observed memory inputs k observed instruction true _ _ Observe Legal Instruction Enabled Rs1 Imm)as Guards.
 exists(memory_request_observed_guards instruction true(store_reference_address bank instruction)),(bank(to_nat(rf_instruction_address true instruction))).
 split;[exact Data|].
 intros node Member. apply Guards.
 cbn[reference_store_request_data_guards List.In]in Member.
 repeat destruct Member as[<-|Member];try contradiction;vm_compute;tauto.
Qed.
