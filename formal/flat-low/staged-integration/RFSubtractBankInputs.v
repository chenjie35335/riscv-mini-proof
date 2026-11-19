Require Import RFSingleWriteBankInputs ReferenceBankGuardedObserved ReferenceBankSelectedData ReferenceBankCycleInputs RFAddReferenceData RFSubtractReferenceData RFEffectState RFScalarControl RFReferenceWriteEffect RFReferenceNopHistory ReferenceInstructionDecode FormalLocalHistory CoreSocModel.
From Coq Require Import NArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Theorem rf_subtract_bank_inputs_nonzero memory inputs k observed instruction bank :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 VM.find 1(formal_external_inputs(generated_observation_input inputs k))=Some(Gval(Fuint 1)[::false]) ->
 VM.find 7750(top_environment observed)=Some(Gval(Fuint 32)instruction) ->
 N.land(to_N instruction)(reference_instruction_mask 19%nat )=reference_instruction_code 19%nat  ->
 to_nat(rf_instruction_rd instruction)<>0%nat ->rf_reference_bank_at(top_environment observed)bank ->
 ref_bank_guarded_controls(top_environment observed) /\ref_write_selected_data_concrete(top_environment observed) /\
 VM.find 3221(top_environment observed)=Some(Gval(Fuint 5)(ref_write_destination(top_environment observed))).
Proof.
 intros Observe Legal Reset Instruction Match Nonzero Bank.
 pose proof(rf_nonzero_reference_active memory inputs k observed instruction Observe Legal Reset Instruction Nonzero)as Enabled.
 pose proof(rf_subtract_reference_data_active memory inputs k observed instruction bank Observe Legal Reset Enabled Instruction Match Bank)as Data.
 rewrite<-rf_subtract_write_node in Data.
 eapply(rf_single_write_bank_inputs memory inputs k observed instruction 19%nat (cycle_subtract_semantics bank instruction));
 [exact Observe|exact Legal|exact Enabled|exact Instruction| |exact Match| |exact Data|apply cycle_subtract_semantics_size|].
 - lia.
 - reflexivity.
 - intro Depth;discriminate Depth.
Qed.
