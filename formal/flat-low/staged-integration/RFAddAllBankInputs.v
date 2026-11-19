Require Import RFNonNopActive FormalInstructionResetConstants RFSingleWriteBankInputs ReferenceBankGuardedObserved ReferenceBankSelectedData ReferenceBankCycleInputs RFAddCycle RFAddReferenceData RFEffectState RFScalarControl RFReferenceWriteEffect RFReferenceNopHistory ReferenceInstructionDecode FormalLocalHistory CoreSocModel.
From Coq Require Import NArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Theorem rf_add_bank_inputs_nonnop memory inputs k observed instruction lane bank :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 VM.find 1(formal_external_inputs(generated_observation_input inputs k))=Some(Gval(Fuint 1)[::false]) ->
 (lane<2)%coq_nat ->VM.find 7750(top_environment observed)=Some(Gval(Fuint 32)instruction) ->
 N.land(to_N instruction)(reference_instruction_mask(rf_add_class lane))=reference_instruction_code(rf_add_class lane) ->
 instruction<>instruction_nop ->rf_reference_bank_at(top_environment observed)bank ->
 ref_bank_guarded_controls(top_environment observed) /\ref_write_selected_data_concrete(top_environment observed) /\
 VM.find 3221(top_environment observed)=Some(Gval(Fuint 5)(ref_write_destination(top_environment observed))).
Proof.
 intros Observe Legal Reset Lane Instruction Match NonNop Bank.
 pose proof(rf_nonnop_reference_active memory inputs k observed instruction Observe Legal Reset Instruction NonNop)as Enabled.
 pose proof(rf_add_reference_data_active memory inputs k observed instruction lane bank Observe Legal Reset Enabled Lane Instruction Match Bank)as Data.
 rewrite<-(rf_add_write_node lane Lane)in Data.
 eapply(rf_single_write_bank_inputs memory inputs k observed instruction(rf_add_class lane)(cycle_add_semantics lane bank instruction));
 [exact Observe|exact Legal|exact Enabled|exact Instruction| |exact Match| |exact Data|apply cycle_add_semantics_size|].
 - do 2(destruct lane as[|lane];[vm_compute;lia|]);lia.
 - do 2(destruct lane as[|lane];[reflexivity|]);lia.
 - intro Depth. do 2(destruct lane as[|lane];[discriminate Depth|]);lia.
Qed.
