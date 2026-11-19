Require Import RFUpperReferenceEffect RFUpperReferenceData RFUpperSemantics RFSingleWriteBankInputs ReferenceBankGuardedObserved ReferenceBankSelectedData ReferenceBankCycleInputs RFEffectState RFScalarControl RFReferenceWriteEffect RFReadPorts ReferenceInstructionDecode FormalLocalHistory CoreSocModel ObservedJointRegisterConcrete LoadTypeCorrespondence.
From Coq Require Import NArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque generated_modules generated_top.
Theorem rf_upper_bank_inputs memory inputs k observed instruction auipc pc :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 VM.find 1(formal_external_inputs(generated_observation_input inputs k))=Some(Gval(Fuint 1)[::false]) ->
 VM.find 7750(top_environment observed)=Some(Gval(Fuint 32)instruction) ->
 N.land(to_N instruction)(reference_instruction_mask(rf_upper_class auipc))=reference_instruction_code(rf_upper_class auipc) ->
 size pc=32%nat ->VM.find 7331(top_environment observed)=Some(Gval(Fuint 32)pc) ->
 ref_bank_guarded_controls(top_environment observed) /\ref_write_selected_data_concrete(top_environment observed) /\
 VM.find 3221(top_environment observed)=Some(Gval(Fuint 5)(ref_write_destination(top_environment observed))).
Proof.
 intros Observe Legal Reset Instruction Match PcSize PC.
 pose proof(rf_upper_reference_enabled memory inputs k observed instruction auipc Observe Legal Reset Instruction Match)as Enabled.
 pose proof(rf_upper_reference_data_active memory inputs k observed instruction auipc pc Observe Legal Enabled Instruction Match PcSize PC)as Data.
 rewrite<-(rf_upper_reference_write_node auipc)in Data.
 apply(rf_single_write_bank_inputs memory inputs k observed instruction(rf_upper_class auipc)(cycle_upper_semantics auipc pc instruction)Observe Legal Enabled Instruction(rf_upper_class_bound auipc)Match(rf_upper_reference_writes auipc)Data).
 - destruct(observed_joint_register_concrete memory inputs k observed 7750%nat 32%nat Observe Legal load_type_instruction_member)as[word[Size Word]]. rewrite Instruction in Word;inversion Word;subst word.
   exact(cycle_upper_semantics_size auipc pc instruction Size).
 - rewrite(rf_upper_reference_depth auipc). discriminate.
Qed.
