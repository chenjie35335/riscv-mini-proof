Require Import RFShiftReferenceEffect RFShiftCycle RFShiftSemanticBank RFShiftReferenceData RFSingleWriteBankInputs RFNonNopActive ReferenceBankGuardedObserved ReferenceBankSelectedData ReferenceBankCycleInputs RFEffectState RFScalarControl RFReferenceWriteEffect RFReferenceNopHistory RFReadPorts ReferenceInstructionDecode FormalLocalHistory CoreSocModel FormalInstructionResetConstants ObservedJointRegisterConcrete LoadTypeCorrespondence.
From Coq Require Import NArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Theorem rf_shift_bank_inputs memory inputs k observed instruction immediate lane bank :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 VM.find 1(formal_external_inputs(generated_observation_input inputs k))=Some(Gval(Fuint 1)[::false]) ->
 VM.find 7750(top_environment observed)=Some(Gval(Fuint 32)instruction) ->(lane<3)%coq_nat ->
 N.land(to_N instruction)(reference_instruction_mask(rf_shift_class immediate lane))=reference_instruction_code(rf_shift_class immediate lane) ->
 rf_reference_bank_at(top_environment observed)bank ->
 ref_bank_guarded_controls(top_environment observed) /\ref_write_selected_data_concrete(top_environment observed) /\
 VM.find 3221(top_environment observed)=Some(Gval(Fuint 5)(ref_write_destination(top_environment observed))).
Proof.
 intros Observe Legal Reset Instruction Lane Match Bank.
 assert(NonNop:instruction<>instruction_nop).
 { intro Nop;subst instruction. destruct immediate;do 3(destruct lane as[|lane];[discriminate Match|]);lia. }
 pose proof(rf_nonnop_reference_active memory inputs k observed instruction Observe Legal Reset Instruction NonNop)as Enabled.
 pose proof(rf_shift_reference_data_active memory inputs k observed instruction immediate lane bank Observe Legal Enabled Instruction Lane Match Bank)as Data.
 rewrite<-(rf_shift_write_node immediate lane Lane)in Data.
 apply(rf_single_write_bank_inputs memory inputs k observed instruction(rf_shift_class immediate lane)(cycle_shift_semantics immediate lane bank instruction)Observe Legal Enabled Instruction(rf_shift_class_bound immediate lane Lane)Match(rf_shift_writes immediate lane Lane)Data).
 - destruct(observed_joint_register_concrete memory inputs k observed 7750%nat 32%nat Observe Legal load_type_instruction_member)as[word[Size Word]]. rewrite Instruction in Word;inversion Word;subst word.
   assert(Bound:(to_nat(rf_instruction_address false instruction)<32)%coq_nat).
   { pose proof(to_nat_bounded(rf_instruction_address false instruction))as B. rewrite(rf_instruction_address_size false instruction Size)in B. exact(elimT ltP B). }
   apply rf_shift_result_size;exact(proj1(Bank _ Bound)).
 - rewrite(rf_shift_depth immediate lane Lane). discriminate.
Qed.
