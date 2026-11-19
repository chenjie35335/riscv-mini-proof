Require Import RFNonNopActive FormalInstructionResetConstants ReferenceBankCycleInputs RFWriteEffect RFUpperSemantics RFUpperReferenceImmediate RFUpperReferenceData RFReferenceSelectedEffect RFReferenceWriteEffect RFEffectState RFScalarControl RFReadPorts ReferenceInstructionDecode ObservedJointRegisterConcrete LoadTypeCorrespondence FormalLocalHistory CoreSocModel.
From Coq Require Import NArith Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque generated_modules generated_top.
Lemma rf_upper_reference_writes auipc :rf_isa_writes(rf_upper_class auipc)=true.
Proof. destruct auipc;reflexivity. Qed.
Lemma rf_upper_reference_write_node auipc :rf_reference_write_data(rf_isa_write_stage(rf_upper_class auipc))=rf_upper_reference_output auipc.
Proof. destruct auipc;reflexivity. Qed.
Lemma rf_upper_reference_depth auipc :rf_reference_write_depth(rf_isa_write_stage(rf_upper_class auipc))=1%nat.
Proof. destruct auipc;reflexivity. Qed.
Theorem rf_upper_reference_data_active memory inputs k observed instruction auipc pc :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 VM.find 1707(top_environment observed)=Some(Gval(Fuint 1)[::true]) ->
 VM.find 7750(top_environment observed)=Some(Gval(Fuint 32)instruction) ->
 N.land(to_N instruction)(reference_instruction_mask(rf_upper_class auipc))=reference_instruction_code(rf_upper_class auipc) ->
 size pc=32%nat ->VM.find 7331(top_environment observed)=Some(Gval(Fuint 32)pc) ->
 VM.find(rf_upper_reference_output auipc)(top_environment observed)=Some(Gval(Fuint 32)(cycle_upper_semantics auipc pc instruction)).
Proof.
 intros Observe Legal Enabled Instruction Match PcSize PC.
 pose proof(rf_upper_reference_immediate_observed memory inputs k observed instruction auipc Observe Legal Enabled Instruction Match)as Immediate.
 exact(rf_upper_reference_data_observed memory inputs k observed auipc pc(rf_upper_immediate instruction)Observe Legal PcSize PC Immediate).
Qed.
Theorem rf_upper_reference_effect_active memory inputs k observed instruction auipc pc :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 VM.find 1707(top_environment observed)=Some(Gval(Fuint 1)[::true]) ->
 VM.find 7750(top_environment observed)=Some(Gval(Fuint 32)instruction) ->
 N.land(to_N instruction)(reference_instruction_mask(rf_upper_class auipc))=reference_instruction_code(rf_upper_class auipc) ->
 size pc=32%nat ->VM.find 7331(top_environment observed)=Some(Gval(Fuint 32)pc) ->
 ref_write_effect(top_environment observed)=RFWrite(to_nat(rf_instruction_rd instruction))(cycle_upper_semantics auipc pc instruction).
Proof.
 intros Observe Legal Enabled Instruction Match PcSize PC.
 pose proof(rf_upper_reference_data_active memory inputs k observed instruction auipc pc Observe Legal Enabled Instruction Match PcSize PC)as Data.
 rewrite <-(rf_upper_reference_write_node auipc)in Data.
 apply(rf_reference_selected_effect memory inputs k observed instruction(rf_upper_class auipc)_ Observe Legal Enabled Instruction(rf_upper_class_bound auipc)Match(rf_upper_reference_writes auipc)).
 - unfold rf_reference_permission_value. rewrite(rf_upper_reference_depth auipc);reflexivity.
 - rewrite(ref_write_word_actual _ _ _ _ Data).
   destruct(observed_joint_register_concrete memory inputs k observed 7750%nat 32%nat Observe Legal load_type_instruction_member)as[word[Size Word]].
   rewrite Instruction in Word;inversion Word;subst word.
   rewrite <-(cycle_upper_semantics_size auipc pc instruction Size). apply take_size.
Qed.

Lemma rf_upper_reference_enabled memory inputs k observed instruction auipc :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 VM.find 1(formal_external_inputs(generated_observation_input inputs k))=Some(Gval(Fuint 1)[::false]) ->
 VM.find 7750(top_environment observed)=Some(Gval(Fuint 32)instruction) ->
 N.land(to_N instruction)(reference_instruction_mask(rf_upper_class auipc))=reference_instruction_code(rf_upper_class auipc) ->
 VM.find 1707(top_environment observed)=Some(Gval(Fuint 1)[::true]).
Proof.
 intros Observe Legal Reset Instruction Match.
 apply(rf_nonnop_reference_active memory inputs k observed instruction Observe Legal Reset Instruction).
 intro Nop;subst instruction;destruct auipc;discriminate Match.
Qed.
Theorem rf_upper_reference_effect memory inputs k observed instruction auipc pc :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 VM.find 1(formal_external_inputs(generated_observation_input inputs k))=Some(Gval(Fuint 1)[::false]) ->
 VM.find 7750(top_environment observed)=Some(Gval(Fuint 32)instruction) ->
 N.land(to_N instruction)(reference_instruction_mask(rf_upper_class auipc))=reference_instruction_code(rf_upper_class auipc) ->
 size pc=32%nat ->VM.find 7331(top_environment observed)=Some(Gval(Fuint 32)pc) ->
 ref_write_effect(top_environment observed)=RFWrite(to_nat(rf_instruction_rd instruction))(cycle_upper_semantics auipc pc instruction).
Proof.
 intros Observe Legal Reset Instruction Match PcSize PC.
 exact(rf_upper_reference_effect_active memory inputs k observed instruction auipc pc Observe Legal
 (rf_upper_reference_enabled memory inputs k observed instruction auipc Observe Legal Reset Instruction Match)
 Instruction Match PcSize PC).
Qed.
