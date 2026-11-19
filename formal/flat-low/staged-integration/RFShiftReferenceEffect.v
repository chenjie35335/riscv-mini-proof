Require Import RFWriteEffect RFShiftCycle RFShiftALUHistory RFShiftSemanticBank RFShiftReferencePorts RFShiftReferenceImmediate RFShiftReferenceData RFReferenceSelectedEffect RFAddReferenceData RFReferenceNopHistory RFReferenceWriteEffect RFEffectState RFScalarControl RFReadPorts ReferenceBankCycleInputs ReferenceInstructionDecode LoadImmediateSemantics ObservedJointRegisterConcrete LoadTypeCorrespondence FormalLocalHistory CoreSocModel.
From Coq Require Import NArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Lemma rf_shift_writes immediate lane :(lane<3)%coq_nat ->rf_isa_writes(rf_shift_class immediate lane)=true.
Proof. intro Lane. destruct immediate;do 3(destruct lane as[|lane];[reflexivity|]);lia. Qed.
Lemma rf_shift_write_node immediate lane :(lane<3)%coq_nat ->rf_reference_write_data(rf_isa_write_stage(rf_shift_class immediate lane))=rf_ref_shift_output immediate lane.
Proof. intro Lane. destruct immediate;do 3(destruct lane as[|lane];[reflexivity|]);lia. Qed.
Lemma rf_shift_depth immediate lane :(lane<3)%coq_nat ->rf_reference_write_depth(rf_isa_write_stage(rf_shift_class immediate lane))=1%nat.
Proof. intro Lane. destruct immediate;do 3(destruct lane as[|lane];[reflexivity|]);lia. Qed.
Theorem rf_shift_reference_data_active memory inputs k observed instruction immediate lane bank :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 VM.find 1707(top_environment observed)=Some(Gval(Fuint 1)[::true]) ->
 VM.find 7750(top_environment observed)=Some(Gval(Fuint 32)instruction) ->(lane<3)%coq_nat ->
 N.land(to_N instruction)(reference_instruction_mask(rf_shift_class immediate lane))=reference_instruction_code(rf_shift_class immediate lane) ->
 rf_reference_bank_at(top_environment observed)bank ->
 VM.find(rf_ref_shift_output immediate lane)(top_environment observed)=Some(Gval(Fuint 32)(cycle_shift_semantics immediate lane bank instruction)).
Proof.
 intros Observe Legal Enabled Instruction Lane Match Bank.
 destruct(observed_joint_register_concrete memory inputs k observed 7750%nat 32%nat Observe Legal load_type_instruction_member)as[word[Size Word]]. rewrite Instruction in Word;inversion Word;subst word.
 assert(Bound:forall second,(to_nat(rf_instruction_address second instruction)<32)%coq_nat).
 { intro second. pose proof(to_nat_bounded(rf_instruction_address second instruction))as B. rewrite(rf_instruction_address_size second instruction Size)in B. exact(elimT ltP B). }
 pose proof(rf_shift_bank_observed false memory inputs k observed instruction immediate lane bank Observe Legal Enabled Instruction Match Lane ltac:(discriminate) Bank)as Left.
 assert(Right:VM.find(if immediate then 2552 else 2804)(top_environment observed)=Some(Gval(Fuint 32)(rf_shift_right immediate instruction(bank(to_nat(rf_instruction_address true instruction)))))).
 { destruct immediate.
 - exact(rf_shift_immediate_observed memory inputs k observed instruction lane Observe Legal Enabled Instruction Lane Match).
 - exact(rf_shift_bank_observed true memory inputs k observed instruction false lane bank Observe Legal Enabled Instruction Match Lane ltac:(reflexivity)Bank). }
 pose proof(rf_reference_shift_observed memory inputs k observed immediate lane _ _ Observe Legal Lane Left Right)as Data.
 unfold cycle_shift_semantics,rf_shift_result.
 rewrite(rf_ref_shift_word_correct lane _ _ Lane(proj1(Bank _ (Bound false))))in Data.
 - exact Data.
 - unfold rf_shift_right. destruct immediate;[apply load_i_immediate_size;exact Size|exact(proj1(Bank _ (Bound true)))].
Qed.
Theorem rf_shift_reference_effect_active memory inputs k observed instruction immediate lane bank :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 VM.find 1707(top_environment observed)=Some(Gval(Fuint 1)[::true]) ->
 VM.find 7750(top_environment observed)=Some(Gval(Fuint 32)instruction) ->(lane<3)%coq_nat ->
 N.land(to_N instruction)(reference_instruction_mask(rf_shift_class immediate lane))=reference_instruction_code(rf_shift_class immediate lane) ->
 rf_reference_bank_at(top_environment observed)bank ->
 ref_write_effect(top_environment observed)=RFWrite(to_nat(rf_instruction_rd instruction))(cycle_shift_semantics immediate lane bank instruction).
Proof.
 intros Observe Legal Enabled Instruction Lane Match Bank.
 pose proof(rf_shift_reference_data_active memory inputs k observed instruction immediate lane bank Observe Legal Enabled Instruction Lane Match Bank)as Data.
 rewrite <-(rf_shift_write_node immediate lane Lane)in Data.
 apply(rf_reference_selected_effect memory inputs k observed instruction(rf_shift_class immediate lane)_ Observe Legal Enabled Instruction(rf_shift_class_bound immediate lane Lane)Match(rf_shift_writes immediate lane Lane)).
 - unfold rf_reference_permission_value. rewrite(rf_shift_depth immediate lane Lane);reflexivity.
 - rewrite(ref_write_word_actual _ _ _ _ Data).
   destruct(observed_joint_register_concrete memory inputs k observed 7750%nat 32%nat Observe Legal load_type_instruction_member)as[word[Size Word]]. rewrite Instruction in Word;inversion Word;subst word.
   assert(Bound:(to_nat(rf_instruction_address false instruction)<32)%coq_nat).
   { pose proof(to_nat_bounded(rf_instruction_address false instruction))as B. rewrite(rf_instruction_address_size false instruction Size)in B. exact(elimT ltP B). }
   assert(W:size(cycle_shift_semantics immediate lane bank instruction)=32%nat).
   { apply rf_shift_result_size;exact(proj1(Bank _ Bound)). }
   rewrite <-W;apply take_size.
Qed.
