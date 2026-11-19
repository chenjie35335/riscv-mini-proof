Require Import ReferenceBankInactiveCommit RFReferenceNopCycle LoadPipelineClassification ReferenceIllegalObserved RFWriteEffect FormalInstructionResetConstants RFPipelineEnable JointUpdateBoundaryHistory.
Require Import ReferenceBankGuardedCommit RFWriteEffect ReferenceBankCycleControls ReferenceBankCycleTargets ReferenceBankSelectedData ReferenceBankCycleInputs RFReferenceSelectedCommit RFReferenceWriteEffect RFReferenceNopHistory RFArchitecturalRelation ReferenceControlRegisters ReferenceBankObservation FormalObservedHistory FormalLocalHistory PipelinePCAdjacentTransfer ReferencePCResetHistory CoreSocModel ComparisonNodes.
From Coq Require Import NArith List Lia PeanoNat.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Theorem reference_bank_nop_observed_commit memory inputs k observed bank result :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 VM.find 1(formal_external_inputs(generated_observation_input inputs k))=Some(Gval(Fuint 1)[::false]) ->
 rf_reference_bank_at(top_environment observed)bank ->bank 0%nat=nseq 32 false ->
 VM.find 7750(top_environment observed)=Some(Gval(Fuint 32)instruction_nop) ->
 formal_value_iter(formal_invalid_policy(generated_observation_input inputs k)nil)flat_memories(top_environment observed)true(top_environment observed)flat_statements=Some result ->
 rf_reference_bank_at result bank.
Proof.
 intros Observe Legal Reset Bank Zero Instruction Commit.
 destruct(observed_history memory inputs k observed Observe Legal)as[reset[history[Last[Steps Resets]]]].
 assert(ResetBit:reset=false).
 { pose proof(Resets 9259%nat ltac:(lia))as Value. rewrite Last in Value.
   rewrite(adjacent_transfer_observed_reset memory inputs k observed Observe Legal Reset)in Value;congruence. }
 subst reset.
 assert(InitialBank:rf_reference_bank_at(history 0%nat)bank).
 { intros index Bound. destruct(Bank index Bound)as[Size Value]. split;[exact Size|].
   destruct(rf_architectural_register_properties _ (rf_reference_register_member index Bound))as[Present Rest].
   rewrite<-(reference_control_register_history_same _ history 9259 _ Present Steps 9259%nat ltac:(lia)). rewrite Last;exact Value. }
 destruct(load_pipeline_late_observed memory inputs k observed Observe Legal)as[bubble[Bubble Nop]].
 pose proof(reference_enable_observed_bubble memory inputs k observed bubble Observe Legal Reset Bubble)as Enabled.
 destruct bubble.
 - apply(reference_bank_inactive_commit (formal_invalid_policy(generated_observation_input inputs k)nil) history bank result InitialBank Zero).
   + intros t Lower Upper.
     rewrite(ref_bank_controls_stable (generated_observation_input inputs k)nil history 9259 false Resets Steps 1707 ltac:(unfold ref_bank_control_nodes;vm_compute;tauto)t 9259 Lower ltac:(lia)Upper ltac:(lia)).
     rewrite Last;exact Enabled.
   + exact Steps.
   + exact(reference_pc_reset_after_four _ (history 9255%nat)(history 9256%nat)(history 9257%nat)(history 9258%nat)(history 9259%nat)false (Resets 9255%nat ltac:(vm_compute;lia))(Steps 9255%nat ltac:(vm_compute;lia))(Steps 9256%nat ltac:(vm_compute;lia))(Steps 9257%nat ltac:(vm_compute;lia))(Steps 9258%nat ltac:(vm_compute;lia))).
   + rewrite Last;exact Commit.
 - assert(InitialInstruction:VM.find 7750(history 0%nat)=Some(Gval(Fuint 32)instruction_nop)).
   { pose proof(joint_update_register_history_same _ history 9259 7750 32 rf_pipeline_enable_instruction_member Steps 9259%nat ltac:(lia))as Copy.
     change(VM.find 7750(history 9259%nat)=VM.find 7750(history 0%nat))in Copy. rewrite<-Copy. rewrite Last;exact Instruction. }
   pose proof(rf_reference_nop_fullhistory_commit _ history bank result InitialBank Zero InitialInstruction Steps Resets)as Actual.
   assert(BubbleLast:VM.find 7947(history 9259%nat)=Some(Gval(Fuint 1)[::false]))by(rewrite Last;exact Bubble).
   specialize(Actual BubbleLast). rewrite Last in Actual. specialize(Actual Commit).
   intros index Bound. specialize(Actual index Bound). rewrite(rf_apply_effect_no_write bank Zero index)in Actual;exact Actual.
Qed.
Theorem reference_bank_nop_observed_next memory inputs k observed committed next bank :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 generated_run memory inputs(S k)=Some committed ->generated_observe memory inputs(S k)=Some next ->
 VM.find 1(formal_external_inputs(generated_observation_input inputs k))=Some(Gval(Fuint 1)[::false]) ->
 rf_reference_bank_at(top_environment observed)bank ->bank 0%nat=nseq 32 false ->
 VM.find 7750(top_environment observed)=Some(Gval(Fuint 32)instruction_nop) ->
 rf_reference_bank_at(top_environment next)bank.
Proof.
 intros Observe Legal Run Next Reset Bank Zero Instruction.
 apply(reference_bank_next_observed memory inputs k observed committed next _ Observe Run Next).
 intros result Commit;exact(reference_bank_nop_observed_commit memory inputs k observed bank result Observe Legal Reset Bank Zero Instruction Commit).
Qed.
