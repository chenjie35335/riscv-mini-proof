Require Import FormalInstructionResetConstants.
Require Import ExceptionPCSourceRegisters DUTBankCycleHistory RFPreviewEffect RFEffectState RFDutOutputWires RFArchitecturalNormalRelation RFWriteEffect RFScalarControl RFPipelineEnable RFNonAluBubbleHazard
 JointBoundaryRegisters JointUpdateBoundaryHistory ConcreteRegisterInitialization ExceptionSourceNoTrap FormalStallHistory StagedRegisterHold
 CoreSocModel ComparisonNodes FormalLocalHistory.
From Coq Require Import NArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque generated_modules generated_top flat_statements flat_memories.
Theorem dut_original_preview_history inputs path history bank instruction enabled data :
 (forall node width,List.In(node,width)joint_boundary_registers ->map_uint_concrete(N.of_nat node)width(history 0%nat)) ->
 (forall t,(t<9259)%coq_nat ->formal_value_iter(formal_invalid_policy inputs path)flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 (forall t,(t<=9259)%coq_nat ->VM.find 1(history t)=Some(Gval(Fuint 1)[::false])) ->
 VM.find 45(history 9254%nat)=Some(Gval(Fuint 1)[::false]) ->
 rf_dut_bank_at(history 0%nat)bank ->
 size instruction=32%nat ->size data=32%nat ->
 VM.find 7750(history 9259%nat)=Some(Gval(Fuint 32)instruction) ->
 VM.find 7757(history 9259%nat)=Some(Gval(Fuint 1)[::enabled]) ->
 (forall t,(17<=t)%coq_nat ->(t<=9259)%coq_nat ->VM.find 786(history t)=Some(Gval(Fuint 32)data)) ->
 forall index,(index<32)%coq_nat ->
 VM.find(N.of_nat(Nat.add 1399 index))(history 9258%nat)=Some(Gval(Fuint 32)(rf_apply_effect bank(if enabled then RFWrite(to_nat(rf_instruction_rd instruction))data else RFNoWrite)index)).
Proof.
 intros Boundary Steps Resets NoTrap Bank Size DataSize Instruction Enable Data index Index.
 assert(Inst:VM.find 7750(history 9248%nat)=Some(Gval(Fuint 32)instruction)).
 { rewrite(flat_register_history_same _ history 9259 7750(proj2(joint_boundary_register_properties 7750 32 rf_pipeline_enable_instruction_member))Steps 9248 ltac:(vm_compute;lia)).
 rewrite(flat_register_history_same _ history 9259 7750(proj2(joint_boundary_register_properties 7750 32 rf_pipeline_enable_instruction_member))Steps 9259 ltac:(vm_compute;lia))in Instruction. exact Instruction. }
 assert(En:VM.find 7757(history 9248%nat)=Some(Gval(Fuint 1)[::enabled])).
 { rewrite(flat_register_history_same _ history 9259 7757(proj2(joint_boundary_register_properties 7757 1 rf_nonalu_enable_member))Steps 9248 ltac:(vm_compute;lia)).
 rewrite(flat_register_history_same _ history 9259 7757(proj2(joint_boundary_register_properties 7757 1 rf_nonalu_enable_member))Steps 9259 ltac:(vm_compute;lia))in Enable. exact Enable. }
 assert(Stall:VM.find 7765(history 9247%nat)=Some(Gval(Fuint 1)[::false])).
 { exact(stall_after_six _ (history 9241%nat)(history 9242%nat)(history 9243%nat)(history 9244%nat)(history 9245%nat)(history 9246%nat)(history 9247%nat)false(Resets 9241 ltac:(vm_compute;lia))(Steps 9241 ltac:(vm_compute;lia))(Steps 9242 ltac:(vm_compute;lia))(Steps 9243 ltac:(vm_compute;lia))(Steps 9244 ltac:(vm_compute;lia))(Steps 9245 ltac:(vm_compute;lia))(Steps 9246 ltac:(vm_compute;lia))). }
 pose proof(exception_source_false_after_settling inputs path history Boundary Steps NoTrap 9248 ltac:(vm_compute;lia)ltac:(vm_compute;lia))as Exception.
 pose proof(rf_pipeline_wen_after_four _ (history 9247%nat)(history 9248%nat)(history 9249%nat)(history 9250%nat)(history 9251%nat)enabled Stall En Exception(Steps 9247 ltac:(vm_compute;lia))(Steps 9248 ltac:(vm_compute;lia))(Steps 9249 ltac:(vm_compute;lia))(Steps 9250 ltac:(vm_compute;lia)))as Wen.
 pose proof(rf_preview_bank_from_instruction _ (history 9248%nat)(history 9249%nat)(history 9250%nat)(history 9251%nat)(history 9252%nat)(history 9253%nat)instruction data bank enabled
 Size DataSize (fun i B=>proj1(Bank i B))Inst(Data 9250%nat ltac:(vm_compute;lia)ltac:(vm_compute;lia))Wen
 (fun i B=>proj2(rf_dut_bank_history_hold _ history 9259 bank Bank Steps 9248 ltac:(vm_compute;lia)i B))
 (Steps 9248 ltac:(vm_compute;lia))(Steps 9249 ltac:(vm_compute;lia))(Steps 9250 ltac:(vm_compute;lia))(Steps 9251 ltac:(vm_compute;lia))(Steps 9252 ltac:(vm_compute;lia))index Index)as Preview.
 rewrite rf_preview_effect_remove_zero_guard in Preview.
 eapply(rf_dut_output_wires index _ (history 9253%nat)(history 9254%nat)(history 9255%nat)(history 9256%nat)(history 9257%nat)(history 9258%nat));
 [exact Index| |exact Preview|apply Steps;vm_compute;lia|apply Steps;vm_compute;lia|apply Steps;vm_compute;lia|apply Steps;vm_compute;lia|apply Steps;vm_compute;lia].
 apply rf_apply_effect_size;[exact(proj1(Bank index Index))|]. destruct enabled;[exact DataSize|exact I].
Qed.

Require Import RFReferenceNopObservedOutputs.
Theorem rf_dut_nop_original_outputs invalid history bank :
 rf_dut_bank_at (history 0%nat) bank -> bank 0%nat = nseq 32 false ->
 VM.find 7750 (history 0%nat) = Some (Gval (Fuint 32) instruction_nop) ->
 (forall time, (time < 9259)%coq_nat -> formal_value_iter invalid flat_memories (history time) false (history time) flat_statements = Some (history (S time))) ->
 forall index, (index < 32)%coq_nat -> VM.find (N.of_nat (Nat.add 1399 index)) (history 9258%nat) = Some (Gval (Fuint 32) (bank index)).
Proof.
 intros Bank Zero Instruction Steps index Index.
 assert (Preview : VM.find (N.of_nat (1053+index)%nat) (history 9253%nat) = Some (Gval (Fuint 32) (bank index))).
 { eapply (rf_nop_preview_after_four invalid (history 9249%nat) (history 9250%nat) (history 9251%nat) (history 9252%nat) (history 9253%nat) bank);
   [exact (rf_dut_bank_history_hold invalid history 9259 bank Bank Steps 9249 ltac:(vm_compute;lia))|exact Zero| |apply Steps;vm_compute;lia|apply Steps;vm_compute;lia|apply Steps;vm_compute;lia|apply Steps;vm_compute;lia|exact Index].
   exact (rf_nop_gate_history invalid history 9259 Instruction Steps 9252 ltac:(vm_compute;lia)). }
 eapply (rf_dut_output_wires index invalid (history 9253%nat) (history 9254%nat) (history 9255%nat) (history 9256%nat) (history 9257%nat) (history 9258%nat) (bank index));
 [exact Index|exact (proj1 (Bank index Index))|exact Preview|apply Steps;vm_compute;lia|apply Steps;vm_compute;lia|apply Steps;vm_compute;lia|apply Steps;vm_compute;lia|apply Steps;vm_compute;lia].
Qed.
