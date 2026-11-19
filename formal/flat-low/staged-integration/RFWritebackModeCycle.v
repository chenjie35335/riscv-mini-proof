Require Import RFPipelineEnable RFNonAluBubbleHazard RFScalarControl CoreSocModel ComparisonNodes ControlWritebackKill JointBoundaryRegisters JointUpdateBoundaryHistory ConcreteRegisterInitialization EarlyBubbleNopFullHistory ExceptionSourceNoTrap FormalStallHistory FormalCheckerResetConnections FormalPipelineControlHistory InstructionNormalTransfer ExceptionPCSourceRegisters FormalInstructionResetConstants.
From Coq Require Import ZArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque generated_modules generated_top flat_statements flat_memories.
Definition rf_mode_transfer before after :=forall instruction,
 VM.find 7748 before=Some(Gval(Fuint 32)instruction) ->
 VM.find 7756 after=Some(Gval(Fuint 2)[::wbkill_low(wbkill_decode 49 instruction);wbkill_high(wbkill_decode 49 instruction)]).
Theorem rf_mode_normal_fullhistory inputs path history result :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall time, (time < 9259)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history time) false (history time) flat_statements = Some (history (S time))) ->
 (forall time, (time <= 9259)%coq_nat -> VM.find 1 (history time) = Some (Gval (Fuint 1) [::false])) ->
 VM.find 45 (history 9254%nat) = Some (Gval (Fuint 1) [::false]) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories (history 9259%nat) true (history 9259%nat) flat_statements = Some result ->
 rf_mode_transfer(history 9259%nat)result.
Proof.
 intros Boundary Steps Resets NoTrap Commit.
 destruct (Boundary 7748%nat 32%nat early_bubble_front_instruction_member) as [instruction [Size Initial]].
 pose proof (control_writeback_decode_history _ history 9259 instruction Size Initial Steps) as Decode.
 destruct (Decode 9257%nat ltac:(vm_compute;lia) ltac:(vm_compute;lia)) as [_ [Mode Enabled]].
 pose proof (proj1 (Decode 9254%nat ltac:(vm_compute;lia) ltac:(vm_compute;lia))) as Kill.
 pose proof (wbkill_decode_safe 49 instruction ltac:(lia)) as Safe.
 destruct (wbkill_decode 49 instruction) as [kill low high enabled] eqn:Decoded.
 cbn [wbkill_kill wbkill_low wbkill_high wbkill_enable wbkill_safe] in Mode,Enabled,Kill,Safe.
 assert (Stall : forall time, ((6 <= time)%coq_nat /\ (time <= 9259)%coq_nat) -> VM.find 7765 (history time) = Some (Gval (Fuint 1) [::false])).
 { intros time Bounds. do 6 (destruct time as [|time];[lia|]).
   eapply (stall_after_six _ (history time) (history (S time)) (history (S (S time))) (history (S (S (S time)))) (history (S (S (S (S time))))) (history (S (S (S (S (S time)))))) (history (S (S (S (S (S (S time))))))) false);
   [apply Resets|apply Steps|apply Steps|apply Steps|apply Steps|apply Steps|apply Steps];lia. }
 assert (Reset65 : forall time, ((2 <= time)%coq_nat /\ (time <= 9259)%coq_nat) -> VM.find 65 (history time) = Some (Gval (Fuint 1) [::false])).
 { intros time Bounds. do 2 (destruct time as [|time];[lia|]).
   eapply (reset_connection_65_transfer _ (history (S time)) (history (S time)) (history (S (S time))) false);[|apply Steps;lia].
   eapply (reset_connection_24_transfer _ (history time) (history time) (history (S time)) false);[apply Resets;lia|apply Steps;lia]. }
 pose proof (exception_source_false_after_settling inputs path history Boundary Steps NoTrap) as Exception.
 assert (Advance : VM.find 7855 (history 9257%nat) = Some (Gval (Fuint 1) [::true])).
 { eapply (pipeline_advance_after_two _ (history 9255%nat) (history 9256%nat) (history 9257%nat) false false);
   [apply Stall|apply Exception|apply Steps|apply Steps];vm_compute;lia. }
 assert (Flush : VM.find 7852 (history 9258%nat) = Some (Gval (Fuint 1) [::false])).
 { eapply (pipeline_flush_after_three _ (history 9255%nat) (history 9256%nat) (history 9257%nat) (history 9258%nat) false false false);
   [apply Stall|apply Exception|apply Reset65|apply Steps|apply Steps|apply Steps];vm_compute;lia. }
 destruct (joint_update_register_history_concrete _ history 9259 7756 2 rf_nonalu_mode_member (Boundary _ _ rf_nonalu_mode_member) Steps 9257 ltac:(vm_compute;lia)) as [old_mode [OldModeSize OldMode]].
 destruct old_mode as [|old_low [|old_high [|extra rest]]];try discriminate OldModeSize.
 destruct (joint_update_register_history_concrete _ history 9259 7757 1 rf_nonalu_enable_member (Boundary _ _ rf_nonalu_enable_member) Steps 9257 ltac:(vm_compute;lia)) as [old_enable [OldEnableSize OldEnable]].
 destruct old_enable as [|old_enabled [|extra rest]];try discriminate OldEnableSize.
 destruct (rf_writeback_controls_advance _ (history 9257%nat) (history 9258%nat) (history 9259%nat) result old_low old_high old_enabled low high enabled OldMode OldEnable Mode Enabled Advance Flush (Steps 9257%nat ltac:(vm_compute;lia)) (Steps 9258%nat ltac:(vm_compute;lia)) Commit) as [NextMode NextEnable].

 intros next_instruction Instruction.
 assert(FrontFinal:VM.find 7748(history 9259%nat)=Some(Gval(Fuint 32)instruction)).
 { rewrite(flat_register_history_same _ history 9259 7748 (proj2(joint_boundary_register_properties 7748 32 early_bubble_front_instruction_member)) Steps 9259 ltac:(vm_compute;lia)). exact Initial. }
 rewrite FrontFinal in Instruction. inversion Instruction;subst next_instruction.
 rewrite Decoded. exact NextMode.
Qed.
Require Import FormalLocalHistory FormalObservationCommit StagedFlatCircuitIteration ObservedLegalNoTrap JointBoundaryReachable JointBoundaryInitialization JointBoundaryPreparation FormalFetchType FormalResetPreparation.
Theorem rf_mode_normal_successor memory inputs k observed next :
 generated_observe memory inputs k = Some observed -> generated_legal_trace memory inputs k ->
 generated_run memory inputs (S k) = Some next ->
 VM.find 1 (formal_external_inputs (generated_observation_input inputs k)) = Some (Gval (Fuint 1) [::false]) ->
 rf_mode_transfer(top_environment observed)(top_environment next).
Proof.
 intros Observe Legal Next Reset.
 destruct (observed_legal_no_trap_history memory inputs k observed Observe Legal Reset)
 as [committed [initial [history [Run [Prepare [First [Last [Steps NoTrap]]]]]]]].
 destruct (fetch9220_run_type memory inputs k committed Run) as [env [value [Env Rest]]].
 destruct (joint_boundary_reachable memory inputs k committed Run Legal) as [Registers Storage].
 unfold top_environment in Registers. rewrite Env in Registers.
 assert (Boundary : forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)).
 { intros node width Member. rewrite First.
   exact (joint_boundary_prepared_concrete committed env _ initial node width Member (Registers node width Member) Env Prepare). }
 destruct (top_reset_prepared (Some committed) _ initial _ Reset Prepare) as [initial_env [InitialEnv InitialReset]].
 assert (Reset0 : VM.find 1 (history 0%nat) = Some (Gval (Fuint 1) [::false])).
 { rewrite First. unfold top_environment. rewrite InitialEnv. exact InitialReset. }
 pose proof (legal_local_reset_history _ history 9259 false Steps Reset0) as Resets.
 rewrite (observation_then_commit memory inputs k observed Observe) in Next.
 destruct (flat_iteration_projection _ observed true next Next) as [before [after [Before [Step After]]]].
 assert (Top : top_environment observed = before) by (unfold top_environment;rewrite Before;reflexivity).
 change(rf_mode_transfer(top_environment observed)(top_environment next)).
 rewrite <- Top in Step. rewrite <- Last in Step.
 assert(NextEnv:top_environment next=after)by(unfold top_environment;rewrite After;reflexivity).
 rewrite NextEnv. rewrite <- Last.
 exact (rf_mode_normal_fullhistory (generated_observation_input inputs k) nil history after Boundary Steps Resets NoTrap Step).
Qed.
Require Import ReferenceInstructionDecode CycleView ReferenceBankObservation RFALUData CycleRFBitwise MemoryCycleStep.
Theorem cycle_writeback_mode_step memory inputs k current next before after :
 cycle_transition memory inputs k current next ->cycle_reset inputs k false ->
 cycle_view_at(top_environment current)before ->cycle_view_at(top_environment next)after ->
 cv_write_select_low after=wbkill_low(wbkill_decode 49(cv_front_instruction before)) /\
 cv_write_select_high after=wbkill_high(wbkill_decode 49(cv_front_instruction before)).
Proof.
 intros[Observe[Legal[NextObserve[NextLegal[committed Run]]]]]Reset Before After.
 pose proof(rf_mode_normal_successor memory inputs k current committed Observe Legal Run Reset
 (cv_front_instruction before)(cva_front_instruction _ _ Before))as Mode.
 pose proof(joint_register_run_observed memory inputs(S k)committed next 7756 2 rf_nonalu_mode_member Run NextObserve)as Copy.
 rewrite(cva_write_select _ _ After)Mode in Copy. inversion Copy. split;assumption.
Qed.
Theorem cycle_writeback_mode_commit memory inputs k current next before after :
 cycle_transition memory inputs k current next ->cycle_reset inputs k false ->
 cycle_view_at(top_environment current)before ->cycle_view_at(top_environment next)after ->
 cv_write_select_low after=wbkill_low(wbkill_decode 49(cv_commit_instruction after)) /\
 cv_write_select_high after=wbkill_high(wbkill_decode 49(cv_commit_instruction after)).
Proof.
 intros Transition Reset Before After.
 rewrite(cycle_front_to_commit memory inputs k current next before after Transition Reset Before After).
 exact(cycle_writeback_mode_step memory inputs k current next before after Transition Reset Before After).
Qed.
Lemma rf_wb_legal_mode instruction row :(row<37)%coq_nat ->
 N.land(to_N instruction)(reference_instruction_mask row)=reference_instruction_code row ->
 wbkill_decode 49 instruction=wbkill_row_value(rf_wb_row(rf_wb_class_index row)).
Proof.
 intros Row Match. destruct(rf_wb_class_certificate row Row)as[Bound Rest].
 apply(rf_wb_decode_selected instruction(rf_wb_class_index row)49 Bound).
 intros stage Stage. exact(rf_wb_choice_onehot instruction row stage Row Stage Match).
Qed.
Lemma rf_wb_bitwise_mode instruction lane :(lane<6)%coq_nat ->
 N.land(to_N instruction)(reference_instruction_mask(rf_bitwise_class lane))=reference_instruction_code(rf_bitwise_class lane) ->
 wbkill_low(wbkill_decode 49 instruction)=false /\wbkill_high(wbkill_decode 49 instruction)=false.
Proof.
 intros Lane Match. rewrite(rf_wb_legal_mode instruction(rf_bitwise_class lane) ltac:(do 6 (destruct lane as[|lane];[vm_compute;lia|]);lia) Match).
 do 6 (destruct lane as[|lane];[vm_compute;split;reflexivity|]);lia.
Qed.
Theorem cycle_bitwise_mode_step memory inputs k current next before after lane :
 cycle_transition memory inputs k current next ->cycle_reset inputs k false ->
 cycle_view_at(top_environment current)before ->cycle_view_at(top_environment next)after ->
 cycle_bitwise_instruction before lane ->
 cv_write_select_low after=false /\cv_write_select_high after=false.
Proof.
 intros Transition Reset Before After[Lane Match].
 destruct(cycle_writeback_mode_step memory inputs k current next before after Transition Reset Before After)as[Low High].
 rewrite Low High. exact(rf_wb_bitwise_mode(cv_front_instruction before)lane Lane Match).
Qed.
