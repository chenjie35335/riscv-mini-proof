Require Import LoadTypeCorrespondence.
Require Import DataWriterNodePositions DataWriterExpressionCertificates DUTRedirectDecode CoreSocModel ComparisonNodes FormalDeclaredWireCheck JointUpdateNodePositions JointUpdateExpressionCertificates ReferenceRedirectSpine JointBoundaryRegisters JointUpdateBoundaryHistory FormalPCDecodeInputConnections.
Require Import ConcreteRegisterInitialization RFNonAluBubbleHazard JointRegisterCommits7 InstructionNormalTransfer StagedRegisterHold FormalPipelineControlHistory FormalStallHistory FormalCheckerResetConnections ExceptionSourceNoTrap EarlyBubbleNopFullHistory.
Require Import StagedCircuitRegisterHold FormalLocalHistory FormalObservationCommit StagedFlatCircuitIteration ObservedLegalNoTrap JointBoundaryReachable JointBoundaryInitialization JointBoundaryPreparation FormalFetchType FormalResetPreparation RegisterPreparationFrames StagedObservedRegister FormalInstructionResetBase FormalInstructionResetCycle JointBoundaryInduction ExternalReset StagedIterationCount.
From Coq Require Import NArith ZArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top generated_run.
Lemma load_pipeline_row_classify instruction row : (row < 49)%coq_nat -> dut_decode_test instruction row = true ->
 from_N 3 (load_type_row row) = from_N 3 0 \/
 exists lane, (lane < 5)%coq_nat /\ N.land instruction 28799 = load_type_lane_code lane /\ from_N 3 (load_type_row row) = from_N 3 (load_type_lane_kind lane).
Proof.
 intros Row Guard.
 destruct row as [|row].
 { left;reflexivity. }
 destruct row as [|row].
 { left;reflexivity. }
 destruct row as [|row].
 { left;reflexivity. }
 destruct row as [|row].
 { left;reflexivity. }
 destruct row as [|row].
 { left;reflexivity. }
 destruct row as [|row].
 { left;reflexivity. }
 destruct row as [|row].
 { left;reflexivity. }
 destruct row as [|row].
 { left;reflexivity. }
 destruct row as [|row].
 { left;reflexivity. }
 destruct row as [|row].
 { left;reflexivity. }
 destruct row as [|row].
 { right. exists 4%nat. split;[lia|]. split;[|reflexivity].
 cbv [dut_decode_test dut_decode_row dut_decode_certificate_rows nth hd dd_mask dd_code] in Guard.
 apply N.eqb_eq in Guard. exact Guard. }
 destruct row as [|row].
 { right. exists 3%nat. split;[lia|]. split;[|reflexivity].
 cbv [dut_decode_test dut_decode_row dut_decode_certificate_rows nth hd dd_mask dd_code] in Guard.
 apply N.eqb_eq in Guard. exact Guard. }
 destruct row as [|row].
 { right. exists 2%nat. split;[lia|]. split;[|reflexivity].
 cbv [dut_decode_test dut_decode_row dut_decode_certificate_rows nth hd dd_mask dd_code] in Guard.
 apply N.eqb_eq in Guard. exact Guard. }
 destruct row as [|row].
 { right. exists 1%nat. split;[lia|]. split;[|reflexivity].
 cbv [dut_decode_test dut_decode_row dut_decode_certificate_rows nth hd dd_mask dd_code] in Guard.
 apply N.eqb_eq in Guard. exact Guard. }
 destruct row as [|row].
 { right. exists 0%nat. split;[lia|]. split;[|reflexivity].
 cbv [dut_decode_test dut_decode_row dut_decode_certificate_rows nth hd dd_mask dd_code] in Guard.
 apply N.eqb_eq in Guard. exact Guard. }
 destruct row as [|row].
 { left;reflexivity. }
 destruct row as [|row].
 { left;reflexivity. }
 destruct row as [|row].
 { left;reflexivity. }
 destruct row as [|row].
 { left;reflexivity. }
 destruct row as [|row].
 { left;reflexivity. }
 destruct row as [|row].
 { left;reflexivity. }
 destruct row as [|row].
 { left;reflexivity. }
 destruct row as [|row].
 { left;reflexivity. }
 destruct row as [|row].
 { left;reflexivity. }
 destruct row as [|row].
 { left;reflexivity. }
 destruct row as [|row].
 { left;reflexivity. }
 destruct row as [|row].
 { left;reflexivity. }
 destruct row as [|row].
 { left;reflexivity. }
 destruct row as [|row].
 { left;reflexivity. }
 destruct row as [|row].
 { left;reflexivity. }
 destruct row as [|row].
 { left;reflexivity. }
 destruct row as [|row].
 { left;reflexivity. }
 destruct row as [|row].
 { left;reflexivity. }
 destruct row as [|row].
 { left;reflexivity. }
 destruct row as [|row].
 { left;reflexivity. }
 destruct row as [|row].
 { left;reflexivity. }
 destruct row as [|row].
 { left;reflexivity. }
 destruct row as [|row].
 { left;reflexivity. }
 destruct row as [|row].
 { left;reflexivity. }
 destruct row as [|row].
 { left;reflexivity. }
 destruct row as [|row].
 { left;reflexivity. }
 destruct row as [|row].
 { left;reflexivity. }
 destruct row as [|row].
 { left;reflexivity. }
 destruct row as [|row].
 { left;reflexivity. }
 destruct row as [|row].
 { left;reflexivity. }
 destruct row as [|row].
 { left;reflexivity. }
 destruct row as [|row].
 { left;reflexivity. }
 destruct row as [|row].
 { left;reflexivity. }
 destruct row as [|row].
 { left;reflexivity. }
 lia.
Qed.
Theorem load_pipeline_decode_classify instruction count : (count <= 49)%coq_nat ->
 load_type_decode instruction count = from_N 3 0 \/
 exists lane, (lane < 5)%coq_nat /\ N.land instruction 28799 = load_type_lane_code lane /\ load_type_decode instruction count = from_N 3 (load_type_lane_kind lane).
Proof.
 induction count as [|count IH];intro Count;[left;reflexivity|].
 cbn [load_type_decode]. destruct (dut_decode_test instruction (Nat.sub 48 count)) eqn:Guard.
 - apply load_pipeline_row_classify;[lia|exact Guard].
 - apply IH;lia.
Qed.
Definition load_pipeline_exact env : Prop := forall instruction,
 VM.find 7750 env = Some (Gval (Fuint 32) instruction) ->
 VM.find 7755 env = Some (Gval (Fuint 3) (load_type_decode (to_N instruction) 49)).
Theorem load_pipeline_normal_fullhistory inputs path history result :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall time, (time < 9259)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history time) false (history time) flat_statements = Some (history (S time))) ->
 (forall time, (time <= 9259)%coq_nat -> VM.find 1 (history time) = Some (Gval (Fuint 1) [::false])) ->
 VM.find 45 (history 9254%nat) = Some (Gval (Fuint 1) [::false]) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories (history 9259%nat) true (history 9259%nat) flat_statements = Some result ->
 load_pipeline_exact result.
Proof.
 intros Boundary Steps Resets NoTrap Commit.
 destruct (joint_update_register_history_concrete _ history 9259 7748 32 early_bubble_front_instruction_member
 (Boundary _ _ early_bubble_front_instruction_member) Steps 9259 ltac:(vm_compute;lia)) as [front [FrontSize Front]].
 pose proof (load_type_decode_history inputs path history 9259 front Steps Front FrontSize 9257 ltac:(vm_compute;lia) ltac:(vm_compute;lia)) as Decode.
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
 destruct (joint_update_register_history_concrete _ history 9259 7755 3 load_type_register_member
 (Boundary _ _ load_type_register_member) Steps 9257 ltac:(vm_compute;lia)) as [previous [PreviousSize Previous]].
 pose proof (load_type_advance _ (history 9257%nat) (history 9258%nat) (history 9259%nat) result previous _ PreviousSize
 (load_type_decode_size (to_N front) 49) Previous Decode Advance Flush (Steps 9257%nat ltac:(vm_compute;lia)) (Steps 9258%nat ltac:(vm_compute;lia)) Commit) as NextType.
 destruct (joint_update_register_history_concrete _ history 9259 7750 32 load_type_instruction_member
 (Boundary _ _ load_type_instruction_member) Steps 9259 ltac:(vm_compute;lia)) as [old [OldSize Old]].
 pose proof (instruction_transfer_normal_full_history inputs path history result front old Boundary Steps Resets NoTrap FrontSize Front Old Commit) as NextInst.
 intros instruction Instruction. rewrite NextInst in Instruction. inversion Instruction;subst instruction. exact NextType.
Qed.
(* Reset and reachable classification. *)
Require Import FormalSuccessfulNodeEvaluation SelectedNodeSafety FormalTypedNodeEquation FormalNodeEquation DataWriterConnectionCertificates RegisterInvariants RFNonAluReset JointUpdateConnectionCertificates NopBranchShapes ExceptionEventHistory NormalizedBit UIntMuxResultType FormalDeclaredConnectionObservation ScalarSinkTypes FormalRFResetConnections.
Lemma load_pipeline_reset_register_present : has_register 7755 flat_statements = true.
Proof. vm_compute. reflexivity. Qed.
Local Lemma load_pipeline_type_hold invalid old result :
 formal_value_iter invalid flat_memories old false old flat_statements = Some result ->
 VM.find 7755 result = VM.find 7755 old.
Proof. apply staged_combinational_holds_registers. exact load_pipeline_reset_register_present. Qed.
Local Lemma load_pipeline_control_type invalid old result :
 formal_value_iter invalid flat_memories old false old flat_statements = Some result ->
 exists value, VM.find 92 result = Some value /\ type_of_val value = Gtyp (Fuint 3).
Proof.
 intro Step.
 destruct (declared_connection_observation 69 flat_statements data_writer_connection_92_decl data_writer_connection_92_mid data_writer_connection_92_tail
 92 8258 3 invalid flat_memories old old result data_writer_connection_92_position data_writer_connection_92_split data_writer_connection_92_straight data_writer_connection_92_mid_safe data_writer_connection_92_tail_safe data_writer_connection_92_nonregister (Logic.eq_refl _) Step) as [source [value [Source [Adapt Value]]]].
 exists value. split; [exact Value|eapply adapted_uint_result_type;exact Adapt].
Qed.
Lemma load_pipeline_node_shape width node expression (P : hvalue -> Prop) invalid old current result :
 List.In (node,expression) joint_update_expected_nodes ->
 (forall site value, eval_hfexpr_validif_policy (isolated_validif_policy invalid) site flat_memories expression old old = Some value -> P value) ->
 (forall value, P value -> type_of_val value = Gtyp (Fuint width)) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value, VM.find node result = Some value /\ P value.
Proof.
 intros Member Shape Typed Step.
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes node expression joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 destruct (formal_successful_node_evaluation count flat_statements tail node expression invalid flat_memories old false current result Position Step) as [value Eval].
 rewrite add0n in Eval.
 pose proof (Shape _ _ Eval) as Shaped.
 exists value; split; [|exact Shaped].
 eapply formal_combinational_known_node; [exact Position|exact Safe|exact Nonreg|exact Eval|apply Typed;exact Shaped|exact Step].
Qed.
Local Lemma load_pipeline_selected_type invalid old result left right :
 VM.find 92 old = Some left -> type_of_val left = Gtyp (Fuint 3) ->
 VM.find 7755 old = Some right -> type_of_val right = Gtyp (Fuint 3) ->
 formal_value_iter invalid flat_memories old false old flat_statements = Some result ->
 exists value, VM.find 7865 result = Some value /\ type_of_val value = Gtyp (Fuint 3).
Proof.
 intros Left LT Right RT Step. eapply (load_pipeline_node_shape 3 7865 joint_update_expr_7865 (fun value => type_of_val value = Gtyp (Fuint 3)) invalid old old result).
 - apply (List.nth_error_In joint_update_expected_nodes 920%nat). vm_compute. reflexivity.
 - intros site value Eval.
   change (eval_hfexpr_with_memory flat_memories (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 7855)) (@Eref VarOrder.T (@Eid VarOrder.T 92)) (@Eref VarOrder.T (@Eid VarOrder.T 7755))) old old = Some value) in Eval.
   eapply uint_mux_result_type; [exact Left|exact LT|exact Right|exact RT|exact Eval].
 - intros value Typed. exact Typed.
 - exact Step.
Qed.
Theorem load_pipeline_reset_after_five invalid s0 s1 s2 s3 s4 s5 result old_value :
 VM.find 7755 s0 = Some old_value -> type_of_val old_value = Gtyp (Fuint 3) ->
 VM.find 1 s0 = Some (Gval (Fuint 1) [::true]) ->
 formal_value_iter invalid flat_memories s0 false s0 flat_statements = Some s1 ->
 formal_value_iter invalid flat_memories s1 false s1 flat_statements = Some s2 ->
 formal_value_iter invalid flat_memories s2 false s2 flat_statements = Some s3 ->
 formal_value_iter invalid flat_memories s3 false s3 flat_statements = Some s4 ->
 formal_value_iter invalid flat_memories s4 false s4 flat_statements = Some s5 ->
 formal_value_iter invalid flat_memories s5 true s5 flat_statements = Some result ->
 VM.find 7755 result = Some (Gval (Fuint 3) (from_N 3 0)).
Proof.
 intros Old Typed Reset S1 S2 S3 S4 S5 Commit.
 pose proof (reset_connection_24_transfer invalid s0 s0 s1 true Reset S1) as R24.
 pose proof (reset_connection_65_transfer invalid s1 s1 s2 true R24 S2) as R65.
 assert (R7849 : VM.find 7849 s3 = Some (Gval (Fuint 1) [::true])).
 { eapply (reference_redirect_ground_step joint_update_node_offsets joint_update_expected_nodes 7849 joint_update_expr_7849);
   [exact joint_update_node_positions|exact joint_update_node_safety| | |exact S3].
   - apply (List.nth_error_In joint_update_expected_nodes 904%nat). vm_compute. reflexivity.
   - intros site. cbn [joint_update_expr_7849 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite R65. reflexivity. }
 destruct (RFNonAluReset.rf_reset_compare_normalized invalid s1 s2 S2) as [compare [Compare CN]].
 destruct (exception_source128_normalized invalid s1 s1 s2 S2) as [exception [Exception EN]].
 destruct (RFNonAluReset.rf_reset_mask_normalized invalid s2 s3 compare exception Compare CN Exception EN S3) as [masked [Masked MN]].
 assert (Flush : VM.find 7852 s4 = Some (Gval (Fuint 1) [::true])).
 { eapply (reference_redirect_ground_step joint_update_node_offsets joint_update_expected_nodes 7852 joint_update_expr_7852);
   [exact joint_update_node_positions|exact joint_update_node_safety| | |exact S4].
   - apply (List.nth_error_In joint_update_expected_nodes 907%nat). vm_compute. reflexivity.
   - intros site. cbn [joint_update_expr_7852 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite R7849 Masked.
     destruct MN as [bit| | |]; try destruct bit; reflexivity. }
 assert (Old3 : VM.find 7755 s3 = Some old_value).
 { rewrite (load_pipeline_type_hold invalid s2 s3 S3) (load_pipeline_type_hold invalid s1 s2 S2) (load_pipeline_type_hold invalid s0 s1 S1). exact Old. }
 destruct (load_pipeline_control_type invalid s2 s3 S3) as [enable [Enable ENormal]].
 destruct (load_pipeline_selected_type invalid s3 s4 enable old_value Enable ENormal Old3 Typed S4) as [selected [Selected ST]].
 assert (Zero : VM.find 7872 s5 = Some (Gval (Fuint 3) (from_N 3 0))).
 { eapply (reference_redirect_ground_step joint_update_node_offsets joint_update_expected_nodes 7872 joint_update_expr_7872);
   [exact joint_update_node_positions|exact joint_update_node_safety| | |exact S5].
   - apply (List.nth_error_In joint_update_expected_nodes 927%nat). vm_compute. reflexivity.
   - intros site. cbn [joint_update_expr_7872 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Flush.
     cbn [is_zero]. unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref]. rewrite Selected. cbn [option_map]. rewrite ST. reflexivity. }
 assert (Old5 : VM.find 7755 s5 = Some old_value).
 { rewrite (load_pipeline_type_hold invalid s4 s5 S5) (load_pipeline_type_hold invalid s3 s4 S4). exact Old3. }
 eapply (rf_control_direct_commit_exact 8261 flat_statements joint_register_7755_decl joint_register_7755_mid joint_register_7755_tail 7755 7872 joint_register_7755_reg 3 (from_N 3 0) old_value invalid flat_memories s5 s5 result);
 [exact joint_register_7755_position|exact joint_register_7755_split|exact joint_register_7755_straight|exact joint_register_7755_mid_safe|exact joint_register_7755_tail_safe|exact joint_register_7755_identity|exact Old5|exact Typed|reflexivity|exact Zero|reflexivity|exact Commit].
Qed.
Require Import StagedFlatCircuitIteration StagedIterationCount StagedObservedRegister StagedCircuitRegisterHold RegisterPreparationFrames FormalLocalHistory FormalResetTrace FormalResetPreparation ObservedLegalNoTrap.
Theorem load_pipeline_reset_fullhistory invalid history result old_value :
 VM.find 7755 (history 0%nat) = Some old_value -> type_of_val old_value = Gtyp (Fuint 3) ->
 VM.find 1 (history 0%nat) = Some (Gval (Fuint 1) [::true]) ->
 (forall time, (time < 9259)%coq_nat -> formal_value_iter invalid flat_memories (history time) false (history time) flat_statements = Some (history (S time))) ->
 formal_value_iter invalid flat_memories (history 9259%nat) true (history 9259%nat) flat_statements = Some result ->
 VM.find 7755 result = Some (Gval (Fuint 3) (from_N 3 0)).
Proof.
 intros Old Typed Reset Steps Commit.
 pose proof (legal_local_reset_history invalid history 9259 true Steps Reset) as Resets.
 assert (Hold : forall time, (time <= 9259)%coq_nat -> VM.find 7755 (history time) = Some old_value).
 { intros time Bound. induction time as [|time IH]; [exact Old|].
   rewrite (load_pipeline_type_hold invalid (history time) (history (S time)) (Steps time ltac:(lia))). apply IH. lia. }
 exact (load_pipeline_reset_after_five invalid (history 9254%nat) (history 9255%nat) (history 9256%nat) (history 9257%nat) (history 9258%nat) (history 9259%nat) result old_value
 (Hold 9254%nat ltac:(vm_compute;lia)) Typed (Resets 9254%nat ltac:(vm_compute;lia))
 (Steps 9254%nat ltac:(vm_compute;lia)) (Steps 9255%nat ltac:(vm_compute;lia)) (Steps 9256%nat ltac:(vm_compute;lia)) (Steps 9257%nat ltac:(vm_compute;lia)) (Steps 9258%nat ltac:(vm_compute;lia)) Commit).
Qed.
Lemma load_pipeline_reset_initial_safe : initial_register_safe 7755 flat_statements.
Proof. vm_compute. reflexivity. Qed.
Theorem load_pipeline_settle_reset_commit inputs initial stable result old_value :
 state_reset initial true -> staged_register_lookup 7755 initial = Some old_value -> type_of_val old_value = Gtyp (Fuint 3) ->
 circuit_formal_iterations generated_modules generated_top inputs 9259 initial = Some stable ->
 formal_circuit_value_iter (formal_invalid_policy inputs) generated_modules generated_top stable true = Some result ->
 exists env, SVM.find nil result = Some env /\ VM.find 7755 env = Some (Gval (Fuint 3) (from_N 3 0)).
Proof.
 intros [start [Start Reset]] Old Typed Iterations Commit.
 destruct (local_iteration_history inputs 9259 initial stable Iterations) as [history [First [Last Steps]]].
 assert (Reset0 : VM.find 1 (history 0%nat) = Some (Gval (Fuint 1) [::true])).
 { rewrite First. unfold top_environment. rewrite Start. exact Reset. }
 assert (Old0 : VM.find 7755 (history 0%nat) = Some old_value).
 { rewrite First. unfold top_environment. rewrite Start. unfold staged_register_lookup in Old. rewrite Start in Old. exact Old. }
 destruct (flat_iteration_projection (formal_invalid_policy inputs) stable true result Commit) as [before [after [Before [Local After]]]].
 assert (Same : history 9259%nat = before).
 { rewrite Last. unfold top_environment. rewrite Before. reflexivity. }
 exists after. split; [exact After|].
 eapply (load_pipeline_reset_fullhistory (formal_invalid_policy inputs nil) history after old_value); [exact Old0|exact Typed|exact Reset0|exact Steps|].
 rewrite Same. exact Local.
Qed.
Theorem load_pipeline_real_reset_cycle inputs previous old result old_value :
 SVM.find nil previous = Some old -> VM.find 7755 old = Some old_value -> type_of_val old_value = Gtyp (Fuint 3) ->
 VM.find 1 (formal_external_inputs inputs) = Some (Gval (Fuint 1) [::true]) ->
 circuit_formal_cycle generated_modules generated_top (Some previous) inputs = Some result ->
 exists env, SVM.find nil result = Some env /\ VM.find 7755 env = Some (Gval (Fuint 3) (from_N 3 0)).
Proof.
 intros Previous Old Typed Reset Cycle. unfold circuit_formal_cycle in Cycle.
 destruct (circuit_initial_map_with_memory generated_modules generated_top (Some previous) (formal_external_inputs inputs)) as [initial|] eqn:Prepare; [|discriminate Cycle].
 pose proof flat_iteration_count_exact as Count. unfold flat_iteration_count in Count. rewrite Count in Cycle.
 destruct (circuit_formal_iterations generated_modules generated_top inputs 9259 initial) as [stable|] eqn:Iterations; [|discriminate Cycle].
 apply (load_pipeline_settle_reset_commit inputs initial stable result old_value); try assumption.
 - exact (top_reset_prepared (Some previous) _ initial _ Reset Prepare).
 - rewrite (staged_prepared_register_copies previous old _ initial 7755 (Logic.eq_refl _) (Logic.eq_refl _) load_pipeline_reset_initial_safe load_pipeline_reset_register_present Previous Prepare). exact Old.
Qed.
Require Import FormalInstructionInitialization.
From firrtl Require Import FormalInitialization.
Lemma load_pipeline_nop_exact env :
 VM.find 7750 env = Some (Gval (Fuint 32) FormalInstructionResetConstants.instruction_nop) ->
 VM.find 7755 env = Some (Gval (Fuint 3) (from_N 3 0)) -> load_pipeline_exact env.
Proof.
 intros Nop Zero instruction Instruction. rewrite Nop in Instruction. inversion Instruction;subst instruction.
 change (VM.find 7755 env = Some (Gval (Fuint 3) (from_N 3 0))). exact Zero.
Qed.
Theorem load_pipeline_after_reset memory inputs states :
 formal_state_after_reset generated_modules generated_top 1 (Fuint 1) memory inputs = Some states ->
 VM.find 7755 (top_environment states) = Some (Gval (Fuint 3) (from_N 3 0)).
Proof.
 unfold formal_state_after_reset.
 destruct (circuit_symbolic_initial_state generated_modules generated_top memory inputs) as [initial|] eqn:Init;[|discriminate]. intro Reset.
 destruct (instruction_initial_state_concrete memory inputs initial Init) as [old [Old Rest]].
 destruct (joint_boundary_symbolic_initial memory inputs initial Init) as [Registers Storage].
 unfold joint_registers_concrete,top_environment in Registers. rewrite Old in Registers.
 destruct (Registers 7755%nat 3%nat load_type_register_member) as [bits [Size Value]].
 destruct (load_pipeline_real_reset_cycle (force_formal_reset 1 (Fuint 1) inputs) initial old states (Gval (Fuint 3) bits) Old Value (Logic.eq_refl _)
 ltac:(unfold force_formal_reset;cbn [formal_external_inputs];apply RegisterMapFacts.find_add_eq;reflexivity) Reset) as [env [Env Zero]].
 unfold top_environment. rewrite Env. exact Zero.
Qed.
Local Transparent generated_run.
Theorem load_pipeline_run_zero memory inputs states :
 generated_run memory inputs 0 = Some states -> load_pipeline_exact (top_environment states).
Proof.
 intro Run. destruct (instruction_run_zero memory inputs states Run) as [env [Env [Front Nop]]].
 assert (Zero : VM.find 7755 (top_environment states) = Some (Gval (Fuint 3) (from_N 3 0))).
 { unfold generated_run,formal_run_after_reset in Run.
   destruct (formal_state_after_reset generated_modules generated_top generated_reset_id generated_reset_type memory (inputs 0%nat)) as [initial|] eqn:Reset;[|discriminate].
   cbn [circuit_formal_run] in Run. inversion Run;subst states. exact (load_pipeline_after_reset memory (inputs 0%nat) initial Reset). }
 unfold top_environment in *. rewrite Env in Zero |- *. exact (load_pipeline_nop_exact env Nop Zero).
Qed.
Local Opaque generated_run.
Theorem load_pipeline_normal_successor memory inputs k observed next :
 generated_observe memory inputs k = Some observed -> generated_legal_trace memory inputs k ->
 generated_run memory inputs (S k) = Some next ->
 VM.find 1 (formal_external_inputs (generated_observation_input inputs k)) = Some (Gval (Fuint 1) [::false]) ->
 load_pipeline_exact (top_environment next).
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
 unfold top_environment. rewrite After. rewrite <- Top in Step. rewrite <- Last in Step.
 exact (load_pipeline_normal_fullhistory (generated_observation_input inputs k) nil history after Boundary Steps Resets NoTrap Step).
Qed.
Theorem load_pipeline_run memory inputs k states :
 generated_run memory inputs k = Some states -> generated_legal_trace memory inputs k -> load_pipeline_exact (top_environment states).
Proof.
 destruct k as [|k];intros Run Legal.
 - exact (load_pipeline_run_zero memory inputs states Run).
 - assert (PriorLegal : generated_legal_trace memory inputs k) by (apply (joint_legal_trace_prefix memory inputs (S k) k Legal);lia).
   destruct (legal_observation_reset memory inputs k PriorLegal) as [reset Reset].
   destruct reset.
   + pose proof Run as Next. rewrite generated_run_successor in Next.
     destruct (generated_run memory inputs k) as [previous|] eqn:Previous;[|discriminate Next].
     destruct (fetch9220_run_type memory inputs k previous Previous) as [old [value [Old Rest]]].
     destruct (joint_boundary_reachable memory inputs k previous Previous PriorLegal) as [Registers Storage].
     unfold top_environment in Registers. rewrite Old in Registers.
     destruct (Registers 7748%nat 32%nat early_bubble_front_instruction_member) as [front [FrontSize Front]].
     destruct (Registers 7750%nat 32%nat load_type_instruction_member) as [instruction [Size Instruction]].
     destruct (instruction_real_reset_cycle (generated_observation_input inputs k) previous old states
     (Gval (Fuint 32) front) (Gval (Fuint 32) instruction) Old Front (Logic.eq_refl _) Instruction (Logic.eq_refl _) Reset Next)
     as [env [Env [FrontNop Nop]]].
     destruct (Registers 7755%nat 3%nat load_type_register_member) as [mode [ModeSize Mode]].
     destruct (load_pipeline_real_reset_cycle (generated_observation_input inputs k) previous old states
      (Gval (Fuint 3) mode) Old Mode (Logic.eq_refl _) Reset Next) as [env2 [Env2 Zero]].
     rewrite Env in Env2. inversion Env2;subst env2.
     unfold top_environment. rewrite Env. exact (load_pipeline_nop_exact env Nop Zero).
   + destruct (generated_successful_commit memory inputs k states Run) as [observed [Observe Commit]].
     exact (load_pipeline_normal_successor memory inputs k observed states Observe PriorLegal Run Reset).
Qed.
Lemma load_pipeline_comb_hold invalid old current result :
 load_pipeline_exact old -> formal_value_iter invalid flat_memories old false current flat_statements = Some result -> load_pipeline_exact result.
Proof.
 intros Invariant Step instruction Instruction.
 rewrite (staged_combinational_holds_registers invalid flat_memories old current result flat_statements 7750
 (proj2 (joint_boundary_register_properties 7750 32 load_type_instruction_member)) Step) in Instruction.
 rewrite (staged_combinational_holds_registers invalid flat_memories old current result flat_statements 7755
 (proj2 (joint_boundary_register_properties 7755 3 load_type_register_member)) Step).
 exact (Invariant instruction Instruction).
Qed.
Lemma load_pipeline_history_hold invalid history (limit:nat) :
 load_pipeline_exact (history 0%nat) ->
 (forall time, (time < limit)%coq_nat -> formal_value_iter invalid flat_memories (history time) false (history time) flat_statements = Some (history (S time))) ->
 forall time, (time <= limit)%coq_nat -> load_pipeline_exact (history time).
Proof.
 intros Initial Steps time. induction time as [|time IH];intro Bound;[exact Initial|].
 exact (load_pipeline_comb_hold invalid (history time) (history time) (history (S time)) (IH ltac:(lia)) (Steps time ltac:(lia))).
Qed.
Lemma load_pipeline_prepared previous old external initial :
 SVM.find nil previous = Some old -> load_pipeline_exact old ->
 circuit_initial_map_with_memory generated_modules generated_top (Some previous) external = Some initial -> load_pipeline_exact (top_environment initial).
Proof.
 intros Previous Invariant Prepare.
 assert (Copy : forall node width, List.In (node,width) joint_boundary_registers ->
 staged_register_lookup (N.of_nat node) initial = VM.find (N.of_nat node) old).
 { intros node width Member. pose proof joint_boundary_preparation_check as Check.
   rewrite List.forallb_forall in Check. specialize (Check (node,width) Member).
   cbn [fst snd] in Check. move/andP: Check => [/andP [Safe NotClock] NotReset].
   exact (staged_prepared_register_copies previous old external initial _ NotClock NotReset Safe
   (proj2 (joint_boundary_register_properties node width Member)) Previous Prepare). }
 pose proof (Copy 7750%nat 32%nat load_type_instruction_member) as InstructionCopy.
 pose proof (Copy 7755%nat 3%nat load_type_register_member) as TypeCopy.
 intros instruction Instruction.
 unfold staged_register_lookup in InstructionCopy,TypeCopy. unfold top_environment in *.
 destruct (SVM.find nil initial) as [env|];[|discriminate Instruction].
 rewrite InstructionCopy in Instruction. rewrite TypeCopy.
 exact (Invariant instruction Instruction).
Qed.
Theorem load_pipeline_observed memory inputs k observed :
 generated_observe memory inputs k = Some observed -> generated_legal_trace memory inputs k -> load_pipeline_exact (top_environment observed).
Proof.
 intros Observe Legal. pose proof Observe as Expanded. unfold generated_observe,generated_observe_cycle in Expanded.
 destruct (generated_run memory inputs k) as [previous|] eqn:Run;[|discriminate Expanded].
 destruct (circuit_initial_map_with_memory generated_modules generated_top (Some previous) (formal_external_inputs (generated_observation_input inputs k))) as [initial|] eqn:Prepare;[|discriminate Expanded].
 pose proof flat_iteration_count_exact as Count. unfold flat_iteration_count in Count. rewrite Count in Expanded.
 destruct (local_iteration_history (generated_observation_input inputs k) 9259 initial observed Expanded) as [history [First [Last Steps]]].
 pose proof (load_pipeline_run memory inputs k previous Run Legal) as Invariant.
 destruct (fetch9220_run_type memory inputs k previous Run) as [old [value [Old Rest]]].
 unfold top_environment in Invariant. rewrite Old in Invariant.
 rewrite <- Last. eapply (load_pipeline_history_hold _ history 9259);
 [rewrite First;exact (load_pipeline_prepared previous old _ initial Old Invariant Prepare)|exact Steps|vm_compute;lia].
Qed.
Require Import ObservedJointRegisterConcrete.
Theorem load_pipeline_nonzero_observed memory inputs k observed word :
 generated_observe memory inputs k = Some observed -> generated_legal_trace memory inputs k ->
 VM.find 7755 (top_environment observed) = Some (Gval (Fuint 3) word) -> word <> from_N 3 0 ->
 exists instruction lane, (lane < 5)%coq_nat /\
 VM.find 7750 (top_environment observed) = Some (Gval (Fuint 32) instruction) /\
 load_type_is_load instruction lane /\ word = from_N 3 (load_type_lane_kind lane).
Proof.
 intros Observe Legal Mode Nonzero.
 destruct (observed_joint_register_concrete memory inputs k observed 7750%nat 32%nat Observe Legal load_type_instruction_member) as [instruction [Size Instruction]].
 pose proof (load_pipeline_observed memory inputs k observed Observe Legal instruction Instruction) as Exact.
 rewrite Mode in Exact. inversion Exact.
 destruct (load_pipeline_decode_classify (to_N instruction) 49 ltac:(lia)) as [Zero|[lane [Lane [Load Kind]]]].
 - exfalso. apply Nonzero. congruence.
 - exists instruction,lane. repeat split;try assumption;congruence.
Qed.
Require Import EarlyBubbleBitReachable EarlyBubbleNopReachable PipelineBubbleInstructionInvariant ObservedLateBubbleTransfer ObservedInstructionNormalTransfer Bubble7947Type PipelineBubbleInitialization PipelineBubbleResetBase StartupLateBubbleInvariant ObservedPipelinePCRelation.
Definition load_pipeline_late_shape env : Prop := exists bit,
 VM.find 7947 env = Some (Gval (Fuint 1) [::bit]) /\
 (bit = true -> VM.find 7750 env = Some (Gval (Fuint 32) FormalInstructionResetConstants.instruction_nop)).
Theorem load_pipeline_late_run memory inputs k states :
 generated_run memory inputs k = Some states -> generated_legal_trace memory inputs k ->
 load_pipeline_late_shape (top_environment states).
Proof.
 destruct k as [|k];intros Run Legal.
 - destruct (pipeline_bubbles_run_zero memory inputs states Run) as [env [Env [Early Late]]].
   destruct (instruction_run_zero memory inputs states Run) as [env2 [Env2 [Front Nop]]].
   rewrite Env in Env2. inversion Env2;subst env2. exists true. unfold top_environment. rewrite Env. split;[exact Late|intro;exact Nop].
 - assert (PriorLegal : generated_legal_trace memory inputs k) by (apply (joint_legal_trace_prefix memory inputs (S k) k Legal);lia).
   destruct (legal_observation_reset memory inputs k PriorLegal) as [reset Reset]. destruct reset.
   + pose proof (late_bubble_reset_successor memory inputs k states Reset Run) as Late.
     pose proof Run as Next. rewrite generated_run_successor in Next.
     destruct (generated_run memory inputs k) as [previous|] eqn:Previous;[|discriminate Next].
     destruct (fetch9220_run_type memory inputs k previous Previous) as [old [value [Old Rest]]].
     destruct (joint_boundary_reachable memory inputs k previous Previous PriorLegal) as [Registers Storage].
     unfold top_environment in Registers. rewrite Old in Registers.
     destruct (Registers 7748%nat 32%nat early_bubble_front_instruction_member) as [front [FrontSize Front]].
     destruct (Registers 7750%nat 32%nat load_type_instruction_member) as [instruction [Size Instruction]].
     destruct (instruction_real_reset_cycle (generated_observation_input inputs k) previous old states
      (Gval (Fuint 32) front) (Gval (Fuint 32) instruction) Old Front (Logic.eq_refl _) Instruction (Logic.eq_refl _) Reset Next)
      as [env [Env [FrontNop Nop]]].
     exists true. split;[exact Late|]. intro. unfold top_environment. rewrite Env. exact Nop.
   + destruct (generated_successful_commit memory inputs k states Run) as [observed [Observe Commit]].
     destruct (early_bubble_known_observation memory inputs k observed Observe PriorLegal) as [early Early].
     destruct (bubble7947_observe_type memory inputs k observed Observe) as [late [Late Typed]].
     pose proof (observed_late_bubble_normal_step memory inputs k observed states early late Observe PriorLegal Run Reset Early Late Typed) as NextLate.
     exists early. split;[exact NextLate|]. intro E. subst early.
     pose proof (early_bubble_nop_all_observations memory inputs k observed Observe PriorLegal Early) as Front.
     destruct (observed_joint_register_concrete memory inputs k observed 7750%nat 32%nat Observe PriorLegal load_type_instruction_member) as [old [Size Old]].
     exact (observed_instruction_normal_step memory inputs k observed states FormalInstructionResetConstants.instruction_nop old Observe PriorLegal Run Reset (Logic.eq_refl _) Front Old).
Qed.
Theorem load_pipeline_late_observed memory inputs k observed :
 generated_observe memory inputs k = Some observed -> generated_legal_trace memory inputs k ->
 load_pipeline_late_shape (top_environment observed).
Proof.
 intros Observe Legal. pose proof Observe as Expanded. unfold generated_observe in Expanded.
 destruct (generated_run memory inputs k) as [previous|] eqn:Run;[|discriminate Expanded].
 destruct (bubble7947_run_type memory inputs k previous Run) as [old [late [Old [Late Typed]]]].
 destruct (load_pipeline_late_run memory inputs k previous Run Legal) as [bit [Known Nop]].
 unfold top_environment in Known,Nop. rewrite Old in Known,Nop.
 pose proof (staged_observed_register_copies memory inputs k previous old observed 7947
  (Logic.eq_refl true) (Logic.eq_refl true) bubble7947_initial_safe bubble7947_present Run Old Observe) as Copy.
 unfold staged_register_lookup in Copy.
 assert (LateCopy : VM.find 7947 (top_environment observed) = VM.find 7947 old).
 { unfold top_environment. destruct (SVM.find nil observed);exact Copy. }
 exists bit. split;[rewrite LateCopy;exact Known|]. intro True.
 rewrite (observed_joint_register_copy memory inputs k previous old observed 7750%nat 32%nat load_type_instruction_member Run Old Observe).
 exact (Nop True).
Qed.
Theorem load_pipeline_load_active memory inputs k observed instruction lane :
 generated_observe memory inputs k = Some observed -> generated_legal_trace memory inputs k ->
 (lane < 5)%coq_nat -> VM.find 7750 (top_environment observed) = Some (Gval (Fuint 32) instruction) ->
 load_type_is_load instruction lane ->
 VM.find 7947 (top_environment observed) = Some (Gval (Fuint 1) [::false]).
Proof.
 intros Observe Legal Lane Instruction Load.
 destruct (load_pipeline_late_observed memory inputs k observed Observe Legal) as [bit [Late Nop]].
 destruct bit;[|exact Late]. specialize (Nop (Logic.eq_refl _)). rewrite Nop in Instruction. inversion Instruction;subst instruction.
 exfalso. exact (load_type_nop_not_load lane Lane Load).
Qed.
Require Import CheckerValidBubbleValue RFReferenceNopInputs ReferenceControlStabilityHistory.
Theorem load_pipeline_load_reference_enabled memory inputs k observed instruction lane :
 generated_observe memory inputs k = Some observed -> generated_legal_trace memory inputs k ->
 VM.find 1 (formal_external_inputs (generated_observation_input inputs k)) = Some (Gval (Fuint 1) [::false]) ->
 (lane < 5)%coq_nat -> VM.find 7750 (top_environment observed) = Some (Gval (Fuint 32) instruction) ->
 load_type_is_load instruction lane ->
 VM.find 1395 (top_environment observed) = Some (Gval (Fuint 1) [::true]) /\
 VM.find 1707 (top_environment observed) = Some (Gval (Fuint 1) [::true]).
Proof.
 intros Observe Legal Reset Lane Instruction Load.
 pose proof (load_pipeline_load_active memory inputs k observed instruction lane Observe Legal Lane Instruction Load) as Active.
 destruct (observed_legal_no_trap_history memory inputs k observed Observe Legal Reset)
 as [committed [initial [history [Run [Prepare [First [Last [Steps NoTrap]]]]]]]].
 destruct (top_reset_prepared (Some committed) _ initial _ Reset Prepare) as [env [Env InitialReset]].
 assert (Reset0 : VM.find 1 (history 0%nat) = Some (Gval (Fuint 1) [::false])).
 { rewrite First. unfold top_environment. rewrite Env. exact InitialReset. }
 pose proof (legal_local_reset_history _ history 9259 false Steps Reset0) as Resets.
 assert (Valid : VM.find 1395 (history 9259%nat) = Some (Gval (Fuint 1) [::true])).
 { exact (checker_valid_history_from_bubble _ history false Steps Resets ltac:(rewrite Last;exact Active)). }
 split;[rewrite <- Last;exact Valid|]. rewrite <- Last.
 eapply (rf_reference_enable_inputs_history _ history 9259 200);[|exact Steps|vm_compute;lia|vm_compute;lia].
 intros t Lower Upper.
 rewrite (reference_control_stable_1395_history (generated_observation_input inputs k) nil history 9259 false Resets Steps t 9259%nat ltac:(lia) ltac:(lia) Upper ltac:(lia)).
 exact Valid.
Qed.
