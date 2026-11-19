Require Import ComparisonConstantBitShape EarlyControlWireBitNormalization UIntMuxResultType NopBranchShapes NormalizedBit DelayedRedirectNodes JointRegisterCommits8 RFNonAluBubbleHazard StagedRegisterHold RegisterInvariants PipelineRedirectPhase RFNonAluReset CoreSocModel ComparisonNodes JointUpdateNodePositions JointUpdateExpressionCertificates ReferenceRedirectSpine FormalCheckerResetConnections ExceptionEventHistory.
From nbits Require Import NBits.
From Coq Require Import NArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Theorem pipeline_reset_flush_four invalid s0 s1 s2 s3 s4 :
 VM.find 1 s0 = Some (Gval (Fuint 1) [::true]) ->
 formal_value_iter invalid flat_memories s0 false s0 flat_statements = Some s1 ->
 formal_value_iter invalid flat_memories s1 false s1 flat_statements = Some s2 ->
 formal_value_iter invalid flat_memories s2 false s2 flat_statements = Some s3 ->
 formal_value_iter invalid flat_memories s3 false s3 flat_statements = Some s4 ->
 VM.find 7852 s4 = Some (Gval (Fuint 1) [::true]).
Proof. intros Reset S1 S2 S3 S4.
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
 exact Flush. Qed.

Lemma pipeline_delayed_present : has_register 7760 flat_statements = true.
Proof. vm_compute;reflexivity. Qed.
Lemma pipeline_delayed_hold invalid old result :
 formal_value_iter invalid flat_memories old false old flat_statements = Some result ->
 VM.find 7760 result = VM.find 7760 old.
Proof. apply staged_combinational_holds_registers. exact pipeline_delayed_present. Qed.
Lemma pipeline_reset_jump_normalized invalid old result :
 formal_value_iter invalid flat_memories old false old flat_statements = Some result ->
 exists value, VM.find 7858 result = Some value /\ normalized_bit value.
Proof.
 intro Step. eapply (nop_branch_node_shape 7858 joint_update_expr_7858 normalized_bit invalid old old result).
 - exact delayed_redirect_member_7858.
 - intros site value Eval. cbn [joint_update_expr_7858 eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
   destruct (VM.find 84 old) as [source|];[|discriminate]. eapply comparison_uint_constant_right_normalized;exact Eval.
 - exact nop_branch_normalized_type.
 - exact Step.
Qed.
Lemma pipeline_reset_redirect_normalized invalid s0 s1 s2 :
 formal_value_iter invalid flat_memories s0 false s0 flat_statements = Some s1 ->
 formal_value_iter invalid flat_memories s1 false s1 flat_statements = Some s2 ->
 exists value, VM.find 7859 s2 = Some value /\ normalized_bit value.
Proof.
 intros S1 S2. destruct (pipeline_reset_jump_normalized invalid s0 s1 S1) as [jump [Jump JN]].
 destruct (early_control_wire_1360_normalized invalid s0 s0 s1 S1) as [branch [Branch BN]].
 eapply (nop_branch_node_shape 7859 joint_update_expr_7859 normalized_bit invalid s1 s1 s2).
 - exact delayed_redirect_member_7859.
 - intros site value Eval. cbn [joint_update_expr_7859 eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
   rewrite Jump Branch in Eval. destruct JN as [a| | |];destruct BN as [b| | |];try destruct a;try destruct b;
   vm_compute in Eval;inversion Eval;constructor.
 - exact nop_branch_normalized_type.
 - exact S2.
Qed.
Local Lemma pipeline_reset_selected_type invalid old result left right :
 VM.find 7859 old = Some left -> type_of_val left = Gtyp (Fuint 1) ->
 VM.find 7760 old = Some right -> type_of_val right = Gtyp (Fuint 1) ->
 formal_value_iter invalid flat_memories old false old flat_statements = Some result ->
 exists value, VM.find 7870 result = Some value /\ type_of_val value = Gtyp (Fuint 1).
Proof.
 intros Left LT Right RT Step. eapply (nop_branch_node_shape 7870 joint_update_expr_7870 (fun value => type_of_val value = Gtyp (Fuint 1)) invalid old old result).
 - apply (List.nth_error_In joint_update_expected_nodes 925%nat). vm_compute. reflexivity.
 - intros site value Eval.
   change (eval_hfexpr_with_memory flat_memories (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 7855)) (@Eref VarOrder.T (@Eid VarOrder.T 7859)) (@Eref VarOrder.T (@Eid VarOrder.T 7760))) old old = Some value) in Eval.
   eapply uint_mux_result_type; [exact Left|exact LT|exact Right|exact RT|exact Eval].
 - intros value Typed. exact Typed.
 - exact Step.
Qed.
Theorem pipeline_delayed_reset_after_five invalid s0 s1 s2 s3 s4 s5 result old_value :
 VM.find 7760 s0 = Some old_value -> type_of_val old_value = Gtyp (Fuint 1) ->
 VM.find 1 s0 = Some (Gval (Fuint 1) [::true]) ->
 formal_value_iter invalid flat_memories s0 false s0 flat_statements = Some s1 ->
 formal_value_iter invalid flat_memories s1 false s1 flat_statements = Some s2 ->
 formal_value_iter invalid flat_memories s2 false s2 flat_statements = Some s3 ->
 formal_value_iter invalid flat_memories s3 false s3 flat_statements = Some s4 ->
 formal_value_iter invalid flat_memories s4 false s4 flat_statements = Some s5 ->
 formal_value_iter invalid flat_memories s5 true s5 flat_statements = Some result ->
 VM.find 7760 result = Some (Gval (Fuint 1) [::false]).
Proof.
 intros Old Typed Reset S1 S2 S3 S4 S5 Commit.
 pose proof (pipeline_reset_flush_four invalid s0 s1 s2 s3 s4 Reset S1 S2 S3 S4) as Flush.
 assert (Old3 : VM.find 7760 s3 = Some old_value).
 { rewrite (pipeline_delayed_hold invalid s2 s3 S3) (pipeline_delayed_hold invalid s1 s2 S2) (pipeline_delayed_hold invalid s0 s1 S1). exact Old. }
 destruct (pipeline_reset_redirect_normalized invalid s1 s2 s3 S2 S3) as [enable [Enable ENormal]].
 destruct (pipeline_reset_selected_type invalid s3 s4 enable old_value Enable (nop_branch_normalized_type enable ENormal) Old3 Typed S4) as [selected [Selected ST]].
 assert (Zero : VM.find 7876 s5 = Some (Gval (Fuint 1) [::false])).
 { eapply (reference_redirect_ground_step joint_update_node_offsets joint_update_expected_nodes 7876 joint_update_expr_7876);
   [exact joint_update_node_positions|exact joint_update_node_safety| | |exact S5].
   - apply (List.nth_error_In joint_update_expected_nodes 931%nat). vm_compute. reflexivity.
   - intros site. cbn [joint_update_expr_7876 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Flush.
     cbn [is_zero]. unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref]. rewrite Selected. cbn [option_map]. rewrite ST. reflexivity. }
 assert (Old5 : VM.find 7760 s5 = Some old_value).
 { rewrite (pipeline_delayed_hold invalid s4 s5 S5) (pipeline_delayed_hold invalid s3 s4 S4). exact Old3. }
 eapply (rf_control_direct_commit_exact 8266 flat_statements joint_register_7760_decl joint_register_7760_mid joint_register_7760_tail 7760 7876 joint_register_7760_reg 1 [::false] old_value invalid flat_memories s5 s5 result);
 [exact joint_register_7760_position|exact joint_register_7760_split|exact joint_register_7760_straight|exact joint_register_7760_mid_safe|exact joint_register_7760_tail_safe|exact joint_register_7760_identity|exact Old5|exact Typed|reflexivity|exact Zero|reflexivity|exact Commit].
Qed.
Require Import StagedFlatCircuitIteration StagedIterationCount StagedObservedRegister StagedCircuitRegisterHold RegisterPreparationFrames FormalLocalHistory FormalResetTrace FormalResetPreparation ObservedLegalNoTrap.
Theorem pipeline_delayed_reset_fullhistory invalid history result old_value :
 VM.find 7760 (history 0%nat) = Some old_value -> type_of_val old_value = Gtyp (Fuint 1) ->
 VM.find 1 (history 0%nat) = Some (Gval (Fuint 1) [::true]) ->
 (forall time, (time < 9259)%coq_nat -> formal_value_iter invalid flat_memories (history time) false (history time) flat_statements = Some (history (S time))) ->
 formal_value_iter invalid flat_memories (history 9259%nat) true (history 9259%nat) flat_statements = Some result ->
 VM.find 7760 result = Some (Gval (Fuint 1) [::false]).
Proof.
 intros Old Typed Reset Steps Commit.
 pose proof (legal_local_reset_history invalid history 9259 true Steps Reset) as Resets.
 assert (Hold : forall time, (time <= 9259)%coq_nat -> VM.find 7760 (history time) = Some old_value).
 { intros time Bound. induction time as [|time IH]; [exact Old|].
   rewrite (pipeline_delayed_hold invalid (history time) (history (S time)) (Steps time ltac:(lia))). apply IH. lia. }
 exact (pipeline_delayed_reset_after_five invalid (history 9254%nat) (history 9255%nat) (history 9256%nat) (history 9257%nat) (history 9258%nat) (history 9259%nat) result old_value
 (Hold 9254%nat ltac:(vm_compute;lia)) Typed (Resets 9254%nat ltac:(vm_compute;lia))
 (Steps 9254%nat ltac:(vm_compute;lia)) (Steps 9255%nat ltac:(vm_compute;lia)) (Steps 9256%nat ltac:(vm_compute;lia)) (Steps 9257%nat ltac:(vm_compute;lia)) (Steps 9258%nat ltac:(vm_compute;lia)) Commit).
Qed.
Lemma pipeline_delayed_reset_initial_safe : initial_register_safe 7760 flat_statements.
Proof. vm_compute. reflexivity. Qed.
Theorem pipeline_delayed_settle_reset_commit inputs initial stable result old_value :
 state_reset initial true -> staged_register_lookup 7760 initial = Some old_value -> type_of_val old_value = Gtyp (Fuint 1) ->
 circuit_formal_iterations generated_modules generated_top inputs 9259 initial = Some stable ->
 formal_circuit_value_iter (formal_invalid_policy inputs) generated_modules generated_top stable true = Some result ->
 exists env, SVM.find nil result = Some env /\ VM.find 7760 env = Some (Gval (Fuint 1) [::false]).
Proof.
 intros [start [Start Reset]] Old Typed Iterations Commit.
 destruct (local_iteration_history inputs 9259 initial stable Iterations) as [history [First [Last Steps]]].
 assert (Reset0 : VM.find 1 (history 0%nat) = Some (Gval (Fuint 1) [::true])).
 { rewrite First. unfold top_environment. rewrite Start. exact Reset. }
 assert (Old0 : VM.find 7760 (history 0%nat) = Some old_value).
 { rewrite First. unfold top_environment. rewrite Start. unfold staged_register_lookup in Old. rewrite Start in Old. exact Old. }
 destruct (flat_iteration_projection (formal_invalid_policy inputs) stable true result Commit) as [before [after [Before [Local After]]]].
 assert (Same : history 9259%nat = before).
 { rewrite Last. unfold top_environment. rewrite Before. reflexivity. }
 exists after. split; [exact After|].
 eapply (pipeline_delayed_reset_fullhistory (formal_invalid_policy inputs nil) history after old_value); [exact Old0|exact Typed|exact Reset0|exact Steps|].
 rewrite Same. exact Local.
Qed.
Theorem pipeline_delayed_real_reset_cycle inputs previous old result old_value :
 SVM.find nil previous = Some old -> VM.find 7760 old = Some old_value -> type_of_val old_value = Gtyp (Fuint 1) ->
 VM.find 1 (formal_external_inputs inputs) = Some (Gval (Fuint 1) [::true]) ->
 circuit_formal_cycle generated_modules generated_top (Some previous) inputs = Some result ->
 exists env, SVM.find nil result = Some env /\ VM.find 7760 env = Some (Gval (Fuint 1) [::false]).
Proof.
 intros Previous Old Typed Reset Cycle. unfold circuit_formal_cycle in Cycle.
 destruct (circuit_initial_map_with_memory generated_modules generated_top (Some previous) (formal_external_inputs inputs)) as [initial|] eqn:Prepare; [|discriminate Cycle].
 pose proof flat_iteration_count_exact as Count. unfold flat_iteration_count in Count. rewrite Count in Cycle.
 destruct (circuit_formal_iterations generated_modules generated_top inputs 9259 initial) as [stable|] eqn:Iterations; [|discriminate Cycle].
 apply (pipeline_delayed_settle_reset_commit inputs initial stable result old_value); try assumption.
 - exact (top_reset_prepared (Some previous) _ initial _ Reset Prepare).
 - rewrite (staged_prepared_register_copies previous old _ initial 7760 (Logic.eq_refl _) (Logic.eq_refl _) pipeline_delayed_reset_initial_safe pipeline_delayed_present Previous Prepare). exact Old.
Qed.
Require Import JointBoundaryInitialization JointBoundaryReachable JointBoundaryInduction JointBoundaryRegisters ExternalReset FormalObservationCommit.
From firrtl Require Import FormalInitialization.
Lemma pipeline_delayed_member : List.In (7760%nat,1%nat) joint_boundary_registers.
Proof. apply (List.nth_error_In joint_boundary_registers 65%nat);vm_compute;reflexivity. Qed.
Theorem pipeline_delayed_after_formal_reset memory inputs states :
 formal_state_after_reset generated_modules generated_top 1 (Fuint 1) memory inputs = Some states ->
 exists env, SVM.find nil states = Some env /\ VM.find 7760 env = Some (Gval (Fuint 1) [::false]).
Proof.
 unfold formal_state_after_reset.
 destruct (circuit_symbolic_initial_state generated_modules generated_top memory inputs) as [initial|] eqn:Init;[|discriminate].
 intro Reset. destruct (joint_boundary_symbolic_initial memory inputs initial Init) as [Registers Storage].
 destruct (Registers 7760%nat 1%nat pipeline_delayed_member) as [bits [Size Value]].
 unfold top_environment in Value. destruct (SVM.find nil initial) as [old|] eqn:Old;[|discriminate Value].
 apply (pipeline_delayed_real_reset_cycle (force_formal_reset 1 (Fuint 1) inputs) initial old states (Gval (Fuint 1) bits));try assumption;try reflexivity.
 unfold force_formal_reset;cbn [formal_external_inputs]. apply RegisterMapFacts.find_add_eq;reflexivity.
Qed.
Theorem pipeline_delayed_run_zero memory inputs states :
 generated_run memory inputs 0 = Some states ->
 exists env, SVM.find nil states = Some env /\ VM.find 7760 env = Some (Gval (Fuint 1) [::false]).
Proof.
 unfold generated_run,formal_run_after_reset.
 destruct (formal_state_after_reset generated_modules generated_top generated_reset_id generated_reset_type memory (inputs 0%nat)) as [initial|] eqn:Reset;[|discriminate].
 cbn [circuit_formal_run]. intro Run;inversion Run;subst states.
 exact (pipeline_delayed_after_formal_reset memory (inputs 0%nat) initial Reset).
Qed.
Theorem pipeline_late_redirect_phase_reachable memory inputs k states :
 generated_run memory inputs k = Some states -> generated_legal_trace memory inputs k ->
 pipeline_late_redirect_phase (top_environment states).
Proof.
 destruct k as [|k];intros Run Legal.
 - destruct (pipeline_delayed_run_zero memory inputs states Run) as [env [Env Clear]].
   unfold pipeline_late_redirect_phase,top_environment;rewrite Env. intro Taken;rewrite Clear in Taken;discriminate.
 - assert (PriorLegal : generated_legal_trace memory inputs k).
   { apply (joint_legal_trace_prefix memory inputs (S k) k Legal);lia. }
   destruct (legal_observation_reset memory inputs k PriorLegal) as [reset Reset]. destruct reset.
   + pose proof Run as Next. rewrite generated_run_successor in Next.
     destruct (generated_run memory inputs k) as [previous|] eqn:Previous;[|discriminate Next].
     destruct (joint_boundary_reachable memory inputs k previous Previous PriorLegal) as [Registers Storage].
     destruct (Registers 7760%nat 1%nat pipeline_delayed_member) as [bits [Size Value]].
     unfold top_environment in Value. destruct (SVM.find nil previous) as [old|] eqn:Old;[|discriminate Value].
     destruct (pipeline_delayed_real_reset_cycle (generated_observation_input inputs k) previous old states (Gval (Fuint 1) bits) Old Value (Logic.eq_refl _) Reset Next) as [env [Env Clear]].
     unfold pipeline_late_redirect_phase,top_environment;rewrite Env. intro Taken;rewrite Clear in Taken;discriminate.
   + destruct (generated_successful_commit memory inputs k states Run) as [observed [Observe Commit]].
     exact (pipeline_normal_redirect_phase memory inputs k observed states Observe PriorLegal Run Reset).
Qed.
Require Import DelayedDUTRedirectSemantics Bubble7945Type PipelineBubbleInitialization.
Theorem pipeline_late_redirect_phase_observed memory inputs k observed :
 generated_observe memory inputs k = Some observed -> generated_legal_trace memory inputs k ->
 pipeline_late_redirect_phase (top_environment observed).
Proof.
 intros Observe Legal. pose proof Observe as Expanded. unfold generated_observe in Expanded.
 destruct (generated_run memory inputs k) as [previous|] eqn:Run;[|discriminate Expanded].
 pose proof (pipeline_late_redirect_phase_reachable memory inputs k previous Run Legal) as Phase.
 pose proof (delayed_joint_observed_copy memory inputs k previous observed 7760 1 pipeline_delayed_member Run Observe) as Flag.
 pose proof (delayed_joint_observed_copy memory inputs k previous observed 7752 32
 ltac:(apply (List.nth_error_In joint_boundary_registers 57%nat);vm_compute;reflexivity) Run Observe) as ALU.
 pose proof (delayed_joint_observed_copy memory inputs k previous observed 7768 33
 ltac:(apply (List.nth_error_In joint_boundary_registers 67%nat);vm_compute;reflexivity) Run Observe) as Fetch.
 destruct (bubble7945_run_type memory inputs k previous Run) as [old [value [Old [Value Typed]]]].
 pose proof (staged_observed_register_copies memory inputs k previous old observed 7945
 (Logic.eq_refl true) (Logic.eq_refl true) bubble7945_initial_safe bubble7945_present Run Old Observe) as Copy.
 assert (Bubble : VM.find 7945 (top_environment observed) = VM.find 7945 (top_environment previous)).
 { unfold staged_register_lookup in Copy. unfold top_environment;rewrite Old.
   destruct (SVM.find nil observed);[exact Copy|]. rewrite Value in Copy;discriminate. }
 unfold pipeline_late_redirect_phase in *.
 change (VM.find 7760 (top_environment observed) = VM.find 7760 (top_environment previous)) in Flag.
 change (VM.find 7752 (top_environment observed) = VM.find 7752 (top_environment previous)) in ALU.
 change (VM.find 7768 (top_environment observed) = VM.find 7768 (top_environment previous)) in Fetch.
 rewrite Flag ALU Fetch Bubble. exact Phase.
Qed.
