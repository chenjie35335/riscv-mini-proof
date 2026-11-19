Require Import CoreSocModel ComparisonNodes RFNonAluBubbleHazard JointRegisterCommits7 JointUpdateNodePositions JointUpdateExpressionCertificates JointUpdateConnectionCertificates NopBranchShapes ExceptionEventHistory NormalizedBit UIntMuxResultType FormalDeclaredConnectionObservation FormalCheckerResetConnections FormalRFResetConnections ReferenceRedirectSpine StagedRegisterHold RegisterInvariants.
From Coq Require Import ZArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From nbits Require Import NBits.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Lemma rf_nonalu_reset_register_present : has_register 7757 flat_statements = true.
Proof. vm_compute. reflexivity. Qed.
Local Lemma rf_reset_7757_hold invalid old result :
 formal_value_iter invalid flat_memories old false old flat_statements = Some result ->
 VM.find 7757 result = VM.find 7757 old.
Proof. apply staged_combinational_holds_registers. exact rf_nonalu_reset_register_present. Qed.
Local Lemma rf_reset_compare_normalized invalid old result :
 formal_value_iter invalid flat_memories old false old flat_statements = Some result ->
 exists value, VM.find 7850 result = Some value /\ normalized_bit value.
Proof.
 intro Step. eapply (nop_branch_node_shape 7850 joint_update_expr_7850 normalized_bit invalid old old result).
 - apply (List.nth_error_In joint_update_expected_nodes 905%nat). vm_compute. reflexivity.
 - intros site value Eval. cbn [joint_update_expr_7850 eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
   destruct (VM.find 7765 old) as [source|]; [|discriminate]. eapply nop_branch_comparison_false_normalized;exact Eval.
 - exact nop_branch_normalized_type.
 - exact Step.
Qed.
Local Lemma rf_reset_mask_normalized invalid old result left right :
 VM.find 7850 old = Some left -> normalized_bit left ->
 VM.find 128 old = Some right -> normalized_bit right ->
 formal_value_iter invalid flat_memories old false old flat_statements = Some result ->
 exists value, VM.find 7851 result = Some value /\ normalized_bit value.
Proof.
 intros Left LN Right RN Step. eapply (nop_branch_node_shape 7851 joint_update_expr_7851 normalized_bit invalid old old result).
 - apply (List.nth_error_In joint_update_expected_nodes 906%nat). vm_compute. reflexivity.
 - intros site value Eval. cbn [joint_update_expr_7851 eval_hfexpr_validif_policy eval_href_validif_policy] in Eval. rewrite Left Right in Eval.
   destruct LN as [a| | |]; destruct RN as [b| | |]; try destruct a; try destruct b;
   vm_compute in Eval; inversion Eval; constructor.
 - exact nop_branch_normalized_type.
 - exact Step.
Qed.
Local Lemma rf_reset_94_normalized invalid old result :
 formal_value_iter invalid flat_memories old false old flat_statements = Some result ->
 exists value, VM.find 94 result = Some value /\ normalized_bit value.
Proof.
 intro Step.
 destruct (declared_connection_observation 71 flat_statements joint_update_connection_94_decl joint_update_connection_94_mid joint_update_connection_94_tail
 94 8260 1 invalid flat_memories old old result joint_update_connection_94_position joint_update_connection_94_split joint_update_connection_94_straight joint_update_connection_94_mid_safe joint_update_connection_94_tail_safe joint_update_connection_94_nonregister (Logic.eq_refl _) Step) as [source [value [Source [Adapt Value]]]].
 exists value. split; [exact Value|eapply adapted_bit_normalized;exact Adapt].
Qed.
Local Lemma rf_reset_selected_type invalid old result left right :
 VM.find 94 old = Some left -> type_of_val left = Gtyp (Fuint 1) ->
 VM.find 7757 old = Some right -> type_of_val right = Gtyp (Fuint 1) ->
 formal_value_iter invalid flat_memories old false old flat_statements = Some result ->
 exists value, VM.find 7867 result = Some value /\ type_of_val value = Gtyp (Fuint 1).
Proof.
 intros Left LT Right RT Step. eapply (nop_branch_node_shape 7867 joint_update_expr_7867 (fun value => type_of_val value = Gtyp (Fuint 1)) invalid old old result).
 - apply (List.nth_error_In joint_update_expected_nodes 922%nat). vm_compute. reflexivity.
 - intros site value Eval.
   change (eval_hfexpr_with_memory flat_memories (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 7855)) (@Eref VarOrder.T (@Eid VarOrder.T 94)) (@Eref VarOrder.T (@Eid VarOrder.T 7757))) old old = Some value) in Eval.
   eapply uint_mux_result_type; [exact Left|exact LT|exact Right|exact RT|exact Eval].
 - intros value Typed. exact Typed.
 - exact Step.
Qed.
Theorem rf_nonalu_reset_after_five invalid s0 s1 s2 s3 s4 s5 result old_value :
 VM.find 7757 s0 = Some old_value -> type_of_val old_value = Gtyp (Fuint 1) ->
 VM.find 1 s0 = Some (Gval (Fuint 1) [::true]) ->
 formal_value_iter invalid flat_memories s0 false s0 flat_statements = Some s1 ->
 formal_value_iter invalid flat_memories s1 false s1 flat_statements = Some s2 ->
 formal_value_iter invalid flat_memories s2 false s2 flat_statements = Some s3 ->
 formal_value_iter invalid flat_memories s3 false s3 flat_statements = Some s4 ->
 formal_value_iter invalid flat_memories s4 false s4 flat_statements = Some s5 ->
 formal_value_iter invalid flat_memories s5 true s5 flat_statements = Some result ->
 VM.find 7757 result = Some (Gval (Fuint 1) [::false]).
Proof.
 intros Old Typed Reset S1 S2 S3 S4 S5 Commit.
 pose proof (reset_connection_24_transfer invalid s0 s0 s1 true Reset S1) as R24.
 pose proof (reset_connection_65_transfer invalid s1 s1 s2 true R24 S2) as R65.
 assert (R7849 : VM.find 7849 s3 = Some (Gval (Fuint 1) [::true])).
 { eapply (reference_redirect_ground_step joint_update_node_offsets joint_update_expected_nodes 7849 joint_update_expr_7849);
   [exact joint_update_node_positions|exact joint_update_node_safety| | |exact S3].
   - apply (List.nth_error_In joint_update_expected_nodes 904%nat). vm_compute. reflexivity.
   - intros site. cbn [joint_update_expr_7849 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite R65. reflexivity. }
 destruct (rf_reset_compare_normalized invalid s1 s2 S2) as [compare [Compare CN]].
 destruct (exception_source128_normalized invalid s1 s1 s2 S2) as [exception [Exception EN]].
 destruct (rf_reset_mask_normalized invalid s2 s3 compare exception Compare CN Exception EN S3) as [masked [Masked MN]].
 assert (Flush : VM.find 7852 s4 = Some (Gval (Fuint 1) [::true])).
 { eapply (reference_redirect_ground_step joint_update_node_offsets joint_update_expected_nodes 7852 joint_update_expr_7852);
   [exact joint_update_node_positions|exact joint_update_node_safety| | |exact S4].
   - apply (List.nth_error_In joint_update_expected_nodes 907%nat). vm_compute. reflexivity.
   - intros site. cbn [joint_update_expr_7852 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite R7849 Masked.
     destruct MN as [bit| | |]; try destruct bit; reflexivity. }
 assert (Old3 : VM.find 7757 s3 = Some old_value).
 { rewrite (rf_reset_7757_hold invalid s2 s3 S3) (rf_reset_7757_hold invalid s1 s2 S2) (rf_reset_7757_hold invalid s0 s1 S1). exact Old. }
 destruct (rf_reset_94_normalized invalid s2 s3 S3) as [enable [Enable ENormal]].
 destruct (rf_reset_selected_type invalid s3 s4 enable old_value Enable (nop_branch_normalized_type enable ENormal) Old3 Typed S4) as [selected [Selected ST]].
 assert (Zero : VM.find 7873 s5 = Some (Gval (Fuint 1) [::false])).
 { eapply (reference_redirect_ground_step joint_update_node_offsets joint_update_expected_nodes 7873 joint_update_expr_7873);
   [exact joint_update_node_positions|exact joint_update_node_safety| | |exact S5].
   - apply (List.nth_error_In joint_update_expected_nodes 928%nat). vm_compute. reflexivity.
   - intros site. cbn [joint_update_expr_7873 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Flush.
     cbn [is_zero]. unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref]. rewrite Selected. cbn [option_map]. rewrite ST. reflexivity. }
 assert (Old5 : VM.find 7757 s5 = Some old_value).
 { rewrite (rf_reset_7757_hold invalid s4 s5 S5) (rf_reset_7757_hold invalid s3 s4 S4). exact Old3. }
 eapply (rf_control_direct_commit_exact 8263 flat_statements joint_register_7757_decl joint_register_7757_mid joint_register_7757_tail 7757 7873 joint_register_7757_reg 1 [::false] old_value invalid flat_memories s5 s5 result);
 [exact joint_register_7757_position|exact joint_register_7757_split|exact joint_register_7757_straight|exact joint_register_7757_mid_safe|exact joint_register_7757_tail_safe|exact joint_register_7757_identity|exact Old5|exact Typed|reflexivity|exact Zero|reflexivity|exact Commit].
Qed.
Require Import StagedFlatCircuitIteration StagedIterationCount StagedObservedRegister StagedCircuitRegisterHold RegisterPreparationFrames FormalLocalHistory FormalResetTrace FormalResetPreparation ObservedLegalNoTrap.
Theorem rf_nonalu_reset_fullhistory invalid history result old_value :
 VM.find 7757 (history 0%nat) = Some old_value -> type_of_val old_value = Gtyp (Fuint 1) ->
 VM.find 1 (history 0%nat) = Some (Gval (Fuint 1) [::true]) ->
 (forall time, (time < 9259)%coq_nat -> formal_value_iter invalid flat_memories (history time) false (history time) flat_statements = Some (history (S time))) ->
 formal_value_iter invalid flat_memories (history 9259%nat) true (history 9259%nat) flat_statements = Some result ->
 VM.find 7757 result = Some (Gval (Fuint 1) [::false]).
Proof.
 intros Old Typed Reset Steps Commit.
 pose proof (legal_local_reset_history invalid history 9259 true Steps Reset) as Resets.
 assert (Hold : forall time, (time <= 9259)%coq_nat -> VM.find 7757 (history time) = Some old_value).
 { intros time Bound. induction time as [|time IH]; [exact Old|].
   rewrite (rf_reset_7757_hold invalid (history time) (history (S time)) (Steps time ltac:(lia))). apply IH. lia. }
 exact (rf_nonalu_reset_after_five invalid (history 9254%nat) (history 9255%nat) (history 9256%nat) (history 9257%nat) (history 9258%nat) (history 9259%nat) result old_value
 (Hold 9254%nat ltac:(vm_compute;lia)) Typed (Resets 9254%nat ltac:(vm_compute;lia))
 (Steps 9254%nat ltac:(vm_compute;lia)) (Steps 9255%nat ltac:(vm_compute;lia)) (Steps 9256%nat ltac:(vm_compute;lia)) (Steps 9257%nat ltac:(vm_compute;lia)) (Steps 9258%nat ltac:(vm_compute;lia)) Commit).
Qed.
Lemma rf_nonalu_reset_initial_safe : initial_register_safe 7757 flat_statements.
Proof. vm_compute. reflexivity. Qed.
Theorem rf_nonalu_settle_reset_commit inputs initial stable result old_value :
 state_reset initial true -> staged_register_lookup 7757 initial = Some old_value -> type_of_val old_value = Gtyp (Fuint 1) ->
 circuit_formal_iterations generated_modules generated_top inputs 9259 initial = Some stable ->
 formal_circuit_value_iter (formal_invalid_policy inputs) generated_modules generated_top stable true = Some result ->
 exists env, SVM.find nil result = Some env /\ VM.find 7757 env = Some (Gval (Fuint 1) [::false]).
Proof.
 intros [start [Start Reset]] Old Typed Iterations Commit.
 destruct (local_iteration_history inputs 9259 initial stable Iterations) as [history [First [Last Steps]]].
 assert (Reset0 : VM.find 1 (history 0%nat) = Some (Gval (Fuint 1) [::true])).
 { rewrite First. unfold top_environment. rewrite Start. exact Reset. }
 assert (Old0 : VM.find 7757 (history 0%nat) = Some old_value).
 { rewrite First. unfold top_environment. rewrite Start. unfold staged_register_lookup in Old. rewrite Start in Old. exact Old. }
 destruct (flat_iteration_projection (formal_invalid_policy inputs) stable true result Commit) as [before [after [Before [Local After]]]].
 assert (Same : history 9259%nat = before).
 { rewrite Last. unfold top_environment. rewrite Before. reflexivity. }
 exists after. split; [exact After|].
 eapply (rf_nonalu_reset_fullhistory (formal_invalid_policy inputs nil) history after old_value); [exact Old0|exact Typed|exact Reset0|exact Steps|].
 rewrite Same. exact Local.
Qed.
Theorem rf_nonalu_real_reset_cycle inputs previous old result old_value :
 SVM.find nil previous = Some old -> VM.find 7757 old = Some old_value -> type_of_val old_value = Gtyp (Fuint 1) ->
 VM.find 1 (formal_external_inputs inputs) = Some (Gval (Fuint 1) [::true]) ->
 circuit_formal_cycle generated_modules generated_top (Some previous) inputs = Some result ->
 exists env, SVM.find nil result = Some env /\ VM.find 7757 env = Some (Gval (Fuint 1) [::false]).
Proof.
 intros Previous Old Typed Reset Cycle. unfold circuit_formal_cycle in Cycle.
 destruct (circuit_initial_map_with_memory generated_modules generated_top (Some previous) (formal_external_inputs inputs)) as [initial|] eqn:Prepare; [|discriminate Cycle].
 pose proof flat_iteration_count_exact as Count. unfold flat_iteration_count in Count. rewrite Count in Cycle.
 destruct (circuit_formal_iterations generated_modules generated_top inputs 9259 initial) as [stable|] eqn:Iterations; [|discriminate Cycle].
 apply (rf_nonalu_settle_reset_commit inputs initial stable result old_value); try assumption.
 - exact (top_reset_prepared (Some previous) _ initial _ Reset Prepare).
 - rewrite (staged_prepared_register_copies previous old _ initial 7757 (Logic.eq_refl _) (Logic.eq_refl _) rf_nonalu_reset_initial_safe rf_nonalu_reset_register_present Previous Prepare). exact Old.
Qed.
