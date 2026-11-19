Require Import CoreSocModel ComparisonNodes ReferenceRedirectSpine ReferenceRedirectSemantics
 JointUpdateNodePositions JointUpdateExpressionCertificates JointUpdateConnectionCertificates
 FormalSuccessfulNodeEvaluation FormalTypedNodeEquation SelectedNodeSafety SelectedUIntMuxIdentity
 FormalDeclaredConnection JointRegisterCommits7 JointRegisterExpressionCertificates
 FormalRegisterMuxObservation FormalRegisterCommitIdentity FalseUIntMuxIdentity.
From Coq Require Import NArith ZArith Lia List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBitsDef NBitsOp.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths
 Firrtl_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
(* AluArea selects sum for ADD/SUB. Successful evaluation supplies the
   unselected branch's type; only the selected 32-bit word is constrained. *)
Lemma alu_selected_mux_node node condition yes no invalid old current result width bits :
 List.In (node,@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T condition))
   (@Eref VarOrder.T (@Eid VarOrder.T yes)) (@Eref VarOrder.T (@Eid VarOrder.T no))) joint_update_expected_nodes ->
 VM.find condition old = Some (Gval (Fuint 1) [::true]) ->
 VM.find yes old = Some (Gval (Fuint width) bits) ->
 size bits = width ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value, VM.find node result = Some value /\
 adapt_hvalue_as_type value (Gtyp (Fuint width)) = Some (Gval (Fuint width) bits).
Proof.
 intros Member Condition Yes Size Step.
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes node _
   joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 destruct (formal_successful_node_evaluation count flat_statements tail node _ invalid flat_memories old false current result Position Step) as [value Eval].
 pose proof Eval as Original.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval. rewrite Condition in Eval. cbn in Eval. rewrite Yes in Eval.
 destruct (eval_type_of_expr (@Eref VarOrder.T (@Eid VarOrder.T no)) old) as [typ|] eqn:BranchType; [|discriminate].
 unfold extend_hvalue_as_type in Eval.
 destruct typ as [ground|elt length|fields]; try discriminate.
 destruct ground; cbn [type_of_val ftype_mux fgtyp_mux option_map adapt_hvalue_as_type] in Eval; try discriminate.
 inversion Eval; subst value.
 eexists. split.
 - eapply formal_combinational_known_node;
   [exact Position|exact Safe|exact Nonreg|exact Original|reflexivity|exact Step].
 - cbn [adapt_hvalue_as_type]. f_equal. f_equal.
   apply resize_uint_roundtrip; [exact Size|apply leq_maxl].
Qed.

Theorem alu_output_add_history invalid s0 s1 s2 s3 s4 word :
 size word = 32%nat ->
 VM.find 1153 s0 = Some (Gval (Fuint 4) [::false;false;false;false]) ->
 VM.find 1161 s2 = Some (Gval (Fuint 32) word) ->
 formal_value_iter invalid flat_memories s0 false s0 flat_statements = Some s1 ->
 formal_value_iter invalid flat_memories s1 false s1 flat_statements = Some s2 ->
 formal_value_iter invalid flat_memories s2 false s2 flat_statements = Some s3 ->
 formal_value_iter invalid flat_memories s3 false s3 flat_statements = Some s4 ->
 VM.find 1154 s4 = Some (Gval (Fuint 32) word).
Proof.
 intros Size Mode Sum S1 S2 S3 S4.
 assert (H1279 : VM.find 1279 s1 = Some (Gval (Fuint 1) [::true])).
 { eapply (reference_redirect_ground_step joint_update_node_offsets joint_update_expected_nodes 1279 joint_update_expr_1279);
 [exact joint_update_node_positions|exact joint_update_node_safety|apply (List.nth_error_In joint_update_expected_nodes 824%nat); vm_compute;reflexivity| |exact S1].
 intros site. cbn [joint_update_expr_1279 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Mode. reflexivity. }
 assert (H1280 : VM.find 1280 s1 = Some (Gval (Fuint 1) [::false])).
 { eapply (reference_redirect_ground_step joint_update_node_offsets joint_update_expected_nodes 1280 joint_update_expr_1280);
 [exact joint_update_node_positions|exact joint_update_node_safety|apply (List.nth_error_In joint_update_expected_nodes 825%nat); vm_compute;reflexivity| |exact S1].
 intros site. cbn [joint_update_expr_1280 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Mode. reflexivity. }
 assert (Guard : VM.find 1281 s2 = Some (Gval (Fuint 1) [::true])).
 { eapply (reference_redirect_ground_step joint_update_node_offsets joint_update_expected_nodes 1281 joint_update_expr_1281);
 [exact joint_update_node_positions|exact joint_update_node_safety|apply (List.nth_error_In joint_update_expected_nodes 826%nat); vm_compute;reflexivity| |exact S2].
 intros site. cbn [joint_update_expr_1281 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite H1279 H1280. reflexivity. }
 destruct (alu_selected_mux_node 1303 1281 1161 1302 invalid s2 s2 s3 32 word
   ltac:(apply (List.nth_error_In joint_update_expected_nodes 848%nat); vm_compute;reflexivity) Guard Sum Size S3) as [value [Output Adapt]].
 eapply (declared_connection_value 1229 flat_statements joint_update_connection_1154_decl joint_update_connection_1154_mid joint_update_connection_1154_tail 1154 1303 32 value);
 [exact joint_update_connection_1154_position|exact joint_update_connection_1154_split|exact joint_update_connection_1154_straight|exact joint_update_connection_1154_mid_safe|exact joint_update_connection_1154_tail_safe|exact joint_update_connection_1154_nonregister|reflexivity|exact Output|exact Adapt|exact S4].
Qed.
Theorem alu_output_normal_select invalid s0 s1 s2 word old0 old1 :
 size word = 32%nat ->
 VM.find 7855 s0 = Some (Gval (Fuint 1) [::true]) ->
 VM.find 1154 s0 = Some (Gval (Fuint 32) word) ->
 VM.find 7752 s0 = Some (Gval (Fuint 32) old0) ->
 VM.find 7852 s1 = Some (Gval (Fuint 1) [::false]) ->
 VM.find 7752 s1 = Some (Gval (Fuint 32) old1) ->
 formal_value_iter invalid flat_memories s0 false s0 flat_statements = Some s1 ->
 formal_value_iter invalid flat_memories s1 false s1 flat_statements = Some s2 ->
 VM.find 7879 s2 = Some (Gval (Fuint 32) word).
Proof.
 intros Size Advance Output Old0 Flush Old1 S1 S2.
 assert (Selected : VM.find 7862 s1 = Some (Gval (Fuint 32) word)).
 { eapply (reference_redirect_ground_step joint_update_node_offsets joint_update_expected_nodes 7862 joint_update_expr_7862);
 [exact joint_update_node_positions|exact joint_update_node_safety|apply (List.nth_error_In joint_update_expected_nodes 917%nat); vm_compute;reflexivity| |exact S1].
 intros site. cbn [joint_update_expr_7862 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Advance Output Old0.
 cbn [is_zero]. unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref]. rewrite Old0.
 change (adapt_hvalue_as_type (Gval (Fuint 32) word) (Gtyp (Fuint 32)) = Some (Gval (Fuint 32) word)).
 apply reference_redirect_adapt_word; exact Size. }
 eapply (reference_redirect_ground_step joint_update_node_offsets joint_update_expected_nodes 7879 joint_update_expr_7879);
 [exact joint_update_node_positions|exact joint_update_node_safety|apply (List.nth_error_In joint_update_expected_nodes 934%nat); vm_compute;reflexivity| |exact S2].
 intros site. cbn [joint_update_expr_7879 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Flush Selected Old1.
 cbn [is_zero]. unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref]. rewrite Old1.
 change (adapt_hvalue_as_type (Gval (Fuint 32) word) (Gtyp (Fuint 32)) = Some (Gval (Fuint 32) word)).
 apply reference_redirect_adapt_word; exact Size.
Qed.
Theorem alu_output_normal_commit invalid old current result old_value word :
 VM.find 7752 old = Some old_value -> type_of_val old_value = Gtyp (Fuint 32) ->
 VM.find 65 old = Some (Gval (Fuint 1) [::false]) ->
 VM.find 7879 old = Some (Gval (Fuint 32) word) -> size word = 32%nat ->
 formal_value_iter invalid flat_memories old true current flat_statements = Some result ->
 VM.find 7752 result = Some (Gval (Fuint 32) word).
Proof.
 intros Old Typed Reset Selected Size Step.
 unfold formal_value_iter in Step.
 destruct (formal_statements invalid nil 0 flat_memories old true current flat_statements) as [proposed|] eqn:Statements; [|discriminate Step].
 destruct (formal_register_mux_observation 8258 flat_statements joint_register_7752_decl joint_register_7752_mid joint_register_7752_tail
 7752 joint_register_7752_reg (@Eref VarOrder.T (@Eid VarOrder.T 65)) (@Eref VarOrder.T (@Eid VarOrder.T 8162)) (@Eref VarOrder.T (@Eid VarOrder.T 7879)) invalid flat_memories old true current proposed old_value 32
 joint_register_7752_position joint_register_7752_split joint_register_7752_straight joint_register_7752_mid_safe joint_register_7752_tail_safe Old Typed Statements)
 as [source [value [Source [Adapt Value]]]].
 change (eval_hfexpr_with_memory flat_memories (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 65)) (@Eref VarOrder.T (@Eid VarOrder.T 8162)) (@Eref VarOrder.T (@Eid VarOrder.T 7879))) old old = Some source) in Source.
 pose proof (false_uint_mux_identity flat_memories old 65 8162 7879 32 word source value Size Reset Selected Source Adapt) as Same.
 rewrite Same in Value.
 rewrite (formal_finish_identity_preserves flat_statements invalid nil 0 flat_memories old proposed result 7752 joint_register_7752_identity Step).
 exact Value.
Qed.
Theorem alu_output_commit_window invalid history result word old4 old5 old6 :
 size word = 32%nat ->
 VM.find 1153 (history 0%nat) = Some (Gval (Fuint 4) [::false;false;false;false]) ->
 VM.find 1161 (history 2%nat) = Some (Gval (Fuint 32) word) ->
 VM.find 7855 (history 4%nat) = Some (Gval (Fuint 1) [::true]) ->
 VM.find 7852 (history 5%nat) = Some (Gval (Fuint 1) [::false]) ->
 VM.find 65 (history 6%nat) = Some (Gval (Fuint 1) [::false]) ->
 VM.find 7752 (history 4%nat) = Some (Gval (Fuint 32) old4) ->
 VM.find 7752 (history 5%nat) = Some (Gval (Fuint 32) old5) ->
 VM.find 7752 (history 6%nat) = Some (Gval (Fuint 32) old6) ->
 (forall i, (i < 6)%coq_nat -> formal_value_iter invalid flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 formal_value_iter invalid flat_memories (history 6%nat) true (history 6%nat) flat_statements = Some result ->
 VM.find 7752 result = Some (Gval (Fuint 32) word).
Proof.
 intros Size Mode Sum Advance Flush Reset Old4 Old5 Old6 Steps Commit.
 pose proof (alu_output_add_history invalid (history 0%nat) (history 1%nat) (history 2%nat) (history 3%nat) (history 4%nat) word Size Mode Sum
   (Steps 0%nat ltac:(lia)) (Steps 1%nat ltac:(lia)) (Steps 2%nat ltac:(lia)) (Steps 3%nat ltac:(lia))) as Output.
 pose proof (alu_output_normal_select invalid (history 4%nat) (history 5%nat) (history 6%nat) word old4 old5 Size Advance Output Old4 Flush Old5
   (Steps 4%nat ltac:(lia)) (Steps 5%nat ltac:(lia))) as Selected.
 exact (alu_output_normal_commit invalid (history 6%nat) (history 6%nat) result (Gval (Fuint 32) old6) word Old6 (Logic.eq_refl _) Reset Selected Size Commit).
Qed.
Require Import JointBoundaryRegisters JointUpdateBoundaryHistory ConcreteRegisterInitialization
 FormalPipelineControlHistory FormalStallHistory FormalCheckerResetConnections ExceptionSourceNoTrap.
Definition alu_output_tail_window (history : nat -> VM.t hvalue) i :=
 match i with 0%nat => history 9253%nat | 1%nat => history 9254%nat
 | 2%nat => history 9255%nat | 3%nat => history 9256%nat
 | 4%nat => history 9257%nat | 5%nat => history 9258%nat | _ => history 9259%nat end.
Theorem alu_output_normal_full_history inputs path history result word :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < 9259)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 (forall i, (i <= 9259)%coq_nat -> VM.find 1 (history i) = Some (Gval (Fuint 1) [::false])) ->
 VM.find 45 (history 9254%nat) = Some (Gval (Fuint 1) [::false]) ->
 size word = 32%nat ->
 VM.find 1153 (history 9253%nat) = Some (Gval (Fuint 4) [::false;false;false;false]) ->
 VM.find 1161 (history 9255%nat) = Some (Gval (Fuint 32) word) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories (history 9259%nat) true (history 9259%nat) flat_statements = Some result ->
 VM.find 7752 result = Some (Gval (Fuint 32) word).
Proof.
 intros Boundary Steps Resets NoTrap Size Mode Sum Commit.
 pose proof (exception_source_false_after_settling inputs path history Boundary Steps NoTrap) as NoException.
 assert (Member : List.In (7752%nat,32%nat) joint_boundary_registers).
 { apply (List.nth_error_In joint_boundary_registers 57%nat). vm_compute;reflexivity. }
 pose proof (joint_update_register_history_concrete _ history 9259 7752 32 Member (Boundary 7752%nat 32%nat Member) Steps) as Old.
 destruct (Old 9257 ltac:(vm_compute;lia)) as [old4 [_ Old4]].
 destruct (Old 9258 ltac:(vm_compute;lia)) as [old5 [_ Old5]].
 destruct (Old 9259 ltac:(vm_compute;lia)) as [old6 [_ Old6]].
 assert (Stall : VM.find 7765 (history 9255%nat) = Some (Gval (Fuint 1) [::false])).
 { apply (stall_after_six (formal_invalid_policy inputs path) (history 9249%nat) (history 9250%nat) (history 9251%nat) (history 9252%nat) (history 9253%nat) (history 9254%nat) (history 9255%nat) false);
 [apply Resets|apply Steps|apply Steps|apply Steps|apply Steps|apply Steps|apply Steps]; vm_compute;lia. }
 assert (Reset6 : VM.find 65 (history 9256%nat) = Some (Gval (Fuint 1) [::false])).
 { apply (reset_connection_65_transfer (formal_invalid_policy inputs path) (history 9255%nat) (history 9255%nat) (history 9256%nat) false).
 - apply (reset_connection_24_transfer (formal_invalid_policy inputs path) (history 9254%nat) (history 9254%nat) (history 9255%nat) false); [apply Resets|apply Steps];vm_compute;lia.
 - apply Steps;vm_compute;lia. }
 assert (Reset9 : VM.find 65 (history 9259%nat) = Some (Gval (Fuint 1) [::false])).
 { apply (reset_connection_65_transfer (formal_invalid_policy inputs path) (history 9258%nat) (history 9258%nat) (history 9259%nat) false).
 - apply (reset_connection_24_transfer (formal_invalid_policy inputs path) (history 9257%nat) (history 9257%nat) (history 9258%nat) false); [apply Resets|apply Steps];vm_compute;lia.
 - apply Steps;vm_compute;lia. }
 pose proof (pipeline_advance_after_two (formal_invalid_policy inputs path) (history 9255%nat) (history 9256%nat) (history 9257%nat) false false Stall
 (NoException 9255 ltac:(vm_compute;lia) ltac:(vm_compute;lia)) (Steps 9255 ltac:(vm_compute;lia)) (Steps 9256 ltac:(vm_compute;lia))) as Advance.
 pose proof (pipeline_flush_after_three (formal_invalid_policy inputs path) (history 9255%nat) (history 9256%nat) (history 9257%nat) (history 9258%nat) false false false Stall
 (NoException 9256 ltac:(vm_compute;lia) ltac:(vm_compute;lia)) Reset6
 (Steps 9255 ltac:(vm_compute;lia)) (Steps 9256 ltac:(vm_compute;lia)) (Steps 9257 ltac:(vm_compute;lia))) as Flush.
 eapply (alu_output_commit_window (formal_invalid_policy inputs path) (alu_output_tail_window history) result word old4 old5 old6 Size Mode Sum Advance Flush Reset9 Old4 Old5 Old6); [|exact Commit].
 intros i Bound. do 6 (destruct i as [|i]; [apply Steps;vm_compute;lia|]);lia.
Qed.
Require Import ALUAddressSemantics ReferenceLoadSemantics.
Definition alu_output_add_window (history : nat -> VM.t hvalue) i :=
 match i with 0%nat => history 9250%nat | 1%nat => history 9251%nat
 | 2%nat => history 9252%nat | 3%nat => history 9253%nat
 | 4%nat => history 9254%nat | _ => history 9255%nat end.
Theorem alu_add_commit_full_history inputs path history result left right :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < 9259)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 (forall i, (i <= 9259)%coq_nat -> VM.find 1 (history i) = Some (Gval (Fuint 1) [::false])) ->
 VM.find 45 (history 9254%nat) = Some (Gval (Fuint 1) [::false]) ->
 size right = 32%nat ->
 VM.find 1152 (history 9250%nat) = Some (Gval (Fuint 32) right) ->
 VM.find 1153 (history 9251%nat) = Some (Gval (Fuint 4) [::false;false;false;false]) ->
 VM.find 1152 (history 9252%nat) = Some (Gval (Fuint 32) right) ->
 VM.find 1151 (history 9253%nat) = Some (Gval (Fuint 32) left) ->
 VM.find 1153 (history 9253%nat) = Some (Gval (Fuint 4) [::false;false;false;false]) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories (history 9259%nat) true (history 9259%nat) flat_statements = Some result ->
 VM.find 7752 result = Some (Gval (Fuint 32) (reference_load_address left right)).
Proof.
 intros Boundary Steps Resets NoTrap Size Right0 Mode1 Right2 Left3 Mode3 Commit.
 eapply (alu_output_normal_full_history inputs path history result _ Boundary Steps Resets NoTrap); [|exact Mode3| |exact Commit].
 - unfold reference_load_address. rewrite size_take size_from_N. reflexivity.
 - eapply (alu_address_add_from_inputs (formal_invalid_policy inputs path) (alu_output_add_window history) left right Size Right0 Mode1 Right2 Left3).
   intros i Bound. do 5 (destruct i as [|i]; [apply Steps;vm_compute;lia|]);lia.
Qed.
Require Import FormalLocalHistory FormalObservationCommit StagedFlatCircuitIteration ObservedLegalNoTrap
 JointBoundaryReachable JointBoundaryPreparation FormalFetchType FormalResetPreparation.
Theorem alu_output_observed_transfer_context memory inputs k observed next :
 generated_observe memory inputs k = Some observed ->
 generated_legal_trace memory inputs k ->
 generated_run memory inputs (S k) = Some next ->
 VM.find 1 (formal_external_inputs (generated_observation_input inputs k)) = Some (Gval (Fuint 1) [::false]) ->
 exists history,
 history 9259%nat = top_environment observed /\
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) /\
 (forall i, (i < 9259)%coq_nat -> formal_value_iter (formal_invalid_policy (generated_observation_input inputs k) nil) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) /\
 (forall i, (i <= 9259)%coq_nat -> VM.find 1 (history i) = Some (Gval (Fuint 1) [::false])) /\
 (forall left right, size right = 32%nat ->
   VM.find 1152 (history 9250%nat) = Some (Gval (Fuint 32) right) ->
   VM.find 1153 (history 9251%nat) = Some (Gval (Fuint 4) [::false;false;false;false]) ->
   VM.find 1152 (history 9252%nat) = Some (Gval (Fuint 32) right) ->
   VM.find 1151 (history 9253%nat) = Some (Gval (Fuint 32) left) ->
   VM.find 1153 (history 9253%nat) = Some (Gval (Fuint 4) [::false;false;false;false]) ->
   VM.find 7752 (top_environment next) = Some (Gval (Fuint 32) (reference_load_address left right))).
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
 rewrite <- Top in Step. rewrite <- Last in Step.
 exists history. split;[exact Last|]. split;[exact Boundary|]. split;[exact Steps|]. split;[exact Resets|].
 intros left right Size Right0 Mode1 Right2 Left3 Mode3.
 unfold top_environment. rewrite After.
 exact (alu_add_commit_full_history (generated_observation_input inputs k) nil history after left right Boundary Steps Resets NoTrap Size Right0 Mode1 Right2 Left3 Mode3 Step).
Qed.
