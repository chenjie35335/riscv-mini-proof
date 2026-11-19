Require Import CoreSocModel ComparisonNodes FormalLocalHistory FormalPCJumpNodes FormalPCChoiceNodes
 FormalSuccessfulNodeEvaluation FormalTypedNodeEquation FetchPCSequentialExact FormalPCRegister.
From Coq Require Import NArith ZArith Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Definition pipeline_redirect_target word := zext_to 33 ([::false] ++ zext_to 32 (drop 1 word)).
Lemma pipeline_redirect_target_size word : size word = 32%nat -> size (pipeline_redirect_target word) = 33%nat.
Proof. intro Size. unfold pipeline_redirect_target,zext_to. rewrite ?size_zext ?size_cat ?size_zext ?size_drop Size. reflexivity. Qed.
Lemma pipeline_redirect_target_bits word : size word = 32%nat ->
 pipeline_redirect_target word = [::false] ++ drop 1 word ++ [::false].
Proof.
 intro Size. unfold pipeline_redirect_target,zext_to,zext.
 rewrite size_drop Size. cbn. rewrite size_cat size_drop Size. cbn. rewrite cats0. reflexivity.
Qed.
Lemma pipeline_redirect_target_after_two invalid s0 s1 s2 word :
 VM.find 1155 s0 = Some (Gval (Fuint 32) word) ->
 formal_flat_local_step invalid s0 s1 -> formal_flat_local_step invalid s1 s2 ->
 VM.find 7775 s2 = Some (Gval (Fuint 33) (pipeline_redirect_target word)).
Proof.
 intros Sum S1 S2.
 assert (Shift : VM.find 7774 s1 = Some (Gval (Fuint 32) (zext_to 32 (drop 1 word)))).
 { eapply pc_jump_node_7774; [|reflexivity|exact S1].
   cbn [pc_jump_expr_7774 eval_hfexpr_with_memory eval_href_with_memory]. rewrite Sum. reflexivity. }
 eapply pc_jump_node_7775; [|reflexivity|exact S2].
 cbn [pc_jump_expr_7775 eval_hfexpr_with_memory eval_href_with_memory]. rewrite Shift. reflexivity.
Qed.
Lemma pipeline_pc_true_mux_extension mm old (condition yes no : VarOrder.T) base input source :
 size base = 33%nat -> fetch_pc_extension base input ->
 VM.find condition old = Some (Gval (Fuint 1) [::true]) ->
 VM.find yes old = Some input ->
 eval_hfexpr_with_memory mm (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T condition))
 (@Eref VarOrder.T (@Eid VarOrder.T yes)) (@Eref VarOrder.T (@Eid VarOrder.T no))) old old = Some source ->
 fetch_pc_extension base source.
Proof.
 intros Size [width [Width Input]] Condition Yes Eval. subst input.
 cbn [eval_hfexpr_with_memory eval_href_with_memory] in Eval. rewrite Condition in Eval. cbn in Eval. rewrite Yes in Eval.
 destruct (eval_type_of_expr (Eref (Eid no)) old) as [ty|]; [|discriminate].
 unfold extend_hvalue_as_type in Eval. destruct ty as [ground|element count|fields];try discriminate.
 destruct ground;cbn [type_of_val ftype_mux fgtyp_mux option_map adapt_hvalue_as_type] in Eval;try discriminate.
 inversion Eval;subst source. exists (maxn width n). split.
 - exact (leq_trans Width (leq_maxl _ _)).
 - f_equal. apply fetch_pc_resize;[exact Size|exact Width|exact (leq_trans Width (leq_maxl _ _))].
Qed.
Theorem pipeline_pc_taken_source invalid s0 s1 s2 s3 s4 s5 s6 word :
 size word = 32%nat ->
 VM.find 1155 s0 = Some (Gval (Fuint 32) word) ->
 VM.find 7773 s2 = Some (Gval (Fuint 1) [::true]) ->
 VM.find 7771 s3 = Some (Gval (Fuint 1) [::false]) ->
 VM.find 128 s4 = Some (Gval (Fuint 1) [::false]) ->
 VM.find 7765 s5 = Some (Gval (Fuint 1) [::false]) ->
 formal_flat_local_step invalid s0 s1 -> formal_flat_local_step invalid s1 s2 ->
 formal_flat_local_step invalid s2 s3 -> formal_flat_local_step invalid s3 s4 ->
 formal_flat_local_step invalid s4 s5 -> formal_flat_local_step invalid s5 s6 ->
 exists value, VM.find 7781 s6 = Some value /\ fetch_pc_extension (pipeline_redirect_target word) value.
Proof.
 intros Size Sum Taken Eret Trap Stall S1 S2 S3 S4 S5 S6.
 pose proof (pipeline_redirect_target_size word Size) as TS.
 pose proof (pipeline_redirect_target_after_two invalid s0 s1 s2 word Sum S1 S2) as Target.
 destruct (formal_successful_node_evaluation 8284 flat_statements pc_choice_7778_tail 7778 pc_choice_7778_expr invalid flat_memories s2 false s2 s3 pc_choice_7778_position S3) as [value Eval].
 change (eval_hfexpr_with_memory flat_memories pc_choice_7778_expr s2 s2 = Some value) in Eval.
 pose proof (pipeline_pc_true_mux_extension flat_memories s2 7773 7775 7777 _ _ value TS (fetch_pc_base_extension _ TS) Taken Target Eval) as Extension.
 assert (V3 : VM.find 7778 s3 = Some value).
 { destruct Extension as [width [Width Shape]]. subst value. eapply formal_combinational_known_node;
   [exact pc_choice_7778_position|exact pc_choice_7778_suffix|exact pc_choice_7778_nonregister|exact Eval|reflexivity|exact S3]. }
 destruct (fetch_pc_sequential_7779 invalid s3 s3 s4 _ value TS Extension Eret V3 S4) as [v4 [V4 E4]].
 destruct (fetch_pc_sequential_7780 invalid s4 s4 s5 _ v4 TS E4 Trap V4 S5) as [v5 [V5 E5]].
 exact (fetch_pc_sequential_7781 invalid s5 s5 s6 _ v5 TS E5 Stall V5 S6).
Qed.
Theorem pipeline_pc_taken_commit invalid s0 s1 s2 s3 s4 s5 s6 result word pc :
 size word = 32%nat ->
 VM.find 1155 s0 = Some (Gval (Fuint 32) word) ->
 VM.find 7773 s2 = Some (Gval (Fuint 1) [::true]) ->
 VM.find 7771 s3 = Some (Gval (Fuint 1) [::false]) ->
 VM.find 128 s4 = Some (Gval (Fuint 1) [::false]) ->
 VM.find 7765 s5 = Some (Gval (Fuint 1) [::false]) ->
 VM.find 65 s6 = Some (Gval (Fuint 1) [::false]) ->
 VM.find 7768 s6 = Some (Gval (Fuint 33) pc) ->
 formal_flat_local_step invalid s0 s1 -> formal_flat_local_step invalid s1 s2 ->
 formal_flat_local_step invalid s2 s3 -> formal_flat_local_step invalid s3 s4 ->
 formal_flat_local_step invalid s4 s5 -> formal_flat_local_step invalid s5 s6 ->
 formal_value_iter invalid flat_memories s6 true s6 flat_statements = Some result ->
 VM.find 7768 result = Some (Gval (Fuint 33) (pipeline_redirect_target word)).
Proof.
 intros Size Sum Taken Eret Trap Stall Reset PC S1 S2 S3 S4 S5 S6 Commit.
 destruct (pipeline_pc_taken_source invalid s0 s1 s2 s3 s4 s5 s6 word Size Sum Taken Eret Trap Stall S1 S2 S3 S4 S5 S6) as [value [Value Ext]].
 exact (fetch_pc_sequential_commit invalid s6 s6 result pc _ value (pipeline_redirect_target_size word Size) Ext PC Reset Value Commit).
Qed.

Require Import ReferenceRedirectSpine.
Lemma pipeline_pc_to_N_append_false word : to_N (word ++ [::false]) = to_N word.
Proof. rewrite !to_N_nat to_nat_cat. cbn [to_nat foldr]. rewrite mul0n addn0. reflexivity. Qed.
Lemma pipeline_redirect_target_number word : size word = 32%nat ->
 to_N (pipeline_redirect_target word) = N.clearbit (to_N word) 0.
Proof.
 intro Size. rewrite (pipeline_redirect_target_bits word Size).
 destruct word as [|bit word]; [discriminate Size|]. cbn [drop cat].
 rewrite !redirect_to_N_cons pipeline_pc_to_N_append_false drop0.
 destruct (to_N word) as [|p]; destruct bit; reflexivity.
Qed.

Require Import FetchPCSelectorStability ExceptionSourceNoTrap FormalStallHistory FormalCheckerResetConnections JointBoundaryRegisters ConcreteRegisterInitialization.
Theorem pipeline_pc_taken_source_history inputs path history word :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < 9259)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 (forall i, (i <= 9259)%coq_nat -> VM.find 1 (history i) = Some (Gval (Fuint 1) [::false])) ->
 size word = 32%nat ->
 VM.find 1155 (history 9253%nat) = Some (Gval (Fuint 32) word) ->
 VM.find 7773 (history 9259%nat) = Some (Gval (Fuint 1) [::true]) ->
 VM.find 7771 (history 9259%nat) = Some (Gval (Fuint 1) [::false]) ->
 VM.find 45 (history 9254%nat) = Some (Gval (Fuint 1) [::false]) ->
 VM.find 65 (history 9259%nat) = Some (Gval (Fuint 1) [::false]) /\
 exists value, VM.find 7781 (history 9259%nat) = Some value /\ fetch_pc_extension (pipeline_redirect_target word) value.
Proof.
 intros Boundary Steps Resets Size Sum Sel3 Sel4 NoTrap.
 assert (C3 : VM.find 7773 (history 9255%nat) = Some (Gval (Fuint 1) [::true])).
 { rewrite (fetch_pc_selector_7773_same inputs path history 9259 Boundary Steps 9255 9259 ltac:(vm_compute;lia) ltac:(vm_compute;lia) ltac:(vm_compute;lia) ltac:(vm_compute;lia)). exact Sel3. }
 assert (C4 : VM.find 7771 (history 9256%nat) = Some (Gval (Fuint 1) [::false])).
 { rewrite (fetch_pc_selector_7771_same inputs path history 9259 Boundary Steps 9256 9259 ltac:(vm_compute;lia) ltac:(vm_compute;lia) ltac:(vm_compute;lia) ltac:(vm_compute;lia)). exact Sel4. }
 pose proof (exception_source_false_after_settling inputs path history Boundary Steps NoTrap 9257 ltac:(vm_compute;lia) ltac:(vm_compute;lia)) as C5.
 assert (C6 : VM.find 7765 (history 9258%nat) = Some (Gval (Fuint 1) [::false])).
 { apply (stall_after_six (formal_invalid_policy inputs path) (history 9252%nat) (history 9253%nat) (history 9254%nat) (history 9255%nat) (history 9256%nat) (history 9257%nat) (history 9258%nat) false);
 [apply Resets|apply Steps|apply Steps|apply Steps|apply Steps|apply Steps|apply Steps]; vm_compute;lia. }
 assert (Reset : VM.find 65 (history 9259%nat) = Some (Gval (Fuint 1) [::false])).
 { apply (reset_connection_65_transfer (formal_invalid_policy inputs path) (history 9258%nat) (history 9258%nat) (history 9259%nat) false).
 - apply (reset_connection_24_transfer (formal_invalid_policy inputs path) (history 9257%nat) (history 9257%nat) (history 9258%nat) false);
 [apply Resets|apply Steps]; vm_compute;lia.
 - apply Steps. vm_compute;lia. }
 split; [exact Reset|].
 apply (pipeline_pc_taken_source (formal_invalid_policy inputs path) (history 9253%nat) (history 9254%nat) (history 9255%nat) (history 9256%nat) (history 9257%nat) (history 9258%nat) (history 9259%nat) word Size Sum C3 C4 C5 C6);
 apply Steps; vm_compute;lia.
Qed.

Require Import ALUOutputTransfer FormalObservationCommit StagedFlatCircuitIteration
 ObservedJointRegisterConcrete FormalLegalObservation LegalNoTrapWindow JointUpdateBoundaryHistory.
Theorem pipeline_pc_taken_observed_context memory inputs k observed next :
 generated_observe memory inputs k = Some observed ->
 generated_legal_trace memory inputs k ->
 generated_run memory inputs (S k) = Some next ->
 VM.find 1 (formal_external_inputs (generated_observation_input inputs k)) = Some (Gval (Fuint 1) [::false]) ->
 VM.find 7773 (top_environment observed) = Some (Gval (Fuint 1) [::true]) ->
 VM.find 7771 (top_environment observed) = Some (Gval (Fuint 1) [::false]) ->
 exists history,
 history 9259%nat = top_environment observed /\
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) /\
 (forall i, (i < 9259)%coq_nat -> formal_value_iter (formal_invalid_policy (generated_observation_input inputs k) nil) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) /\
 (forall i, (i <= 9259)%coq_nat -> VM.find 1 (history i) = Some (Gval (Fuint 1) [::false])) /\
 (forall word, size word = 32%nat ->
   VM.find 1155 (history 9253%nat) = Some (Gval (Fuint 32) word) ->
   VM.find 7768 (top_environment next) = Some (Gval (Fuint 33) (pipeline_redirect_target word))).
Proof.
 intros Observe Legal Next Reset Taken Eret.
 destruct (alu_output_observed_transfer_context memory inputs k observed next Observe Legal Next Reset)
 as [history [Last [Boundary [Steps [Resets ALU]]]]].
 assert (LocalAssume : generated_assume_m0_0_local (history 9259%nat)).
 { rewrite Last. destruct (legal_observation_assumptions memory inputs k observed Legal Observe) as [_ Assume].
   apply (proj1 (flat_assumption_at_top observed)) in Assume.
   unfold top_environment; destruct (SVM.find nil observed);[exact Assume|contradiction]. }
 assert (NoTrap : VM.find 45 (history 9254%nat) = Some (Gval (Fuint 1) [::false])).
 { apply (legal_no_trap_history_window _ history 9259 9254 Steps); try (vm_compute;lia).
   - apply Resets;vm_compute;lia.
   - exact LocalAssume. }
 assert (Member : List.In (7768%nat,33%nat) joint_boundary_registers).
 { apply (List.nth_error_In joint_boundary_registers 67%nat);vm_compute;reflexivity. }
 destruct (observed_joint_register_concrete memory inputs k observed 7768 33 Observe Legal Member) as [pc [PCSize PC]].
 rewrite (observation_then_commit memory inputs k observed Observe) in Next.
 destruct (flat_iteration_projection _ observed true next Next) as [before [after [Before [Step After]]]].
 assert (Top : top_environment observed = before) by (unfold top_environment;rewrite Before;reflexivity).
 rewrite <- Top in Step. rewrite <- Last in Step.
 exists history. split;[exact Last|]. split;[exact Boundary|]. split;[exact Steps|]. split;[exact Resets|].
 intros word Size Sum.
 destruct (pipeline_pc_taken_source_history (generated_observation_input inputs k) nil history word Boundary Steps Resets Size Sum
 ltac:(rewrite Last;exact Taken) ltac:(rewrite Last;exact Eret) NoTrap) as [Root [value [Value Ext]]].
 unfold top_environment;rewrite After.
 apply (fetch_pc_sequential_commit (formal_invalid_policy (generated_observation_input inputs k) nil) (history 9259%nat) (history 9259%nat) after pc _ value (pipeline_redirect_target_size word Size) Ext).
 - rewrite Last;exact PC.
 - exact Root.
 - exact Value.
 - exact Step.
Qed.
