Require Import StagedRegisterHold StagedObservedRegister RegisterInvariants RFArchitecturalRelation RFArchitecturalResetCommits0 CoreSocModel ComparisonNodes FlatRegFileX0 FormalRFDataShape FormalRFWritebackNodes FormalX0WriteDataShape FormalX0SelectedType FormalSuccessfulNode UInt32ZeroMuxType FormalX0ConeNodes FormalX0TypedBypass FormalX0AddressStability FormalRFDestination JointUpdateNodePositions JointUpdateExpressionCertificates SelectedNodeSafety FormalTypedNodeEquation NormalUIntMuxIdentity FormalUIntRegisterCommitSource JointRegisterCommits2.
From Coq Require Import ZArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque generated_modules generated_top flat_statements flat_memories.
Lemma rf_storage_zero_mux_equivalent mm old (condition : hfexpr VarOrder.T) (yes1 yes2 zero : VarOrder.T) value :
 VM.find yes1 old = Some value -> VM.find yes2 old = Some value ->
 type_of_val value = Gtyp (Fuint 32) -> VM.find zero old = Some rf_zero32 ->
 eval_hfexpr_with_memory mm (Emux condition (Eref (Eid yes1)) (Eref (Eid zero))) old old =
 eval_hfexpr_with_memory mm (Emux condition (Eref (Eid yes2)) (@Econst VarOrder.T (Fuint 1) [::false])) old old.
Proof.
 intros Left Right Typed Zero.
 assert (LeftType : eval_type_of_expr (Eref (Eid yes1)) old = Some (Gtyp (Fuint 32))).
 { unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref]. rewrite Left. cbn [option_map]. rewrite Typed. reflexivity. }
 assert (RightType : eval_type_of_expr (Eref (Eid yes2)) old = Some (Gtyp (Fuint 32))).
 { unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref]. rewrite Right. cbn [option_map]. rewrite Typed. reflexivity. }
 assert (ZeroType : eval_type_of_expr (Eref (Eid zero)) old = Some (Gtyp (Fuint 32))).
 { unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref]. rewrite Zero. reflexivity. }
 cbn [eval_hfexpr_with_memory eval_href_with_memory].
 rewrite Left Right Zero LeftType RightType ZeroType.
 destruct (eval_hfexpr_with_memory mm condition old old) as [control|]; [|reflexivity].
 destruct control as [ground bits|element values|fields|typ|typ|typ]; try reflexivity.
 - destruct ground; try reflexivity. destruct (is_zero bits);
   unfold extend_hvalue_as_type; rewrite ?Typed; reflexivity.
Qed.
Theorem rf_storage_x0_matches_preview_after_four invalid s0 s1 s2 s3 s4 :
 VM.find 851 s2 = Some rf_zero32 -> VM.find 851 s3 = Some rf_zero32 ->
 formal_value_iter invalid flat_memories s0 false s0 flat_statements = Some s1 ->
 formal_value_iter invalid flat_memories s1 false s1 flat_statements = Some s2 ->
 formal_value_iter invalid flat_memories s2 false s2 flat_statements = Some s3 ->
 formal_value_iter invalid flat_memories s3 false s3 flat_statements = Some s4 ->
 VM.find 1021 s4 = VM.find 1053 s4.
Proof.
 intros Zero2 Zero3 S1 S2 S3 S4.
 destruct (rf_input_data_typed invalid s0 s0 s1 S1) as [data [Data Typed]].
 pose proof (rf_source_node_955 invalid s1 s1 s2 data Data Typed S2) as Data955.
 pose proof (rf_source_node_988 invalid s1 s1 s2 data Data Typed S2) as Data988.
 destruct (x0_selected_type invalid s2 s2 s3 data Data988 Typed S3) as [selected [Selected SelectedType]].
 pose proof Selected as Eval989. rewrite (node_989_full_iteration invalid s2 s2 s3 S3) in Eval989.
 assert (Selected956 : VM.find 956 s3 = Some selected).
 {
 assert (Member : List.In (956,joint_update_expr_956) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 611%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 956 joint_update_expr_956 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node; [exact Position|exact Safe|exact Nonreg| |exact SelectedType|exact S3].
 change (eval_hfexpr_with_memory flat_memories joint_update_expr_956 s2 s2 = Some selected).
 unfold joint_update_expr_956.
 rewrite (rf_storage_zero_mux_equivalent flat_memories s2 _ 955 988 851 data Data955 Data988 Typed Zero2).
 exact Eval989.
 }
 destruct (formal_successful_node _ _ _ _ _ invalid flat_memories s3 false s3 s4 position_1053 S4) as [value Eval1053].
 change (eval_hfexpr_with_memory flat_memories expr_1053 s3 s3 = Some value) in Eval1053.
 assert (ValueType : type_of_val value = Gtyp (Fuint 32)).
 { unfold expr_1053 in Eval1053. eapply uint32_zero_mux_result_type; [exact Selected|exact SelectedType|exact Eval1053]. }
 rewrite (node_1053_full_iteration invalid s3 s3 s4 S4) Eval1053.
 assert (Member : List.In (1021,joint_update_expr_1021) joint_update_expected_nodes).
 { apply (List.nth_error_In joint_update_expected_nodes 643%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 1021 joint_update_expr_1021 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node; [exact Position|exact Safe|exact Nonreg| |exact ValueType|exact S4].
 change (eval_hfexpr_with_memory flat_memories joint_update_expr_1021 s3 s3 = Some value).
 unfold joint_update_expr_1021.
 rewrite (rf_storage_zero_mux_equivalent flat_memories s3 _ 956 989 851 selected Selected956 Selected SelectedType Zero3).
 exact Eval1053.
Qed.
Theorem rf_storage_x0_source_after_five invalid s0 s1 s2 s3 s4 s5 instruction enable :
 size instruction = 32%nat -> VM.find 7750 s0 = Some (Gval (Fuint 32) instruction) ->
 VM.find 784 s3 = Some (Gval (Fuint 1) [::enable]) ->
 VM.find 851 s3 = Some rf_zero32 -> VM.find 851 s4 = Some rf_zero32 ->
 formal_value_iter invalid flat_memories s0 false s0 flat_statements = Some s1 ->
 formal_value_iter invalid flat_memories s1 false s1 flat_statements = Some s2 ->
 formal_value_iter invalid flat_memories s2 false s2 flat_statements = Some s3 ->
 formal_value_iter invalid flat_memories s3 false s3 flat_statements = Some s4 ->
 formal_value_iter invalid flat_memories s4 false s4 flat_statements = Some s5 ->
 VM.find 1021 s5 = Some rf_zero32.
Proof.
 intros Size Instruction Enable Zero3 Zero4 S1 S2 S3 S4 S5.
 rewrite (rf_storage_x0_matches_preview_after_four invalid s1 s2 s3 s4 s5 Zero3 Zero4 S2 S3 S4 S5).
 destruct (x0_address_stable_after_three invalid s0 s1 s2 s3 instruction Size Instruction S1 S2 S3) as [Addr2 Addr3].
 destruct (five_bits_decompose (drop 7 (take 12 instruction)) (rf_destination_width instruction Size)) as [b0 [b1 [b2 [b3 [b4 Bits]]]]].
 rewrite Bits in Addr2 Addr3.
 exact (x0_bypass_after_four invalid s1 s2 s3 s4 s5 enable b0 b1 b2 b3 b4 Addr2 Addr3 Enable S2 S3 S4 S5).
Qed.
Require Import X0BoundaryRegisters X0BoundaryHistory X0ConcreteGraphPropagation FormalConcreteX0Enable ConcreteRegisterInitialization JointBoundaryRegisters JointUpdateBoundaryHistory.
Lemma rf_storage_x0_joint_member : List.In (851%nat,32%nat) joint_boundary_registers.
Proof. apply (List.nth_error_In joint_boundary_registers 21%nat). reflexivity. Qed.
Theorem rf_storage_x0_source_history inputs path history limit :
 VM.find 851 (history 0%nat) = Some rf_zero32 ->
 (forall node width, List.In (node,width) x0_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall time, (time <= limit)%coq_nat -> exists bit, VM.find 1 (history time) = Some (Gval (Fuint 1) [::bit])) ->
 (forall time, (time < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history time) false (history time) flat_statements = Some (history (S time))) ->
 forall time, (51 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 1021 (history time) = Some rf_zero32.
Proof.
 intros Zero Initial Reset Steps time Lower Upper.
 set (start := Nat.sub time 5).
 assert (End : (start + 5)%coq_nat = time) by (unfold start;lia).
 assert (FiveSteps : forall j, (j < 5)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history (start+j)%coq_nat) false (history (start+j)%coq_nat) flat_statements = Some (history (start+S j)%coq_nat)).
 { intros j Small. replace (start+S j)%coq_nat with (S (Nat.add start j)) by lia. apply Steps;lia. }
 pose proof (x0_rank_zero_history_concrete (formal_invalid_policy inputs path) history limit Initial Reset Steps) as Boundary.
 destruct (x0_concrete_history_targets inputs path history limit Boundary Steps (start+3)%coq_nat ltac:(lia) ltac:(lia)) as [Enable Rest].
 destruct (concrete_x0_enable_is_bit (formal_invalid_policy inputs path) (history (start+2)%coq_nat) (history (start+2)%coq_nat) (history (start+3)%coq_nat) (FiveSteps 2%nat ltac:(lia)) Enable) as [bit EnableBit].
 assert (InstructionMember : List.In (7750%nat,32%nat) x0_boundary_registers).
 { unfold x0_boundary_registers;right;left;reflexivity. }
 destruct (x0_register_history_concrete (formal_invalid_policy inputs path) history limit 7750%nat 32%nat InstructionMember (Initial _ _ InstructionMember) Steps (start+0)%coq_nat ltac:(lia)) as [instruction [Size Instruction]].
 assert (Zeros : forall t, (t <= limit)%coq_nat -> VM.find 851 (history t) = Some rf_zero32).
 { intros t Bound. rewrite (joint_update_register_history_same (formal_invalid_policy inputs path) history limit 851 32 rf_storage_x0_joint_member Steps t Bound). exact Zero. }
 rewrite <- End.
 apply (rf_storage_x0_source_after_five (formal_invalid_policy inputs path)
 (history (start+0)%coq_nat) (history (start+1)%coq_nat) (history (start+2)%coq_nat)
 (history (start+3)%coq_nat) (history (start+4)%coq_nat) (history (start+5)%coq_nat) instruction bit Size Instruction EnableBit).
 - apply Zeros;lia.
 - apply Zeros;lia.
 - exact (FiveSteps 0%nat ltac:(lia)).
 - exact (FiveSteps 1%nat ltac:(lia)).
 - exact (FiveSteps 2%nat ltac:(lia)).
 - exact (FiveSteps 3%nat ltac:(lia)).
 - exact (FiveSteps 4%nat ltac:(lia)).
Qed.
Lemma rf_storage_x0_normal_commit invalid old current result old_value :
 VM.find 851 old = Some old_value -> type_of_val old_value = Gtyp (Fuint 32) ->
 VM.find 779 old = Some (Gval (Fuint 1) [::false]) ->
 VM.find 1021 old = Some rf_zero32 ->
 formal_value_iter invalid flat_memories old true current flat_statements = Some result ->
 VM.find 851 result = Some rf_zero32.
Proof.
 intros Old Typed Reset Normal Commit.
 destruct (formal_committed_uint_register_mux_observation 860 flat_statements joint_register_851_decl joint_register_851_mid joint_register_851_tail
 851 joint_register_851_reg (@Eref VarOrder.T (@Eid VarOrder.T 779)) (@Eref VarOrder.T (@Eid VarOrder.T 1085)) (@Eref VarOrder.T (@Eid VarOrder.T 1021)) invalid flat_memories old current result old_value 32
 joint_register_851_position joint_register_851_split joint_register_851_straight joint_register_851_mid_safe joint_register_851_tail_safe Old Typed joint_register_851_identity Commit)
 as [source [value [Source [Adapt Value]]]].
 change (eval_hfexpr_with_memory flat_memories (Emux (@Eref VarOrder.T (@Eid VarOrder.T 779)) (@Eref VarOrder.T (@Eid VarOrder.T 1085)) (@Eref VarOrder.T (@Eid VarOrder.T 1021))) old old = Some source) in Source.
 pose proof (unselected_uint_mux_identity flat_memories old 779 1085 1021 32 (zeros 32) source value (Logic.eq_refl _) Reset Normal Source Adapt) as Equal.
 rewrite Equal in Value. exact Value.
Qed.
Require Import RFArchitecturalResetSources0 FormalLocalHistory StagedFlatCircuitIteration StagedCircuitRegisterHold StagedIterationCount FormalResetTrace FormalResetPreparation FormalRFResetControl RegisterPreparationFrames FormalSingletonSymbolic.
From firrtl Require Import FormalInitialization.
Lemma rf_storage_x0_properties :
 has_register 851 flat_statements = true /\ initial_register_safe 851 flat_statements.
Proof.
 assert (Member : List.In 851%nat rf_architectural_register_ids) by (left;reflexivity).
 destruct (rf_architectural_register_properties 851 Member) as [Present [Typed Safe]]. split;assumption.
Qed.
Theorem rf_storage_x0_reset_settle inputs initial stable result old_value :
 state_reset initial true -> staged_register_lookup 851 initial = Some old_value ->
 type_of_val old_value = Gtyp (Fuint 32) ->
 circuit_formal_iterations generated_modules generated_top inputs 9259 initial = Some stable ->
 formal_circuit_value_iter (formal_invalid_policy inputs) generated_modules generated_top stable true = Some result ->
 exists env, SVM.find nil result = Some env /\ VM.find 851 env = Some rf_zero32.
Proof.
 intros Reset Old Typed Iterations Commit.
 destruct (rf_control_9259 inputs initial stable true Reset Iterations) as [control [Control ResetBit]].
 destruct (local_iteration_history inputs 9259 initial stable Iterations) as [history [First [Last Steps]]].
 pose proof (rfa_reset_history_1085 inputs nil history 9259 Steps 9259 ltac:(vm_compute;lia) ltac:(lia)) as Source.
 destruct (flat_iteration_projection (formal_invalid_policy inputs) stable true result Commit) as [before [after [Before [Local After]]]].
 rewrite Last in Source. unfold top_environment in Source. rewrite Before in Source.
 rewrite Before in Control. inversion Control;subst control.
 pose proof (staged_iterations_hold_register inputs 9259 initial stable 851 (proj1 rf_storage_x0_properties) Iterations) as Held.
 rewrite Old in Held. unfold staged_register_lookup in Held. rewrite Before in Held.
 exists after;split;[exact After|].
 exact (rfa_reset_commit_851 (formal_invalid_policy inputs nil) before before after old_value (rfa_reset_word_0 inputs nil) Held Typed ResetBit Source (rfa_reset_word_0_size inputs nil) Local).
Qed.
Theorem rf_storage_x0_reset_cycle inputs previous old result old_value :
 SVM.find nil previous = Some old -> VM.find 851 old = Some old_value -> type_of_val old_value = Gtyp (Fuint 32) ->
 VM.find 1 (formal_external_inputs inputs) = Some (Gval (Fuint 1) [::true]) ->
 circuit_formal_cycle generated_modules generated_top (Some previous) inputs = Some result ->
 exists env, SVM.find nil result = Some env /\ VM.find 851 env = Some rf_zero32.
Proof.
 intros Previous Old Typed Reset Cycle. unfold circuit_formal_cycle in Cycle.
 destruct (circuit_initial_map_with_memory generated_modules generated_top (Some previous) (formal_external_inputs inputs)) as [initial|] eqn:Prepare; [|discriminate Cycle].
 pose proof flat_iteration_count_exact as Count. unfold flat_iteration_count in Count. rewrite Count in Cycle.
 destruct (circuit_formal_iterations generated_modules generated_top inputs 9259 initial) as [stable|] eqn:Iterations; [|discriminate Cycle].
 apply (rf_storage_x0_reset_settle inputs initial stable result old_value); [| |exact Typed|exact Iterations|exact Cycle].
 - exact (top_reset_prepared (Some previous) _ initial _ Reset Prepare).
 - rewrite (staged_prepared_register_copies previous old _ initial 851 (Logic.eq_refl _) (Logic.eq_refl _) (proj2 rf_storage_x0_properties) (proj1 rf_storage_x0_properties) Previous Prepare). exact Old.
Qed.
Theorem rf_storage_x0_after_reset memory inputs states :
 formal_state_after_reset generated_modules generated_top 1 (Fuint 1) memory inputs = Some states ->
 exists env, SVM.find nil states = Some env /\ VM.find 851 env = Some rf_zero32.
Proof.
 unfold formal_state_after_reset.
 destruct (circuit_symbolic_initial_state generated_modules generated_top memory inputs) as [initial|] eqn:Init; [|discriminate]. intro Reset.
 destruct (rf_architectural_symbolic_initial_concrete memory inputs initial Init) as [old [Old Concrete]].
 destruct (Concrete 851%nat (or_introl (Logic.eq_refl _))) as [word [Size Value]].
 apply (rf_storage_x0_reset_cycle (force_formal_reset 1 (Fuint 1) inputs) initial old states (Gval (Fuint 32) word)); try assumption;try reflexivity.
 unfold force_formal_reset. cbn [formal_external_inputs]. apply RegisterMapFacts.find_add_eq. reflexivity.
Qed.
Theorem rf_storage_x0_run_zero memory inputs states :
 generated_run memory inputs 0 = Some states ->
 exists env, SVM.find nil states = Some env /\ VM.find 851 env = Some rf_zero32.
Proof.
 unfold generated_run, formal_run_after_reset.
 destruct (formal_state_after_reset generated_modules generated_top generated_reset_id generated_reset_type memory (inputs 0%nat)) as [initial|] eqn:Reset;[|discriminate].
 cbn [circuit_formal_run]. intro Run;inversion Run;subst states.
 exact (rf_storage_x0_after_reset memory (inputs 0%nat) initial Reset).
Qed.
Require Import JointBoundaryIncludes JointBoundaryPreparation JointBoundaryInitialization JointBoundaryReachable JointBoundaryInduction FormalObservationCommit ExternalReset ObservedLegalNoTrap.
Theorem rf_storage_x0_observed_sources memory inputs k committed old observed :
 generated_run memory inputs k = Some committed -> SVM.find nil committed = Some old ->
 VM.find 851 old = Some rf_zero32 -> generated_observe memory inputs k = Some observed ->
 generated_legal_trace memory inputs k -> joint_registers_concrete old ->
 exists bit, VM.find 779 (top_environment observed) = Some (Gval (Fuint 1) [::bit]) /\
 VM.find 1085 (top_environment observed) = Some rf_zero32 /\
 VM.find 1021 (top_environment observed) = Some rf_zero32 /\
 VM.find 851 (top_environment observed) = Some rf_zero32.
Proof.
 intros Run Old Zero Observe Legal Boundary.
 destruct (legal_observation_reset memory inputs k Legal) as [bit External].
 pose proof Observe as Expanded. unfold generated_observe, generated_observe_cycle in Expanded. rewrite Run in Expanded.
 destruct (circuit_initial_map_with_memory generated_modules generated_top (Some committed) (formal_external_inputs (generated_observation_input inputs k))) as [prepared|] eqn:Prepare; [|discriminate Expanded].
 pose proof flat_iteration_count_exact as Count. unfold flat_iteration_count in Count. rewrite Count in Expanded.
 destruct (local_iteration_history (generated_observation_input inputs k) 9259 prepared observed Expanded) as [history [First [Last Steps]]].
 destruct (top_reset_prepared (Some committed) _ prepared _ External Prepare) as [env [Env Reset]].
 assert (StateReset : state_reset prepared bit) by (exists env;split;assumption).
 destruct (rf_control_9259 (generated_observation_input inputs k) prepared observed bit StateReset Expanded) as [control [Control ControlBit]].
 assert (Reset0 : VM.find 1 (history 0%nat) = Some (Gval (Fuint 1) [::bit])).
 { rewrite First. unfold top_environment. rewrite Env. exact Reset. }
 pose proof (legal_local_reset_history _ history 9259 bit Steps Reset0) as Resets.
 assert (Zero0 : VM.find 851 (history 0%nat) = Some rf_zero32).
 { pose proof (staged_prepared_register_copies committed old _ prepared 851 (Logic.eq_refl _) (Logic.eq_refl _) (proj2 rf_storage_x0_properties) (proj1 rf_storage_x0_properties) Old Prepare) as Copy.
   rewrite Zero in Copy. unfold staged_register_lookup in Copy. rewrite Env in Copy.
   rewrite First. unfold top_environment. rewrite Env. exact Copy. }
 assert (Initial : forall node width, List.In (node,width) x0_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)).
 { intros node width Member. rewrite First.
   apply (joint_boundary_prepared_concrete committed old (formal_external_inputs (generated_observation_input inputs k)) prepared node width (joint_includes_x0 node width Member)); [apply Boundary;apply joint_includes_x0;exact Member|exact Old|exact Prepare]. }
 exists bit. split.
 - unfold top_environment. rewrite Control. exact ControlBit.
 - rewrite <- Last. split.
   + exact (rfa_reset_history_1085 (generated_observation_input inputs k) nil history 9259 Steps 9259 ltac:(vm_compute;lia) ltac:(lia)).
   + split.
     * apply (rf_storage_x0_source_history (generated_observation_input inputs k) nil history 9259 Zero0 Initial); [|exact Steps|vm_compute;lia|lia].
       intros t Bound;exists bit;exact (Resets t Bound).
     * rewrite (joint_update_register_history_same _ history 9259 851 32 rf_storage_x0_joint_member Steps 9259 (Nat.le_refl 9259)). exact Zero0.
Qed.
Theorem rf_storage_x0_run_step memory inputs k committed old observed next :
 generated_run memory inputs k = Some committed -> SVM.find nil committed = Some old ->
 VM.find 851 old = Some rf_zero32 -> generated_observe memory inputs k = Some observed ->
 generated_run memory inputs (S k) = Some next -> generated_legal_trace memory inputs k ->
 exists env, SVM.find nil next = Some env /\ VM.find 851 env = Some rf_zero32.
Proof.
 intros Run Old Zero Observe Next Legal.
 destruct (joint_boundary_reachable memory inputs k committed Run Legal) as [Boundary Storage].
 unfold joint_registers_concrete, top_environment in Boundary. rewrite Old in Boundary.
 destruct (rf_storage_x0_observed_sources memory inputs k committed old observed Run Old Zero Observe Legal Boundary) as [bit [Reset [ResetSource [NormalSource Held]]]].
 rewrite (observation_then_commit memory inputs k observed Observe) in Next.
 destruct (flat_iteration_projection _ observed true next Next) as [before [after [Before [Commit After]]]].
 assert (Top : top_environment observed = before) by (unfold top_environment;rewrite Before;reflexivity).
 rewrite Top in Reset, ResetSource, NormalSource, Held.
 exists after;split;[exact After|]. destruct bit.
 - exact (rfa_reset_commit_851 _ before before after rf_zero32 (zeros 32) Held (Logic.eq_refl _) Reset ResetSource (Logic.eq_refl _) Commit).
 - exact (rf_storage_x0_normal_commit _ before before after rf_zero32 Held (Logic.eq_refl _) Reset NormalSource Commit).
Qed.
Theorem rf_storage_x0_reachable memory inputs k states :
 generated_run memory inputs k = Some states -> generated_legal_trace memory inputs k ->
 exists env, SVM.find nil states = Some env /\ VM.find 851 env = Some rf_zero32.
Proof.
 revert states. induction k as [|k IH]; intros states Run Legal.
 - exact (rf_storage_x0_run_zero memory inputs states Run).
 - pose proof Run as Expanded. rewrite generated_run_successor in Expanded.
   destruct (generated_run memory inputs k) as [committed|] eqn:Previous;[|discriminate Expanded].
   assert (PriorLegal : generated_legal_trace memory inputs k) by (exact (joint_legal_trace_prefix memory inputs (S k) k Legal (Nat.le_succ_diag_r k))).
   destruct (IH committed (Logic.eq_refl _) PriorLegal) as [old [Old Zero]].
   destruct (generated_successful_commit memory inputs k states Run) as [observed [Observe Commit]].
   exact (rf_storage_x0_run_step memory inputs k committed old observed states Previous Old Zero Observe Run PriorLegal).
Qed.
Require Import RFWriteEffect UIntMuxResultType FormalSuccessfulNodeEvaluation FormalRFNopDisable.
Definition rf_dut_bank_at env (bank : rf_bank) : Prop := forall index, (index < 32)%coq_nat ->
 size (bank index) = 32%nat /\ VM.find (N.of_nat (851+index)%nat) env = Some (Gval (Fuint 32) (bank index)).
Definition rf_dut_select_expr (index : nat) : hfexpr VarOrder.T :=
 @Emux VarOrder.T (@Eprim_binop VarOrder.T (Bcomp Beq)
 (@Econst VarOrder.T (Fuint (S (Nat.log2 index))) (from_N (S (Nat.log2 index)) (N.of_nat index)))
 (@Eref VarOrder.T (@Eid VarOrder.T 785))) (@Eref VarOrder.T (@Eid VarOrder.T 955)) (@Eref VarOrder.T (@Eid VarOrder.T (N.of_nat (851+index)%nat))).
Definition rf_dut_normal_expr (index : nat) : hfexpr VarOrder.T :=
 @Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 954)) (@Eref VarOrder.T (@Eid VarOrder.T (N.of_nat (956+index)%nat))) (@Eref VarOrder.T (@Eid VarOrder.T (N.of_nat (851+index)%nat))).
Lemma rf_dut_select_member index : (index < 32)%coq_nat ->
 List.In (N.of_nat (956+index)%nat,rf_dut_select_expr index) joint_update_expected_nodes.
Proof.
 intro Bound. apply (List.nth_error_In joint_update_expected_nodes (611+index)%nat).
 do 32 (destruct index as [|index]; [vm_compute;reflexivity|]). lia.
Qed.
Lemma rf_dut_normal_member index : (index < 32)%coq_nat ->
 List.In (N.of_nat (1021+index)%nat,rf_dut_normal_expr index) joint_update_expected_nodes.
Proof.
 intro Bound. apply (List.nth_error_In joint_update_expected_nodes (643+index)%nat).
 do 32 (destruct index as [|index]; [vm_compute;reflexivity|]). lia.
Qed.
Lemma rf_dut_register_member index : (index < 32)%coq_nat ->
 List.In (851+index)%nat rf_architectural_register_ids.
Proof.
 intro Bound. apply (List.nth_error_In rf_architectural_register_ids (2*index)%nat).
 do 32 (destruct index as [|index]; [vm_compute;reflexivity|]). lia.
Qed.
Lemma rf_dut_bank_comb_hold invalid old current result bank :
 rf_dut_bank_at old bank -> formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 rf_dut_bank_at result bank.
Proof.
 intros Bank Step index Bound. destruct (Bank index Bound) as [Size Value]. split;[exact Size|].
 destruct (rf_architectural_register_properties _ (rf_dut_register_member index Bound)) as [Present Rest].
 rewrite (staged_combinational_holds_registers invalid flat_memories old current result flat_statements _ Present Step). exact Value.
Qed.
Lemma rf_dut_disabled_mux_eval mm old (yes no : VarOrder.T) value word :
 VM.find 954 old = Some (Gval (Fuint 1) [::false]) ->
 VM.find yes old = Some value -> type_of_val value = Gtyp (Fuint 32) ->
 VM.find no old = Some (Gval (Fuint 32) word) -> size word = 32%nat ->
 eval_hfexpr_with_memory mm (Emux (@Eref VarOrder.T (@Eid VarOrder.T 954)) (Eref (Eid yes)) (Eref (Eid no))) old old = Some (Gval (Fuint 32) word).
Proof.
 intros Gate Yes Typed No Size.
 cbn [eval_hfexpr_with_memory eval_href_with_memory]. rewrite Gate. change (is_zero [::false]) with true. cbn.
 unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref]. rewrite Yes No.
 cbn [option_map]. rewrite Typed. cbn [make_ftype_explicit extend_hvalue_as_type type_of_val ftype_mux fgtyp_mux option_map adapt_hvalue_as_type].
 rewrite maxnn -Size take_size. unfold zext_to,zext. rewrite subnn cats0. reflexivity.
Qed.
Theorem rf_dut_no_write_source_step invalid s0 s1 s2 index word data :
 (index < 32)%coq_nat -> size word = 32%nat ->
 VM.find (N.of_nat (851+index)%nat) s0 = Some (Gval (Fuint 32) word) ->
 VM.find (N.of_nat (851+index)%nat) s1 = Some (Gval (Fuint 32) word) ->
 VM.find 955 s0 = Some data -> type_of_val data = Gtyp (Fuint 32) ->
 VM.find 954 s1 = Some (Gval (Fuint 1) [::false]) ->
 formal_value_iter invalid flat_memories s0 false s0 flat_statements = Some s1 ->
 formal_value_iter invalid flat_memories s1 false s1 flat_statements = Some s2 ->
 VM.find (N.of_nat (1021+index)%nat) s2 = Some (Gval (Fuint 32) word).
Proof.
 intros Bound Size Old0 Old1 Data Typed Gate S1 S2.
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes _ _ joint_update_node_positions joint_update_node_safety (rf_dut_select_member index Bound)) as [count [tail [Position [Safe Nonreg]]]].
 destruct (formal_successful_node_evaluation count flat_statements tail _ _ invalid flat_memories s0 false s0 s1 Position S1) as [selected Eval]. rewrite add0n in Eval.
 change (eval_hfexpr_with_memory flat_memories (rf_dut_select_expr index) s0 s0 = Some selected) in Eval.
 assert (SelectedType : type_of_val selected = Gtyp (Fuint 32)).
 { unfold rf_dut_select_expr in Eval. eapply uint_mux_result_type;[exact Data|exact Typed|exact Old0|reflexivity|exact Eval]. }
 assert (Selected : VM.find (N.of_nat (956+index)%nat) s1 = Some selected).
 { eapply formal_combinational_known_node;[exact Position|exact Safe|exact Nonreg|exact Eval|exact SelectedType|exact S1]. }
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes _ _ joint_update_node_positions joint_update_node_safety (rf_dut_normal_member index Bound)) as [count2 [tail2 [Position2 [Safe2 Nonreg2]]]].
 eapply formal_combinational_known_node;[exact Position2|exact Safe2|exact Nonreg2| |reflexivity|exact S2].
 change (eval_hfexpr_with_memory flat_memories (rf_dut_normal_expr index) s1 s1 = Some (Gval (Fuint 32) word)).
 exact (rf_dut_disabled_mux_eval flat_memories s1 _ _ selected word Gate Selected SelectedType Old1 Size).
Qed.
Theorem rf_dut_no_write_sources_after_four invalid s0 s1 s2 s3 s4 bank :
 rf_dut_bank_at s0 bank -> VM.find 954 s3 = Some (Gval (Fuint 1) [::false]) ->
 formal_value_iter invalid flat_memories s0 false s0 flat_statements = Some s1 ->
 formal_value_iter invalid flat_memories s1 false s1 flat_statements = Some s2 ->
 formal_value_iter invalid flat_memories s2 false s2 flat_statements = Some s3 ->
 formal_value_iter invalid flat_memories s3 false s3 flat_statements = Some s4 ->
 forall index, (index < 32)%coq_nat ->
 VM.find (N.of_nat (1021+index)%nat) s4 = Some (Gval (Fuint 32) (bank index)).
Proof.
 intros Bank Gate S1 S2 S3 S4 index Bound.
 pose proof (rf_dut_bank_comb_hold invalid s0 s0 s1 bank Bank S1) as Bank1.
 pose proof (rf_dut_bank_comb_hold invalid s1 s1 s2 bank Bank1 S2) as Bank2.
 pose proof (rf_dut_bank_comb_hold invalid s2 s2 s3 bank Bank2 S3) as Bank3.
 destruct (rf_internal_data_typed_after_two invalid s0 s1 s2 S1 S2) as [data [Data Typed]].
 exact (rf_dut_no_write_source_step invalid s2 s3 s4 index (bank index) data Bound (proj1 (Bank index Bound)) (proj2 (Bank2 index Bound)) (proj2 (Bank3 index Bound)) Data Typed Gate S3 S4).
Qed.
Require Import ScalarNodeFrames FormalTypedNodeFrames FormalStatementSegments RegisterCommitCertificate JointRegisterCommits3 JointRegisterCommits4 JointRegisterCommits5 JointRegisterCommits6.
Lemma rf_storage_normal_commit_certificate count declared middle tail node reg yes no invalid old current result old_value word :
 straight_drop count flat_statements = Some (@Qcons VarOrder.T (@Sreg VarOrder.T node reg) declared) ->
 declared = statement_append middle (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T node) (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 779)) (@Eref VarOrder.T (@Eid VarOrder.T yes)) (@Eref VarOrder.T (@Eid VarOrder.T no)))) tail) ->
 straight_statements middle -> formal_typed_suffix_safe flat_memories node middle -> formal_typed_suffix_safe flat_memories node tail -> register_identity_b node flat_statements ->
 VM.find node old = Some old_value -> type_of_val old_value = Gtyp (Fuint 32) ->
 VM.find 779 old = Some (Gval (Fuint 1) [::false]) ->
 VM.find no old = Some (Gval (Fuint 32) word) -> size word = 32%nat ->
 formal_value_iter invalid flat_memories old true current flat_statements = Some result ->
 VM.find node result = Some (Gval (Fuint 32) word).
Proof.
 intros Position Split Straight MiddleSafe TailSafe Identity Old Typed Reset Source Size Commit.
 destruct (formal_committed_uint_register_mux_observation count flat_statements declared middle tail node reg
 (@Eref VarOrder.T (@Eid VarOrder.T 779)) (@Eref VarOrder.T (@Eid VarOrder.T yes)) (@Eref VarOrder.T (@Eid VarOrder.T no)) invalid flat_memories old current result old_value 32
 Position Split Straight MiddleSafe TailSafe Old Typed Identity Commit) as [source [value [Eval [Adapt Value]]]].
 change (eval_hfexpr_with_memory flat_memories (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 779)) (@Eref VarOrder.T (@Eid VarOrder.T yes)) (@Eref VarOrder.T (@Eid VarOrder.T no))) old old = Some source) in Eval.
 pose proof (unselected_uint_mux_identity flat_memories old 779 yes no 32 word source value Size Reset Source Eval Adapt) as Same.
 rewrite Same in Value. exact Value.
Qed.
Theorem rf_dut_normal_commit_value invalid old current result index old_value word :
 (index < 32)%coq_nat ->
 VM.find (N.of_nat (851+index)%nat) old = Some old_value -> type_of_val old_value = Gtyp (Fuint 32) ->
 VM.find 779 old = Some (Gval (Fuint 1) [::false]) ->
 VM.find (N.of_nat (1021+index)%nat) old = Some (Gval (Fuint 32) word) -> size word = 32%nat ->
 formal_value_iter invalid flat_memories old true current flat_statements = Some result ->
 VM.find (N.of_nat (851+index)%nat) result = Some (Gval (Fuint 32) word).
Proof.
 intros Bound Old Typed Reset Source Size Commit.
 destruct index as [|index].
 - exact (rf_storage_normal_commit_certificate 860 joint_register_851_decl joint_register_851_mid joint_register_851_tail 851 joint_register_851_reg 1085 1021 invalid old current result old_value word
 joint_register_851_position joint_register_851_split joint_register_851_straight joint_register_851_mid_safe joint_register_851_tail_safe joint_register_851_identity Old Typed Reset Source Size Commit).
 destruct index as [|index].
 - exact (rf_storage_normal_commit_certificate 861 joint_register_852_decl joint_register_852_mid joint_register_852_tail 852 joint_register_852_reg 1086 1022 invalid old current result old_value word
 joint_register_852_position joint_register_852_split joint_register_852_straight joint_register_852_mid_safe joint_register_852_tail_safe joint_register_852_identity Old Typed Reset Source Size Commit).
 destruct index as [|index].
 - exact (rf_storage_normal_commit_certificate 862 joint_register_853_decl joint_register_853_mid joint_register_853_tail 853 joint_register_853_reg 1087 1023 invalid old current result old_value word
 joint_register_853_position joint_register_853_split joint_register_853_straight joint_register_853_mid_safe joint_register_853_tail_safe joint_register_853_identity Old Typed Reset Source Size Commit).
 destruct index as [|index].
 - exact (rf_storage_normal_commit_certificate 863 joint_register_854_decl joint_register_854_mid joint_register_854_tail 854 joint_register_854_reg 1088 1024 invalid old current result old_value word
 joint_register_854_position joint_register_854_split joint_register_854_straight joint_register_854_mid_safe joint_register_854_tail_safe joint_register_854_identity Old Typed Reset Source Size Commit).
 destruct index as [|index].
 - exact (rf_storage_normal_commit_certificate 864 joint_register_855_decl joint_register_855_mid joint_register_855_tail 855 joint_register_855_reg 1089 1025 invalid old current result old_value word
 joint_register_855_position joint_register_855_split joint_register_855_straight joint_register_855_mid_safe joint_register_855_tail_safe joint_register_855_identity Old Typed Reset Source Size Commit).
 destruct index as [|index].
 - exact (rf_storage_normal_commit_certificate 865 joint_register_856_decl joint_register_856_mid joint_register_856_tail 856 joint_register_856_reg 1090 1026 invalid old current result old_value word
 joint_register_856_position joint_register_856_split joint_register_856_straight joint_register_856_mid_safe joint_register_856_tail_safe joint_register_856_identity Old Typed Reset Source Size Commit).
 destruct index as [|index].
 - exact (rf_storage_normal_commit_certificate 866 joint_register_857_decl joint_register_857_mid joint_register_857_tail 857 joint_register_857_reg 1091 1027 invalid old current result old_value word
 joint_register_857_position joint_register_857_split joint_register_857_straight joint_register_857_mid_safe joint_register_857_tail_safe joint_register_857_identity Old Typed Reset Source Size Commit).
 destruct index as [|index].
 - exact (rf_storage_normal_commit_certificate 867 joint_register_858_decl joint_register_858_mid joint_register_858_tail 858 joint_register_858_reg 1092 1028 invalid old current result old_value word
 joint_register_858_position joint_register_858_split joint_register_858_straight joint_register_858_mid_safe joint_register_858_tail_safe joint_register_858_identity Old Typed Reset Source Size Commit).
 destruct index as [|index].
 - exact (rf_storage_normal_commit_certificate 868 joint_register_859_decl joint_register_859_mid joint_register_859_tail 859 joint_register_859_reg 1093 1029 invalid old current result old_value word
 joint_register_859_position joint_register_859_split joint_register_859_straight joint_register_859_mid_safe joint_register_859_tail_safe joint_register_859_identity Old Typed Reset Source Size Commit).
 destruct index as [|index].
 - exact (rf_storage_normal_commit_certificate 869 joint_register_860_decl joint_register_860_mid joint_register_860_tail 860 joint_register_860_reg 1094 1030 invalid old current result old_value word
 joint_register_860_position joint_register_860_split joint_register_860_straight joint_register_860_mid_safe joint_register_860_tail_safe joint_register_860_identity Old Typed Reset Source Size Commit).
 destruct index as [|index].
 - exact (rf_storage_normal_commit_certificate 870 joint_register_861_decl joint_register_861_mid joint_register_861_tail 861 joint_register_861_reg 1095 1031 invalid old current result old_value word
 joint_register_861_position joint_register_861_split joint_register_861_straight joint_register_861_mid_safe joint_register_861_tail_safe joint_register_861_identity Old Typed Reset Source Size Commit).
 destruct index as [|index].
 - exact (rf_storage_normal_commit_certificate 871 joint_register_862_decl joint_register_862_mid joint_register_862_tail 862 joint_register_862_reg 1096 1032 invalid old current result old_value word
 joint_register_862_position joint_register_862_split joint_register_862_straight joint_register_862_mid_safe joint_register_862_tail_safe joint_register_862_identity Old Typed Reset Source Size Commit).
 destruct index as [|index].
 - exact (rf_storage_normal_commit_certificate 872 joint_register_863_decl joint_register_863_mid joint_register_863_tail 863 joint_register_863_reg 1097 1033 invalid old current result old_value word
 joint_register_863_position joint_register_863_split joint_register_863_straight joint_register_863_mid_safe joint_register_863_tail_safe joint_register_863_identity Old Typed Reset Source Size Commit).
 destruct index as [|index].
 - exact (rf_storage_normal_commit_certificate 873 joint_register_864_decl joint_register_864_mid joint_register_864_tail 864 joint_register_864_reg 1098 1034 invalid old current result old_value word
 joint_register_864_position joint_register_864_split joint_register_864_straight joint_register_864_mid_safe joint_register_864_tail_safe joint_register_864_identity Old Typed Reset Source Size Commit).
 destruct index as [|index].
 - exact (rf_storage_normal_commit_certificate 874 joint_register_865_decl joint_register_865_mid joint_register_865_tail 865 joint_register_865_reg 1099 1035 invalid old current result old_value word
 joint_register_865_position joint_register_865_split joint_register_865_straight joint_register_865_mid_safe joint_register_865_tail_safe joint_register_865_identity Old Typed Reset Source Size Commit).
 destruct index as [|index].
 - exact (rf_storage_normal_commit_certificate 875 joint_register_866_decl joint_register_866_mid joint_register_866_tail 866 joint_register_866_reg 1100 1036 invalid old current result old_value word
 joint_register_866_position joint_register_866_split joint_register_866_straight joint_register_866_mid_safe joint_register_866_tail_safe joint_register_866_identity Old Typed Reset Source Size Commit).
 destruct index as [|index].
 - exact (rf_storage_normal_commit_certificate 876 joint_register_867_decl joint_register_867_mid joint_register_867_tail 867 joint_register_867_reg 1101 1037 invalid old current result old_value word
 joint_register_867_position joint_register_867_split joint_register_867_straight joint_register_867_mid_safe joint_register_867_tail_safe joint_register_867_identity Old Typed Reset Source Size Commit).
 destruct index as [|index].
 - exact (rf_storage_normal_commit_certificate 877 joint_register_868_decl joint_register_868_mid joint_register_868_tail 868 joint_register_868_reg 1102 1038 invalid old current result old_value word
 joint_register_868_position joint_register_868_split joint_register_868_straight joint_register_868_mid_safe joint_register_868_tail_safe joint_register_868_identity Old Typed Reset Source Size Commit).
 destruct index as [|index].
 - exact (rf_storage_normal_commit_certificate 878 joint_register_869_decl joint_register_869_mid joint_register_869_tail 869 joint_register_869_reg 1103 1039 invalid old current result old_value word
 joint_register_869_position joint_register_869_split joint_register_869_straight joint_register_869_mid_safe joint_register_869_tail_safe joint_register_869_identity Old Typed Reset Source Size Commit).
 destruct index as [|index].
 - exact (rf_storage_normal_commit_certificate 879 joint_register_870_decl joint_register_870_mid joint_register_870_tail 870 joint_register_870_reg 1104 1040 invalid old current result old_value word
 joint_register_870_position joint_register_870_split joint_register_870_straight joint_register_870_mid_safe joint_register_870_tail_safe joint_register_870_identity Old Typed Reset Source Size Commit).
 destruct index as [|index].
 - exact (rf_storage_normal_commit_certificate 880 joint_register_871_decl joint_register_871_mid joint_register_871_tail 871 joint_register_871_reg 1105 1041 invalid old current result old_value word
 joint_register_871_position joint_register_871_split joint_register_871_straight joint_register_871_mid_safe joint_register_871_tail_safe joint_register_871_identity Old Typed Reset Source Size Commit).
 destruct index as [|index].
 - exact (rf_storage_normal_commit_certificate 881 joint_register_872_decl joint_register_872_mid joint_register_872_tail 872 joint_register_872_reg 1106 1042 invalid old current result old_value word
 joint_register_872_position joint_register_872_split joint_register_872_straight joint_register_872_mid_safe joint_register_872_tail_safe joint_register_872_identity Old Typed Reset Source Size Commit).
 destruct index as [|index].
 - exact (rf_storage_normal_commit_certificate 882 joint_register_873_decl joint_register_873_mid joint_register_873_tail 873 joint_register_873_reg 1107 1043 invalid old current result old_value word
 joint_register_873_position joint_register_873_split joint_register_873_straight joint_register_873_mid_safe joint_register_873_tail_safe joint_register_873_identity Old Typed Reset Source Size Commit).
 destruct index as [|index].
 - exact (rf_storage_normal_commit_certificate 883 joint_register_874_decl joint_register_874_mid joint_register_874_tail 874 joint_register_874_reg 1108 1044 invalid old current result old_value word
 joint_register_874_position joint_register_874_split joint_register_874_straight joint_register_874_mid_safe joint_register_874_tail_safe joint_register_874_identity Old Typed Reset Source Size Commit).
 destruct index as [|index].
 - exact (rf_storage_normal_commit_certificate 884 joint_register_875_decl joint_register_875_mid joint_register_875_tail 875 joint_register_875_reg 1109 1045 invalid old current result old_value word
 joint_register_875_position joint_register_875_split joint_register_875_straight joint_register_875_mid_safe joint_register_875_tail_safe joint_register_875_identity Old Typed Reset Source Size Commit).
 destruct index as [|index].
 - exact (rf_storage_normal_commit_certificate 885 joint_register_876_decl joint_register_876_mid joint_register_876_tail 876 joint_register_876_reg 1110 1046 invalid old current result old_value word
 joint_register_876_position joint_register_876_split joint_register_876_straight joint_register_876_mid_safe joint_register_876_tail_safe joint_register_876_identity Old Typed Reset Source Size Commit).
 destruct index as [|index].
 - exact (rf_storage_normal_commit_certificate 886 joint_register_877_decl joint_register_877_mid joint_register_877_tail 877 joint_register_877_reg 1111 1047 invalid old current result old_value word
 joint_register_877_position joint_register_877_split joint_register_877_straight joint_register_877_mid_safe joint_register_877_tail_safe joint_register_877_identity Old Typed Reset Source Size Commit).
 destruct index as [|index].
 - exact (rf_storage_normal_commit_certificate 887 joint_register_878_decl joint_register_878_mid joint_register_878_tail 878 joint_register_878_reg 1112 1048 invalid old current result old_value word
 joint_register_878_position joint_register_878_split joint_register_878_straight joint_register_878_mid_safe joint_register_878_tail_safe joint_register_878_identity Old Typed Reset Source Size Commit).
 destruct index as [|index].
 - exact (rf_storage_normal_commit_certificate 888 joint_register_879_decl joint_register_879_mid joint_register_879_tail 879 joint_register_879_reg 1113 1049 invalid old current result old_value word
 joint_register_879_position joint_register_879_split joint_register_879_straight joint_register_879_mid_safe joint_register_879_tail_safe joint_register_879_identity Old Typed Reset Source Size Commit).
 destruct index as [|index].
 - exact (rf_storage_normal_commit_certificate 889 joint_register_880_decl joint_register_880_mid joint_register_880_tail 880 joint_register_880_reg 1114 1050 invalid old current result old_value word
 joint_register_880_position joint_register_880_split joint_register_880_straight joint_register_880_mid_safe joint_register_880_tail_safe joint_register_880_identity Old Typed Reset Source Size Commit).
 destruct index as [|index].
 - exact (rf_storage_normal_commit_certificate 890 joint_register_881_decl joint_register_881_mid joint_register_881_tail 881 joint_register_881_reg 1115 1051 invalid old current result old_value word
 joint_register_881_position joint_register_881_split joint_register_881_straight joint_register_881_mid_safe joint_register_881_tail_safe joint_register_881_identity Old Typed Reset Source Size Commit).
 destruct index as [|index].
 - exact (rf_storage_normal_commit_certificate 891 joint_register_882_decl joint_register_882_mid joint_register_882_tail 882 joint_register_882_reg 1116 1052 invalid old current result old_value word
 joint_register_882_position joint_register_882_split joint_register_882_straight joint_register_882_mid_safe joint_register_882_tail_safe joint_register_882_identity Old Typed Reset Source Size Commit).
 lia.
Qed.
Theorem rf_dut_no_write_commit invalid old current result bank :
 rf_dut_bank_at old bank -> VM.find 779 old = Some (Gval (Fuint 1) [::false]) ->
 (forall index, (index < 32)%coq_nat -> VM.find (N.of_nat (1021+index)%nat) old = Some (Gval (Fuint 32) (bank index))) ->
 formal_value_iter invalid flat_memories old true current flat_statements = Some result ->
 rf_dut_bank_at result bank.
Proof.
 intros Bank Reset Sources Commit index Bound.
 destruct (Bank index Bound) as [Size Old]. split;[exact Size|].
 exact (rf_dut_normal_commit_value invalid old current result index (Gval (Fuint 32) (bank index)) (bank index) Bound Old (Logic.eq_refl _) Reset (Sources index Bound) Size Commit).
Qed.
Theorem rf_dut_no_write_after_four_and_commit invalid s0 s1 s2 s3 s4 result bank :
 rf_dut_bank_at s0 bank -> VM.find 954 s3 = Some (Gval (Fuint 1) [::false]) ->
 VM.find 779 s4 = Some (Gval (Fuint 1) [::false]) ->
 formal_value_iter invalid flat_memories s0 false s0 flat_statements = Some s1 ->
 formal_value_iter invalid flat_memories s1 false s1 flat_statements = Some s2 ->
 formal_value_iter invalid flat_memories s2 false s2 flat_statements = Some s3 ->
 formal_value_iter invalid flat_memories s3 false s3 flat_statements = Some s4 ->
 formal_value_iter invalid flat_memories s4 true s4 flat_statements = Some result ->
 rf_dut_bank_at result bank.
Proof.
 intros Bank Gate Reset S1 S2 S3 S4 Commit.
 pose proof (rf_dut_bank_comb_hold invalid s0 s0 s1 bank Bank S1) as B1.
 pose proof (rf_dut_bank_comb_hold invalid s1 s1 s2 bank B1 S2) as B2.
 pose proof (rf_dut_bank_comb_hold invalid s2 s2 s3 bank B2 S3) as B3.
 pose proof (rf_dut_bank_comb_hold invalid s3 s3 s4 bank B3 S4) as B4.
 exact (rf_dut_no_write_commit invalid s4 s4 result bank B4 Reset
 (rf_dut_no_write_sources_after_four invalid s0 s1 s2 s3 s4 bank Bank Gate S1 S2 S3 S4) Commit).
Qed.
Lemma rf_dut_bank_history_hold invalid history limit bank :
 rf_dut_bank_at (history 0%nat) bank ->
 (forall t, (t < limit)%coq_nat -> formal_value_iter invalid flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (t <= limit)%coq_nat -> rf_dut_bank_at (history t) bank.
Proof.
 intros Initial Steps t. induction t as [|t IH]; intro Bound;[exact Initial|].
 exact (rf_dut_bank_comb_hold invalid (history t) (history t) (history (S t)) bank (IH ltac:(lia)) (Steps t ltac:(lia))).
Qed.
Lemma rf_dut_bank_circuit_hold inputs n initial stable bank :
 rf_dut_bank_at (top_environment initial) bank ->
 circuit_formal_iterations generated_modules generated_top inputs n initial = Some stable ->
 rf_dut_bank_at (top_environment stable) bank.
Proof.
 intros Bank Iterations. destruct (local_iteration_history inputs n initial stable Iterations) as [history [First [Last Steps]]].
 rewrite <- Last. apply (rf_dut_bank_history_hold (formal_invalid_policy inputs nil) history n bank);[rewrite First;exact Bank|exact Steps|lia].
Qed.
Require Import StagedIterationLemmas FormalInstructionResetCycle FormalInstructionResetConstants.
Theorem rf_dut_nop_settle_and_commit inputs initial stable result bank :
 rf_dut_bank_at (top_environment initial) bank ->
 staged_register_lookup 7750 initial = Some (Gval (Fuint 32) instruction_nop) ->
 state_reset initial false ->
 circuit_formal_iterations generated_modules generated_top inputs 9259 initial = Some stable ->
 formal_circuit_value_iter (formal_invalid_policy inputs) generated_modules generated_top stable true = Some result ->
 exists env, SVM.find nil result = Some env /\ rf_dut_bank_at env bank.
Proof.
 intros Bank Instruction Reset Iterations Commit.
 destruct (rf_control_9259 inputs initial stable false Reset Iterations) as [control [Control ResetBit]].
 pose proof Iterations as Split.
 change (circuit_formal_iterations generated_modules generated_top inputs (Nat.add 9255 4) initial = Some stable) in Split.
 rewrite formal_iterations_append in Split.
 destruct (circuit_formal_iterations generated_modules generated_top inputs 9255 initial) as [middle|] eqn:Prefix;[|discriminate Split].
 cbn [circuit_formal_iterations] in Split.
 destruct (formal_circuit_value_iter (formal_invalid_policy inputs) generated_modules generated_top middle false) as [s1|] eqn:S1;[|discriminate Split].
 destruct (formal_circuit_value_iter (formal_invalid_policy inputs) generated_modules generated_top s1 false) as [s2|] eqn:S2;[|discriminate Split].
 destruct (formal_circuit_value_iter (formal_invalid_policy inputs) generated_modules generated_top s2 false) as [s3|] eqn:S3;[|discriminate Split].
 destruct (formal_circuit_value_iter (formal_invalid_policy inputs) generated_modules generated_top s3 false) as [s4|] eqn:S4;[|discriminate Split].
 inversion Split;subst s4.
 assert (Prefix3 : circuit_formal_iterations generated_modules generated_top inputs 9258 initial = Some s3).
 { change (circuit_formal_iterations generated_modules generated_top inputs (Nat.add 9255 3) initial = Some s3).
   rewrite formal_iterations_append Prefix. cbn [circuit_formal_iterations]. rewrite S1 S2 S3. reflexivity. }
 destruct (rf_nop_disables_settled inputs 9254 initial s3 Instruction Prefix3) as [guard [Guard Disabled]].
 assert (Gate : VM.find 954 (top_environment s3) = Some (Gval (Fuint 1) [::false])).
 { unfold top_environment. rewrite Guard. exact Disabled. }
 assert (Reset779 : VM.find 779 (top_environment stable) = Some (Gval (Fuint 1) [::false])).
 { unfold top_environment. rewrite Control. exact ResetBit. }
 destruct (flat_iteration_projection (formal_invalid_policy inputs) stable true result Commit) as [before [after [Before [Local After]]]].
 assert (Top : top_environment stable = before) by (unfold top_environment;rewrite Before;reflexivity).
 rewrite <- Top in Local.
 exists after;split;[exact After|].
 exact (rf_dut_no_write_after_four_and_commit (formal_invalid_policy inputs nil)
 (top_environment middle) (top_environment s1) (top_environment s2) (top_environment s3) (top_environment stable) after bank
 (rf_dut_bank_circuit_hold inputs 9255 initial middle bank Bank Prefix) Gate Reset779
 (circuit_step_local inputs middle s1 S1) (circuit_step_local inputs s1 s2 S2) (circuit_step_local inputs s2 s3 S3) (circuit_step_local inputs s3 stable S4) Local).
Qed.
Lemma rf_dut_bank_prepared previous old external initial bank :
 SVM.find nil previous = Some old -> rf_dut_bank_at old bank ->
 circuit_initial_map_with_memory generated_modules generated_top (Some previous) external = Some initial ->
 rf_dut_bank_at (top_environment initial) bank.
Proof.
 intros Previous Bank Prepare index Bound. destruct (Bank index Bound) as [Size Value]. split;[exact Size|].
 pose proof (rf_dut_register_member index Bound) as Member.
 destruct (rf_architectural_nonexternal _ Member) as [Nonclock Nonreset].
 destruct (rf_architectural_register_properties _ Member) as [Present [Typed Safe]].
 pose proof (staged_prepared_register_copies previous old external initial _ Nonclock Nonreset Safe Present Previous Prepare) as Copy.
 rewrite Value in Copy. unfold staged_register_lookup in Copy. unfold top_environment.
 destruct (SVM.find nil initial);[exact Copy|discriminate Copy].
Qed.
Theorem rf_dut_nop_real_cycle inputs previous old result bank :
 SVM.find nil previous = Some old -> rf_dut_bank_at old bank ->
 VM.find 7750 old = Some (Gval (Fuint 32) instruction_nop) ->
 VM.find 1 (formal_external_inputs inputs) = Some (Gval (Fuint 1) [::false]) ->
 circuit_formal_cycle generated_modules generated_top (Some previous) inputs = Some result ->
 exists env, SVM.find nil result = Some env /\ rf_dut_bank_at env bank.
Proof.
 intros Previous Bank Instruction Reset Cycle. unfold circuit_formal_cycle in Cycle.
 destruct (circuit_initial_map_with_memory generated_modules generated_top (Some previous) (formal_external_inputs inputs)) as [initial|] eqn:Prepare;[|discriminate Cycle].
 pose proof flat_iteration_count_exact as Count. unfold flat_iteration_count in Count. rewrite Count in Cycle.
 destruct (circuit_formal_iterations generated_modules generated_top inputs 9259 initial) as [stable|] eqn:Iterations;[|discriminate Cycle].
 apply (rf_dut_nop_settle_and_commit inputs initial stable result bank);[| | |exact Iterations|exact Cycle].
 - exact (rf_dut_bank_prepared previous old _ initial bank Previous Bank Prepare).
 - destruct (instruction_register_shape 7750 ltac:(vm_compute;reflexivity)) as [Safe Present].
   rewrite (staged_prepared_register_copies previous old _ initial 7750 (Logic.eq_refl _) (Logic.eq_refl _) Safe Present Previous Prepare). exact Instruction.
 - exact (top_reset_prepared (Some previous) _ initial _ Reset Prepare).
Qed.
Corollary rf_dut_nop_real_cycle_effect inputs previous old result bank :
 SVM.find nil previous = Some old -> rf_dut_bank_at old bank -> bank 0%nat = nseq 32 false ->
 VM.find 7750 old = Some (Gval (Fuint 32) instruction_nop) ->
 VM.find 1 (formal_external_inputs inputs) = Some (Gval (Fuint 1) [::false]) ->
 circuit_formal_cycle generated_modules generated_top (Some previous) inputs = Some result ->
 exists env, SVM.find nil result = Some env /\ rf_dut_bank_at env (fun index => rf_apply_effect bank RFNoWrite index).
Proof.
 intros Previous Bank Zero Instruction Reset Cycle.
 destruct (rf_dut_nop_real_cycle inputs previous old result bank Previous Bank Instruction Reset Cycle) as [env [Env Next]].
 exists env;split;[exact Env|]. intros index Bound.
 rewrite (rf_apply_effect_no_write bank Zero index). exact (Next index Bound).
Qed.
