Require Import DataWriterNodePositions DataWriterExpressionCertificates DUTRedirectDecode CoreSocModel ComparisonNodes FormalDeclaredWireCheck JointUpdateNodePositions JointUpdateExpressionCertificates ReferenceRedirectSpine JointBoundaryRegisters JointUpdateBoundaryHistory FormalPCDecodeInputConnections.
From Coq Require Import NArith ZArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Definition load_type_values : seq N := [::0;0;0;0;0;0;0;0;0;0;3;2;1;5;4;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0].
Definition load_type_indices : seq nat := [::119%nat;118%nat;117%nat;116%nat;115%nat;114%nat;113%nat;112%nat;111%nat;110%nat;109%nat;108%nat;107%nat;106%nat;105%nat;104%nat;103%nat;102%nat;101%nat;100%nat;99%nat;98%nat;97%nat;96%nat;95%nat;94%nat;93%nat;92%nat;91%nat;90%nat;89%nat;88%nat;87%nat;86%nat;85%nat;84%nat;83%nat;82%nat;81%nat;80%nat;79%nat;78%nat;77%nat;76%nat;75%nat;74%nat;73%nat;72%nat;71%nat].
Lemma load_type_wire_8258_checked : declared_wire_check flat_memories flat_statements 9018%nat 749%nat 8258 8801 3%nat = true.
Proof. vm_compute. reflexivity. Qed.
Lemma load_type_wire_92_checked : declared_wire_check flat_memories flat_statements 69%nat 9928%nat 92 8258 3%nat = true.
Proof. vm_compute. reflexivity. Qed.
Local Opaque flat_statements flat_memories generated_modules generated_top.
(* Load type decode and pipeline correspondence. *)
Definition load_type_row n := nth 0 load_type_values n.
Definition load_type_mux_node n := 8753 + N.of_nat n.
Definition load_type_mux_expression n :=
 @Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T (dut_decode_guard_node (Nat.sub 48 n))))
 (@Econst VarOrder.T (Fuint 3) (from_N 3 (load_type_row (Nat.sub 48 n))))
 (match n with O => @Econst VarOrder.T (Fuint 3) (from_N 3 0)
 | S before => @Eref VarOrder.T (@Eid VarOrder.T (load_type_mux_node before)) end).
Fixpoint load_type_decode instruction count :=
 match count with O => from_N 3 0
 | S n => if dut_decode_test instruction (Nat.sub 48 n) then
  from_N 3 (load_type_row (Nat.sub 48 n)) else load_type_decode instruction n end.
Lemma load_type_mux_certificates n : (n < 49)%coq_nat ->
 nth_error data_writer_expected_nodes (nth 0%nat load_type_indices (Nat.sub 48 n)) =
 Some (load_type_mux_node n,load_type_mux_expression n).
Proof. intro Bound. do 49 (destruct n as [|n]; [vm_compute;reflexivity|]);lia. Qed.
Lemma load_type_decode_size instruction count : size (load_type_decode instruction count) = 3%nat.
Proof.
 induction count as [|count IH];cbn [load_type_decode];[apply size_from_N|].
 destruct (dut_decode_test instruction (Nat.sub 48 count));[apply size_from_N|exact IH].
Qed.
Theorem load_type_mux_history inputs path history limit instruction :
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 (forall i, ((2 <= i)%coq_nat /\ (i <= limit)%coq_nat) -> VM.find 8249 (history i) = Some (Gval (Fuint 32) instruction)) ->
 forall n time, (n < 49)%coq_nat -> (Nat.add 5 n <= time)%coq_nat -> (time <= limit)%coq_nat ->
 VM.find (load_type_mux_node n) (history time) = Some (Gval (Fuint 3) (load_type_decode (to_N instruction) (S n))).
Proof.
 intros Steps Instruction n. induction n as [|n IH]; intros time Bound Lower Upper; destruct time as [|time]; try lia.
 - eapply (reference_redirect_ground_step data_writer_node_offsets data_writer_expected_nodes _ (load_type_mux_expression 0));
   [exact data_writer_node_positions|exact data_writer_node_safety|eapply List.nth_error_In; apply load_type_mux_certificates; lia| |apply Steps; lia].
   intros site. unfold load_type_mux_expression. change (48-0)%nat with 48%nat.
   cbn [load_type_decode]. eapply dut_decode_mux_eval.
   + intros inner. cbn [eval_hfexpr_validif_policy eval_href_validif_policy]. apply (dut_decode_guard_history inputs path history limit instruction 48 ltac:(lia) Steps Instruction time); lia.
   + intro inner. apply dut_decode_constant.
   + intro inner. apply dut_decode_constant.
   + apply dut_decode_constant_type.
   + apply dut_decode_constant_type.
   + apply size_from_N.
   + apply size_from_N.
 - pose proof (IH time ltac:(lia) ltac:(lia) ltac:(lia)) as Previous.
   eapply (reference_redirect_ground_step data_writer_node_offsets data_writer_expected_nodes _ (load_type_mux_expression (S n)));
   [exact data_writer_node_positions|exact data_writer_node_safety|eapply List.nth_error_In; apply load_type_mux_certificates; lia| |apply Steps; lia].
   intros site. unfold load_type_mux_expression. cbn [load_type_decode]. eapply dut_decode_mux_eval.
   + intros inner. cbn [eval_hfexpr_validif_policy eval_href_validif_policy]. apply (dut_decode_guard_history inputs path history limit instruction (Nat.sub 48 (S n)) ltac:(lia) Steps Instruction time); lia.
   + intro inner. apply dut_decode_constant.
   + intro inner. exact Previous.
   + apply dut_decode_constant_type.
   + unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref]. rewrite Previous. reflexivity.
   + apply size_from_N.
   + exact (load_type_decode_size (to_N instruction) (S n)).
Qed.
Theorem load_type_decode_history inputs path history limit instruction :
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 VM.find 7748 (history limit) = Some (Gval (Fuint 32) instruction) -> size instruction = 32%nat ->
 forall time, (55 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 VM.find 92 (history time) = Some (Gval (Fuint 3) (load_type_decode (to_N instruction) 49)).
Proof.
 intros Steps Front Size time Lower Upper.
 assert (Source : forall i, (i <= limit)%coq_nat -> VM.find 7748 (history i) = Some (Gval (Fuint 32) instruction)).
 { intros i Bound.
   pose proof (joint_update_register_history_same (formal_invalid_policy inputs path) history limit 7748 32
     ltac:(apply (List.nth_error_In joint_boundary_registers 53%nat); vm_compute; reflexivity) Steps) as Hold.
   rewrite (Hold i Bound). rewrite <- (Hold limit ltac:(lia)). exact Front. }
 assert (Instruction : forall i, ((2 <= i)%coq_nat /\ (i <= limit)%coq_nat) -> VM.find 8249 (history i) = Some (Gval (Fuint 32) instruction)).
 { intros [|[|i]] Bound; try lia.
   eapply decode_input_connection_8249; [|apply dut_decode_adapt; exact Size|apply Steps; lia].
   eapply decode_input_connection_83; [|apply dut_decode_adapt; exact Size|apply Steps; lia]. apply Source; lia. }
 destruct time as [|[|time]]; try lia.
 eapply (declared_wire_checked_value flat_memories flat_statements 69%nat 9928%nat 92 8258 3);
 [exact load_type_wire_92_checked| |apply dut_decode_adapt;apply load_type_decode_size|apply Steps;lia].
 eapply (declared_wire_checked_value flat_memories flat_statements 9018%nat 749%nat 8258 8801 3);
 [exact load_type_wire_8258_checked| |apply dut_decode_adapt;apply load_type_decode_size|apply Steps;lia].
 exact (load_type_mux_history inputs path history limit instruction Steps Instruction 48 time ltac:(lia) ltac:(lia) ltac:(lia)).
Qed.
Definition load_type_lane_code lane : N := nth 0 [::20483;16387;8195;4099;3] lane.
Definition load_type_lane_kind lane : N := nth 0 [::4;5;1;2;3] lane.
Definition load_type_lane_row lane : nat := nth 0%nat [::14%nat;13%nat;12%nat;11%nat;10%nat] lane.
Definition load_type_is_load instruction lane := N.land (to_N instruction) 28799 = load_type_lane_code lane.
Lemma load_type_mask_projection instruction mask code :
 N.land mask 127 = 127 -> N.land instruction mask = code -> N.land instruction 127 = N.land code 127.
Proof.
 intros Mask Match. pose proof (f_equal (fun value => N.land value 127) Match) as Projection.
 rewrite -N.land_assoc Mask in Projection. exact Projection.
Qed.
Lemma load_type_nonload_row index : (index < 49)%coq_nat ->
 ((index < 10)%coq_nat \/ (14 < index)%coq_nat) ->
 N.land (dd_mask (dut_decode_row index)) 127 = 127 /\ N.land (dd_code (dut_decode_row index)) 127 <> 3.
Proof.
 intros Bound Other.
 do 49 (destruct index as [|index]; [first [lia|vm_compute;split;[reflexivity|discriminate]]|]). lia.
Qed.
Lemma load_type_other_guard instruction index : (index < 49)%coq_nat ->
 ((index < 10)%coq_nat \/ (14 < index)%coq_nat) -> N.land instruction 127 = 3 -> dut_decode_test instruction index = false.
Proof.
 intros Bound Other Opcode. unfold dut_decode_test. apply N.eqb_neq. intro Match.
 destruct (load_type_nonload_row index Bound Other) as [Mask Different].
 pose proof (load_type_mask_projection instruction _ _ Mask Match) as Projection.
 rewrite Opcode in Projection. apply Different. symmetry. exact Projection.
Qed.
Lemma load_type_load_guard instruction lane index :
 (lane < 5)%coq_nat -> (index < 49)%coq_nat ->
 N.land instruction 28799 = load_type_lane_code lane ->
 dut_decode_test instruction index = Nat.eqb index (load_type_lane_row lane).
Proof.
 intros Lane Index Code.
 assert (Opcode : N.land instruction 127 = 3).
 { pose proof (load_type_mask_projection instruction 28799 (load_type_lane_code lane) ltac:(reflexivity) Code) as E.
   rewrite E. do 5 (destruct lane as [|lane]; [reflexivity|]). lia. }
 assert (Outside : forall j, (j < 49)%coq_nat -> ((j < 10)%coq_nat \/ (14 < j)%coq_nat) ->
 dut_decode_test instruction j = Nat.eqb j (load_type_lane_row lane)).
 { intros j Bound Other. rewrite (load_type_other_guard instruction j Bound Other Opcode).
   symmetry. apply Nat.eqb_neq. do 5 (destruct lane as [|lane]; [cbv [load_type_lane_row nth];lia|]). lia. }
 do 10 (destruct index as [|index]; [apply Outside;lia|]).
 do 5 (destruct index as [|index];
 [do 5 (destruct lane as [|lane];
 [cbv [dut_decode_test dut_decode_row dut_decode_certificate_rows hd nth dd_mask dd_code];
 rewrite Code;reflexivity|]);lia|]).
 apply Outside;lia.
Qed.
Theorem load_type_decode_load instruction lane : (lane < 5)%coq_nat ->
 N.land instruction 28799 = load_type_lane_code lane ->
 load_type_decode instruction 49 = from_N 3 (load_type_lane_kind lane).
Proof.
 intros Lane Code. cbn [load_type_decode].
 repeat match goal with |- context[dut_decode_test instruction ?index] =>
 rewrite (load_type_load_guard instruction lane index Lane ltac:(vm_compute;lia) Code) end.
 do 5 (destruct lane as [|lane]; [reflexivity|]). lia.
Qed.
Lemma load_type_nop_not_load lane : (lane < 5)%coq_nat ->
 ~load_type_is_load FormalInstructionResetConstants.instruction_nop lane.
Proof. intros Lane. do 5 (destruct lane as [|lane]; [vm_compute;discriminate|]). lia. Qed.
Require Import ConcreteRegisterInitialization RFNonAluBubbleHazard JointRegisterCommits7 InstructionNormalTransfer StagedRegisterHold FormalPipelineControlHistory FormalStallHistory FormalCheckerResetConnections ExceptionSourceNoTrap EarlyBubbleNopFullHistory.
Lemma load_type_register_member : List.In (7755%nat,3%nat) joint_boundary_registers.
Proof. apply (List.nth_error_In joint_boundary_registers 60%nat). vm_compute. reflexivity. Qed.
Lemma load_type_instruction_member : List.In (7750%nat,32%nat) joint_boundary_registers.
Proof. apply (List.nth_error_In joint_boundary_registers 55%nat). vm_compute. reflexivity. Qed.
Theorem load_type_advance invalid s0 s1 s2 result previous word :
 size previous = 3%nat -> size word = 3%nat ->
 VM.find 7755 s0 = Some (Gval (Fuint 3) previous) -> VM.find 92 s0 = Some (Gval (Fuint 3) word) ->
 VM.find 7855 s0 = Some (Gval (Fuint 1) [::true]) -> VM.find 7852 s1 = Some (Gval (Fuint 1) [::false]) ->
 formal_value_iter invalid flat_memories s0 false s0 flat_statements = Some s1 ->
 formal_value_iter invalid flat_memories s1 false s1 flat_statements = Some s2 ->
 formal_value_iter invalid flat_memories s2 true s2 flat_statements = Some result ->
 VM.find 7755 result = Some (Gval (Fuint 3) word).
Proof.
 intros PreviousSize Size Previous Word Advance Flush S1 S2 Commit.
 assert (Old2 : VM.find 7755 s2 = Some (Gval (Fuint 3) previous)).
 { rewrite (staged_combinational_holds_registers invalid flat_memories s1 s1 s2 flat_statements 7755
   (proj2 (joint_boundary_register_properties 7755 3 load_type_register_member)) S2).
   rewrite (staged_combinational_holds_registers invalid flat_memories s0 s0 s1 flat_statements 7755
   (proj2 (joint_boundary_register_properties 7755 3 load_type_register_member)) S1). exact Previous. }
 assert (A : VM.find 7865 s1 = Some (Gval (Fuint 3) word)).
 { eapply (reference_redirect_ground_step joint_update_node_offsets joint_update_expected_nodes 7865 joint_update_expr_7865);
   [exact joint_update_node_positions|exact joint_update_node_safety| | |exact S1].
   - apply (List.nth_error_In joint_update_expected_nodes 920%nat). vm_compute. reflexivity.
   - intros site. cbn [joint_update_expr_7865 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Advance.
     cbn. unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref]. rewrite Word Previous.
     change (adapt_hvalue_as_type (Gval (Fuint 3) word) (Gtyp (Fuint 3)) = Some (Gval (Fuint 3) word)).
     apply dut_decode_adapt. exact Size. }
 assert (B : VM.find 7872 s2 = Some (Gval (Fuint 3) word)).
 { eapply (reference_redirect_ground_step joint_update_node_offsets joint_update_expected_nodes 7872 joint_update_expr_7872);
   [exact joint_update_node_positions|exact joint_update_node_safety| | |exact S2].
   - apply (List.nth_error_In joint_update_expected_nodes 927%nat). vm_compute. reflexivity.
   - intros site. cbn [joint_update_expr_7872 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Flush.
     cbn. rewrite A.
     change (adapt_hvalue_as_type (Gval (Fuint 3) word) (Gtyp (Fuint 3)) = Some (Gval (Fuint 3) word)).
     apply dut_decode_adapt. exact Size. }
 eapply (rf_control_direct_commit_exact 8261 flat_statements joint_register_7755_decl joint_register_7755_mid joint_register_7755_tail 7755 7872 joint_register_7755_reg 3 word);
 [exact joint_register_7755_position|exact joint_register_7755_split|exact joint_register_7755_straight|exact joint_register_7755_mid_safe|exact joint_register_7755_tail_safe|exact joint_register_7755_identity|exact Old2|reflexivity|reflexivity|exact B|exact Size|exact Commit].
Qed.
Definition load_type_invariant env : Prop := forall instruction lane,
 (lane < 5)%coq_nat -> VM.find 7750 env = Some (Gval (Fuint 32) instruction) -> load_type_is_load instruction lane ->
 VM.find 7755 env = Some (Gval (Fuint 3) (from_N 3 (load_type_lane_kind lane))).
Theorem load_type_normal_fullhistory inputs path history result :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall time, (time < 9259)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history time) false (history time) flat_statements = Some (history (S time))) ->
 (forall time, (time <= 9259)%coq_nat -> VM.find 1 (history time) = Some (Gval (Fuint 1) [::false])) ->
 VM.find 45 (history 9254%nat) = Some (Gval (Fuint 1) [::false]) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories (history 9259%nat) true (history 9259%nat) flat_statements = Some result ->
 load_type_invariant result.
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
 intros instruction lane Lane Instruction Load. rewrite NextInst in Instruction. inversion Instruction;subst instruction.
 unfold load_type_is_load in Load. rewrite (load_type_decode_load (to_N front) lane Lane Load) in NextType. exact NextType.
Qed.
Require Import StagedCircuitRegisterHold FormalLocalHistory FormalObservationCommit StagedFlatCircuitIteration ObservedLegalNoTrap JointBoundaryReachable JointBoundaryInitialization JointBoundaryPreparation FormalFetchType FormalResetPreparation RegisterPreparationFrames StagedObservedRegister FormalInstructionResetBase FormalInstructionResetCycle JointBoundaryInduction ExternalReset StagedIterationCount.
Local Opaque generated_run.
Theorem load_type_normal_successor memory inputs k observed next :
 generated_observe memory inputs k = Some observed -> generated_legal_trace memory inputs k ->
 generated_run memory inputs (S k) = Some next ->
 VM.find 1 (formal_external_inputs (generated_observation_input inputs k)) = Some (Gval (Fuint 1) [::false]) ->
 load_type_invariant (top_environment next).
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
 exact (load_type_normal_fullhistory (generated_observation_input inputs k) nil history after Boundary Steps Resets NoTrap Step).
Qed.
Lemma load_type_nop_invariant env : VM.find 7750 env = Some (Gval (Fuint 32) FormalInstructionResetConstants.instruction_nop) -> load_type_invariant env.
Proof.
 intros Nop instruction lane Lane Instruction Load. rewrite Nop in Instruction. inversion Instruction;subst instruction.
 exfalso. exact (load_type_nop_not_load lane Lane Load).
Qed.
Theorem load_type_run memory inputs k states :
 generated_run memory inputs k = Some states -> generated_legal_trace memory inputs k -> load_type_invariant (top_environment states).
Proof.
 destruct k as [|k];intros Run Legal.
 - destruct (instruction_run_zero memory inputs states Run) as [env [Env [Front Nop]]].
   unfold top_environment. rewrite Env. exact (load_type_nop_invariant env Nop).
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
     unfold top_environment. rewrite Env. exact (load_type_nop_invariant env Nop).
   + destruct (generated_successful_commit memory inputs k states Run) as [observed [Observe Commit]].
     exact (load_type_normal_successor memory inputs k observed states Observe PriorLegal Run Reset).
Qed.
Lemma load_type_comb_hold invalid old current result :
 load_type_invariant old -> formal_value_iter invalid flat_memories old false current flat_statements = Some result -> load_type_invariant result.
Proof.
 intros Invariant Step instruction lane Lane Instruction Load.
 rewrite (staged_combinational_holds_registers invalid flat_memories old current result flat_statements 7750
 (proj2 (joint_boundary_register_properties 7750 32 load_type_instruction_member)) Step) in Instruction.
 rewrite (staged_combinational_holds_registers invalid flat_memories old current result flat_statements 7755
 (proj2 (joint_boundary_register_properties 7755 3 load_type_register_member)) Step).
 exact (Invariant instruction lane Lane Instruction Load).
Qed.
Lemma load_type_history_hold invalid history (limit:nat) :
 load_type_invariant (history 0%nat) ->
 (forall time, (time < limit)%coq_nat -> formal_value_iter invalid flat_memories (history time) false (history time) flat_statements = Some (history (S time))) ->
 forall time, (time <= limit)%coq_nat -> load_type_invariant (history time).
Proof.
 intros Initial Steps time. induction time as [|time IH];intro Bound;[exact Initial|].
 exact (load_type_comb_hold invalid (history time) (history time) (history (S time)) (IH ltac:(lia)) (Steps time ltac:(lia))).
Qed.
Lemma load_type_prepared previous old external initial :
 SVM.find nil previous = Some old -> load_type_invariant old ->
 circuit_initial_map_with_memory generated_modules generated_top (Some previous) external = Some initial -> load_type_invariant (top_environment initial).
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
 intros instruction lane Lane Instruction Load.
 unfold staged_register_lookup in InstructionCopy,TypeCopy. unfold top_environment in *.
 destruct (SVM.find nil initial) as [env|];[|discriminate Instruction].
 rewrite InstructionCopy in Instruction. rewrite TypeCopy.
 exact (Invariant instruction lane Lane Instruction Load).
Qed.
Theorem load_type_observed memory inputs k observed :
 generated_observe memory inputs k = Some observed -> generated_legal_trace memory inputs k -> load_type_invariant (top_environment observed).
Proof.
 intros Observe Legal. pose proof Observe as Expanded. unfold generated_observe,generated_observe_cycle in Expanded.
 destruct (generated_run memory inputs k) as [previous|] eqn:Run;[|discriminate Expanded].
 destruct (circuit_initial_map_with_memory generated_modules generated_top (Some previous) (formal_external_inputs (generated_observation_input inputs k))) as [initial|] eqn:Prepare;[|discriminate Expanded].
 pose proof flat_iteration_count_exact as Count. unfold flat_iteration_count in Count. rewrite Count in Expanded.
 destruct (local_iteration_history (generated_observation_input inputs k) 9259 initial observed Expanded) as [history [First [Last Steps]]].
 pose proof (load_type_run memory inputs k previous Run Legal) as Invariant.
 destruct (fetch9220_run_type memory inputs k previous Run) as [old [value [Old Rest]]].
 unfold top_environment in Invariant. rewrite Old in Invariant.
 rewrite <- Last. eapply (load_type_history_hold _ history 9259);
 [rewrite First;exact (load_type_prepared previous old _ initial Old Invariant Prepare)|exact Steps|vm_compute;lia].
Qed.
Theorem load_type_instruction_observed memory inputs k observed instruction lane :
 generated_observe memory inputs k = Some observed -> generated_legal_trace memory inputs k ->
 (lane < 5)%coq_nat -> VM.find 7750 (top_environment observed) = Some (Gval (Fuint 32) instruction) ->
 load_type_is_load instruction lane ->
 VM.find 7755 (top_environment observed) = Some (Gval (Fuint 3) (from_N 3 (load_type_lane_kind lane))).
Proof.
 intros Observe Legal Lane Instruction Load.
 exact (load_type_observed memory inputs k observed Observe Legal instruction lane Lane Instruction Load).
Qed.
