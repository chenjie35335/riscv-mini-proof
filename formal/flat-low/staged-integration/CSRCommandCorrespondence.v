Require Import DataWriterNodePositions DataWriterExpressionCertificates DUTRedirectDecode CoreSocModel ComparisonNodes FormalDeclaredWireCheck JointUpdateNodePositions JointUpdateExpressionCertificates ReferenceRedirectSpine JointBoundaryRegisters JointUpdateBoundaryHistory FormalPCDecodeInputConnections.
From Coq Require Import NArith ZArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Definition csr_command_values : seq N := [::0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;1;2;3;1;2;3;4;4;4;0].
Definition csr_command_indices : seq nat := [::1339%nat;1338%nat;1337%nat;1336%nat;1335%nat;1334%nat;1333%nat;1332%nat;1331%nat;1330%nat;1329%nat;1328%nat;1327%nat;1326%nat;1325%nat;1324%nat;1323%nat;1322%nat;1321%nat;1320%nat;1319%nat;1318%nat;1317%nat;1316%nat;1315%nat;1314%nat;1313%nat;1312%nat;1311%nat;1310%nat;1309%nat;1308%nat;1307%nat;1306%nat;1305%nat;1304%nat;1303%nat;1302%nat;1301%nat;1300%nat;1299%nat;1298%nat;1297%nat;1296%nat;1295%nat;1294%nat;1293%nat;1292%nat;1291%nat].
Lemma csr_command_wire_8261_checked : declared_wire_check flat_memories flat_statements 9021%nat 749%nat 8261 8948 3%nat = true.
Proof. vm_compute. reflexivity. Qed.
Lemma csr_command_wire_95_checked : declared_wire_check flat_memories flat_statements 72%nat 9928%nat 95 8261 3%nat = true.
Proof. vm_compute. reflexivity. Qed.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Definition csr_command_row n := nth 0 csr_command_values n.
Definition csr_command_mux_node n := 8900 + N.of_nat n.
Definition csr_command_mux_expression n :=
 @Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T (dut_decode_guard_node (Nat.sub 48 n))))
 (@Econst VarOrder.T (Fuint 3) (from_N 3 (csr_command_row (Nat.sub 48 n))))
 (match n with O => @Econst VarOrder.T (Fuint 3) (from_N 3 0)
 | S before => @Eref VarOrder.T (@Eid VarOrder.T (csr_command_mux_node before)) end).
Fixpoint csr_command_decode instruction count :=
 match count with O => from_N 3 0
 | S n => if dut_decode_test instruction (Nat.sub 48 n) then
  from_N 3 (csr_command_row (Nat.sub 48 n)) else csr_command_decode instruction n end.
Lemma csr_command_mux_certificates n : (n < 49)%coq_nat ->
 nth_error joint_update_expected_nodes (nth 0%nat csr_command_indices (Nat.sub 48 n)) =
 Some (csr_command_mux_node n,csr_command_mux_expression n).
Proof. intro Bound. do 49 (destruct n as [|n]; [vm_compute;reflexivity|]);lia. Qed.
Lemma csr_command_decode_size instruction count : size (csr_command_decode instruction count) = 3%nat.
Proof.
 induction count as [|count IH];cbn [csr_command_decode];[apply size_from_N|].
 destruct (dut_decode_test instruction (Nat.sub 48 count));[apply size_from_N|exact IH].
Qed.
Theorem csr_command_mux_history inputs path history limit instruction :
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 (forall i, ((2 <= i)%coq_nat /\ (i <= limit)%coq_nat) -> VM.find 8249 (history i) = Some (Gval (Fuint 32) instruction)) ->
 forall n time, (n < 49)%coq_nat -> (Nat.add 5 n <= time)%coq_nat -> (time <= limit)%coq_nat ->
 VM.find (csr_command_mux_node n) (history time) = Some (Gval (Fuint 3) (csr_command_decode (to_N instruction) (S n))).
Proof.
 intros Steps Instruction n. induction n as [|n IH]; intros time Bound Lower Upper; destruct time as [|time]; try lia.
 - eapply (reference_redirect_ground_step joint_update_node_offsets joint_update_expected_nodes _ (csr_command_mux_expression 0));
   [exact joint_update_node_positions|exact joint_update_node_safety|eapply List.nth_error_In; apply csr_command_mux_certificates; lia| |apply Steps; lia].
   intros site. unfold csr_command_mux_expression. change (48-0)%nat with 48%nat.
   cbn [csr_command_decode]. eapply dut_decode_mux_eval.
   + intros inner. cbn [eval_hfexpr_validif_policy eval_href_validif_policy]. apply (dut_decode_guard_history inputs path history limit instruction 48 ltac:(lia) Steps Instruction time); lia.
   + intro inner. apply dut_decode_constant.
   + intro inner. apply dut_decode_constant.
   + apply dut_decode_constant_type.
   + apply dut_decode_constant_type.
   + apply size_from_N.
   + apply size_from_N.
 - pose proof (IH time ltac:(lia) ltac:(lia) ltac:(lia)) as Previous.
   eapply (reference_redirect_ground_step joint_update_node_offsets joint_update_expected_nodes _ (csr_command_mux_expression (S n)));
   [exact joint_update_node_positions|exact joint_update_node_safety|eapply List.nth_error_In; apply csr_command_mux_certificates; lia| |apply Steps; lia].
   intros site. unfold csr_command_mux_expression. cbn [csr_command_decode]. eapply dut_decode_mux_eval.
   + intros inner. cbn [eval_hfexpr_validif_policy eval_href_validif_policy]. apply (dut_decode_guard_history inputs path history limit instruction (Nat.sub 48 (S n)) ltac:(lia) Steps Instruction time); lia.
   + intro inner. apply dut_decode_constant.
   + intro inner. exact Previous.
   + apply dut_decode_constant_type.
   + unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref]. rewrite Previous. reflexivity.
   + apply size_from_N.
   + exact (csr_command_decode_size (to_N instruction) (S n)).
Qed.
Theorem csr_command_decode_history inputs path history limit instruction :
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 VM.find 7748 (history limit) = Some (Gval (Fuint 32) instruction) -> size instruction = 32%nat ->
 forall time, (55 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 VM.find 95 (history time) = Some (Gval (Fuint 3) (csr_command_decode (to_N instruction) 49)).
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
 eapply (declared_wire_checked_value flat_memories flat_statements 72%nat 9928%nat 95 8261 3);
 [exact csr_command_wire_95_checked| |apply dut_decode_adapt;apply csr_command_decode_size|apply Steps;lia].
 eapply (declared_wire_checked_value flat_memories flat_statements 9021%nat 749%nat 8261 8948 3);
 [exact csr_command_wire_8261_checked| |apply dut_decode_adapt;apply csr_command_decode_size|apply Steps;lia].
 exact (csr_command_mux_history inputs path history limit instruction Steps Instruction 48 time ltac:(lia) ltac:(lia) ltac:(lia)).
Qed.
Lemma csr_command_ecall : csr_command_decode 115 49 = from_N 3 4.
Proof. vm_compute. reflexivity. Qed.
Lemma csr_command_ebreak : csr_command_decode 1048691 49 = from_N 3 4.
Proof. vm_compute. reflexivity. Qed.
Print Assumptions csr_command_ecall.
Print Assumptions csr_command_ebreak.
(* CSR pipeline extension. *)

Require Import ConcreteRegisterInitialization RFNonAluBubbleHazard JointRegisterCommits7 StagedRegisterHold.
Lemma csr_command_register_member : List.In (7758%nat,3%nat) joint_boundary_registers.
Proof. apply (List.nth_error_In joint_boundary_registers 63%nat). vm_compute. reflexivity. Qed.
Theorem csr_command_advance invalid s0 s1 s2 result previous word :
 size previous = 3%nat -> size word = 3%nat ->
 VM.find 7758 s0 = Some (Gval (Fuint 3) previous) -> VM.find 95 s0 = Some (Gval (Fuint 3) word) ->
 VM.find 7855 s0 = Some (Gval (Fuint 1) [::true]) -> VM.find 7852 s1 = Some (Gval (Fuint 1) [::false]) ->
 formal_value_iter invalid flat_memories s0 false s0 flat_statements = Some s1 ->
 formal_value_iter invalid flat_memories s1 false s1 flat_statements = Some s2 ->
 formal_value_iter invalid flat_memories s2 true s2 flat_statements = Some result ->
 VM.find 7758 result = Some (Gval (Fuint 3) word).
Proof.
 intros PreviousSize Size Previous Word Advance Flush S1 S2 Commit.
 assert (Old2 : VM.find 7758 s2 = Some (Gval (Fuint 3) previous)).
 { rewrite (staged_combinational_holds_registers invalid flat_memories s1 s1 s2 flat_statements 7758
   (proj2 (joint_boundary_register_properties 7758 3 csr_command_register_member)) S2).
   rewrite (staged_combinational_holds_registers invalid flat_memories s0 s0 s1 flat_statements 7758
   (proj2 (joint_boundary_register_properties 7758 3 csr_command_register_member)) S1). exact Previous. }
 assert (A : VM.find 7868 s1 = Some (Gval (Fuint 3) word)).
 { eapply (reference_redirect_ground_step joint_update_node_offsets joint_update_expected_nodes 7868 joint_update_expr_7868);
   [exact joint_update_node_positions|exact joint_update_node_safety| | |exact S1].
   - apply (List.nth_error_In joint_update_expected_nodes 923%nat). vm_compute. reflexivity.
   - intros site. cbn [joint_update_expr_7868 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Advance.
     cbn. unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref]. rewrite Word Previous.
     change (adapt_hvalue_as_type (Gval (Fuint 3) word) (Gtyp (Fuint 3)) = Some (Gval (Fuint 3) word)).
     apply dut_decode_adapt. exact Size. }
 assert (B : VM.find 7874 s2 = Some (Gval (Fuint 3) word)).
 { eapply (reference_redirect_ground_step joint_update_node_offsets joint_update_expected_nodes 7874 joint_update_expr_7874);
   [exact joint_update_node_positions|exact joint_update_node_safety| | |exact S2].
   - apply (List.nth_error_In joint_update_expected_nodes 929%nat). vm_compute. reflexivity.
   - intros site. cbn [joint_update_expr_7874 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Flush.
     cbn. rewrite A.
     change (adapt_hvalue_as_type (Gval (Fuint 3) word) (Gtyp (Fuint 3)) = Some (Gval (Fuint 3) word)).
     apply dut_decode_adapt. exact Size. }
 eapply (rf_control_direct_commit_exact 8264 flat_statements joint_register_7758_decl joint_register_7758_mid joint_register_7758_tail 7758 7874 joint_register_7758_reg 3 word);
 [exact joint_register_7758_position|exact joint_register_7758_split|exact joint_register_7758_straight|exact joint_register_7758_mid_safe|exact joint_register_7758_tail_safe|exact joint_register_7758_identity|exact Old2|reflexivity|reflexivity|exact B|exact Size|exact Commit].
Qed.

Require Import NormalPipelineTail LoadTypeCorrespondence InstructionNormalTransfer EarlyBubbleNopFullHistory.
Definition csr_pipeline_exact env : Prop := forall instruction,
 VM.find 7750 env = Some (Gval (Fuint 32) instruction) ->
 VM.find 7758 env = Some (Gval (Fuint 3) (csr_command_decode (to_N instruction) 49)).
Theorem csr_pipeline_normal_fullhistory inputs path history result :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall time, (time < 9259)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history time) false (history time) flat_statements = Some (history (S time))) ->
 (forall time, (time <= 9259)%coq_nat -> VM.find 1 (history time) = Some (Gval (Fuint 1) [::false])) ->
 VM.find 45 (history 9254%nat) = Some (Gval (Fuint 1) [::false]) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories (history 9259%nat) true (history 9259%nat) flat_statements = Some result ->
 csr_pipeline_exact result.
Proof.
 intros Boundary Steps Resets NoTrap Commit.
 destruct (joint_update_register_history_concrete _ history 9259 7748 32 early_bubble_front_instruction_member
 (Boundary _ _ early_bubble_front_instruction_member) Steps 9259 ltac:(vm_compute;lia)) as [front [FrontSize Front]].
 pose proof (csr_command_decode_history inputs path history 9259 front Steps Front FrontSize 9257 ltac:(vm_compute;lia) ltac:(vm_compute;lia)) as Decode.
 destruct (normal_pipeline_tail_controls inputs path history Boundary Steps Resets NoTrap) as [Advance Flush].
 destruct (joint_update_register_history_concrete _ history 9259 7758 3 csr_command_register_member
 (Boundary _ _ csr_command_register_member) Steps 9257 ltac:(vm_compute;lia)) as [previous [PreviousSize Previous]].
 pose proof (csr_command_advance _ (history 9257%nat) (history 9258%nat) (history 9259%nat) result previous _ PreviousSize
 (csr_command_decode_size (to_N front) 49) Previous Decode Advance Flush (Steps 9257%nat ltac:(vm_compute;lia)) (Steps 9258%nat ltac:(vm_compute;lia)) Commit) as NextType.
 destruct (joint_update_register_history_concrete _ history 9259 7750 32 load_type_instruction_member
 (Boundary _ _ load_type_instruction_member) Steps 9259 ltac:(vm_compute;lia)) as [old [OldSize Old]].
 pose proof (instruction_transfer_normal_full_history inputs path history result front old Boundary Steps Resets NoTrap FrontSize Front Old Commit) as NextInst.
 intros instruction Instruction. rewrite NextInst in Instruction. inversion Instruction;subst instruction. exact NextType.
Qed.

Definition csr_system_instruction instruction (lane:nat) :=
 instruction = from_N 32 (if Nat.eqb lane 0 then 115 else 1048691).
Definition csr_system_invariant env : Prop := forall instruction lane,
 (lane < 2)%coq_nat -> VM.find 7750 env = Some (Gval (Fuint 32) instruction) -> csr_system_instruction instruction lane ->
 VM.find 7758 env = Some (Gval (Fuint 3) (from_N 3 4)).
Lemma csr_system_decode instruction lane : (lane < 2)%coq_nat -> csr_system_instruction instruction lane ->
 csr_command_decode (to_N instruction) 49 = from_N 3 4.
Proof.
 intros Lane Code. unfold csr_system_instruction in Code. subst instruction.
 do 2 (destruct lane as [|lane]; [vm_compute;reflexivity|]). lia.
Qed.
Lemma csr_system_nop_not_load lane : (lane < 2)%coq_nat ->
 ~csr_system_instruction FormalInstructionResetConstants.instruction_nop lane.
Proof. intro Lane. do 2 (destruct lane as [|lane]; [vm_compute;discriminate|]). lia. Qed.
Definition csr_system_instruction_member := load_type_instruction_member.
Definition csr_system_register_member := csr_command_register_member.
Theorem csr_system_normal_fullhistory inputs path history result :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall time, (time < 9259)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history time) false (history time) flat_statements = Some (history (S time))) ->
 (forall time, (time <= 9259)%coq_nat -> VM.find 1 (history time) = Some (Gval (Fuint 1) [::false])) ->
 VM.find 45 (history 9254%nat) = Some (Gval (Fuint 1) [::false]) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories (history 9259%nat) true (history 9259%nat) flat_statements = Some result ->
 csr_system_invariant result.
Proof.
 intros Boundary Steps Resets NoTrap Commit instruction lane Lane Instruction Code.
 pose proof (csr_pipeline_normal_fullhistory inputs path history result Boundary Steps Resets NoTrap Commit instruction Instruction) as Value.
 rewrite (csr_system_decode instruction lane Lane Code) in Value. exact Value.
Qed.
Require Import StagedCircuitRegisterHold FormalLocalHistory FormalObservationCommit StagedFlatCircuitIteration ObservedLegalNoTrap JointBoundaryReachable JointBoundaryInitialization JointBoundaryPreparation FormalFetchType FormalResetPreparation RegisterPreparationFrames StagedObservedRegister FormalInstructionResetBase FormalInstructionResetCycle JointBoundaryInduction ExternalReset StagedIterationCount.
Local Opaque generated_run.
Theorem csr_system_normal_successor memory inputs k observed next :
 generated_observe memory inputs k = Some observed -> generated_legal_trace memory inputs k ->
 generated_run memory inputs (S k) = Some next ->
 VM.find 1 (formal_external_inputs (generated_observation_input inputs k)) = Some (Gval (Fuint 1) [::false]) ->
 csr_system_invariant (top_environment next).
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
 exact (csr_system_normal_fullhistory (generated_observation_input inputs k) nil history after Boundary Steps Resets NoTrap Step).
Qed.
Lemma csr_system_nop_invariant env : VM.find 7750 env = Some (Gval (Fuint 32) FormalInstructionResetConstants.instruction_nop) -> csr_system_invariant env.
Proof.
 intros Nop instruction lane Lane Instruction Load. rewrite Nop in Instruction. inversion Instruction;subst instruction.
 exfalso. exact (csr_system_nop_not_load lane Lane Load).
Qed.
Theorem csr_system_run memory inputs k states :
 generated_run memory inputs k = Some states -> generated_legal_trace memory inputs k -> csr_system_invariant (top_environment states).
Proof.
 destruct k as [|k];intros Run Legal.
 - destruct (instruction_run_zero memory inputs states Run) as [env [Env [Front Nop]]].
   unfold top_environment. rewrite Env. exact (csr_system_nop_invariant env Nop).
 - assert (PriorLegal : generated_legal_trace memory inputs k) by (apply (joint_legal_trace_prefix memory inputs (S k) k Legal);lia).
   destruct (legal_observation_reset memory inputs k PriorLegal) as [reset Reset].
   destruct reset.
   + pose proof Run as Next. rewrite generated_run_successor in Next.
     destruct (generated_run memory inputs k) as [previous|] eqn:Previous;[|discriminate Next].
     destruct (fetch9220_run_type memory inputs k previous Previous) as [old [value [Old Rest]]].
     destruct (joint_boundary_reachable memory inputs k previous Previous PriorLegal) as [Registers Storage].
     unfold top_environment in Registers. rewrite Old in Registers.
     destruct (Registers 7748%nat 32%nat early_bubble_front_instruction_member) as [front [FrontSize Front]].
     destruct (Registers 7750%nat 32%nat csr_system_instruction_member) as [instruction [Size Instruction]].
     destruct (instruction_real_reset_cycle (generated_observation_input inputs k) previous old states
     (Gval (Fuint 32) front) (Gval (Fuint 32) instruction) Old Front (Logic.eq_refl _) Instruction (Logic.eq_refl _) Reset Next)
     as [env [Env [FrontNop Nop]]].
     unfold top_environment. rewrite Env. exact (csr_system_nop_invariant env Nop).
   + destruct (generated_successful_commit memory inputs k states Run) as [observed [Observe Commit]].
     exact (csr_system_normal_successor memory inputs k observed states Observe PriorLegal Run Reset).
Qed.
Lemma csr_system_comb_hold invalid old current result :
 csr_system_invariant old -> formal_value_iter invalid flat_memories old false current flat_statements = Some result -> csr_system_invariant result.
Proof.
 intros Invariant Step instruction lane Lane Instruction Load.
 rewrite (staged_combinational_holds_registers invalid flat_memories old current result flat_statements 7750
 (proj2 (joint_boundary_register_properties 7750 32 csr_system_instruction_member)) Step) in Instruction.
 rewrite (staged_combinational_holds_registers invalid flat_memories old current result flat_statements 7758
 (proj2 (joint_boundary_register_properties 7758 3 csr_system_register_member)) Step).
 exact (Invariant instruction lane Lane Instruction Load).
Qed.
Lemma csr_system_history_hold invalid history (limit:nat) :
 csr_system_invariant (history 0%nat) ->
 (forall time, (time < limit)%coq_nat -> formal_value_iter invalid flat_memories (history time) false (history time) flat_statements = Some (history (S time))) ->
 forall time, (time <= limit)%coq_nat -> csr_system_invariant (history time).
Proof.
 intros Initial Steps time. induction time as [|time IH];intro Bound;[exact Initial|].
 exact (csr_system_comb_hold invalid (history time) (history time) (history (S time)) (IH ltac:(lia)) (Steps time ltac:(lia))).
Qed.
Lemma csr_system_prepared previous old external initial :
 SVM.find nil previous = Some old -> csr_system_invariant old ->
 circuit_initial_map_with_memory generated_modules generated_top (Some previous) external = Some initial -> csr_system_invariant (top_environment initial).
Proof.
 intros Previous Invariant Prepare.
 assert (Copy : forall node width, List.In (node,width) joint_boundary_registers ->
 staged_register_lookup (N.of_nat node) initial = VM.find (N.of_nat node) old).
 { intros node width Member. pose proof joint_boundary_preparation_check as Check.
   rewrite List.forallb_forall in Check. specialize (Check (node,width) Member).
   cbn [fst snd] in Check. move/andP: Check => [/andP [Safe NotClock] NotReset].
   exact (staged_prepared_register_copies previous old external initial _ NotClock NotReset Safe
   (proj2 (joint_boundary_register_properties node width Member)) Previous Prepare). }
 pose proof (Copy 7750%nat 32%nat csr_system_instruction_member) as InstructionCopy.
 pose proof (Copy 7758%nat 3%nat csr_system_register_member) as TypeCopy.
 intros instruction lane Lane Instruction Load.
 unfold staged_register_lookup in InstructionCopy,TypeCopy. unfold top_environment in *.
 destruct (SVM.find nil initial) as [env|];[|discriminate Instruction].
 rewrite InstructionCopy in Instruction. rewrite TypeCopy.
 exact (Invariant instruction lane Lane Instruction Load).
Qed.
Theorem csr_system_observed memory inputs k observed :
 generated_observe memory inputs k = Some observed -> generated_legal_trace memory inputs k -> csr_system_invariant (top_environment observed).
Proof.
 intros Observe Legal. pose proof Observe as Expanded. unfold generated_observe,generated_observe_cycle in Expanded.
 destruct (generated_run memory inputs k) as [previous|] eqn:Run;[|discriminate Expanded].
 destruct (circuit_initial_map_with_memory generated_modules generated_top (Some previous) (formal_external_inputs (generated_observation_input inputs k))) as [initial|] eqn:Prepare;[|discriminate Expanded].
 pose proof flat_iteration_count_exact as Count. unfold flat_iteration_count in Count. rewrite Count in Expanded.
 destruct (local_iteration_history (generated_observation_input inputs k) 9259 initial observed Expanded) as [history [First [Last Steps]]].
 pose proof (csr_system_run memory inputs k previous Run Legal) as Invariant.
 destruct (fetch9220_run_type memory inputs k previous Run) as [old [value [Old Rest]]].
 unfold top_environment in Invariant. rewrite Old in Invariant.
 rewrite <- Last. eapply (csr_system_history_hold _ history 9259);
 [rewrite First;exact (csr_system_prepared previous old _ initial Old Invariant Prepare)|exact Steps|vm_compute;lia].
Qed.
