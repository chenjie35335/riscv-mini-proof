Require Import CoreSocModel ComparisonNodes RFReadForwarding RFWriteEffect FormalInstructionResetConstants DataAddressExpressionCertificates DataAddressPositionCertificate DataAddressSafetyCertificate SelectedNodeSafety FormalTypedNodeEquation EarlyBubbleValues EarlyBubbleInstructionControl FrontInstructionNopCommit.
From Coq Require Import ZArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
(* The invariant is guarded by wb_en: ECALL/EBREAK select CSR but do not write. *)
Definition rf_nonalu_bubble_invariant env : Prop := forall low high,
 VM.find 7757 env = Some (Gval (Fuint 1) [::true]) ->
 VM.find 7756 env = Some (Gval (Fuint 2) [::low;high]) ->
 low || high = true -> VM.find 7748 env = Some (Gval (Fuint 32) instruction_nop).
Lemma rf_kill_injects_front_nop invalid s0 s1 s2 s3 s4 s5 result started branch exception fetched held :
 VM.find 7762 s0 = Some (Gval (Fuint 1) [::started]) ->
 VM.find 85 s0 = Some (Gval (Fuint 1) [::true]) ->
 VM.find 1360 s1 = Some (Gval (Fuint 1) [::branch]) ->
 VM.find 128 s2 = Some (Gval (Fuint 1) [::exception]) ->
 VM.find 75 s3 = Some fetched -> type_of_val fetched = Gtyp (Fuint 32) ->
 VM.find 7748 s3 = Some held -> type_of_val held = Gtyp (Fuint 32) ->
 VM.find 7799 s4 = Some (Gval (Fuint 1) [::true]) ->
 VM.find 65 s5 = Some (Gval (Fuint 1) [::false]) ->
 formal_value_iter invalid flat_memories s0 false s0 flat_statements = Some s1 ->
 formal_value_iter invalid flat_memories s1 false s1 flat_statements = Some s2 ->
 formal_value_iter invalid flat_memories s2 false s2 flat_statements = Some s3 ->
 formal_value_iter invalid flat_memories s3 false s3 flat_statements = Some s4 ->
 formal_value_iter invalid flat_memories s4 false s4 flat_statements = Some s5 ->
 formal_value_iter invalid flat_memories s5 true s5 flat_statements = Some result ->
 VM.find 7748 result = Some (Gval (Fuint 32) instruction_nop).
Proof.
 intros Started Kill Branch Exception Fetched FetchedType Held HeldType Advance Reset S1 S2 S3 S4 S5 Commit.
 pose proof (early_bubble_value_after_three invalid s0 s1 s2 s3 started true branch exception Started Kill Branch Exception S1 S2 S3) as Value.
 rewrite orbT !orTb in Value.
 rewrite (early_bubble_instruction_control_after_three invalid s0 s1 s2 s3 S1 S2 S3) in Value.
 exact (front_instruction_nop_commit_after_two invalid s3 s4 s5 result fetched held Value Fetched FetchedType Held HeldType Advance Reset S4 S5 Commit).
Qed.
Lemma rf_front_nop_read_address second invalid old result :
 VM.find 7748 old = Some (Gval (Fuint 32) instruction_nop) ->
 formal_value_iter invalid flat_memories old false old flat_statements = Some result ->
 VM.find (rf_source_address second) result = Some (Gval (Fuint 5) (nseq 5 false)).
Proof.
 intros Nop Step.
 assert (Member : List.In (rf_source_address second,if second then address_expr_7804 else address_expr_7803) data_address_expected_nodes).
 { destruct second; [apply (List.nth_error_In data_address_expected_nodes 126%nat)|apply (List.nth_error_In data_address_expected_nodes 125%nat)];vm_compute;reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements data_address_expected_nodes _ _ data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;[exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 destruct second; cbn [address_expr_7803 address_expr_7804 eval_hfexpr_validif_policy eval_href_validif_policy];rewrite Nop;reflexivity.
Qed.
Theorem rf_nonalu_bubble_no_read_collision second invalid old result enabled low high address destination :
 rf_nonalu_bubble_invariant old ->
 VM.find 7757 old = Some (Gval (Fuint 1) [::enabled]) ->
 VM.find 7756 old = Some (Gval (Fuint 2) [::low;high]) ->
 VM.find (rf_source_address second) result = Some (Gval (Fuint 5) address) ->
 formal_value_iter invalid flat_memories old false old flat_statements = Some result ->
 (~~low && ~~high) = false -> rf_write_hits enabled destination (to_nat address) = false.
Proof.
 intros Invariant Enabled Mode Address Step NonAlu.
 destruct enabled;[|unfold rf_write_hits;reflexivity].
 assert (Nonzero : low || high = true) by (destruct low,high;try discriminate NonAlu;reflexivity).
 pose proof (rf_front_nop_read_address second invalid old result (Invariant low high Enabled Mode Nonzero) Step) as Zero.
 rewrite Address in Zero. inversion Zero;subst address. unfold rf_write_hits. reflexivity.
Qed.

Require Import ConcreteGroundUIntAdapt FormalDeclaredConnection FormalRegisterCommitIdentity RegisterCommitCertificate.
Require Import ConcreteGroundAdapt ConcreteGroundOperations ScalarSinkObservation ScalarSinkTypes.
Require Import RegisterInvariants ScalarNodeFrames FormalStatementSegments FormalTypedNodeFrames FormalConnectionTail FormalNodeEquation StagedRegisterHold.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths
 HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.

Theorem rf_control_direct_commit_exact count stmts declared_tail middle tail
 (node source : VarOrder.T) reg width word old_value invalid mm old current result :
 straight_drop count stmts = Some (Qcons (Sreg node reg) declared_tail) ->
 declared_tail = statement_append middle (Qcons (Sfcnct (Eid node) (Eref (Eid source))) tail) ->
 straight_statements middle ->
 formal_typed_suffix_safe mm node middle -> formal_typed_suffix_safe mm node tail ->
 register_identity_b node stmts ->
 VM.find node old = Some old_value -> type_of_val old_value = Gtyp (Fuint width) -> node != source ->
 VM.find source old = Some (Gval (Fuint width) word) -> size word = width ->
 formal_value_iter invalid mm old true current stmts = Some result ->
 VM.find node result = Some (Gval (Fuint width) word).
Proof.
 intros Position Split Straight MiddleSafe TailSafe Identity Old Typed Different Source Size Step.
 unfold formal_value_iter in Step.
 destruct (formal_statements invalid [::] 0 mm old true current stmts) as [proposed|] eqn:Statements;
 [|discriminate Step].
 pose proof (formal_finish_identity_preserves stmts invalid nil 0 mm old proposed result node Identity Step) as Projection.
 destruct (formal_straight_prefix count stmts _ invalid nil 0 mm old true current proposed Position Statements)
   as [at_declaration Decl].
 cbn [formal_statements] in Decl. rewrite Old in Decl.
 rewrite Split in Decl.
 destruct (successful_straight_segment middle _ invalid nil (S (0 + count)) mm old true
  (VM.add node old_value at_declaration) proposed Straight Decl)
  as [at_connection [Middle Connection]].
 assert (Before : VM.find node at_connection = Some old_value).
 { eapply formal_typed_suffix_preserves_value;
   [exact MiddleSafe|exact Typed| |exact Middle].
   apply RegisterMapFacts.find_add_eq. exact (eqxx node). }
 cbn [formal_statements is_memory_writer_ref] in Connection.
 destruct (bidirectional_connect_with_memory mm (@Eid VarOrder.T node) (@Eid VarOrder.T source) old at_connection)
 as [next|] eqn:Connect; [|discriminate Connection].
 destruct (bidirectional_uint_sink_observation mm node (@Eid VarOrder.T source)
 old at_connection next old_value width Different Before Typed Connect)
 as [read [written [Read [Written Next]]]].
 cbn [eval_href_with_memory] in Read. rewrite Source in Read. inversion Read; subst read.
 assert (Adapt : adapt_hvalue_as_type (Gval (Fuint width) word) (Gtyp (Fuint width)) = Some (Gval (Fuint width) word)).
 { cbn [adapt_hvalue_as_type]. rewrite -Size take_size. unfold zext_to,zext. rewrite subnn cats0. reflexivity. }
 rewrite Adapt in Written. inversion Written;subst written.
 rewrite Projection.
 eapply formal_typed_suffix_preserves_value;
 [exact TailSafe|reflexivity|exact Next|exact Connection].
Qed.
Require Import JointUpdateNodePositions JointUpdateExpressionCertificates JointRegisterCommits7 FormalSuccessfulNodeEvaluation.
Local Lemma rf_control_known_node node expression width word invalid old result :
 List.In (node,expression) joint_update_expected_nodes ->
 (forall site, eval_hfexpr_validif_policy (isolated_validif_policy invalid) site flat_memories expression old old = Some (Gval (Fuint width) word)) ->
 formal_value_iter invalid flat_memories old false old flat_statements = Some result ->
 VM.find node result = Some (Gval (Fuint width) word).
Proof.
 intros Member Eval Step.
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes _ _ joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;[exact Position|exact Safe|exact Nonreg|apply Eval|reflexivity|exact Step].
Qed.
Theorem rf_writeback_controls_advance invalid s0 s1 s2 result old_low old_high old_enabled low high enabled :
 VM.find 7756 s0 = Some (Gval (Fuint 2) [::old_low;old_high]) ->
 VM.find 7757 s0 = Some (Gval (Fuint 1) [::old_enabled]) ->
 VM.find 93 s0 = Some (Gval (Fuint 2) [::low;high]) ->
 VM.find 94 s0 = Some (Gval (Fuint 1) [::enabled]) ->
 VM.find 7855 s0 = Some (Gval (Fuint 1) [::true]) ->
 VM.find 7852 s1 = Some (Gval (Fuint 1) [::false]) ->
 formal_value_iter invalid flat_memories s0 false s0 flat_statements = Some s1 ->
 formal_value_iter invalid flat_memories s1 false s1 flat_statements = Some s2 ->
 formal_value_iter invalid flat_memories s2 true s2 flat_statements = Some result ->
 VM.find 7756 result = Some (Gval (Fuint 2) [::low;high]) /\ VM.find 7757 result = Some (Gval (Fuint 1) [::enabled]).
Proof.
 intros OldMode OldEnabled Mode Enabled Advance Flush S1 S2 Commit.
 assert (Mode1 : VM.find 7756 s1 = Some (Gval (Fuint 2) [::old_low;old_high])).
 { rewrite (staged_combinational_holds_registers invalid flat_memories s0 s0 s1 flat_statements 7756 ltac:(vm_compute;reflexivity) S1). exact OldMode. }
 assert (Mode2 : VM.find 7756 s2 = Some (Gval (Fuint 2) [::old_low;old_high])).
 { rewrite (staged_combinational_holds_registers invalid flat_memories s1 s1 s2 flat_statements 7756 ltac:(vm_compute;reflexivity) S2). exact Mode1. }
 assert (Enabled2 : VM.find 7757 s2 = Some (Gval (Fuint 1) [::old_enabled])).
 { rewrite (staged_combinational_holds_registers invalid flat_memories s1 s1 s2 flat_statements 7757 ltac:(vm_compute;reflexivity) S2).
   rewrite (staged_combinational_holds_registers invalid flat_memories s0 s0 s1 flat_statements 7757 ltac:(vm_compute;reflexivity) S1). exact OldEnabled. }
 assert (A : VM.find 7866 s1 = Some (Gval (Fuint 2) [::low;high])).
 { eapply (rf_control_known_node 7866 joint_update_expr_7866);[apply (List.nth_error_In joint_update_expected_nodes 921%nat);vm_compute;reflexivity| |exact S1].
   intros site. cbn [joint_update_expr_7866 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Advance.
   cbn. unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref]. rewrite Mode OldMode. destruct low,high,old_low,old_high;reflexivity. }
 assert (B : VM.find 7867 s1 = Some (Gval (Fuint 1) [::enabled])).
 { eapply (rf_control_known_node 7867 joint_update_expr_7867);[apply (List.nth_error_In joint_update_expected_nodes 922%nat);vm_compute;reflexivity| |exact S1].
   intros site. cbn [joint_update_expr_7867 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Advance.
   cbn. unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref]. rewrite Enabled OldEnabled. destruct enabled,old_enabled;reflexivity. }
 assert (C : VM.find 7881 s2 = Some (Gval (Fuint 2) [::low;high])).
 { eapply (rf_control_known_node 7881 joint_update_expr_7881);[apply (List.nth_error_In joint_update_expected_nodes 936%nat);vm_compute;reflexivity| |exact S2].
   intros site. cbn [joint_update_expr_7881 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Flush.
   cbn. unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref]. rewrite A Mode1. destruct low,high,old_low,old_high;reflexivity. }
 assert (D : VM.find 7873 s2 = Some (Gval (Fuint 1) [::enabled])).
 { eapply (rf_control_known_node 7873 joint_update_expr_7873);[apply (List.nth_error_In joint_update_expected_nodes 928%nat);vm_compute;reflexivity| |exact S2].
   intros site. cbn [joint_update_expr_7873 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Flush.
   cbn. rewrite B. destruct enabled;reflexivity. }
 split.
 - eapply (rf_control_direct_commit_exact 8262 flat_statements joint_register_7756_decl joint_register_7756_mid joint_register_7756_tail 7756 7881 joint_register_7756_reg 2 [::low;high]);
 [exact joint_register_7756_position|exact joint_register_7756_split|exact joint_register_7756_straight|exact joint_register_7756_mid_safe|exact joint_register_7756_tail_safe|exact joint_register_7756_identity|exact Mode2|reflexivity|reflexivity|exact C|reflexivity|exact Commit].
 - eapply (rf_control_direct_commit_exact 8263 flat_statements joint_register_7757_decl joint_register_7757_mid joint_register_7757_tail 7757 7873 joint_register_7757_reg 1 [::enabled]);
 [exact joint_register_7757_position|exact joint_register_7757_split|exact joint_register_7757_straight|exact joint_register_7757_mid_safe|exact joint_register_7757_tail_safe|exact joint_register_7757_identity|exact Enabled2|reflexivity|reflexivity|exact D|reflexivity|exact Commit].
Qed.
Require Import ControlWritebackKill JointBoundaryRegisters JointUpdateBoundaryHistory ConcreteRegisterInitialization EarlyBubbleNopFullHistory EarlyBubbleNopControlKnown EarlyControlWireBitNormalization EarlyControlStabilityHistory StartupFlagInitialization ExceptionSourceNoTrap FrontInstructionFetchType FrontPCSelectionNodes FormalStallHistory FormalCheckerResetConnections FormalPipelineControlHistory.
Lemma rf_nonalu_mode_member : List.In (7756%nat,2%nat) joint_boundary_registers.
Proof. apply (List.nth_error_In joint_boundary_registers 61%nat). vm_compute;reflexivity. Qed.
Lemma rf_nonalu_enable_member : List.In (7757%nat,1%nat) joint_boundary_registers.
Proof. apply (List.nth_error_In joint_boundary_registers 62%nat). vm_compute;reflexivity. Qed.
Theorem rf_nonalu_normal_fullhistory inputs path history result :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall time, (time < 9259)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history time) false (history time) flat_statements = Some (history (S time))) ->
 (forall time, (time <= 9259)%coq_nat -> VM.find 1 (history time) = Some (Gval (Fuint 1) [::false])) ->
 VM.find 45 (history 9254%nat) = Some (Gval (Fuint 1) [::false]) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories (history 9259%nat) true (history 9259%nat) flat_statements = Some result ->
 rf_nonalu_bubble_invariant result.
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
 intros next_low next_high Writes NonAlu Nonzero.
 rewrite NextMode in NonAlu. inversion NonAlu;subst next_low next_high.
 rewrite NextEnable in Writes. inversion Writes;subst enabled.
 assert (KillTrue : kill = true) by (destruct kill,low,high;cbn in Safe,Nonzero;try discriminate;reflexivity).
 rewrite KillTrue in Kill.
 destruct (joint_update_register_history_concrete _ history 9259 7762 1 startup_register_member (Boundary _ _ startup_register_member) Steps 9254 ltac:(vm_compute;lia)) as [started_word [StartedSize Started]].
 destruct started_word as [|started [|extra rest]];try discriminate StartedSize.
 destruct (early_control_wire_1360_normalized _ (history 9254%nat) (history 9254%nat) (history 9255%nat) (Steps 9254%nat ltac:(vm_compute;lia))) as [branch_value [BranchValue BranchNormal]].
 destruct (early_bubble_normalized_concrete _ 1360 branch_value BranchValue BranchNormal (early_control_concrete_1360_history inputs path history 9259 Boundary Steps 9255 ltac:(vm_compute;lia) ltac:(vm_compute;lia))) as [branch Branch].
 destruct (front_instruction_fetch_type _ (history 9256%nat) (history 9256%nat) (history 9257%nat) (Steps 9256%nat ltac:(vm_compute;lia))) as [fetched [Fetched FetchedType]].
 destruct (joint_update_register_history_concrete _ history 9259 7748 32 early_bubble_front_instruction_member (Boundary _ _ early_bubble_front_instruction_member) Steps 9257 ltac:(vm_compute;lia)) as [held [HeldSize Held]].
 assert (FrontAdvance : VM.find 7799 (history 9258%nat) = Some (Gval (Fuint 1) [::true])).
 { eapply (front_pc_advance_control _ (history 9257%nat) (history 9257%nat) (history 9258%nat));[apply Stall;vm_compute;lia|apply Steps;vm_compute;lia]. }
 eapply (rf_kill_injects_front_nop _ (history 9254%nat) (history 9255%nat) (history 9256%nat) (history 9257%nat) (history 9258%nat) (history 9259%nat) result started branch false fetched (Gval (Fuint 32) held));
 [exact Started|exact Kill|exact Branch|apply Exception;vm_compute;lia|exact Fetched|exact FetchedType|exact Held|reflexivity|exact FrontAdvance|apply Reset65;vm_compute;lia|apply Steps;vm_compute;lia|apply Steps;vm_compute;lia|apply Steps;vm_compute;lia|apply Steps;vm_compute;lia|apply Steps;vm_compute;lia|exact Commit].
Qed.
