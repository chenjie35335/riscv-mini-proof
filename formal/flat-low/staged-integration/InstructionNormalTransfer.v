Require Import CoreSocModel ComparisonNodes JointUpdateNodePositions JointUpdateExpressionCertificates SelectedNodeSafety FormalTypedNodeEquation FormalInstructionResetConstants FormalInstructionWordsNormalCommit CommitPCAdvance CommitPCSelection JointBoundaryRegisters RegisterInvariants.
From Coq Require Import ZArith List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Lemma instruction_transfer_member_7861 : List.In (7861,joint_update_expr_7861) joint_update_expected_nodes.
Proof. apply (List.nth_error_In joint_update_expected_nodes 916%nat). vm_compute. reflexivity. Qed.
Theorem instruction_transfer_node_7861 invalid old current result value :
 eval_hfexpr_with_memory flat_memories joint_update_expr_7861 old old = Some value ->
 type_of_val value = Gtyp (Fuint 32) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 7861 result = Some value.
Proof.
 intros Eval Typed Step.
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 7861 joint_update_expr_7861 joint_update_node_positions joint_update_node_safety instruction_transfer_member_7861)
 as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg|exact Eval|exact Typed|exact Step].
Qed.
Lemma instruction_transfer_member_7878 : List.In (7878,joint_update_expr_7878) joint_update_expected_nodes.
Proof. apply (List.nth_error_In joint_update_expected_nodes 933%nat). vm_compute. reflexivity. Qed.
Theorem instruction_transfer_node_7878 invalid old current result value :
 eval_hfexpr_with_memory flat_memories joint_update_expr_7878 old old = Some value ->
 type_of_val value = Gtyp (Fuint 32) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 7878 result = Some value.
Proof.
 intros Eval Typed Step.
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 7878 joint_update_expr_7878 joint_update_node_positions joint_update_node_safety instruction_transfer_member_7878)
 as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg|exact Eval|exact Typed|exact Step].
Qed.
Lemma instruction_transfer_register : has_register 7750 flat_statements = true.
Proof. exact (proj2 (joint_boundary_register_properties 7750 32 ltac:(apply (List.nth_error_In joint_boundary_registers 55%nat); vm_compute;reflexivity))). Qed.

Require Import  ExactWordMux StagedRegisterHold ExceptionPCSourceRegisters.
Require Import RegisterInvariants CoreSocModel ComparisonNodes ScalarNodeFrames FormalTypedNodeFrames FormalTypedNodeEquation.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths Firrtl_with_implicit_widths HiEnv_with_implicit_widths
 HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Theorem instruction_transfer_after_two invalid old middle result advance stall ex ew :
 VM.find 7748 old = Some (Gval (Fuint 32) ex) ->
 VM.find 7750 old = Some (Gval (Fuint 32) ew) ->
 VM.find 7855 old = Some (Gval (Fuint 1) [::advance]) ->
 VM.find 7852 middle = Some (Gval (Fuint 1) [::stall]) ->
 formal_value_iter invalid flat_memories old false old flat_statements = Some middle ->
 formal_value_iter invalid flat_memories middle false middle flat_statements = Some result ->
 VM.find 7878 result = Some (Gval (Fuint 32) (commit_pc_next stall advance ex ew)).
Proof.
 intros Ex Ew Advance Stall First Second.
 assert (Selected : VM.find 7861 middle = Some (Gval (Fuint 32) (mux_word advance ex ew))).
 { apply (instruction_transfer_node_7861 invalid old old middle (Gval (Fuint 32) (mux_word advance ex ew)));
   [exact (exact_word_mux flat_memories old 7855 7748 7750 advance ex ew Advance Ex Ew)|reflexivity|exact First]. }
 assert (Held : VM.find 7750 middle = Some (Gval (Fuint 32) ew)).
 { rewrite (staged_combinational_holds_registers invalid flat_memories old old middle flat_statements 7750
   instruction_transfer_register First). exact Ew. }
 apply (instruction_transfer_node_7878 invalid middle middle result (Gval (Fuint 32) (commit_pc_next stall advance ex ew)));
 [|reflexivity|exact Second].
 exact (exact_word_mux flat_memories middle 7852 7750 7861 stall ew (mux_word advance ex ew) Stall Held Selected).
Qed.


Require Import FormalPipelineControlHistory .
Require Import  ExactWordMux StagedRegisterHold ExceptionPCSourceRegisters JointBoundaryRegisters.
Require Import RegisterInvariants CoreSocModel ComparisonNodes ScalarNodeFrames FormalTypedNodeFrames FormalTypedNodeEquation.
From Coq Require Import ZArith List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths Firrtl_with_implicit_widths HiEnv_with_implicit_widths
 HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Theorem instruction_transfer_controlled_after_four invalid s0 s1 s2 s3 s4 ex ew stall exception reset :
 VM.find 7748 s0 = Some (Gval (Fuint 32) ex) ->
 VM.find 7750 s0 = Some (Gval (Fuint 32) ew) ->
 VM.find 7765 s0 = Some (Gval (Fuint 1) [::stall]) ->
 VM.find 128 s0 = Some (Gval (Fuint 1) [::exception]) ->
 VM.find 128 s1 = Some (Gval (Fuint 1) [::exception]) ->
 VM.find 65 s1 = Some (Gval (Fuint 1) [::reset]) ->
 formal_value_iter invalid flat_memories s0 false s0 flat_statements = Some s1 ->
 formal_value_iter invalid flat_memories s1 false s1 flat_statements = Some s2 ->
 formal_value_iter invalid flat_memories s2 false s2 flat_statements = Some s3 ->
 formal_value_iter invalid flat_memories s3 false s3 flat_statements = Some s4 ->
 VM.find 7878 s4 = Some (Gval (Fuint 32)
 (commit_pc_next (reset || (negb stall && exception)) (negb stall && negb exception) ex ew)).
Proof.
 intros Ex Ew Stall Exception0 Exception1 Reset S1 S2 S3 S4.
 pose proof (pipeline_advance_after_two invalid s0 s1 s2 stall exception Stall Exception0 S1 S2) as Advance.
 pose proof (pipeline_flush_after_three invalid s0 s1 s2 s3 stall exception reset Stall Exception1 Reset S1 S2 S3) as Flush.
 assert (Held : forall id value, id \in [::7748;7750] -> VM.find id s0 = Some value -> VM.find id s2 = Some value).
 { intros id value Member Value.
   assert (Present : has_register id flat_statements = true).
   { move: Member. rewrite in_cons in_cons in_nil orbF. move/orP => [/eqP Eq|/eqP Eq]; subst id.
     - apply (proj2 (joint_boundary_register_properties 7748 32 ltac:(apply (List.nth_error_In joint_boundary_registers 53%nat); vm_compute; reflexivity))).
     - exact instruction_transfer_register. }
   rewrite (staged_combinational_holds_registers invalid flat_memories s1 s1 s2 flat_statements id Present S2).
   rewrite (staged_combinational_holds_registers invalid flat_memories s0 s0 s1 flat_statements id Present S1). exact Value. }
 apply (instruction_transfer_after_two invalid s2 s3 s4 (negb stall && negb exception) (reset || (negb stall && exception)) ex ew);
 [exact (Held 7748 _ ltac:(vm_compute; reflexivity) Ex)|exact (Held 7750 _ ltac:(vm_compute; reflexivity) Ew)|exact Advance|exact Flush|exact S3|exact S4].
Qed.


Require Import CoreSocModel ComparisonNodes  CommitPCAdvance CommitPCNormalCommit ExceptionPCSourceRegisters StagedRegisterHold.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Theorem instruction_transfer_normal_advance invalid s0 s1 s2 s3 s4 result front old :
 size front = 32%nat ->
 VM.find 7748 s0 = Some (Gval (Fuint 32) front) ->
 VM.find 7750 s0 = Some (Gval (Fuint 32) old) ->
 VM.find 7765 s0 = Some (Gval (Fuint 1) [::false]) ->
 VM.find 128 s0 = Some (Gval (Fuint 1) [::false]) ->
 VM.find 128 s1 = Some (Gval (Fuint 1) [::false]) ->
 VM.find 65 s1 = Some (Gval (Fuint 1) [::false]) ->
 VM.find 65 s4 = Some (Gval (Fuint 1) [::false]) ->
 formal_value_iter invalid flat_memories s0 false s0 flat_statements = Some s1 ->
 formal_value_iter invalid flat_memories s1 false s1 flat_statements = Some s2 ->
 formal_value_iter invalid flat_memories s2 false s2 flat_statements = Some s3 ->
 formal_value_iter invalid flat_memories s3 false s3 flat_statements = Some s4 ->
 formal_value_iter invalid flat_memories s4 true s4 flat_statements = Some result ->
 VM.find 7750 result = Some (Gval (Fuint 32) front).
Proof.
 intros Size Front Old Stall Ex0 Ex1 Reset1 Reset4 S1 S2 S3 S4 Commit.
 pose proof (instruction_transfer_controlled_after_four invalid s0 s1 s2 s3 s4 front old false false false
 Front Old Stall Ex0 Ex1 Reset1 S1 S2 S3 S4) as Source.
 change (VM.find 7878 s4 = Some (Gval (Fuint 32) (CommitPCSelection.commit_pc_next false true front old))) in Source.
 rewrite (commit_pc_advance_value front old Size) in Source.
 assert (Old4 : VM.find 7750 s4 = Some (Gval (Fuint 32) old)).
 {
 rewrite (staged_combinational_holds_registers invalid flat_memories s3 s3 s4 flat_statements 7750 instruction_transfer_register S4).
 rewrite (staged_combinational_holds_registers invalid flat_memories s2 s2 s3 flat_statements 7750 instruction_transfer_register S3).
 rewrite (staged_combinational_holds_registers invalid flat_memories s1 s1 s2 flat_statements 7750 instruction_transfer_register S2).
 rewrite (staged_combinational_holds_registers invalid flat_memories s0 s0 s1 flat_statements 7750 instruction_transfer_register S1).
 exact Old. }
 exact (instruction_7750_formal_normal_commit invalid s4 s4 result (Gval (Fuint 32) old) front Old4 (Logic.eq_refl _) Reset4 Source Size Commit).
Qed.


Require Import CoreSocModel ComparisonNodes  ExceptionSourceNoTrap ExceptionPCSourceRegisters JointBoundaryRegisters ConcreteRegisterInitialization FormalStallHistory FormalCheckerResetConnections.
From Coq Require Import ZArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories.
Theorem instruction_transfer_normal_full_history inputs path history result front old :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < 9259)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 (forall i, (i <= 9259)%coq_nat -> VM.find 1 (history i) = Some (Gval (Fuint 1) [::false])) ->
 VM.find 45 (history 9254%nat) = Some (Gval (Fuint 1) [::false]) ->
 size front = 32%nat ->
 VM.find 7748 (history 9259%nat) = Some (Gval (Fuint 32) front) ->
 VM.find 7750 (history 9259%nat) = Some (Gval (Fuint 32) old) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories (history 9259%nat) true (history 9259%nat) flat_statements = Some result ->
 VM.find 7750 result = Some (Gval (Fuint 32) front).
Proof.
 intros Boundary Steps Resets NoTrap Size Front Old Commit.
 pose proof (exception_source_false_after_settling inputs path history Boundary Steps NoTrap) as NoException.
 assert (Present : RegisterInvariants.has_register 7748 flat_statements = true).
 { exact (proj2 (joint_boundary_register_properties 7748 32 ltac:(apply (List.nth_error_In joint_boundary_registers 53%nat); vm_compute;reflexivity))). }
 assert (F : VM.find 7748 (history 9255%nat) = Some (Gval (Fuint 32) front)).
 { rewrite (flat_register_history_same _ history 9259 7748 Present Steps 9255 ltac:(vm_compute;lia)).
   rewrite (flat_register_history_same _ history 9259 7748 Present Steps 9259 ltac:(vm_compute;lia)) in Front. exact Front. }
 assert (O : VM.find 7750 (history 9255%nat) = Some (Gval (Fuint 32) old)).
 { rewrite (flat_register_history_same _ history 9259 7750 instruction_transfer_register Steps 9255 ltac:(vm_compute;lia)).
   rewrite (flat_register_history_same _ history 9259 7750 instruction_transfer_register Steps 9259 ltac:(vm_compute;lia)) in Old. exact Old. }
 assert (Stall : VM.find 7765 (history 9255%nat) = Some (Gval (Fuint 1) [::false])).
 { apply (stall_after_six (formal_invalid_policy inputs path) (history 9249%nat) (history 9250%nat) (history 9251%nat)
 (history 9252%nat) (history 9253%nat) (history 9254%nat) (history 9255%nat) false);
 [apply Resets|apply Steps|apply Steps|apply Steps|apply Steps|apply Steps|apply Steps]; vm_compute;lia. }
 assert (R9256 : VM.find 65 (history 9256%nat) = Some (Gval (Fuint 1) [::false])).
 { apply (reset_connection_65_transfer (formal_invalid_policy inputs path) (history 9255%nat) (history 9255%nat) (history 9256%nat) false).
 - apply (reset_connection_24_transfer (formal_invalid_policy inputs path) (history 9254%nat) (history 9254%nat) (history 9255%nat) false); [apply Resets|apply Steps]; vm_compute;lia.
 - apply Steps. vm_compute;lia. }
 assert (R9259 : VM.find 65 (history 9259%nat) = Some (Gval (Fuint 1) [::false])).
 { apply (reset_connection_65_transfer (formal_invalid_policy inputs path) (history 9258%nat) (history 9258%nat) (history 9259%nat) false).
 - apply (reset_connection_24_transfer (formal_invalid_policy inputs path) (history 9257%nat) (history 9257%nat) (history 9258%nat) false); [apply Resets|apply Steps]; vm_compute;lia.
 - apply Steps. vm_compute;lia. }
 apply (instruction_transfer_normal_advance (formal_invalid_policy inputs path) (history 9255%nat) (history 9256%nat)
 (history 9257%nat) (history 9258%nat) (history 9259%nat) result front old);
 try assumption; try (apply NoException; vm_compute;lia); apply Steps; vm_compute;lia.
Qed.

