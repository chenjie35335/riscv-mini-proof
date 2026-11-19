Require Import CoreSocModel ComparisonNodes CommitPCNormalAdvance ExceptionSourceNoTrap ExceptionPCSourceRegisters JointBoundaryRegisters ConcreteRegisterInitialization FormalStallHistory FormalCheckerResetConnections.
From Coq Require Import ZArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories.
Theorem commit_pc_normal_full_history inputs path history result front old :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < 9259)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 (forall i, (i <= 9259)%coq_nat -> VM.find 1 (history i) = Some (Gval (Fuint 1) [::false])) ->
 VM.find 45 (history 9254%nat) = Some (Gval (Fuint 1) [::false]) ->
 size front = 32%nat ->
 VM.find 7749 (history 9259%nat) = Some (Gval (Fuint 32) front) ->
 VM.find 7751 (history 9259%nat) = Some (Gval (Fuint 32) old) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories (history 9259%nat) true (history 9259%nat) flat_statements = Some result ->
 VM.find 7751 result = Some (Gval (Fuint 32) front).
Proof.
 intros Boundary Steps Resets NoTrap Size Front Old Commit.
 pose proof (exception_source_false_after_settling inputs path history Boundary Steps NoTrap) as NoException.
 assert (Present : RegisterInvariants.has_register 7749 flat_statements = true).
 { exact (proj2 (joint_boundary_register_properties 7749 32 ltac:(apply (List.nth_error_In joint_boundary_registers 54%nat); vm_compute;reflexivity))). }
 assert (F : VM.find 7749 (history 9255%nat) = Some (Gval (Fuint 32) front)).
 { rewrite (flat_register_history_same _ history 9259 7749 Present Steps 9255 ltac:(vm_compute;lia)).
   rewrite (flat_register_history_same _ history 9259 7749 Present Steps 9259 ltac:(vm_compute;lia)) in Front. exact Front. }
 assert (O : VM.find 7751 (history 9255%nat) = Some (Gval (Fuint 32) old)).
 { rewrite (flat_register_history_same _ history 9259 7751 exception_pc_implementation_register Steps 9255 ltac:(vm_compute;lia)).
   rewrite (flat_register_history_same _ history 9259 7751 exception_pc_implementation_register Steps 9259 ltac:(vm_compute;lia)) in Old. exact Old. }
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
 apply (commit_pc_normal_advance (formal_invalid_policy inputs path) (history 9255%nat) (history 9256%nat)
 (history 9257%nat) (history 9258%nat) (history 9259%nat) result front old);
 try assumption; try (apply NoException; vm_compute;lia); apply Steps; vm_compute;lia.
Qed.
Print Assumptions commit_pc_normal_full_history.
