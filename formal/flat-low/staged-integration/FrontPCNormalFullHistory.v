Require Import CoreSocModel ComparisonNodes FrontPCNormalCommit FrontPCSelectionNodes FormalStallHistory FormalCheckerResetConnections ExceptionPCSourceRegisters FormalPCRegister JointBoundaryRegisters RegisterInvariants.
From Coq Require Import ZArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories.
Theorem front_pc_normal_full_history invalid history result fetch front :
 (forall i, (i < 9259)%coq_nat -> formal_value_iter invalid flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 (forall i, (i <= 9259)%coq_nat -> VM.find 1 (history i) = Some (Gval (Fuint 1) [::false])) ->
 size fetch = 33%nat ->
 VM.find 7768 (history 9259%nat) = Some (Gval (Fuint 33) fetch) ->
 VM.find 7749 (history 9259%nat) = Some (Gval (Fuint 32) front) ->
 formal_value_iter invalid flat_memories (history 9259%nat) true (history 9259%nat) flat_statements = Some result ->
 VM.find 7749 result = Some (Gval (Fuint 32) (take 32 fetch)).
Proof.
 intros Steps Resets Size Fetch Front Commit.
 assert (FrontPresent : has_register 7749 flat_statements = true).
 { exact (proj2 (joint_boundary_register_properties 7749 32 ltac:(apply (List.nth_error_In joint_boundary_registers 54%nat); vm_compute;reflexivity))). }
 assert (F : VM.find 7768 (history 9258%nat) = Some (Gval (Fuint 33) fetch)).
 { rewrite (flat_register_history_same invalid history 9259 7768 pc_register_present Steps 9258 ltac:(vm_compute;lia)).
   rewrite (flat_register_history_same invalid history 9259 7768 pc_register_present Steps 9259 ltac:(vm_compute;lia)) in Fetch. exact Fetch. }
 assert (P : VM.find 7749 (history 9258%nat) = Some (Gval (Fuint 32) front)).
 { rewrite (flat_register_history_same invalid history 9259 7749 FrontPresent Steps 9258 ltac:(vm_compute;lia)).
   rewrite (flat_register_history_same invalid history 9259 7749 FrontPresent Steps 9259 ltac:(vm_compute;lia)) in Front. exact Front. }
 assert (Stall : VM.find 7765 (history 9257%nat) = Some (Gval (Fuint 1) [::false])).
 { apply (stall_after_six invalid (history 9251%nat) (history 9252%nat) (history 9253%nat)
 (history 9254%nat) (history 9255%nat) (history 9256%nat) (history 9257%nat) false);
 [apply Resets|apply Steps|apply Steps|apply Steps|apply Steps|apply Steps|apply Steps]; vm_compute;lia. }
 pose proof (front_pc_advance_control invalid (history 9257%nat) (history 9257%nat) (history 9258%nat)
 Stall (Steps 9257%nat ltac:(vm_compute;lia))) as Advance.
 pose proof (front_pc_fetch_selection invalid (history 9258%nat) (history 9258%nat) (history 9259%nat)
 fetch front Advance F Size P (Steps 9258%nat ltac:(vm_compute;lia))) as Source.
 pose proof (front_pc_reset_constant invalid (history 9258%nat) (history 9258%nat) (history 9259%nat)
 (Steps 9258%nat ltac:(vm_compute;lia))) as Constant.
 assert (Reset : VM.find 65 (history 9259%nat) = Some (Gval (Fuint 1) [::false])).
 { apply (reset_connection_65_transfer invalid (history 9258%nat) (history 9258%nat) (history 9259%nat) false).
 - apply (reset_connection_24_transfer invalid (history 9257%nat) (history 9257%nat) (history 9258%nat) false);
 [apply Resets|apply Steps]; vm_compute;lia.
 - apply Steps. vm_compute;lia. }
 exact (front_pc_normal_commit invalid (history 9259%nat) (history 9259%nat) result (Gval (Fuint 32) front)
 fetch (nseq 32 false) Front (Logic.eq_refl _) Reset Source Size Constant Commit).
Qed.
Print Assumptions front_pc_normal_full_history.
