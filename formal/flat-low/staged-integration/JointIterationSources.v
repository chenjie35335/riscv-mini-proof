Require Import CoreSocModel FormalLocalHistory FormalTopResetHold JointBoundaryRegisters JointUpdateDependencyRanks JointUpdateGraphPropagation JointUpdateFromBoundaryHistory JointUpdateTargets ConcreteRegisterInitialization.
From Coq Require Import ZArith List Lia PeanoNat.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Opaque generated_modules generated_top.
Theorem joint_iteration_sources inputs initial final bit :
 circuit_formal_iterations generated_modules generated_top inputs 9259 initial = Some final ->
 (forall node width, List.In (node,width) joint_boundary_registers ->
 map_uint_concrete (N.of_nat node) width (top_environment initial)) ->
 VM.find (N.of_nat 1) (top_environment initial) = Some (Gval (Fuint 1) [::bit]) ->
 forall node, List.In node joint_update_targets -> joint_update_ground_at (top_environment final) node.
Proof.
 intros Iterations Boundary Reset node Target.
 destruct (local_iteration_history inputs 9259 initial final Iterations) as [history [First [Last Steps]]].
 assert (Initial : forall node width, List.In (node,width) joint_boundary_registers ->
 map_uint_concrete (N.of_nat node) width (history 0%nat)).
 { intros n w Member. rewrite First. exact (Boundary n w Member). }
 assert (Resets : forall i, (i <= 9259)%coq_nat ->
 VM.find (N.of_nat 1) (history i) = Some (Gval (Fuint 1) [::bit])).
 { intros i. induction i as [|i IH]; intro Bound.
   - rewrite First. exact Reset.
   - eapply top_reset_iteration; [apply IH; lia|apply Steps; lia]. }
 destruct (joint_update_target_entry node Target) as [rank [deps [Depth Member]]].
 rewrite <- Last.
 eapply (joint_update_from_boundary_history inputs nil history 9259 Initial).
 - intros time Within. exists bit. exact (Resets time Within).
 - exact Steps.
 - exact (Nat.le_refl 9259).
 - exact Member.
 - apply (Nat.le_trans _ 112 _ Depth). vm_compute. lia.
Qed.
Print Assumptions joint_iteration_sources.
