Require Import CoreSocModel FormalLocalHistory JointBoundaryRegisters JointUpdateBoundaryHistory ConcreteRegisterInitialization.
From Coq Require Import ZArith List PeanoNat.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Opaque generated_modules generated_top.
Theorem joint_iteration_boundary inputs count initial final :
 circuit_formal_iterations generated_modules generated_top inputs count initial = Some final ->
 (forall node width, List.In (node,width) joint_boundary_registers ->
 map_uint_concrete (N.of_nat node) width (top_environment initial)) ->
 forall node width, List.In (node,width) joint_boundary_registers ->
 map_uint_concrete (N.of_nat node) width (top_environment final).
Proof.
 intros Iterations Boundary node width Member.
 destruct (local_iteration_history inputs count initial final Iterations) as [history [First [Last Steps]]].
 rewrite <- Last.
 eapply (joint_update_register_history_concrete _ history count node width Member).
 - rewrite First. exact (Boundary node width Member).
 - exact Steps.
 - exact (Nat.le_refl count).
Qed.
Print Assumptions joint_iteration_boundary.
