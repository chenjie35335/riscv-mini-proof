Require Import CoreSocModel FormalLocalHistory JointBoundaryRegisters JointScalarRegisterCommit JointUpdateTargets ConcreteRegisterInitialization StagedFlatCircuitIteration.
From Coq Require Import ZArith List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Opaque generated_modules generated_top flat_statements flat_memories.
Theorem joint_scalar_circuit_commit inputs observed next :
 (forall node width, List.In (node,width) joint_boundary_registers ->
 map_uint_concrete (N.of_nat node) width (top_environment observed)) ->
 (forall source, List.In source joint_update_targets -> exists ground bits,
 VM.find (N.of_nat source) (top_environment observed) = Some (Gval ground bits)) ->
 formal_circuit_value_iter (formal_invalid_policy inputs) generated_modules generated_top observed true = Some next ->
 forall node width, List.In (node,width) joint_boundary_registers ->
 node <> 9220%nat -> node <> 9222%nat -> map_uint_concrete (N.of_nat node) width (top_environment next).
Proof.
 intros Boundary Sources Commit.
 destruct (flat_iteration_projection _ observed true next Commit) as [before [after [Before [Step After]]]].
 assert (Top : top_environment observed = before) by (unfold top_environment; rewrite Before; reflexivity).
 rewrite Top in Boundary. rewrite Top in Sources.
 unfold top_environment. rewrite After.
 exact (joint_scalar_registers_commit inputs nil before before after Boundary Sources Step).
Qed.
Print Assumptions joint_scalar_circuit_commit.
