Require Import CoreSocModel FormalLocalHistory JointBoundaryRegisters JointIterationBoundary JointIterationSources JointScalarCircuitCommit ConcreteRegisterInitialization.
From Coq Require Import ZArith List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Opaque generated_modules generated_top.
Theorem joint_scalar_iteration_commit inputs initial stable next bit :
 circuit_formal_iterations generated_modules generated_top inputs 9259 initial = Some stable ->
 (forall node width, List.In (node,width) joint_boundary_registers ->
 map_uint_concrete (N.of_nat node) width (top_environment initial)) ->
 VM.find (N.of_nat 1) (top_environment initial) = Some (Gval (Fuint 1) [::bit]) ->
 formal_circuit_value_iter (formal_invalid_policy inputs) generated_modules generated_top stable true = Some next ->
 forall node width, List.In (node,width) joint_boundary_registers ->
 node <> 9220%nat -> node <> 9222%nat -> map_uint_concrete (N.of_nat node) width (top_environment next).
Proof.
 intros Iterations Boundary Reset Commit.
 exact (joint_scalar_circuit_commit inputs stable next
 (joint_iteration_boundary inputs 9259 initial stable Iterations Boundary)
 (joint_iteration_sources inputs initial stable bit Iterations Boundary Reset) Commit).
Qed.
Print Assumptions joint_scalar_iteration_commit.
