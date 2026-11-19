Require Import StagedObservedRegister CoreSocModel JointBoundaryRegisters ConcreteRegisterInitialization FormalSingletonSymbolic StagedFlatCircuitIteration FormalDataStorageInitialization FormalLocalHistory.
From Coq Require Import ZArith List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory FormalInitialization.
Definition joint_registers_concrete env := forall node width,
 List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width env.
Definition joint_boundary_concrete states :=
 joint_registers_concrete (top_environment states) /\ data_storage_concrete states.
Local Opaque generated_modules generated_top flat_statements.
Theorem joint_boundary_symbolic_initial memory inputs states :
 circuit_symbolic_initial_state generated_modules generated_top memory inputs = Some states ->
 joint_boundary_concrete states.
Proof.
 intro Init. split.
 - destruct (singleton_symbolic_property generated_modules generated_top (N.of_nat 0) staged_top_ports flat_statements
 memory inputs states joint_registers_concrete flat_instance_map_exact flat_module_exact) as [env [Env Concrete]].
   + intros initial node width Member. exact (joint_boundary_registers_symbolic inputs nil initial node width Member).
   + exact Init.
   + unfold top_environment. rewrite Env. exact Concrete.
 - exact (symbolic_data_storage_concrete memory inputs states Init).
Qed.
Print Assumptions joint_boundary_symbolic_initial.
