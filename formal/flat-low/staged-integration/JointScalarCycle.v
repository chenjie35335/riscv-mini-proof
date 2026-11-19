Require Import CoreSocModel FormalLocalHistory JointBoundaryRegisters JointBoundaryPreparation JointScalarIterationCommit ConcreteRegisterInitialization StagedIterationCount FormalResetPreparation.
From Coq Require Import ZArith List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Opaque generated_modules generated_top.
Theorem joint_scalar_cycle inputs previous old next bit :
 SVM.find nil previous = Some old ->
 (forall node width, List.In (node,width) joint_boundary_registers ->
 map_uint_concrete (N.of_nat node) width old) ->
 VM.find (N.of_nat 1) (formal_external_inputs inputs) = Some (Gval (Fuint 1) [::bit]) ->
 circuit_formal_cycle generated_modules generated_top (Some previous) inputs = Some next ->
 forall node width, List.In (node,width) joint_boundary_registers ->
 node <> 9220%nat -> node <> 9222%nat -> map_uint_concrete (N.of_nat node) width (top_environment next).
Proof.
 intros Old Boundary Reset Cycle. unfold circuit_formal_cycle in Cycle.
 destruct (circuit_initial_map_with_memory generated_modules generated_top (Some previous)
 (formal_external_inputs inputs)) as [prepared|] eqn:Prepare; [|discriminate Cycle].
 pose proof flat_iteration_count_exact as Count. unfold flat_iteration_count in Count. rewrite Count in Cycle.
 destruct (circuit_formal_iterations generated_modules generated_top inputs 9259 prepared) as [stable|] eqn:Iterations; [|discriminate Cycle].
 eapply (joint_scalar_iteration_commit inputs prepared stable next bit Iterations).
 - intros node width Member. exact (joint_boundary_prepared_concrete previous old _ prepared node width Member
     (Boundary node width Member) Old Prepare).
 - destruct (top_reset_prepared (Some previous) _ prepared _ Reset Prepare) as [env [Env Value]].
   unfold top_environment. rewrite Env. exact Value.
 - exact Cycle.
Qed.
Print Assumptions joint_scalar_cycle.
