Require Import CoreSocModel JointBoundaryInitialization JointBoundaryIncludes FormalDataBoundaryStep ObservedX0FromCommittedBoundary FormalLocalHistory FormalDataStorageInitialization.
From Coq Require Import ZArith List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Theorem joint_boundary_x0 memory inputs k committed old observed :
 generated_run memory inputs k = Some committed ->
 SVM.find nil committed = Some old ->
 generated_observe memory inputs k = Some observed ->
 generated_legal_trace memory inputs k ->
 joint_boundary_concrete committed -> generated_assert_m0_8_all observed.
Proof.
 intros Run Old Observe Legal [Registers Storage].
 unfold joint_registers_concrete, top_environment in Registers. rewrite Old in Registers.
 eapply (observed_x0_from_committed_boundary memory inputs k committed old observed Run Old); [|exact Observe|exact Legal].
 intros node width Member. apply Registers. apply joint_includes_x0. exact Member.
Qed.
Theorem joint_boundary_data_step memory inputs k committed old observed next :
 generated_run memory inputs k = Some committed ->
 SVM.find nil committed = Some old ->
 generated_observe memory inputs k = Some observed ->
 generated_run memory inputs (S k) = Some next ->
 generated_legal_trace memory inputs k ->
 joint_boundary_concrete committed ->
 data_storage_concrete next /\
 exists word, VM.find (N.of_nat 9222) (top_environment next) = Some (Gval (Fuint 32) word).
Proof.
 intros Run Old Observe Next Legal [Registers Storage].
 unfold joint_registers_concrete, top_environment in Registers. rewrite Old in Registers.
 eapply (data_memory_boundary_step memory inputs k committed old observed next Run Old Observe Next Legal); [|exact Storage].
 intros node width Member. apply Registers. apply joint_includes_writer. exact Member.
Qed.
Print Assumptions joint_boundary_x0.
Print Assumptions joint_boundary_data_step.
