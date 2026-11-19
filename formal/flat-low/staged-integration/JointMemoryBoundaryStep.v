Require Import CoreSocModel FormalLocalHistory JointBoundaryInitialization JointBoundaryIncludes DataWriterBoundaryIncludesAddress ConcreteRegisterInitialization FormalDataStorageInitialization ObservedDataCommitReady FormalDataStorageRunStep FormalLoadSizedFromDataBoundary FormalFetchSizedFromJointBoundary.
From Coq Require Import ZArith List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Theorem joint_memory_boundary_step memory inputs k committed old observed next :
 generated_run memory inputs k = Some committed ->
 SVM.find nil committed = Some old ->
 generated_observe memory inputs k = Some observed ->
 generated_run memory inputs (S k) = Some next ->
 generated_legal_trace memory inputs k ->
 joint_boundary_concrete committed ->
 data_storage_concrete next /\ map_uint_concrete 9220 32 (top_environment next) /\
 map_uint_concrete 9222 32 (top_environment next).
Proof.
 intros Run Old Observe Next Legal [Registers Storage].
 unfold joint_registers_concrete, top_environment in Registers. rewrite Old in Registers.
 split.
 - eapply (data_storage_run_step memory inputs k committed observed next Run Observe Next Storage).
   eapply (observed_data_commit_ready memory inputs k committed old observed Run Old Observe Legal); [|exact Storage].
   intros node width Member. apply Registers. apply joint_includes_writer. exact Member.
 - split.
   + exact (fetch_sized_from_joint_boundary memory inputs k committed old observed next Run Old Observe Next Legal Registers).
   + eapply (load_sized_from_data_boundary memory inputs k committed old observed next Run Old Observe Next Legal); [|exact Storage].
     intros node width Member. apply Registers. apply joint_includes_writer. apply data_writer_includes_address. exact Member.
Qed.
Print Assumptions joint_memory_boundary_step.
