Require Import CoreSocModel FormalLocalHistory ObservedCommitPCAdvance ObservedJointRegisterConcrete JointBoundaryRegisters ConcreteRegisterInitialization.
From Coq Require Import ZArith List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Theorem observed_commit_pc_transfer memory inputs k observed next front :
 generated_observe memory inputs k = Some observed ->
 generated_legal_trace memory inputs k ->
 generated_run memory inputs (S k) = Some next ->
 VM.find 1 (formal_external_inputs (generated_observation_input inputs k)) = Some (Gval (Fuint 1) [::false]) ->
 size front = 32%nat ->
 VM.find 7749 (top_environment observed) = Some (Gval (Fuint 32) front) ->
 VM.find 7751 (top_environment next) = Some (Gval (Fuint 32) front).
Proof.
 intros Observe Legal Next Reset Size Front.
 destruct (observed_joint_register_concrete memory inputs k observed 7751%nat 32%nat Observe Legal
 ltac:(apply (List.nth_error_In joint_boundary_registers 56%nat); vm_compute;reflexivity)) as [old [OldSize Old]].
 exact (observed_commit_pc_normal_step memory inputs k observed next front old Observe Legal Next Reset Size Front Old).
Qed.
