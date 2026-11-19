Require Import CoreSocModel FormalLocalHistory ObservedPipelinePCRelation JointBoundaryReachable JointBoundaryInitialization JointBoundaryRegisters FormalFetchType ConcreteRegisterInitialization.
From Coq Require Import ZArith List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Opaque generated_modules generated_top generated_run.
Theorem observed_joint_register_concrete memory inputs k observed node width :
 generated_observe memory inputs k = Some observed ->
 generated_legal_trace memory inputs k ->
 List.In (node,width) joint_boundary_registers ->
 map_uint_concrete (N.of_nat node) width (top_environment observed).
Proof.
 intros Observe Legal Member. pose proof Observe as Expanded.
 unfold generated_observe in Expanded.
 destruct (generated_run memory inputs k) as [previous|] eqn:Run; [|discriminate Expanded].
 destruct (fetch9220_run_type memory inputs k previous Run) as [env [value [Env Rest]]].
 destruct (joint_boundary_reachable memory inputs k previous Run Legal) as [Registers Storage].
 unfold top_environment in Registers. rewrite Env in Registers.
 destruct (Registers node width Member) as [bits [Size Value]].
 exists bits. split; [exact Size|].
 rewrite (observed_joint_register_copy memory inputs k previous env observed node width Member Run Env Observe).
 exact Value.
Qed.
