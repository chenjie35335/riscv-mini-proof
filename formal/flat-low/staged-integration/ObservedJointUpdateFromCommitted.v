Require Import CoreSocModel FormalLocalHistory ObservedJointUpdateFromBoundary JointBoundaryPreparation JointBoundaryRegisters ConcreteRegisterInitialization JointUpdateGraphPropagation JointUpdateTargets.
From Coq Require Import ZArith List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Theorem observed_joint_update_from_committed memory inputs k committed old observed :
 generated_run memory inputs k = Some committed ->
 SVM.find nil committed = Some old ->
 generated_observe memory inputs k = Some observed ->
 generated_legal_trace memory inputs k ->
 (forall node width, List.In (node,width) joint_boundary_registers ->
   map_uint_concrete (N.of_nat node) width old) ->
 forall node, List.In node joint_update_targets -> joint_update_ground_at (top_environment observed) node.
Proof.
 intros Run Old Observe Legal Boundary.
 apply (observed_joint_update_from_boundary memory inputs k observed Observe Legal).
 intros node width Member.
 exact (joint_boundary_observed_concrete memory inputs k committed old observed node width
   Member (Boundary node width Member) Run Old Observe).
Qed.
Print Assumptions observed_joint_update_from_committed.
