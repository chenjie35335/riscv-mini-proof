Require Import CoreSocModel FormalLocalHistory JointBoundaryRegisters JointBoundaryPreparation ConcreteRegisterInitialization ObservedFetchAddressFromJointBoundary FormalObservedFetchType FormalFetchSizedCommit.
From Coq Require Import ZArith List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Theorem fetch_sized_from_joint_boundary memory inputs k committed old observed next :
 generated_run memory inputs k = Some committed ->
 SVM.find nil committed = Some old ->
 generated_observe memory inputs k = Some observed ->
 generated_run memory inputs (S k) = Some next ->
 generated_legal_trace memory inputs k ->
 (forall node width, List.In (node,width) joint_boundary_registers ->
 map_uint_concrete (N.of_nat node) width old) ->
 map_uint_concrete 9220 32 (top_environment next).
Proof.
 intros Run Old Observe Next Legal Boundary.
 assert (ObservedBoundary : forall node width, List.In (node,width) joint_boundary_registers ->
 map_uint_concrete (N.of_nat node) width (top_environment observed)).
 { intros node width Member. exact (joint_boundary_observed_concrete memory inputs k committed old observed
 node width Member (Boundary node width Member) Run Old Observe). }
 destruct (observed_fetch_address_from_joint_boundary memory inputs k observed Observe Legal ObservedBoundary) as [address Address].
 destruct (observed_fetch_type memory inputs k observed Observe) as [value [Value Typed]].
 exact (observed_fetch_commit_sized memory inputs k observed next value address 16 Observe Next Value Typed Address).
Qed.
Print Assumptions fetch_sized_from_joint_boundary.
