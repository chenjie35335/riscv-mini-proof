Require Import CoreSocModel FormalLocalHistory JointBoundaryInitialization JointBoundaryRegisters JointBoundaryPreparation JointMemoryBoundaryStep JointScalarRegisterCommit ObservedJointUpdateFromCommitted FormalObservationCommit StagedFlatCircuitIteration ConcreteRegisterInitialization.
From Coq Require Import ZArith List Arith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Lemma joint_fetch_register_width width : List.In (9220%nat,width) joint_boundary_registers -> width = 32%nat.
Proof.
 unfold joint_boundary_registers. intro Member.
 repeat destruct Member as [Equal|Member]; try contradiction; inversion Equal; reflexivity.
Qed.
Lemma joint_load_register_width width : List.In (9222%nat,width) joint_boundary_registers -> width = 32%nat.
Proof.
 unfold joint_boundary_registers. intro Member.
 repeat destruct Member as [Equal|Member]; try contradiction; inversion Equal; reflexivity.
Qed.
Local Opaque generated_modules generated_top flat_statements flat_memories.
Theorem joint_boundary_run_step memory inputs k committed old observed next :
 generated_run memory inputs k = Some committed ->
 SVM.find nil committed = Some old ->
 generated_observe memory inputs k = Some observed ->
 generated_run memory inputs (S k) = Some next ->
 generated_legal_trace memory inputs k ->
 joint_boundary_concrete committed -> joint_boundary_concrete next.
Proof.
 intros Run Old Observe Next Legal Invariant.
 destruct (joint_memory_boundary_step memory inputs k committed old observed next Run Old Observe Next Legal Invariant)
 as [Storage [Fetch Load]].
 destruct Invariant as [Registers OldStorage].
 unfold joint_registers_concrete, top_environment in Registers. rewrite Old in Registers.
 assert (ObservedRegisters : forall node width, List.In (node,width) joint_boundary_registers ->
 map_uint_concrete (N.of_nat node) width (top_environment observed)).
 { intros node width Member. exact (joint_boundary_observed_concrete memory inputs k committed old observed node width
 Member (Registers node width Member) Run Old Observe). }
 pose proof (observed_joint_update_from_committed memory inputs k committed old observed Run Old Observe Legal Registers) as Sources.
 rewrite (observation_then_commit memory inputs k observed Observe) in Next.
 destruct (flat_iteration_projection _ observed true next Next) as [before [after [Before [Step After]]]].
 assert (Top : top_environment observed = before) by (unfold top_environment; rewrite Before; reflexivity).
 rewrite Top in ObservedRegisters. rewrite Top in Sources.
 split; [|exact Storage]. intros node width Member.
 destruct (Nat.eq_dec node 9220) as [Equal|NotFetch].
 - subst node. rewrite (joint_fetch_register_width width Member). exact Fetch.
 - destruct (Nat.eq_dec node 9222) as [Equal|NotLoad].
   + subst node. rewrite (joint_load_register_width width Member). exact Load.
   + unfold top_environment. rewrite After.
     exact (joint_scalar_registers_commit _ nil before before after ObservedRegisters Sources Step node width Member NotFetch NotLoad).
Qed.
Print Assumptions joint_boundary_run_step.
