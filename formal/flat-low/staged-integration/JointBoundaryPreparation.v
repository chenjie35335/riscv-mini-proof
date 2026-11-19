Require Import CoreSocModel ComparisonNodes JointBoundaryRegisters RegisterPreparationFrames StagedObservedRegister StagedCircuitRegisterHold FormalLocalHistory ConcreteRegisterInitialization.
From Coq Require Import ZArith List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Lemma joint_boundary_preparation_check :
 List.forallb (fun entry =>
 initial_register_safe (N.of_nat (fst entry)) flat_statements &&
 (N.of_nat (fst entry) != N.of_nat 0) && (N.of_nat (fst entry) != N.of_nat 1)) joint_boundary_registers = true.
Proof. vm_compute. reflexivity. Qed.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Theorem joint_boundary_prepared_concrete previous old external prepared node width :
 List.In (node,width) joint_boundary_registers ->
 map_uint_concrete (N.of_nat node) width old ->
 SVM.find nil previous = Some old ->
 circuit_initial_map_with_memory generated_modules generated_top (Some previous) external = Some prepared ->
 map_uint_concrete (N.of_nat node) width (top_environment prepared).
Proof.
 intros Member [bits [Size Value]] Old Prepare.
 pose proof joint_boundary_preparation_check as Check.
 rewrite List.forallb_forall in Check. specialize (Check (node,width) Member).
 cbn [fst snd] in Check. move/andP: Check => [/andP [Safe NotClock] NotReset].
 destruct (joint_boundary_register_properties node width Member) as [_ Present].
 pose proof (staged_prepared_register_copies previous old external prepared (N.of_nat node)
 NotClock NotReset Safe Present Old Prepare) as Copy.
 rewrite Value in Copy. unfold staged_register_lookup in Copy.
 unfold top_environment. destruct (SVM.find nil prepared) as [env|]; [|discriminate Copy].
 exists bits. split; assumption.
Qed.
Print Assumptions joint_boundary_prepared_concrete.
Theorem joint_boundary_observed_concrete memory inputs k committed old observed node width :
 List.In (node,width) joint_boundary_registers ->
 map_uint_concrete (N.of_nat node) width old ->
 generated_run memory inputs k = Some committed -> SVM.find nil committed = Some old ->
 generated_observe memory inputs k = Some observed ->
 map_uint_concrete (N.of_nat node) width (top_environment observed).
Proof.
 intros Member [bits [Size Value]] Run Old Observe.
 pose proof joint_boundary_preparation_check as Check.
 rewrite List.forallb_forall in Check. specialize (Check (node,width) Member).
 cbn [fst snd] in Check. move/andP: Check => [/andP [Safe NotClock] NotReset].
 destruct (joint_boundary_register_properties node width Member) as [_ Present].
 pose proof (staged_observed_register_copies memory inputs k committed old observed (N.of_nat node)
 NotClock NotReset Safe Present Run Old Observe) as Copy.
 rewrite Value in Copy. unfold staged_register_lookup in Copy.
 unfold top_environment. destruct (SVM.find nil observed) as [env|]; [|discriminate Copy].
 exists bits. split; assumption.
Qed.
Print Assumptions joint_boundary_observed_concrete.
