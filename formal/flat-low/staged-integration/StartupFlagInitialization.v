Require Import RegisterInvariants CoreSocModel ComparisonNodes JointBoundaryRegisters JointBoundaryInitialization JointBoundaryPreparation RegisterPreparationFrames FormalLocalHistory ConcreteRegisterInitialization.
From Coq Require Import ZArith List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory FormalInitialization.
Local Open Scope N_scope.
Lemma startup_register_member : List.In (7762%nat,1%nat) joint_boundary_registers.
Proof. apply (List.nth_error_In joint_boundary_registers 66%nat). vm_compute. reflexivity. Qed.
Lemma startup_register_present : has_register 7762 flat_statements = true.
Proof. exact (proj2 (joint_boundary_register_properties 7762 1 startup_register_member)). Qed.
Lemma startup_initial_safe : initial_register_safe 7762 flat_statements.
Proof.
 pose proof joint_boundary_preparation_check as Check.
 rewrite List.forallb_forall in Check. specialize (Check (7762%nat,1%nat) startup_register_member).
 cbn [fst snd] in Check. move/andP: Check => [/andP [Safe NotClock] NotReset]. exact Safe.
Qed.
Theorem startup_initial_state_concrete memory inputs states :
 circuit_symbolic_initial_state generated_modules generated_top memory inputs = Some states ->
 exists env, SVM.find nil states = Some env /\ map_uint_concrete 7762 1 env.
Proof.
 intro Init.
 destruct (joint_boundary_symbolic_initial memory inputs states Init) as [Registers Storage].
 specialize (Registers 7762%nat 1%nat startup_register_member).
 unfold top_environment in Registers.
 destruct (SVM.find nil states) as [env|] eqn:Env.
 - exists env. split; [reflexivity|exact Registers].
 - destruct Registers as [bits [Size Value]]. discriminate Value.
Qed.
Print Assumptions startup_initial_state_concrete.
