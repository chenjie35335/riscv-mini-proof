Require Import CoreSocModel StartupFlagInitialization StartupFlagCycle JointBoundaryInitialization JointBoundaryReachable FormalObservationCommit FormalLocalHistory ConcreteRegisterInitialization.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory FormalInitialization.
Local Open Scope N_scope.
Local Opaque generated_modules generated_top generated_run generated_legal_trace generated_observation_input.
Theorem startup_flag_run_successor memory inputs k result bit :
 generated_legal_trace memory inputs k ->
 VM.find 1 (formal_external_inputs (generated_observation_input inputs k)) =
 Some (Gval (Fuint 1) [::bit]) ->
 generated_run memory inputs (S k) = Some result ->
 exists env, SVM.find nil result = Some env /\
 VM.find 7762 env = Some (Gval (Fuint 1) [::bit]).
Proof.
 intros Legal Reset Next.
 rewrite FormalObservationCommit.generated_run_successor in Next.
 destruct (generated_run memory inputs k) as [previous|] eqn:Run; [|discriminate Next].
 destruct (joint_boundary_reachable memory inputs k previous Run Legal) as [Registers Storage].
 specialize (Registers 7762%nat 1%nat startup_register_member).
 unfold top_environment in Registers.
 destruct (SVM.find nil previous) as [old|] eqn:Old.
 - destruct Registers as [bits [Size Value]].
   exact (startup_flag_real_cycle (generated_observation_input inputs k) previous old result
    (Gval (Fuint 1) bits) bit Old Value (Logic.eq_refl _) Reset Next).
 - destruct Registers as [bits [Size Value]]. discriminate Value.
Qed.
Corollary startup_flag_normal_successor memory inputs k result :
 generated_legal_trace memory inputs k ->
 VM.find 1 (formal_external_inputs (generated_observation_input inputs k)) =
 Some (Gval (Fuint 1) [::false]) ->
 generated_run memory inputs (S k) = Some result ->
 exists env, SVM.find nil result = Some env /\
 VM.find 7762 env = Some (Gval (Fuint 1) [::false]).
Proof. exact (startup_flag_run_successor memory inputs k result false). Qed.
(* Dependency assumption audit is separate: StartupFlagReachableAssumptions.v. *)
