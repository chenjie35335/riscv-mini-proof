Require Import CoreSocModel ComparisonNodes FormalLocalHistory FormalObservedHistory FormalObservationCommit StagedFlatCircuitIteration FrontPCNormalFullHistory ObservedJointRegisterConcrete JointBoundaryRegisters ConcreteRegisterInitialization.
From Coq Require Import ZArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque generated_modules generated_top flat_statements flat_memories.
Theorem observed_front_pc_transfer memory inputs k observed next bits :
 generated_observe memory inputs k = Some observed ->
 generated_legal_trace memory inputs k ->
 generated_run memory inputs (S k) = Some next ->
 VM.find 1 (top_environment observed) = Some (Gval (Fuint 1) [::false]) ->
 size bits = 33%nat ->
 VM.find 7768 (top_environment observed) = Some (Gval (Fuint 33) bits) ->
 VM.find 7749 (top_environment next) = Some (Gval (Fuint 32) (take 32 bits)).
Proof.
 intros Observe Legal Next Reset Size Source.
 destruct (observed_joint_register_concrete memory inputs k observed 7749%nat 32%nat Observe Legal
 ltac:(apply (List.nth_error_In joint_boundary_registers 54%nat); vm_compute;reflexivity)) as [front [FrontSize Front]].
 destruct (observed_history memory inputs k observed Observe Legal)
 as [bit [history [Last [Steps Resets]]]].
 assert (FalseBit : bit = false).
 { pose proof (Resets 9259%nat ltac:(vm_compute; lia)) as R. rewrite Last Reset in R.
   destruct bit; [discriminate R|reflexivity]. }
 subst bit.
 rewrite (observation_then_commit memory inputs k observed Observe) in Next.
 destruct (flat_iteration_projection _ observed true next Next) as [before [after [Before [Step After]]]].
 assert (Top : top_environment observed = before) by (unfold top_environment; rewrite Before; reflexivity).
 unfold top_environment. rewrite After.
 rewrite <- Top in Step. rewrite <- Last in Step.
 apply (front_pc_normal_full_history (formal_invalid_policy (generated_observation_input inputs k) nil) history after bits front Steps Resets Size).
 - rewrite Last. exact Source.
 - rewrite Last. exact Front.
 - exact Step.
Qed.
(* Transitive assumption audit: ObservedFrontPCTransferAssumptions.v. *)
