Require Import CoreSocModel FormalLocalHistory PipelineBubbleInstructionInvariant EarlyBubbleNopObservedStep FormalObservationCommit JointBoundaryInduction JointBoundaryReachable JointBoundaryInitialization JointBoundaryRegisters FormalFetchType FormalInstructionResetCycle FormalInstructionResetConstants ExternalReset.
From Coq Require Import ZArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque generated_modules generated_top generated_run.
Theorem early_bubble_nop_reachable memory inputs k states :
 generated_run memory inputs k = Some states ->
 generated_legal_trace memory inputs k -> early_bubble_nop (top_environment states).
Proof.
 destruct k as [|k]; intros Run Legal.
 - destruct (early_bubble_nop_run_zero memory inputs states Run) as [env [Env Property]].
   unfold top_environment. rewrite Env. exact Property.
 - assert (PriorLegal : generated_legal_trace memory inputs k).
   { apply (joint_legal_trace_prefix memory inputs (S k) k Legal). lia. }
   destruct (generated_successful_commit memory inputs k states Run) as [observed [Observe Commit]].
   destruct (legal_observation_reset memory inputs k PriorLegal) as [bit Reset].
   destruct bit.
   + pose proof Run as Expanded. rewrite FormalObservationCommit.generated_run_successor in Expanded.
     destruct (generated_run memory inputs k) as [previous|] eqn:Previous; [|discriminate Expanded].
     destruct (fetch9220_run_type memory inputs k previous Previous) as [old [value [Old Rest]]].
     destruct (joint_boundary_reachable memory inputs k previous Previous PriorLegal) as [Registers Storage].
     unfold top_environment in Registers. rewrite Old in Registers.
     destruct (Registers 7748%nat 32%nat ltac:(apply (List.nth_error_In joint_boundary_registers 53%nat); vm_compute;reflexivity)) as [front [FrontSize Front]].
     destruct (Registers 7750%nat 32%nat ltac:(apply (List.nth_error_In joint_boundary_registers 55%nat); vm_compute;reflexivity)) as [late [LateSize Late]].
     destruct (instruction_real_reset_cycle (generated_observation_input inputs k) previous old states
      (Gval (Fuint 32) front) (Gval (Fuint 32) late) Old Front (Logic.eq_refl _) Late (Logic.eq_refl _) Reset Expanded)
      as [env [Env [Nop Other]]].
     intro Bubble. unfold top_environment. rewrite Env. exact Nop.
   + intro Bubble. exact (observed_early_bubble_nop_successor memory inputs k observed states Observe PriorLegal Run Reset Bubble).
Qed.
Theorem early_bubble_nop_all_observations memory inputs k observed :
 generated_observe memory inputs k = Some observed ->
 generated_legal_trace memory inputs k -> early_bubble_nop (top_environment observed).
Proof.
 intros Observe Legal. pose proof Observe as Expanded. unfold generated_observe in Expanded.
 destruct (generated_run memory inputs k) as [previous|] eqn:Run; [|discriminate Expanded].
 destruct (fetch9220_run_type memory inputs k previous Run) as [old [value [Old Rest]]].
 pose proof (early_bubble_nop_reachable memory inputs k previous Run Legal) as Property.
 unfold top_environment in Property. rewrite Old in Property.
 exact (early_bubble_nop_observed memory inputs k previous old observed Run Old Observe Property).
Qed.
(* Independent audit: EarlyBubbleNopReachableAssumptions.v. *)
