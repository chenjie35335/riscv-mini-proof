Require Import ComparisonNodes StagedCircuitRegisterHold CoreSocModel FormalLocalHistory FormalObservationCommit Bubble7947Type PipelineBubbleInitialization PipelineBubbleResetCommit PipelineBubbleResetBase BooleanRegisterResetCycle StartupFlagReachable JointBoundaryInduction ExternalReset ObservedPipelinePCRelation JointBoundaryRegisters StagedObservedRegister.
From Coq Require Import ZArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque generated_modules generated_top flat_statements flat_memories generated_run.
Theorem late_bubble_reset_successor memory inputs k next :
 VM.find 1 (formal_external_inputs (generated_observation_input inputs k)) = Some (Gval (Fuint 1) [::true]) ->
 generated_run memory inputs (S k) = Some next ->
 VM.find 7947 (top_environment next) = Some (Gval (Fuint 1) [::true]).
Proof.
 intros Reset Next. rewrite generated_run_successor in Next.
 destruct (generated_run memory inputs k) as [previous|] eqn:Run; [|discriminate Next].
 destruct (bubble7947_run_type memory inputs k previous Run) as [old [late [Old [Late Typed]]]].
 destruct (boolean_register_reset_cycle 7947 bubble7947_present (Logic.eq_refl true) (Logic.eq_refl true)
 bubble7947_initial_safe pipeline_bubble_7947_reset_commit (generated_observation_input inputs k) previous old next late
 Old Late Typed Reset Next) as [env [Env Value]].
 unfold top_environment. rewrite Env. exact Value.
Qed.
Theorem active_run_startup_false memory inputs k states :
 generated_run memory inputs k = Some states ->
 generated_legal_trace memory inputs k ->
 VM.find 7947 (top_environment states) = Some (Gval (Fuint 1) [::false]) ->
 VM.find 7762 (top_environment states) = Some (Gval (Fuint 1) [::false]).
Proof.
 destruct k as [|k]; intros Run Legal Active.
 - destruct (pipeline_bubbles_run_zero memory inputs states Run) as [env [Env [Early Late]]].
   unfold top_environment in Active. rewrite Env Late in Active. discriminate Active.
 - assert (PriorLegal : generated_legal_trace memory inputs k).
   { apply (joint_legal_trace_prefix memory inputs (S k) k Legal). lia. }
   destruct (legal_observation_reset memory inputs k PriorLegal) as [reset Reset].
   destruct reset.
   + pose proof (late_bubble_reset_successor memory inputs k states Reset Run) as Late.
     rewrite Late in Active. discriminate Active.
   + destruct (startup_flag_normal_successor memory inputs k states PriorLegal Reset Run) as [env [Env Value]].
     unfold top_environment. rewrite Env. exact Value.
Qed.
Theorem active_observation_startup_false memory inputs k observed :
 generated_observe memory inputs k = Some observed ->
 generated_legal_trace memory inputs k ->
 VM.find 7947 (top_environment observed) = Some (Gval (Fuint 1) [::false]) ->
 VM.find 7762 (top_environment observed) = Some (Gval (Fuint 1) [::false]).
Proof.
 intros Observe Legal Active. pose proof Observe as Expanded. unfold generated_observe in Expanded.
 destruct (generated_run memory inputs k) as [previous|] eqn:Run; [|discriminate Expanded].
 destruct (bubble7947_run_type memory inputs k previous Run) as [old [late [Old [Late Typed]]]].
 pose proof (staged_observed_register_copies memory inputs k previous old observed 7947
 (Logic.eq_refl true) (Logic.eq_refl true) bubble7947_initial_safe bubble7947_present Run Old Observe) as Copy.
 unfold staged_register_lookup in Copy.
 assert (ActiveOld : VM.find 7947 (top_environment previous) = Some (Gval (Fuint 1) [::false])).
 { unfold top_environment. rewrite Old. rewrite <- Copy.
   unfold top_environment in Active. destruct (SVM.find nil observed); [exact Active|discriminate Active]. }
 pose proof (active_run_startup_false memory inputs k previous Run Legal ActiveOld) as Started.
 unfold top_environment in Started. rewrite Old in Started.
 rewrite (observed_joint_register_copy memory inputs k previous old observed 7762%nat 1%nat
 ltac:(apply (List.nth_error_In joint_boundary_registers 66%nat); vm_compute;reflexivity) Run Old Observe).
 exact Started.
Qed.
