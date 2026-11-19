Require Import CoreSocModel FormalLocalHistory FormalObservationCommit PipelinePCRelation ReferencePCResetCycle FetchPCResetCycle BooleanRegisterResetCycle Bubble7945Type Bubble7947Type ReferencePCType PipelineBubbleInitialization PipelineBubbleResetCommit StartupFlagReachable JointBoundaryReachable JointBoundaryInitialization JointBoundaryRegisters ConcreteRegisterInitialization FetchPCResetValue ReferencePCResetValue ReferencePCResetFacts.
From Coq Require Import ZArith List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque generated_modules generated_top generated_run generated_legal_trace generated_observation_input.
Theorem pipeline_pc_reset_successor memory inputs k next :
 generated_legal_trace memory inputs k ->
 VM.find 1 (formal_external_inputs (generated_observation_input inputs k)) = Some (Gval (Fuint 1) [::true]) ->
 generated_run memory inputs (S k) = Some next ->
 pipeline_pc_relation (top_environment next).
Proof.
 intros Legal Reset Next.
 destruct (startup_flag_run_successor memory inputs k next true Legal Reset Next)
 as [startup [Startup Started]].
 rewrite FormalObservationCommit.generated_run_successor in Next.
 destruct (generated_run memory inputs k) as [previous|] eqn:Run; [|discriminate Next].
 destruct (reference_pc7331_run_type memory inputs k previous Run) as [old [reference [Old [Reference TypedReference]]]].
 destruct (joint_boundary_reachable memory inputs k previous Run Legal) as [Registers Storage].
 destruct (Registers 7768%nat 33%nat ltac:(apply (List.nth_error_In joint_boundary_registers 67%nat); vm_compute;reflexivity)) as [fetch [FetchSize Fetch]].
 unfold top_environment in Fetch. rewrite Old in Fetch.
 destruct (fetch_pc_real_reset_cycle (generated_observation_input inputs k) previous old next (Gval (Fuint 33) fetch)
 Old Fetch (Logic.eq_refl _) Reset Next) as [env [Env FetchNext]].
 destruct (reference_pc_real_reset_cycle (generated_observation_input inputs k) previous old next reference
 Old Reference TypedReference Reset Next) as [refenv [Refenv ReferenceNext]].
 rewrite Env in Refenv. inversion Refenv; subst refenv.
 destruct (bubble7945_run_type memory inputs k previous Run) as [earlyenv [early [Earlyenv [Early EarlyType]]]].
 rewrite Old in Earlyenv. inversion Earlyenv; subst earlyenv.
 destruct (boolean_register_reset_cycle 7945 bubble7945_present (Logic.eq_refl true) (Logic.eq_refl true)
 bubble7945_initial_safe pipeline_bubble_7945_reset_commit (generated_observation_input inputs k) previous old next early
 Old Early EarlyType Reset Next) as [earlynext [Earlynext EarlyNext]].
 rewrite Env in Earlynext. inversion Earlynext; subst earlynext.
 destruct (bubble7947_run_type memory inputs k previous Run) as [lateenv [late [Lateenv [Late LateType]]]].
 rewrite Old in Lateenv. inversion Lateenv; subst lateenv.
 destruct (boolean_register_reset_cycle 7947 bubble7947_present (Logic.eq_refl true) (Logic.eq_refl true)
 bubble7947_initial_safe pipeline_bubble_7947_reset_commit (generated_observation_input inputs k) previous old next late
 Old Late LateType Reset Next) as [latenext [Latenext LateNext]].
 rewrite Env in Latenext. inversion Latenext; subst latenext.
 rewrite Env in Startup. inversion Startup; subst startup.
 unfold top_environment. rewrite Env.
 exists reference_pc_reset_bits. split; [exact reference_pc_reset_size|].
 split; [exact reference_pc_reset_aligned|]. split; [exact ReferenceNext|].
 right. right. split; [exact LateNext|]. split; [exact EarlyNext|].
 exists fetch_pc_reset_word33. split; [exact fetch_pc_reset_size33|]. split; [exact FetchNext|].
 right. split; [exact Started|].
 rewrite reference_pc_reset_unsigned fetch_pc_reset_unsigned. vm_compute. reflexivity.
Qed.
Corollary pipeline_pc_reset_transition memory inputs k observed next :
 generated_observe memory inputs k = Some observed ->
 generated_legal_trace memory inputs k ->
 generated_run memory inputs (S k) = Some next ->
 VM.find 1 (formal_external_inputs (generated_observation_input inputs k)) = Some (Gval (Fuint 1) [::true]) ->
 pipeline_pc_relation (top_environment next).
Proof. intros Observe Legal Next Reset. exact (pipeline_pc_reset_successor memory inputs k next Legal Reset Next). Qed.
