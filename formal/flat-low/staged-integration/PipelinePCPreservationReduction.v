Require Import CoreSocModel FormalLocalHistory PipelinePCRelation PipelinePCBubbleTransition PipelinePCResetTransition PipelinePCReachabilityInduction ExternalReset ObservedAssertion43FromPipeline.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Definition pipeline_pc_active_preservation memory inputs :=
 forall k observed next,
 generated_observe memory inputs k = Some observed ->
 generated_legal_trace memory inputs k ->
 generated_run memory inputs (S k) = Some next ->
 VM.find 1 (formal_external_inputs (generated_observation_input inputs k)) = Some (Gval (Fuint 1) [::false]) ->
 pipeline_pc_relation (top_environment observed) ->
 VM.find 7947 (top_environment observed) = Some (Gval (Fuint 1) [::false]) ->
 pipeline_pc_relation (top_environment next).
Theorem pipeline_pc_step_from_active memory inputs :
 pipeline_pc_active_preservation memory inputs ->
 forall k observed next,
 generated_observe memory inputs k = Some observed ->
 generated_legal_trace memory inputs k ->
 generated_run memory inputs (S k) = Some next ->
 pipeline_pc_relation (top_environment observed) ->
 pipeline_pc_relation (top_environment next).
Proof.
 intros Active k observed next Observe Legal Next Relation.
 destruct (legal_observation_reset memory inputs k Legal) as [reset Reset].
 destruct reset.
 - exact (pipeline_pc_reset_transition memory inputs k observed next Observe Legal Next Reset).
 - destruct (pipeline_pc_relation_bubble _ Relation) as [bubble Bubble].
   destruct bubble.
   + exact (pipeline_pc_bubble_transition memory inputs k observed next Observe Legal Next Reset Relation Bubble).
   + exact (Active k observed next Observe Legal Next Reset Relation Bubble).
Qed.
Theorem assertion43_from_active_preservation memory inputs :
 pipeline_pc_active_preservation memory inputs ->
 forall k observed, generated_observe memory inputs k = Some observed ->
 generated_legal_trace memory inputs k -> generated_assert_m0_43_all observed.
Proof.
 intros Active k observed Observe Legal.
 apply (observed_assertion43_from_pipeline memory inputs k observed Observe Legal).
 exact (pipeline_pc_observation_from_preservation memory inputs
 (pipeline_pc_step_from_active memory inputs Active) k observed Observe Legal).
Qed.
(* Conditional reduction only: active preservation requires a stronger reachable
   invariant linking in-flight successors and architectural operands. *)
