Require Import CoreSocModel PipelinePCRelation ObservedPipelinePCRelation FormalLocalHistory FormalObservationCommit FormalFetchType JointBoundaryInduction.
From Coq Require Import Arith Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Opaque generated_modules generated_top.
Theorem pipeline_pc_reachability_induction memory inputs :
 (forall k observed next,
  generated_observe memory inputs k = Some observed ->
  generated_legal_trace memory inputs k ->
  generated_run memory inputs (S k) = Some next ->
  pipeline_pc_relation (top_environment observed) ->
  pipeline_pc_relation (top_environment next)) ->
 forall k states, generated_run memory inputs k = Some states ->
 generated_legal_trace memory inputs k -> pipeline_pc_relation (top_environment states).
Proof.
 intros Preserve k. induction k as [|k IH]; intros states Run Legal.
 - destruct (pipeline_pc_relation_initial memory inputs states Run) as [env [Env Relation]].
   unfold top_environment. rewrite Env. exact Relation.
 - pose proof Run as Expanded. rewrite generated_run_successor in Expanded.
   destruct (generated_run memory inputs k) as [previous|] eqn:Previous; [|discriminate Expanded].
   destruct (generated_successful_commit memory inputs k states Run) as [observed [Observe Commit]].
   destruct (fetch9220_run_type memory inputs k previous Previous) as [old [value [Old Rest]]].
   assert (PriorLegal : generated_legal_trace memory inputs k).
   { apply (joint_legal_trace_prefix memory inputs (S k) k Legal). lia. }
   pose proof (IH previous (Logic.eq_refl _) PriorLegal) as Relation.
   unfold top_environment in Relation. rewrite Old in Relation.
   apply (Preserve k observed states Observe PriorLegal Run).
   exact (observed_pipeline_pc_relation memory inputs k previous old observed Previous Old Observe Relation).
Qed.
Theorem pipeline_pc_observation_from_preservation memory inputs :
 (forall k observed next,
  generated_observe memory inputs k = Some observed ->
  generated_legal_trace memory inputs k ->
  generated_run memory inputs (S k) = Some next ->
  pipeline_pc_relation (top_environment observed) ->
  pipeline_pc_relation (top_environment next)) ->
 forall k observed, generated_observe memory inputs k = Some observed ->
 generated_legal_trace memory inputs k -> pipeline_pc_relation (top_environment observed).
Proof.
 intros Preserve k observed Observe Legal.
 pose proof Observe as Expanded. unfold generated_observe in Expanded.
 destruct (generated_run memory inputs k) as [previous|] eqn:Run; [|discriminate Expanded].
 destruct (fetch9220_run_type memory inputs k previous Run) as [old [value [Old Rest]]].
 pose proof (pipeline_pc_reachability_induction memory inputs Preserve k previous Run Legal) as Relation.
 unfold top_environment in Relation. rewrite Old in Relation.
 exact (observed_pipeline_pc_relation memory inputs k previous old observed Run Old Observe Relation).
Qed.
