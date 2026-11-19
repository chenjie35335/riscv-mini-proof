Require Import CoreSocModel FormalLocalHistory PipelinePCRelation PipelinePCAdjacentTransfer PipelinePCActiveSequential PipelinePCActiveBubbleSequential ReferencePCSequentialObserved EarlyBubbleBitReachable.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque generated_modules generated_top generated_run.
(* The sequential successor is carried by the next non-bubble pipeline stage.
   Establishing these address relations from reachability remains an obligation. *)
Definition active_sequential_addresses env : Prop :=
 (VM.find 7945 env = Some (Gval (Fuint 1) [::false]) -> pipeline_commit_front_adjacent env) /\
 (VM.find 7945 env = Some (Gval (Fuint 1) [::true]) -> pipeline_commit_fetch_adjacent env).
Theorem pipeline_pc_active_sequential_cases memory inputs k observed next :
 generated_observe memory inputs k = Some observed ->
 generated_legal_trace memory inputs k ->
 generated_run memory inputs (S k) = Some next ->
 VM.find 1 (formal_external_inputs (generated_observation_input inputs k)) = Some (Gval (Fuint 1) [::false]) ->
 reference_pc_sequential_control_window (formal_invalid_policy (generated_observation_input inputs k) nil) (top_environment observed) ->
 pipeline_pc_relation (top_environment observed) ->
 active_sequential_addresses (top_environment observed) ->
 VM.find 7947 (top_environment observed) = Some (Gval (Fuint 1) [::false]) ->
 pipeline_pc_relation (top_environment next).
Proof.
 intros Observe Legal Next Reset Window Relation [Front Fetch] Late.
 destruct (early_bubble_known_observation memory inputs k observed Observe Legal) as [early Early].
 destruct early.
 - exact (pipeline_pc_active_bubble_sequential_window memory inputs k observed next
 Observe Legal Next Reset Window Relation (Fetch Early) Late Early).
 - exact (pipeline_pc_active_sequential_window memory inputs k observed next
 Observe Legal Next Reset Window Relation (Front Early) Late Early).
Qed.
