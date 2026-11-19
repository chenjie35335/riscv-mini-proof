Require Import CoreSocModel FormalLocalHistory PipelinePCRelation PipelinePCFrontToCommit PipelinePCFetchNopTransition PipelinePCStartupTransition.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Theorem pipeline_pc_bubble_transition memory inputs k observed next :
 generated_observe memory inputs k = Some observed ->
 generated_legal_trace memory inputs k ->
 generated_run memory inputs (S k) = Some next ->
 VM.find 1 (formal_external_inputs (generated_observation_input inputs k)) = Some (Gval (Fuint 1) [::false]) ->
 pipeline_pc_relation (top_environment observed) ->
 VM.find 7947 (top_environment observed) = Some (Gval (Fuint 1) [::true]) ->
 pipeline_pc_relation (top_environment next).
Proof.
 intros Observe Legal Next Reset Relation Late.
 destruct Relation as [bits [Size [Aligned [Reference Phase]]]].
 destruct Phase as [[L Commit]|[[L [Early Front]]|[L [Early [fetch [FetchSize [Fetch State]]]]]]].
 - rewrite Late in L. discriminate L.
 - exact (pipeline_pc_front_to_commit memory inputs k observed next bits Observe Legal Next Reset Size Aligned Reference Front Late Early).
 - destruct State as [[Started Match]|[Started Numeric]].
   + subst bits. exact (pipeline_pc_fetch_to_front memory inputs k observed next fetch Observe Legal Next Reset FetchSize Aligned Fetch Reference Late Early Started).
   + apply (pipeline_pc_startup_transition memory inputs k observed next Observe Legal Next Reset); try assumption.
     exists bits. split; [exact Size|]. split; [exact Aligned|]. split; [exact Reference|].
     right. right. split; [exact Late|]. split; [exact Early|].
     exists fetch. split; [exact FetchSize|]. split; [exact Fetch|]. right. split; assumption.
Qed.
