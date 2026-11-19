Require Import CoreSocModel FormalLocalHistory PipelinePCAdjacentTransfer PipelinePCFetchAdjacency FetchPCSequentialObserved FetchPCSequentialExact ObservedFrontPCTransfer.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Theorem pipeline_pc_sequential_front_fetch_adjacent memory inputs k observed next fetch :
 generated_observe memory inputs k = Some observed ->
 generated_legal_trace memory inputs k ->
 generated_run memory inputs (S k) = Some next ->
 VM.find 1 (formal_external_inputs (generated_observation_input inputs k)) = Some (Gval (Fuint 1) [::false]) ->
 VM.find 7776 (top_environment observed) = Some (Gval (Fuint 1) [::false]) ->
 VM.find 7773 (top_environment observed) = Some (Gval (Fuint 1) [::false]) ->
 VM.find 7771 (top_environment observed) = Some (Gval (Fuint 1) [::false]) ->
 size fetch = 33%nat ->
 VM.find 7768 (top_environment observed) = Some (Gval (Fuint 33) fetch) ->
 pipeline_front_fetch_adjacent (top_environment next).
Proof.
 intros Observe Legal Next Reset Sel2 Sel3 Sel4 Size Fetch.
 pose proof (adjacent_transfer_observed_reset memory inputs k observed Observe Legal Reset) as Root.
 pose proof (observed_front_pc_transfer memory inputs k observed next fetch Observe Legal Next Root Size Fetch) as FrontNext.
 pose proof (fetch_pc_sequential_observed memory inputs k observed next fetch Observe Legal Next Root Sel2 Sel3 Sel4 Fetch) as FetchNext.
 exists (take 32 fetch), (fetch_pc_plus_four fetch).
 split; [apply fetch_pc_plus_four_size|]. split; [exact FrontNext|]. split; [exact FetchNext|].
 exact (fetch_pc_successor_low_adjacent fetch Size).
Qed.
