Require Import ObservedNopControls EarlyBubbleNopReachable PipelineBubbleInstructionInvariant PipelinePCFetchToFront CoreSocModel FormalLocalHistory PipelinePCRelation ObservedFrontPCTransfer ObservedEarlyBubbleClear ObservedLateBubbleTransfer ObservedCheckerBubbleValue ObservedReferencePCStutter.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Theorem pipeline_pc_fetch_to_front memory inputs k observed next fetch :
 generated_observe memory inputs k = Some observed ->
 generated_legal_trace memory inputs k ->
 generated_run memory inputs (S k) = Some next ->
 VM.find 1 (formal_external_inputs (generated_observation_input inputs k)) = Some (Gval (Fuint 1) [::false]) ->
 size fetch = 33%nat -> take 2 (take 32 fetch) = [::false;false] ->
 VM.find 7768 (top_environment observed) = Some (Gval (Fuint 33) fetch) ->
 VM.find 7331 (top_environment observed) = Some (Gval (Fuint 32) (take 32 fetch)) ->
 VM.find 7947 (top_environment observed) = Some (Gval (Fuint 1) [::true]) ->
 VM.find 7945 (top_environment observed) = Some (Gval (Fuint 1) [::true]) ->
 VM.find 7762 (top_environment observed) = Some (Gval (Fuint 1) [::false]) ->
 pipeline_pc_relation (top_environment next).
Proof.
 intros Observe Legal Next Reset Size Aligned Fetch Reference Late Early Started.
 pose proof (early_bubble_nop_all_observations memory inputs k observed Observe Legal Early) as Nop.
 destruct (observed_nop_controls_false memory inputs k observed Observe Legal Nop) as [Kill Branch].
 exact (pipeline_pc_fetch_to_front_controlled memory inputs k observed next fetch
 Observe Legal Next Reset Size Aligned Fetch Reference Late Early Started Kill Branch).
Qed.
