Require Import StoreAssertionHistory ReferenceStoreRequestData CoreSocModel ComparisonNodes FormalObservedHistory FormalLocalHistory.
From Coq Require Import NArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Theorem store_assertion5_observed memory inputs k observed guards source a0 a1 tail b0 b1 b2 b3 word :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->size word=32%nat ->
 VM.find 8004(top_environment observed)=Some(Gval(Fuint 32)(a0::a1::tail)) ->
 VM.find 7924(top_environment observed)=Some(Gval(Fuint 4)[::b0;b1;b2;b3]) ->
 VM.find 7925(top_environment observed)=Some(Gval(Fuint 32)word) ->
 VM.find 2804(top_environment observed)=Some(Gval(Fuint 32)source) ->
 (forall node,List.In node reference_store_request_data_guards ->VM.find node(top_environment observed)=Some(Gval(Fuint 1)[::guards node])) ->
 VM.find 1481(top_environment observed)=VM.find 1526(top_environment observed) ->
 generated_assert_m0_5_local(top_environment observed).
Proof.
 intros Observe Legal Size Address Mask Data Source Guards Agree.
 destruct(observed_history memory inputs k observed Observe Legal)as[reset[history[Last[Steps Resets]]]].
 rewrite <-Last.
 apply(store_assertion5_history (generated_observation_input inputs k)nil history reset guards source a0 a1 tail b0 b1 b2 b3 word Size Resets Steps).
 - rewrite Last. exact Address.
 - rewrite Last. exact Mask.
 - rewrite Last. exact Data.
 - rewrite Last. exact Source.
 - intros node Member. rewrite Last. apply Guards;exact Member.
 - rewrite Last. exact Agree.
Qed.
