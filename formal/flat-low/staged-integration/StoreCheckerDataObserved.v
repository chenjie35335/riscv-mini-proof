Require Import StoreCheckerDataHistory CoreSocModel ComparisonNodes FormalObservedHistory FormalLocalHistory.
From Coq Require Import NArith Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Theorem store_checker_data_observed memory inputs k observed a0 a1 tail b0 b1 b2 b3 word :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->size word=32%nat ->
 VM.find 8004(top_environment observed)=Some(Gval(Fuint 32)(a0::a1::tail)) ->
 VM.find 7924(top_environment observed)=Some(Gval(Fuint 4)[::b0;b1;b2;b3]) ->
 VM.find 7925(top_environment observed)=Some(Gval(Fuint 32)word) ->
 VM.find 1481(top_environment observed)=Some(Gval(Fuint 32)(store_checker_data_word a0 a1 b0 b1 b2 b3 word)).
Proof.
 intros Observe Legal Size Address Mask Word.
 destruct(observed_history memory inputs k observed Observe Legal)as[reset[history[Last[Steps Resets]]]].
 rewrite <-Last.
 apply(store_checker_data_history_from_last _ history 9259 a0 a1 tail b0 b1 b2 b3 word Size Steps).
 - rewrite Last. exact Address.
 - rewrite Last. exact Mask.
 - rewrite Last. exact Word.
 - vm_compute;lia.
 - vm_compute;lia.
Qed.
Theorem store_checker_data_history_stable invalid history limit a0 a1 tail b0 b1 b2 b3 word :
 size word=32%nat ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter invalid flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 VM.find 8004(history limit)=Some(Gval(Fuint 32)(a0::a1::tail)) ->
 VM.find 7924(history limit)=Some(Gval(Fuint 4)[::b0;b1;b2;b3]) ->
 VM.find 7925(history limit)=Some(Gval(Fuint 32)word) ->
 forall t u,(10<=t)%coq_nat ->(t<=limit)%coq_nat ->(10<=u)%coq_nat ->(u<=limit)%coq_nat ->
 VM.find 1481(history t)=VM.find 1481(history u).
Proof.
 intros Size Steps Address Mask Word t u LT UT LU UU.
 rewrite(store_checker_data_history_from_last invalid history limit a0 a1 tail b0 b1 b2 b3 word Size Steps Address Mask Word t LT UT).
 rewrite(store_checker_data_history_from_last invalid history limit a0 a1 tail b0 b1 b2 b3 word Size Steps Address Mask Word u LU UU).
 reflexivity.
Qed.
