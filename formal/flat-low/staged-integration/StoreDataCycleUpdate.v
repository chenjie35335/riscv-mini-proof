Require Import StoreDataCommit StoreDataResetCommit StoreDataCycleCommit.
Require Import CoreSocModel StoreRequestDataObserved StoreDataCommitStep StoreOffsetValue StoreRequestDataValue
 FormalObservationCommit StagedFlatCircuitIteration FormalLocalHistory FormalCoreResetControl
 FormalResetPreparation FormalResetTrace StagedIterationCount ConcreteRegisterInitialization ObservedRFPortsConcrete.
From Coq Require Import NArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque generated_modules generated_top.
Require Import StoreDataReachableType StoreDataCycleTyped.
Theorem store_data_cycle_update memory inputs k observed next b0 b1 tail word reset :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 generated_run memory inputs(S k)=Some next ->
 VM.find 1(formal_external_inputs(generated_observation_input inputs k))=Some(Gval(Fuint 1)[::reset]) ->
 VM.find 1155(top_environment observed)=Some(Gval(Fuint 32)(b0::b1::tail)) ->
 VM.find 7819(top_environment observed)=Some(Gval(Fuint 32)word) ->
 VM.find 7925(top_environment next)=Some(Gval(Fuint 32)
 (if reset then zeros 32 else take 32(zeros(to_nat(store_offset_word b0 b1))++word))).
Proof.
 intros Observe Legal Next Reset Address Word.
 destruct(store_data_observed_type memory inputs k observed Observe)as[value[Value Typed]].
 exact(store_data_cycle_commit_typed memory inputs k observed next b0 b1 tail word reset value
 Observe Legal Next Reset Value Typed Address Word).
Qed.
