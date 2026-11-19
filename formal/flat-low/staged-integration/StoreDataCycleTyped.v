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
Theorem store_data_cycle_commit_typed memory inputs k observed next b0 b1 tail word reset old_value :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 generated_run memory inputs(S k)=Some next ->
 VM.find 1(formal_external_inputs(generated_observation_input inputs k))=Some(Gval(Fuint 1)[::reset]) ->
 VM.find 7925(top_environment observed)=Some old_value ->
 type_of_val old_value=Gtyp(Fuint 32) ->
 VM.find 1155(top_environment observed)=Some(Gval(Fuint 32)(b0::b1::tail)) ->
 VM.find 7819(top_environment observed)=Some(Gval(Fuint 32)word) ->
 VM.find 7925(top_environment next)=Some(Gval(Fuint 32)
 (if reset then zeros 32 else take 32(zeros(to_nat(store_offset_word b0 b1))++word))).
Proof.
 intros Observe Legal Next Reset Old Typed Address Word.
 pose proof(store_request_data_observed memory inputs k observed b0 b1 tail word Observe Legal Address Word)as Data.
 pose proof(store_observed_core_reset memory inputs k observed reset Reset Observe)as Control.
 destruct(proj1(proj2(observed_rf_ports_concrete memory inputs k observed Observe Legal)))as[actual[Size Actual]].
 rewrite Word in Actual. inversion Actual;subst actual.
 assert(DataSize:size(take 32(zeros(to_nat(store_offset_word b0 b1))++word))=32%nat).
 { rewrite -(store_request_word8_low word (store_offset_word b0 b1) Size).
   apply store_request_word8_size;[exact Size|reflexivity]. }
 rewrite(observation_then_commit memory inputs k observed Observe)in Next.
 destruct(flat_iteration_projection _ observed true next Next)as[before[after[Before[Step After]]]].
 assert(Top:top_environment observed=before)by(unfold top_environment;rewrite Before;reflexivity).
 rewrite <-Top in Step.
 unfold top_environment. rewrite After.
 destruct reset.
 - exact(store_data_commit_reset _ _ _ _ old_value _ Old Typed Control Data DataSize Step).
 - exact(store_data_commit_normal _ _ _ _ old_value _ Old Typed Control Data DataSize Step).
Qed.
