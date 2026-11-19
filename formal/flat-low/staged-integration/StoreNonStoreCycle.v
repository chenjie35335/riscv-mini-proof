Require Import StoreNonStoreCompareObserved StoreWriteValidCommit StoreDataCycleCommit
 FormalObservationCommit StagedFlatCircuitIteration FormalLocalHistory CoreSocModel.
From Coq Require Import NArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque generated_modules generated_top.
Theorem store_nonstore_write_valid_cycle_typed memory inputs k observed next instruction old_value :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 generated_run memory inputs(S k)=Some next ->
 VM.find 1(formal_external_inputs(generated_observation_input inputs k))=Some(Gval(Fuint 1)[::false]) ->
 VM.find 7748(top_environment observed)=Some(Gval(Fuint 32)instruction) ->
 (forall lane,(lane<3)%coq_nat ->~StoreTypeCorrespondence.store_type_is_store instruction lane) ->
 VM.find 8028(top_environment observed)=Some old_value ->type_of_val old_value=Gtyp(Fuint 1) ->
 VM.find 8028(top_environment next)=Some(Gval(Fuint 1)[::false]).
Proof.
 intros Observe Legal Next Reset Instruction NonStore Old Typed.
 pose proof(store_nonstore_compare_observed memory inputs k observed instruction Observe Legal Reset Instruction NonStore)as Compare.
 pose proof(store_observed_core_reset memory inputs k observed false Reset Observe)as Control.
 rewrite(observation_then_commit memory inputs k observed Observe)in Next.
 destruct(flat_iteration_projection _ observed true next Next)as[before[after[Before[Step After]]]].
 assert(Top:top_environment observed=before)by(unfold top_environment;rewrite Before;reflexivity).
 rewrite <-Top in Step. unfold top_environment. rewrite After.
 exact(store_write_valid_commit _ _ _ _ old_value false false Old Typed Control Compare Step).
Qed.
Require Import StoreWriteValidReachableType.
Theorem store_nonstore_write_valid_cycle memory inputs k observed next instruction :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 generated_run memory inputs(S k)=Some next ->
 VM.find 1(formal_external_inputs(generated_observation_input inputs k))=Some(Gval(Fuint 1)[::false]) ->
 VM.find 7748(top_environment observed)=Some(Gval(Fuint 32)instruction) ->
 (forall lane,(lane<3)%coq_nat ->~StoreTypeCorrespondence.store_type_is_store instruction lane) ->
 VM.find 8028(top_environment next)=Some(Gval(Fuint 1)[::false]).
Proof.
 intros Observe Legal Next Reset Instruction NonStore.
 destruct(store_write_valid_observed_type memory inputs k observed Observe)as[value[Value Typed]].
 exact(store_nonstore_write_valid_cycle_typed memory inputs k observed next instruction value
 Observe Legal Next Reset Instruction NonStore Value Typed).
Qed.
