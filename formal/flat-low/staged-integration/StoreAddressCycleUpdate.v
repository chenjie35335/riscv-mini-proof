Require Import StoreAddressCommit StoreAddressResetCommit StoreAddressReachableType StoreDataCycleCommit CoreSocModel FormalObservationCommit StagedFlatCircuitIteration FormalLocalHistory.
From Coq Require Import NArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque generated_modules generated_top.
Theorem store_address_cycle_update memory inputs k observed next word reset :
 generated_observe memory inputs k=Some observed ->generated_run memory inputs(S k)=Some next ->
 VM.find 1(formal_external_inputs(generated_observation_input inputs k))=Some(Gval(Fuint 1)[::reset]) ->
 VM.find 8003(top_environment observed)=Some(Gval(Fuint 32)word) ->size word=32%nat ->
 VM.find 8004(top_environment next)=Some(Gval(Fuint 32)(if reset then zeros 32 else word)).
Proof.
 intros Observe Next Reset Mask Size.
 destruct(store_address_observed_type memory inputs k observed Observe)as[value[Old Typed]].
 pose proof(store_observed_core_reset memory inputs k observed reset Reset Observe)as Control.
 rewrite(observation_then_commit memory inputs k observed Observe)in Next.
 destruct(flat_iteration_projection _ observed true next Next)as[before[after[Before[Step After]]]].
 assert(Top:top_environment observed=before)by(unfold top_environment;rewrite Before;reflexivity).
 rewrite <-Top in Step. unfold top_environment. rewrite After.
 destruct reset.
 - exact(store_address_commit_reset _ _ _ _ value word Old Typed Control Mask Size Step).
 - exact(store_address_commit_normal _ _ _ _ value word Old Typed Control Mask Size Step).
Qed.
