Require Import CoreSocModel FormalLocalHistory FormalDataStorageInitialization FormalDataStorageHold FormalDataStoragePreparation.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque generated_modules generated_top.
Theorem observed_data_storage_copies memory inputs k committed states value :
 generated_run memory inputs k = Some committed ->
 VM.find 9179 (top_environment committed) = Some value ->
 generated_observe memory inputs k = Some states ->
 VM.find 9179 (top_environment states) = Some value.
Proof.
 intros Run Value Observe.
 unfold generated_observe, generated_observe_cycle in Observe. rewrite Run in Observe.
 unfold top_environment in Value.
 destruct (SVM.find nil committed) as [old|] eqn:Old; [|discriminate Value].
 destruct (circuit_initial_map_with_memory generated_modules generated_top (Some committed)
 (formal_external_inputs (generated_observation_input inputs k))) as [prepared|] eqn:Prepare; [|discriminate Observe].
 destruct (circuit_iter_count_with_memory generated_modules generated_top Gtyp_connect_count)
 as [n|]; [|discriminate Observe].
 apply (circuit_data_storage_iterations (generated_observation_input inputs k) n prepared states value); [|exact Observe].
 rewrite (prepared_data_storage_copies committed old _ prepared Old Prepare). exact Value.
Qed.
Theorem observed_data_storage_concrete memory inputs k committed states :
 generated_run memory inputs k = Some committed ->
 data_storage_concrete committed ->
 generated_observe memory inputs k = Some states ->
 data_storage_concrete states.
Proof.
 intros Run [values [Value Concrete]] Observe.
 exists values. split; [|exact Concrete].
 exact (observed_data_storage_copies memory inputs k committed states _ Run Value Observe).
Qed.
Print Assumptions observed_data_storage_copies.
Print Assumptions observed_data_storage_concrete.
