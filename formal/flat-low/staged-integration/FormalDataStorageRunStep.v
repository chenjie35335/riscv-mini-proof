Require Import CoreSocModel FormalLocalHistory FormalDataStorageInitialization FormalCircuitDataCommit ObservedDataStorage FormalObservationCommit.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From firrtl Require Import Semantics_with_implicit_widths Semantics_with_memory.
Local Opaque generated_modules generated_top.
Theorem data_storage_run_step memory inputs k committed observed next :
 generated_run memory inputs k = Some committed ->
 generated_observe memory inputs k = Some observed ->
 generated_run memory inputs (S k) = Some next ->
 data_storage_concrete committed ->
 data_commit_ready (top_environment observed) ->
 data_storage_concrete next.
Proof.
 intros Run Observe Next Storage Ready.
 rewrite (observation_then_commit memory inputs k observed Observe) in Next.
 exact (circuit_data_commit_concrete _ observed next
   (observed_data_storage_concrete memory inputs k committed observed Run Storage Observe) Ready Next).
Qed.
Print Assumptions data_storage_run_step.
