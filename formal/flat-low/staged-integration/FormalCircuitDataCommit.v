Require Import CoreSocModel FormalLocalHistory FormalDataStorageInitialization FormalDataStorageCommit StagedFlatCircuitIteration.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Definition data_commit_ready env := exists sw sb ew eb mw mb aw ab,
 VM.find 9234 env = Some (Gval (Fuint sw) sb) /\
 read_memory_port_field env 9178 0 1 = Some (Gval (Fuint ew) eb) /\
 read_memory_port_field env 9178 0 3 = Some (Gval (Fuint mw) mb) /\
 read_memory_port_field env 9178 0 0 = Some (Gval (Fuint aw) ab).
Local Opaque generated_modules generated_top.
Theorem circuit_data_commit_concrete invalid before after :
 data_storage_concrete before ->
 data_commit_ready (top_environment before) ->
 formal_circuit_value_iter invalid generated_modules generated_top before true = Some after ->
 data_storage_concrete after.
Proof.
 intros [values [Storage Concrete]] [sw [sb [ew [eb [mw [mb [aw [ab [Source [Enable [Mask Address]]]]]]]]]]] Step.
 destruct (flat_iteration_projection invalid before true after Step)
 as [old [next [Old [LocalStep Next]]]].
 unfold top_environment in Storage, Source, Enable, Mask, Address |- *.
 rewrite Old in Storage, Source, Enable, Mask, Address.
 unfold data_storage_concrete, top_environment. rewrite Next.
 exact (data_storage_commit_from_concrete_ports (invalid nil) old old next values
 sw sb ew eb mw mb aw ab Storage Concrete Source Enable Mask Address LocalStep).
Qed.
Print Assumptions circuit_data_commit_concrete.
