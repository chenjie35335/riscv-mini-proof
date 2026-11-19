Require Import CoreSocModel ComparisonNodes FormalLocalHistory FormalLoadRegisterCommit FormalLoadMemoryCommit DataMemoryReaders FormalDataStorageInitialization FormalDataReadersInvariant FormalDataReaderAddresses ConcreteRegisterInitialization ConcreteGroundUIntAdapt StagedFlatCircuitIteration.
From Coq Require Import ZArith List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque generated_modules generated_top.
Theorem load_circuit_sized_commit inputs observed next :
 data_storage_concrete observed ->
 data_reader_addresses_concrete (top_environment observed) ->
 data_readers_enabled (top_environment observed) ->
 map_uint_concrete 9222 32 (top_environment observed) ->
 formal_circuit_value_iter (formal_invalid_policy inputs) generated_modules generated_top observed true = Some next ->
 map_uint_concrete 9222 32 (top_environment next).
Proof.
 intros [values [Storage Concrete]] Addresses Enabled [oldbits [OldSize Old]] Commit.
 destruct (Addresses 1 (or_introl (Logic.eq_refl _))) as [address Address].
 pose proof (Enabled 1 (or_introl (Logic.eq_refl _))) as Enable.
 destruct (flat_iteration_projection _ observed true next Commit) as [before [after [Before [Step After]]]].
 assert (Top : top_environment observed = before) by (unfold top_environment; rewrite Before; reflexivity).
 rewrite Top in Storage. rewrite Top in Address. rewrite Top in Enable. rewrite Top in Old.
 destruct (load_register_formal_commit_source _ before before after (Gval (Fuint 32) oldbits) Old (Logic.eq_refl _) Step)
 as [source [value [Source [Adapt Value]]]].
 rewrite load_reference_reads_memory in Source.
 destruct (data_memory_any_reader_concrete 1 before before values [::true] address 16 source
 (or_introl (Logic.eq_refl _)) Storage Enable (Logic.eq_refl _) Address Concrete Source) as [bits Equal].
 subst source.
 destruct (concrete_ground_uint_adapt (Fuint 32) bits 32 value Adapt) as [word [Size Equal]].
 subst value. exists word. split; [exact Size|]. unfold top_environment. rewrite After. exact Value.
Qed.
Print Assumptions load_circuit_sized_commit.
