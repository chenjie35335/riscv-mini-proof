Require Import CoreSocModel ComparisonNodes FormalLocalHistory FormalFetchRegisterCommit FormalFetchMemoryCommit InstructionMemoryRead FormalInstructionStorageInitialization  ConcreteRegisterInitialization ConcreteGroundUIntAdapt StagedFlatCircuitIteration.
From Coq Require Import ZArith List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque generated_modules generated_top.
Theorem fetch_circuit_sized_commit inputs observed next :
 instruction_storage_concrete observed ->
 (exists address, read_memory_port_field (top_environment observed) 9176 0 0 = Some (Gval (Fuint 16) address)) ->
 read_memory_port_field (top_environment observed) 9176 0 1 = Some (Gval (Fuint 1) [::true]) ->
 map_uint_concrete 9220 32 (top_environment observed) ->
 formal_circuit_value_iter (formal_invalid_policy inputs) generated_modules generated_top observed true = Some next ->
 map_uint_concrete 9220 32 (top_environment next).
Proof.
 intros [values [Storage Concrete]] [address Address] Enable [oldbits [OldSize Old]] Commit.
 destruct (flat_iteration_projection _ observed true next Commit) as [before [after [Before [Step After]]]].
 assert (Top : top_environment observed = before) by (unfold top_environment; rewrite Before; reflexivity).
 rewrite Top in Storage. rewrite Top in Address. rewrite Top in Enable. rewrite Top in Old.
 destruct (fetch_register_formal_commit_source _ before before after (Gval (Fuint 32) oldbits) Old (Logic.eq_refl _) Step)
 as [source [value [Source [Adapt Value]]]].
 rewrite fetch_reference_reads_memory in Source.
 destruct (instruction_memory_read_concrete before before values [::true] address 16 source
 Storage Enable (Logic.eq_refl _) Address Concrete Source) as [bits Equal].
 subst source.
 destruct (concrete_ground_uint_adapt (Fuint 32) bits 32 value Adapt) as [word [Size Equal]].
 subst value. exists word. split; [exact Size|]. unfold top_environment. rewrite After. exact Value.
Qed.
Print Assumptions fetch_circuit_sized_commit.
