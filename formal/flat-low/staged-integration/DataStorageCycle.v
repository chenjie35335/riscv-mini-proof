Require Import CoreSocModel FormalLocalHistory DataWriterBoundaryRegisters DataWriterBoundaryPreparation ConcreteRegisterInitialization StagedIterationCount FormalResetPreparation FormalDataStorageInitialization FormalDataStoragePreparation FormalDataStorageHold FormalDataPortPreparation FormalDataPortsInvariant FormalDataReadersInvariant DataIterationCommitReady FormalCircuitDataCommit.
From Coq Require Import ZArith List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Opaque generated_modules generated_top.
Theorem data_storage_cycle inputs previous old next bit :
 SVM.find nil previous = Some old ->
 (forall node width, List.In (node,width) data_writer_boundary_registers ->
 map_uint_concrete (N.of_nat node) width old) ->
 data_storage_concrete previous ->
 VM.find (N.of_nat 1) (formal_external_inputs inputs) = Some (Gval (Fuint 1) [::bit]) ->
 circuit_formal_cycle generated_modules generated_top (Some previous) inputs = Some next ->
 data_storage_concrete next.
Proof.
 intros Old Boundary [values [Storage Concrete]] Reset Cycle. unfold circuit_formal_cycle in Cycle.
 destruct (circuit_initial_map_with_memory generated_modules generated_top (Some previous)
 (formal_external_inputs inputs)) as [prepared|] eqn:Prepare; [|discriminate Cycle].
 pose proof flat_iteration_count_exact as Count. unfold flat_iteration_count in Count. rewrite Count in Cycle.
 destruct (circuit_formal_iterations generated_modules generated_top inputs 9259 prepared) as [stable|] eqn:Iterations; [|discriminate Cycle].
 assert (PreparedStorage : VM.find (N.of_nat 9179) (top_environment prepared) = Some (Aval (Gtyp (Fuint 32)) values)).
 { rewrite (prepared_data_storage_copies previous old _ prepared Old Prepare).
   unfold top_environment in Storage. rewrite Old in Storage. exact Storage. }
 apply (circuit_data_commit_concrete (formal_invalid_policy inputs) stable next); [| |exact Cycle].
 - exists values. split; [|exact Concrete].
   exact (circuit_data_storage_iterations inputs 9259 prepared stable _ PreparedStorage Iterations).
 - eapply (data_iteration_commit_ready inputs prepared stable bit Iterations).
   + intros node width Member. exact (data_writer_boundary_prepared_concrete previous old _ prepared node width Member
       (Boundary node width Member) Old Prepare).
   + exists values. split; assumption.
   + exact (data_readers_initial_typed _ (circuit_data_port_prepared (Some previous) _ prepared Prepare)).
   + exact (data_ports_initial_typed _ (circuit_data_port_prepared (Some previous) _ prepared Prepare)).
   + destruct (top_reset_prepared (Some previous) _ prepared _ Reset Prepare) as [env [Env Value]].
     unfold top_environment. rewrite Env. exact Value.
Qed.
Print Assumptions data_storage_cycle.
