Require Import DataAddressBoundaryRegisters JointBoundaryRegisters JointBoundaryPreparation JointBoundaryIncludes DataWriterBoundaryIncludesAddress JointIterationBoundary DataIterationReaders LoadCircuitSizedCommit CoreSocModel FormalLocalHistory DataWriterBoundaryRegisters DataWriterBoundaryPreparation ConcreteRegisterInitialization StagedIterationCount FormalResetPreparation FormalDataStorageInitialization FormalDataStoragePreparation FormalDataStorageHold FormalDataPortPreparation FormalDataPortsInvariant FormalDataReadersInvariant DataIterationCommitReady FormalCircuitDataCommit.
From Coq Require Import ZArith List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Opaque generated_modules generated_top.
Theorem load_sized_cycle inputs previous old next bit :
 SVM.find nil previous = Some old ->
 (forall node width, List.In (node,width) joint_boundary_registers ->
 map_uint_concrete (N.of_nat node) width old) ->
 data_storage_concrete previous ->
 VM.find (N.of_nat 1) (formal_external_inputs inputs) = Some (Gval (Fuint 1) [::bit]) ->
 circuit_formal_cycle generated_modules generated_top (Some previous) inputs = Some next ->
 map_uint_concrete (N.of_nat 9222) 32 (top_environment next).
Proof.
 intros Old Boundary [values [Storage Concrete]] Reset Cycle. unfold circuit_formal_cycle in Cycle.
 destruct (circuit_initial_map_with_memory generated_modules generated_top (Some previous)
 (formal_external_inputs inputs)) as [prepared|] eqn:Prepare; [|discriminate Cycle].
 pose proof flat_iteration_count_exact as Count. unfold flat_iteration_count in Count. rewrite Count in Cycle.
 destruct (circuit_formal_iterations generated_modules generated_top inputs 9259 prepared) as [stable|] eqn:Iterations; [|discriminate Cycle].
 assert (PreparedStorage : VM.find (N.of_nat 9179) (top_environment prepared) = Some (Aval (Gtyp (Fuint 32)) values)).
 { rewrite (prepared_data_storage_copies previous old _ prepared Old Prepare).
   unfold top_environment in Storage. rewrite Old in Storage. exact Storage. }
 assert (PreparedBoundary : forall node width, List.In (node,width) joint_boundary_registers ->
 map_uint_concrete (N.of_nat node) width (top_environment prepared)).
 { intros node width Member. exact (joint_boundary_prepared_concrete previous old _ prepared node width Member (Boundary node width Member) Old Prepare). }
 assert (PreparedReset : VM.find (N.of_nat 1) (top_environment prepared) = Some (Gval (Fuint 1) [::bit])).
 { destruct (top_reset_prepared (Some previous) _ prepared _ Reset Prepare) as [env [Env Value]].
   unfold top_environment. rewrite Env. exact Value. }
 assert (AddressBoundary : forall node width, List.In (node,width) data_address_boundary_registers ->
 map_uint_concrete (N.of_nat node) width (top_environment prepared)).
 { intros node width Member. apply PreparedBoundary. apply joint_includes_writer. apply data_writer_includes_address. exact Member. }
 destruct (data_iteration_readers inputs prepared stable bit Iterations AddressBoundary
   (data_readers_initial_typed _ (circuit_data_port_prepared (Some previous) _ prepared Prepare)) PreparedReset) as [Addresses Enabled].
 apply (load_circuit_sized_commit inputs stable next); [|exact Addresses|exact Enabled| |exact Cycle].
 - exists values. split; [|exact Concrete].
   exact (circuit_data_storage_iterations inputs 9259 prepared stable _ PreparedStorage Iterations).
 - apply (joint_iteration_boundary inputs 9259 prepared stable Iterations PreparedBoundary 9222%nat 32%nat).
   apply (@List.nth_error_In _ joint_boundary_registers 69 (9222%nat,32%nat)). vm_compute. reflexivity.
Qed.
Print Assumptions load_sized_cycle.
