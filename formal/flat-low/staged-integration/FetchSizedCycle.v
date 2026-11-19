Require Import FormalInstructionStorageInitialization FormalInstructionStoragePreparation FormalInstructionStorageHold FormalInstructionPortPreparation FormalInstructionPortInvariant InstructionIterationEnabled FetchIterationAddress FetchCircuitSizedCommit DataAddressBoundaryRegisters JointBoundaryRegisters JointBoundaryPreparation JointBoundaryIncludes DataWriterBoundaryIncludesAddress JointIterationBoundary DataIterationReaders LoadCircuitSizedCommit CoreSocModel FormalLocalHistory DataWriterBoundaryRegisters DataWriterBoundaryPreparation ConcreteRegisterInitialization StagedIterationCount FormalResetPreparation FormalDataStorageInitialization FormalDataStoragePreparation FormalDataStorageHold FormalDataPortPreparation FormalDataPortsInvariant FormalDataReadersInvariant DataIterationCommitReady FormalCircuitDataCommit.
From Coq Require Import ZArith List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Opaque generated_modules generated_top.
Theorem fetch_sized_cycle inputs previous old next bit :
 SVM.find nil previous = Some old ->
 (forall node width, List.In (node,width) joint_boundary_registers ->
 map_uint_concrete (N.of_nat node) width old) ->
 instruction_storage_concrete previous ->
 VM.find (N.of_nat 1) (formal_external_inputs inputs) = Some (Gval (Fuint 1) [::bit]) ->
 circuit_formal_cycle generated_modules generated_top (Some previous) inputs = Some next ->
 map_uint_concrete (N.of_nat 9220) 32 (top_environment next).
Proof.
 intros Old Boundary [values [Storage Concrete]] Reset Cycle. unfold circuit_formal_cycle in Cycle.
 destruct (circuit_initial_map_with_memory generated_modules generated_top (Some previous)
 (formal_external_inputs inputs)) as [prepared|] eqn:Prepare; [|discriminate Cycle].
 pose proof flat_iteration_count_exact as Count. unfold flat_iteration_count in Count. rewrite Count in Cycle.
 destruct (circuit_formal_iterations generated_modules generated_top inputs 9259 prepared) as [stable|] eqn:Iterations; [|discriminate Cycle].
 assert (PreparedStorage : VM.find (N.of_nat 9177) (top_environment prepared) = Some (Aval (Gtyp (Fuint 32)) values)).
 { rewrite (prepared_instruction_storage_copies previous old _ prepared Old Prepare).
   unfold top_environment in Storage. rewrite Old in Storage. exact Storage. }
 assert (PreparedBoundary : forall node width, List.In (node,width) joint_boundary_registers ->
 map_uint_concrete (N.of_nat node) width (top_environment prepared)).
 { intros node width Member. exact (joint_boundary_prepared_concrete previous old _ prepared node width Member (Boundary node width Member) Old Prepare). }
 assert (PreparedReset : VM.find (N.of_nat 1) (top_environment prepared) = Some (Gval (Fuint 1) [::bit])).
 { destruct (top_reset_prepared (Some previous) _ prepared _ Reset Prepare) as [env [Env Value]].
   unfold top_environment. rewrite Env. exact Value. }
 pose proof (circuit_instruction_port_prepared (Some previous) _ prepared Prepare) as PortTyped.
 pose proof (fetch_iteration_address inputs prepared stable bit Iterations PreparedBoundary PortTyped PreparedReset) as Addresses.
 pose proof (instruction_iterations_enabled inputs 9258 prepared stable PortTyped Iterations) as Enabled.
 apply (fetch_circuit_sized_commit inputs stable next); [|exact Addresses|exact Enabled| |exact Cycle].
 - exists values. split; [|exact Concrete].
   exact (circuit_instruction_storage_iterations inputs 9259 prepared stable _ PreparedStorage Iterations).
 - apply (joint_iteration_boundary inputs 9259 prepared stable Iterations PreparedBoundary 9220%nat 32%nat).
   apply (@List.nth_error_In _ joint_boundary_registers 68 (9220%nat,32%nat)). vm_compute. reflexivity.
Qed.
Print Assumptions fetch_sized_cycle.
