Require Import CoreSocModel ComparisonNodes FormalLocalHistory StagedIterationCount ExternalReset FormalResetPreparation FormalTopResetHold DataWriterBoundaryRegisters DataWriterBoundaryPreparation DataWriterTargetsFromBoundary ConcreteRegisterInitialization FormalDataPortPreparation FormalDataPortsInvariant FormalDataReadersInvariant FormalDataStoragePreparation FormalDataStorageInitialization FormalDataWriterControls FormalCircuitDataCommit.
From Coq Require Import ZArith List Lia PeanoNat.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Opaque generated_modules generated_top flat_statements flat_memories.
Theorem observed_data_commit_ready memory inputs k committed old observed :
 generated_run memory inputs k = Some committed ->
 SVM.find nil committed = Some old ->
 generated_observe memory inputs k = Some observed ->
 generated_legal_trace memory inputs k ->
 (forall node width, List.In (node,width) data_writer_boundary_registers ->
 map_uint_concrete (N.of_nat node) width old) ->
 data_storage_concrete committed ->
 data_commit_ready (top_environment observed).
Proof.
 intros Run Old Observe Legal Boundary [values [Storage Concrete]].
 destruct (legal_observation_reset memory inputs k Legal) as [bit External].
 unfold generated_observe, generated_observe_cycle in Observe. rewrite Run in Observe.
 destruct (circuit_initial_map_with_memory generated_modules generated_top (Some committed)
 (formal_external_inputs (generated_observation_input inputs k))) as [prepared|] eqn:Prepare; [|discriminate Observe].
 pose proof flat_iteration_count_exact as Count. unfold flat_iteration_count in Count. rewrite Count in Observe.
 destruct (local_iteration_history (generated_observation_input inputs k) 9259 prepared observed Observe)
 as [history [First [Last Steps]]].
 assert (Initial : forall node width, List.In (node,width) data_writer_boundary_registers ->
 map_uint_concrete (N.of_nat node) width (history 0%nat)).
 { intros node width Member. rewrite First.
   exact (data_writer_boundary_prepared_concrete committed old _ prepared node width Member (Boundary node width Member) Old Prepare). }
 assert (InitialStorage : VM.find (N.of_nat 9179) (history 0%nat) = Some (Aval (Gtyp (Fuint 32)) values)).
 { rewrite First. rewrite (prepared_data_storage_copies committed old _ prepared Old Prepare).
   unfold top_environment in Storage. rewrite Old in Storage. exact Storage. }
 pose proof (circuit_data_port_prepared (Some committed) _ prepared Prepare) as PortValue.
 assert (InitialReaders : data_readers_typed (history 0%nat)).
 { rewrite First. exact (data_readers_initial_typed _ PortValue). }
 assert (InitialPorts : data_ports_typed (history 0%nat)).
 { rewrite First. exact (data_ports_initial_typed _ PortValue). }
 assert (Typed : forall i, (i <= 9259)%coq_nat -> data_ports_typed (history i)).
 { intros i. induction i as [|i IH]; intro Bound; [exact InitialPorts|].
   exact (data_ports_typed_step _ (history i) (history i) (history (S i)) false
     (IH ltac:(lia)) (Steps i ltac:(lia))). }
 destruct (top_reset_prepared (Some committed) _ prepared _ External Prepare) as [env [Env Reset]].
 assert (Resets : forall i, (i <= 9259)%coq_nat -> exists b,
 VM.find (N.of_nat 1) (history i) = Some (Gval (Fuint 1) [::b])).
 { assert (Fixed : forall i, (i <= 9259)%coq_nat ->
 VM.find (N.of_nat 1) (history i) = Some (Gval (Fuint 1) [::bit])).
   { intros i. induction i as [|i IH]; intro Bound.
     - rewrite First. unfold top_environment. rewrite Env. exact Reset.
     - eapply top_reset_iteration; [apply IH; lia|apply Steps; lia]. }
   intros i Bound. exists bit. exact (Fixed i Bound). }
 pose proof (data_writer_targets_from_boundary (generated_observation_input inputs k) nil history 9259 values
 Initial InitialReaders InitialStorage Concrete Resets Steps) as Targets.
 rewrite <- Last. apply data_commit_ready_from_controls.
 - eapply (data_writer_controls_step _ false (history 9258%nat) (history 9258%nat) (history 9259%nat)).
   + exact (Typed 9258%nat (Nat.le_succ_diag_r 9258)).
   + unfold data_writer_sources_concrete. repeat split.
     * exact (Targets 9258%nat 9230%nat (Nat.le_succ_diag_r 9258) ltac:(vm_compute; lia) (or_introl (Logic.eq_refl _))).
     * exact (Targets 9258%nat 9232%nat (Nat.le_succ_diag_r 9258) ltac:(vm_compute; lia) (or_intror (or_introl (Logic.eq_refl _)))).
     * exact (Targets 9258%nat 9233%nat (Nat.le_succ_diag_r 9258) ltac:(vm_compute; lia) (or_intror (or_intror (or_introl (Logic.eq_refl _))))).
   + exact (Steps 9258%nat (Nat.le_refl 9259)).
 - exact (Targets 9259%nat 9234%nat (Nat.le_refl 9259) ltac:(vm_compute; lia)
     (or_intror (or_intror (or_intror (or_introl (Logic.eq_refl _)))))).
Qed.
Print Assumptions observed_data_commit_ready.
