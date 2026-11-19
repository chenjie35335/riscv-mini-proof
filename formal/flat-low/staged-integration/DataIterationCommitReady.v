Require Import CoreSocModel ComparisonNodes FormalLocalHistory StagedIterationCount ExternalReset FormalResetPreparation FormalTopResetHold DataWriterBoundaryRegisters DataWriterBoundaryPreparation DataWriterTargetsFromBoundary ConcreteRegisterInitialization FormalDataPortPreparation FormalDataPortsInvariant FormalDataReadersInvariant FormalDataStoragePreparation FormalDataStorageInitialization FormalDataWriterControls FormalCircuitDataCommit.
From Coq Require Import ZArith List Lia PeanoNat.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Opaque generated_modules generated_top flat_statements flat_memories.
Theorem data_iteration_commit_ready inputs prepared observed bit :
 circuit_formal_iterations generated_modules generated_top inputs 9259 prepared = Some observed ->
 (forall node width, List.In (node,width) data_writer_boundary_registers ->
 map_uint_concrete (N.of_nat node) width (top_environment prepared)) ->
 data_storage_concrete prepared ->
 data_readers_typed (top_environment prepared) ->
 data_ports_typed (top_environment prepared) ->
 VM.find (N.of_nat 1) (top_environment prepared) = Some (Gval (Fuint 1) [::bit]) ->
 data_commit_ready (top_environment observed).
Proof.
 intros Iterations Boundary [values [Storage Concrete]] Readers Ports Reset.
 destruct (local_iteration_history inputs 9259 prepared observed Iterations) as [history [First [Last Steps]]].
 assert (Initial : forall node width, List.In (node,width) data_writer_boundary_registers ->
 map_uint_concrete (N.of_nat node) width (history 0%nat)).
 { intros node width Member. rewrite First. exact (Boundary node width Member). }
 assert (InitialStorage : VM.find (N.of_nat 9179) (history 0%nat) = Some (Aval (Gtyp (Fuint 32)) values)).
 { rewrite First. exact Storage. }
 assert (InitialReaders : data_readers_typed (history 0%nat)).
 { rewrite First. exact Readers. }
 assert (InitialPorts : data_ports_typed (history 0%nat)).
 { rewrite First. exact Ports. }
 assert (Typed : forall i, (i <= 9259)%coq_nat -> data_ports_typed (history i)).
 { intros i. induction i as [|i IH]; intro Bound; [exact InitialPorts|].
   exact (data_ports_typed_step _ (history i) (history i) (history (S i)) false
     (IH ltac:(lia)) (Steps i ltac:(lia))). }
 assert (Resets : forall i, (i <= 9259)%coq_nat -> exists b,
 VM.find (N.of_nat 1) (history i) = Some (Gval (Fuint 1) [::b])).
 { assert (Fixed : forall i, (i <= 9259)%coq_nat ->
 VM.find (N.of_nat 1) (history i) = Some (Gval (Fuint 1) [::bit])).
   { intros i. induction i as [|i IH]; intro Bound.
     - rewrite First. exact Reset.
     - eapply top_reset_iteration; [apply IH; lia|apply Steps; lia]. }
   intros i Bound. exists bit. exact (Fixed i Bound). }
 pose proof (data_writer_targets_from_boundary inputs nil history 9259 values
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
Print Assumptions data_iteration_commit_ready.
