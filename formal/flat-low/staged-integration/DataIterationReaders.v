Require Import CoreSocModel FormalLocalHistory FormalTopResetHold DataAddressBoundaryRegisters DataAddressHistoryWarmup ConcreteRegisterInitialization FormalDataReadersInvariant FormalDataReaderAddresses.
From Coq Require Import ZArith List Lia PeanoNat.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Opaque generated_modules generated_top.
Theorem data_iteration_readers inputs initial final bit :
 circuit_formal_iterations generated_modules generated_top inputs 9259 initial = Some final ->
 (forall node width, List.In (node,width) data_address_boundary_registers ->
 map_uint_concrete (N.of_nat node) width (top_environment initial)) ->
 data_readers_typed (top_environment initial) ->
 VM.find (N.of_nat 1) (top_environment initial) = Some (Gval (Fuint 1) [::bit]) ->
 data_reader_addresses_concrete (top_environment final) /\ data_readers_enabled (top_environment final).
Proof.
 intros Iterations Boundary Readers Reset.
 destruct (local_iteration_history inputs 9259 initial final Iterations) as [history [First [Last Steps]]].
 assert (Initial : forall node width, List.In (node,width) data_address_boundary_registers ->
 map_uint_concrete (N.of_nat node) width (history 0%nat)).
 { intros n w Member. rewrite First. exact (Boundary n w Member). }
 assert (Resets : forall i, (i <= 9259)%coq_nat ->
 VM.find (N.of_nat 1) (history i) = Some (Gval (Fuint 1) [::bit])).
 { intros i. induction i as [|i IH]; intro Bound.
   - rewrite First. exact Reset.
   - eapply top_reset_iteration; [apply IH; lia|apply Steps; lia]. }
 assert (InitialReaders : data_readers_typed (history 0%nat)).
 { rewrite First. exact Readers. }
 assert (ResetValues : forall time, (time <= 9259)%coq_nat -> exists b,
 VM.find (N.of_nat 1) (history time) = Some (Gval (Fuint 1) [::b])).
 { intros time Within. exists bit. exact (Resets time Within). }
 rewrite <- Last.
 exact (data_reader_history_after_warmup inputs nil history 9259 Initial InitialReaders ResetValues Steps
 9257 ltac:(vm_compute; lia) (Nat.le_refl 9259)).
Qed.
Print Assumptions data_iteration_readers.
