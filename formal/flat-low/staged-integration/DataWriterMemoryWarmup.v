Require Import CoreSocModel ComparisonNodes DataWriterGraphPropagation DataAddressHistoryWarmup DataAddressBoundaryRegisters ConcreteRegisterInitialization FormalDataReadersInvariant FormalDataReaderAddresses FormalDataStorageHold ConcreteMemoryRead.
From Coq Require Import ZArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Theorem writer_memory_history_after_warmup inputs path history limit values :
 (forall node width, List.In (node,width) data_address_boundary_registers ->
 map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 data_readers_typed (history 0%nat) ->
 VM.find (N.of_nat 9179) (history 0%nat) = Some (Aval (Gtyp (Fuint 32)) values) ->
 concrete_uint_array 32 values ->
 (forall time, (time <= limit)%coq_nat -> exists bit,
 VM.find (N.of_nat 1) (history time) = Some (Gval (Fuint 1) [::bit])) ->
 (forall time, (time < limit)%coq_nat ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories (history time) false (history time) flat_statements = Some (history (S time))) ->
 forall time, (81 <= time)%coq_nat -> (time <= limit)%coq_nat -> writer_memory_ready (history time).
Proof.
 intros Initial Ports Storage Concrete Reset Steps.
 assert (StorageHistory : forall i, (i <= limit)%coq_nat ->
   VM.find (N.of_nat 9179) (history i) = Some (Aval (Gtyp (Fuint 32)) values)).
 { intros i. induction i as [|i IH]; intro Bound; [exact Storage|].
   exact (data_storage_iteration _ (history i) (history i) (history (S i)) _
     (IH ltac:(lia)) (Steps i ltac:(lia))). }
 intros time Depth Within.
 destruct time as [|[|time]]; try lia.
 destruct (data_reader_history_after_warmup inputs path history limit Initial Ports Reset Steps
 time ltac:(lia) Within) as [Addresses Enabled].
 exists values. split; [apply StorageHistory; exact Within|]. split; [exact Concrete|].
 intros port Member.
 assert (Reader : List.In port [::N.of_nat 1;N.of_nat 2;N.of_nat 3;N.of_nat 4;N.of_nat 5]) by (right; exact Member).
 split; [exact (Enabled port Reader)|].
 destruct (Addresses port Reader) as [address Address]. exists 16%nat, address. exact Address.
Qed.
Print Assumptions writer_memory_history_after_warmup.
