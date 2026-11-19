Require Import CoreSocModel FormalLocalHistory ObservedDataAddressesFromCommitted DataAddressBoundaryRegisters ConcreteRegisterInitialization FormalDataReaderAddresses FormalDataStorageInitialization ObservedDataStorage FormalObservedLoadType ObservedDataRead ComparisonNodes.
From Coq Require Import ZArith List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque generated_modules generated_top.
Theorem observed_data_read_from_committed_boundary memory inputs k committed old observed port value :
 generated_run memory inputs k = Some committed ->
 SVM.find nil committed = Some old ->
 generated_observe memory inputs k = Some observed ->
 generated_legal_trace memory inputs k ->
 (forall node width, List.In (node,width) data_address_boundary_registers ->
   map_uint_concrete (N.of_nat node) width old) ->
 data_storage_concrete committed ->
 List.In port [::1;2;3;4;5] ->
 eval_memory_reader_data flat_memories 9178 port (top_environment observed) (top_environment observed) = Some value ->
 exists bits, value = Gval (Fuint 32) bits.
Proof.
 intros Run Old Observe Legal Boundary Storage Member Read.
 pose proof (observed_data_addresses_from_committed memory inputs k committed old observed
   Run Old Observe Legal Boundary) as Addresses.
 destruct (Addresses port Member) as [address Address].
 exact (observed_data_read_concrete memory inputs k observed port address 16 value Observe Member
   (observed_data_storage_concrete memory inputs k committed observed Run Storage Observe) Address Read).
Qed.
Theorem load_commit_from_data_boundary memory inputs k committed old observed next :
 generated_run memory inputs k = Some committed ->
 SVM.find nil committed = Some old ->
 generated_observe memory inputs k = Some observed ->
 generated_run memory inputs (S k) = Some next ->
 generated_legal_trace memory inputs k ->
 (forall node width, List.In (node,width) data_address_boundary_registers ->
   map_uint_concrete (N.of_nat node) width old) ->
 data_storage_concrete committed ->
 exists word, VM.find 9222 (top_environment next) = Some (Gval (Fuint 32) word).
Proof.
 intros Run Old Observe Next Legal Boundary Storage.
 pose proof (observed_data_addresses_from_committed memory inputs k committed old observed
   Run Old Observe Legal Boundary) as Addresses.
 destruct (Addresses 1 (or_introl (Logic.eq_refl _))) as [address Address].
 exact (observed_load_commit_concrete_address memory inputs k observed next address 16 Observe Next
   (observed_data_storage_concrete memory inputs k committed observed Run Storage Observe) Address).
Qed.
Print Assumptions observed_data_read_from_committed_boundary.
Print Assumptions load_commit_from_data_boundary.
