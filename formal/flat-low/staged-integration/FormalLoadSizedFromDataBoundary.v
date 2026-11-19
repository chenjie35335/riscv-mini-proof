Require Import CoreSocModel FormalLocalHistory ObservedDataAddressesFromCommitted DataAddressBoundaryRegisters ConcreteRegisterInitialization FormalDataReaderAddresses FormalDataStorageInitialization ObservedDataStorage FormalObservedLoadType FormalLoadSizedCommit.
From Coq Require Import ZArith List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Theorem load_sized_from_data_boundary memory inputs k committed old observed next :
 generated_run memory inputs k = Some committed ->
 SVM.find nil committed = Some old ->
 generated_observe memory inputs k = Some observed ->
 generated_run memory inputs (S k) = Some next ->
 generated_legal_trace memory inputs k ->
 (forall node width, List.In (node,width) data_address_boundary_registers ->
 map_uint_concrete (N.of_nat node) width old) ->
 data_storage_concrete committed ->
 map_uint_concrete 9222 32 (top_environment next).
Proof.
 intros Run Old Observe Next Legal Boundary Storage.
 pose proof (observed_data_addresses_from_committed memory inputs k committed old observed Run Old Observe Legal Boundary) as Addresses.
 destruct (Addresses 1 (or_introl (Logic.eq_refl _))) as [address Address].
 destruct (observed_load_type memory inputs k observed Observe) as [value [Value Typed]].
 exact (observed_load_commit_sized memory inputs k observed next value address 16 Observe Next
 (observed_data_storage_concrete memory inputs k committed observed Run Storage Observe) Value Typed Address).
Qed.
Print Assumptions load_sized_from_data_boundary.
