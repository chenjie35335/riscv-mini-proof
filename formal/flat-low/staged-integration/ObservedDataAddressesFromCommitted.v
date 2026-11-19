Require Import CoreSocModel FormalLocalHistory ObservedDataAddressesFromBoundary DataAddressBoundaryPreparation DataAddressBoundaryRegisters ConcreteRegisterInitialization FormalDataReaderAddresses.
From Coq Require Import ZArith List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Theorem observed_data_addresses_from_committed memory inputs k committed old observed :
 generated_run memory inputs k = Some committed ->
 SVM.find nil committed = Some old ->
 generated_observe memory inputs k = Some observed ->
 generated_legal_trace memory inputs k ->
 (forall node width, List.In (node,width) data_address_boundary_registers ->
   map_uint_concrete (N.of_nat node) width old) ->
 data_reader_addresses_concrete (top_environment observed).
Proof.
 intros Run Old Observe Legal Boundary.
 apply (observed_data_addresses_from_boundary memory inputs k observed Observe Legal).
 intros node width Member.
 exact (data_address_boundary_observed_concrete memory inputs k committed old observed node width
   Member (Boundary node width Member) Run Old Observe).
Qed.
Print Assumptions observed_data_addresses_from_committed.
