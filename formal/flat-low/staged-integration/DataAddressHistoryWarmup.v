Require Import CoreSocModel ComparisonNodes DataAddressFromBoundaryHistory DataAddressBoundaryRegisters DataAddressGraphPropagation ConcreteRegisterInitialization FormalDataReadersInvariant FormalDataReaderAddresses DataAddressUIntTargets.
From Coq Require Import ZArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Theorem data_reader_history_after_warmup inputs path history limit :
 (forall node width, List.In (node,width) data_address_boundary_registers ->
 map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 data_readers_typed (history 0%nat) ->
 (forall time, (time <= limit)%coq_nat -> exists bit,
 VM.find (N.of_nat 1) (history time) = Some (Gval (Fuint 1) [::bit])) ->
 (forall time, (time < limit)%coq_nat ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories (history time) false (history time) flat_statements = Some (history (S time))) ->
 forall time, (79 <= time)%coq_nat -> (S (S time) <= limit)%coq_nat ->
 data_reader_addresses_concrete (history (S (S time))) /\ data_readers_enabled (history (S (S time))).
Proof.
 intros Initial Ports Reset Steps time Depth Within.
 assert (Typed : forall i, (i <= limit)%coq_nat -> data_readers_typed (history i)).
 { intros i. induction i as [|i IH]; intro Bound; [exact Ports|].
   exact (proj1 (data_readers_typed_step _ (history i) (history i) (history (S i)) false
     (IH ltac:(lia)) (Steps i ltac:(lia)))). }
 pose proof (data_address_source_from_boundary_history inputs path history limit Initial Reset Steps
   time ltac:(lia) Depth) as Source.
 assert (Sources : data_reader_sources_concrete (history (S time))).
 { eapply data_address_sources_from_9182; [exact Source|apply Steps; lia]. }
 split.
 - exact (data_reader_addresses_step _ (history (S time)) (history (S time)) (history (S (S time))) false
     (Typed (S time) ltac:(lia)) Sources (Steps (S time) ltac:(lia))).
 - exact (proj2 (data_readers_typed_step _ (history (S time)) (history (S time)) (history (S (S time))) false
     (Typed (S time) ltac:(lia)) (Steps (S time) ltac:(lia)))).
Qed.
Print Assumptions data_reader_history_after_warmup.
