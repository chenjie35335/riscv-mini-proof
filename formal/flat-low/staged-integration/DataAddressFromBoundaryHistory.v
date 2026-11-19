Require Import CoreSocModel ComparisonNodes DataAddressSourcePropagation DataAddressGraphPropagation DataAddressBoundaryHistory DataAddressBoundaryRegisters ConcreteRegisterInitialization.
From Coq Require Import ZArith List Arith Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Theorem data_address_source_from_boundary_history inputs path history limit :
 (forall node width, List.In (node,width) data_address_boundary_registers ->
   map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall time, (time <= limit)%coq_nat -> exists bit,
   VM.find (N.of_nat 1) (history time) = Some (Gval (Fuint 1) [::bit])) ->
 (forall time, (time < limit)%coq_nat ->
   formal_value_iter (formal_invalid_policy inputs path) flat_memories (history time) false (history time) flat_statements = Some (history (S time))) ->
 forall time, (time <= limit)%coq_nat -> (79 <= time)%coq_nat ->
 data_address_ground_at (history time) 9182.
Proof.
 intros Initial Reset Steps.
 apply (data_address_source_history inputs path history limit).
 - intros time node dependencies Within Member.
   destruct (data_address_rank_zero_history_concrete _ history limit Initial Reset Steps
     time node dependencies Within Member) as [width [bits Lookup]].
   exists (Fuint width), bits. exact Lookup.
 - intros time Within.
   assert (Member : List.In (851%nat,32%nat) data_address_boundary_registers).
   { left. reflexivity. }
   destruct (data_address_register_history_concrete _ history limit 851 32 Member
     (Initial 851 32 Member) Steps time ltac:(lia)) as [bits [_ Lookup]].
   exists 32%nat, bits. exact Lookup.
 - exact Steps.
Qed.
Print Assumptions data_address_source_from_boundary_history.
