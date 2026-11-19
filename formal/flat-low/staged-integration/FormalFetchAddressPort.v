Require Import CoreSocModel ComparisonNodes FormalInstructionPortInvariant FormalInstructionPortConcreteAddress InstructionPortConnection FormalFetchAddressHistory FormalLocalHistory.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Lemma concrete_address_port_step invalid old phase current result address_bits :
 instruction_port_typed old ->
 VM.find 9219 old = Some (Gval (Fuint 4) address_bits) ->
 formal_value_iter invalid flat_memories old phase current flat_statements = Some result ->
 exists address, read_memory_port_field result 9176 0 0 = Some (Gval (Fuint 16) address).
Proof.
 intros [address [enable [clock [mask [data [Old [AddressType [EnableType [ClockType DataType]]]]]]]]] Bits Step.
 destruct (instruction_port_iteration_concrete_address invalid old phase current result address enable clock mask data address_bits
 Old AddressType EnableType ClockType DataType Bits Step) as [new_address [new_clock [[word Concrete] [NewClock Result]]]].
 subst new_address. exists word.
 exact (instruction_port_address result (Gval (Fuint 16) word) (Gval (Fuint 1) [::true]) new_clock mask data Result).
Qed.
Theorem fetch_address_port_after_three invalid s0 s1 s2 s3 pc :
 VM.find 30 s0 = Some (Gval (Fuint 32) pc) ->
 instruction_port_typed s2 ->
 formal_flat_local_step invalid s0 s1 -> formal_flat_local_step invalid s1 s2 -> formal_flat_local_step invalid s2 s3 ->
 exists address, read_memory_port_field s3 9176 0 0 = Some (Gval (Fuint 16) address).
Proof.
 intros PC Typed First Second Third.
 destruct (fetch_address_after_two invalid s0 s1 s2 pc PC First Second) as [bits Bits].
 exact (concrete_address_port_step invalid s2 false s2 s3 bits Typed Bits Third).
Qed.
Print Assumptions fetch_address_port_after_three.
