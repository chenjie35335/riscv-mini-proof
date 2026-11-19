Require Import CoreSocModel ComparisonNodes FormalPCGroundAddressHistory FormalFetchAddressPort FormalInstructionPortInvariant FormalLocalHistory.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Theorem next_pc_ground_fetch_address_after_five invalid s0 s1 s2 s3 s4 s5 ground pc :
 VM.find 7781 s0 = Some (Gval ground pc) ->
 instruction_port_typed s4 ->
 formal_flat_local_step invalid s0 s1 -> formal_flat_local_step invalid s1 s2 ->
 formal_flat_local_step invalid s2 s3 -> formal_flat_local_step invalid s3 s4 ->
 formal_flat_local_step invalid s4 s5 ->
 exists address, read_memory_port_field s5 9176 0 0 = Some (Gval (Fuint 16) address).
Proof.
 intros PC Typed S1 S2 S3 S4 S5.
 destruct (pc_address_ground_after_two invalid s0 s1 s2 ground pc PC S1 S2) as [word Word].
 exact (fetch_address_port_after_three invalid s2 s3 s4 s5 word Word Typed S3 S4 S5).
Qed.
Print Assumptions next_pc_ground_fetch_address_after_five.
