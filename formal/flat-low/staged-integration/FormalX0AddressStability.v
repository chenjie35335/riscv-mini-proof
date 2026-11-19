Require Import CoreSocModel ComparisonNodes FormalRFDestination StagedRegisterHold RegisterInvariants.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Lemma x0_instruction_register : has_register 7750 flat_statements = true.
Proof. vm_compute. reflexivity. Qed.
Theorem x0_address_stable_after_three invalid s0 s1 s2 s3 instruction :
 size instruction = 32%nat ->
 VM.find 7750 s0 = Some (Gval (Fuint 32) instruction) ->
 formal_value_iter invalid flat_memories s0 false s0 flat_statements = Some s1 ->
 formal_value_iter invalid flat_memories s1 false s1 flat_statements = Some s2 ->
 formal_value_iter invalid flat_memories s2 false s2 flat_statements = Some s3 ->
 VM.find 785 s2 = Some (Gval (Fuint 5) (drop 7 (take 12 instruction))) /\
 VM.find 785 s3 = Some (Gval (Fuint 5) (drop 7 (take 12 instruction))).
Proof.
 intros Size Instruction S1 S2 S3.
 assert (Held : VM.find 7750 s1 = Some (Gval (Fuint 32) instruction)).
 { rewrite (staged_combinational_holds_registers invalid flat_memories s0 s0 s1 flat_statements 7750 x0_instruction_register S1). exact Instruction. }
 split.
 - exact (rf_destination_port_after_two invalid s0 s1 s2 instruction Size Instruction S1 S2).
 - exact (rf_destination_port_after_two invalid s1 s2 s3 instruction Size Held S2 S3).
Qed.
Lemma five_bits_decompose (bits : seq bool) : size bits = 5%nat ->
 exists b0 b1 b2 b3 b4, bits = [::b0;b1;b2;b3;b4].
Proof.
 destruct bits as [|b0 bits]; [discriminate|].
 destruct bits as [|b1 bits]; [discriminate|].
 destruct bits as [|b2 bits]; [discriminate|].
 destruct bits as [|b3 bits]; [discriminate|].
 destruct bits as [|b4 bits]; [discriminate|].
 destruct bits; [intros _; do 5 eexists; reflexivity|discriminate].
Qed.
Print Assumptions x0_address_stable_after_three.
