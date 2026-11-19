Require Import CoreSocModel ComparisonNodes FlatRegFileX0 FormalX0NineSteps FormalX0AddressStability FormalRFDestination.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Theorem x0_output_from_instruction invalid s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 instruction enable :
 size instruction = 32%nat ->
 VM.find 7750 s0 = Some (Gval (Fuint 32) instruction) ->
 VM.find 784 s3 = Some (Gval (Fuint 1) [::enable]) ->
 formal_value_iter invalid flat_memories s0 false s0 flat_statements = Some s1 ->
 formal_value_iter invalid flat_memories s1 false s1 flat_statements = Some s2 ->
 formal_value_iter invalid flat_memories s2 false s2 flat_statements = Some s3 ->
 formal_value_iter invalid flat_memories s3 false s3 flat_statements = Some s4 ->
 formal_value_iter invalid flat_memories s4 false s4 flat_statements = Some s5 ->
 formal_value_iter invalid flat_memories s5 false s5 flat_statements = Some s6 ->
 formal_value_iter invalid flat_memories s6 false s6 flat_statements = Some s7 ->
 formal_value_iter invalid flat_memories s7 false s7 flat_statements = Some s8 ->
 formal_value_iter invalid flat_memories s8 false s8 flat_statements = Some s9 ->
 formal_value_iter invalid flat_memories s9 false s9 flat_statements = Some s10 ->
 VM.find 1399 s10 = Some rf_zero32.
Proof.
 intros Size Instruction Enable S1 S2 S3 S4 S5 S6 S7 S8 S9 S10.
 destruct (x0_address_stable_after_three invalid s0 s1 s2 s3 instruction Size Instruction S1 S2 S3) as [Addr2 Addr3].
 destruct (five_bits_decompose (drop 7 (take 12 instruction)) (rf_destination_width instruction Size)) as [b0 [b1 [b2 [b3 [b4 Bits]]]]].
 rewrite Bits in Addr2 Addr3.
 exact (x0_output_after_nine invalid s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 enable b0 b1 b2 b3 b4 Addr2 Addr3 Enable S2 S3 S4 S5 S6 S7 S8 S9 S10).
Qed.
Print Assumptions x0_output_from_instruction.
