Require Import ExceptionInstructionAgreement ExceptionPayloadNonzeroHistory.
Require Import CoreSocModel ComparisonNodes ComparisonTruth ExceptionPayloadHistory ExceptionInstructionHistory JointBoundaryRegisters.
From Coq Require Import ZArith List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Theorem exception_instruction_nonzero_agreement_after_eleven invalid s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 bits :
 size bits = 32%nat ->
 VM.find 7750 s0 = Some (Gval (Fuint 32) bits) ->
 VM.find 1707 s3 = Some (Gval (Fuint 1) [::true]) ->
 (exists cw cb, VM.find 6780 s6 = Some (Gval (Fuint cw) cb) /\ is_zero cb = false) ->
 VM.find 1707 s7 = Some (Gval (Fuint 1) [::true]) ->
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
 formal_value_iter invalid flat_memories s10 false s10 flat_statements = Some s11 ->
 comparison_inputs_agree s11 1473 1671.
Proof.
 intros Size Source Valid3 Raise6 Valid7 S1 S2 S3 S4 S5 S6 S7 S8 S9 S10 S11.
 assert (Source5 : VM.find 7750 s5 = Some (Gval (Fuint 32) bits)).
 {
  rewrite (exception_instruction_register_hold invalid s4 s4 s5 S5).
  rewrite (exception_instruction_register_hold invalid s3 s3 s4 S4).
  rewrite (exception_instruction_register_hold invalid s2 s2 s3 S3).
  rewrite (exception_instruction_register_hold invalid s1 s1 s2 S2).
  rewrite (exception_instruction_register_hold invalid s0 s0 s1 S1).
  exact Source.
 }
 pose proof (implementation_exception_instruction_after_six invalid s5 s6 s7 s8 s9 s10 s11 bits
 Size Source5 S6 S7 S8 S9 S10 S11) as Left.
 pose proof (reference_exception_payload_nonzero_after_eleven invalid s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 bits
 Size Source Valid3 Raise6 Valid7 S1 S2 S3 S4 S5 S6 S7 S8 S9 S10 S11) as Right.
 exists 32%nat, 32%nat, bits, bits.
 split; [exact Left|]. split; [exact Right|reflexivity].
Qed.
Print Assumptions exception_instruction_nonzero_agreement_after_eleven.
