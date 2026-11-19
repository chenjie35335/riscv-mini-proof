Require Import ExceptionSelectionNonzero.
Require Import CoreSocModel ComparisonNodes ExceptionPayloadNodes ExceptionPayloadConnections ExceptionSelectionNodes ExceptionSelectionValues ExceptionInstructionHistory FormalRFResetPropagation.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Theorem reference_exception_payload_nonzero_after_eleven invalid s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 bits :
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
 VM.find 1671 s11 = Some (Gval (Fuint 32) bits).
Proof.
 intros Size Source Valid3 Raise6 Valid7 S1 S2 S3 S4 S5 S6 S7 S8 S9 S10 S11.
 destruct Raise6 as [cw [cb [Raise6 Nonzero]]].
 pose proof (sized_uint_adapt_identity 32 bits Size) as Adapt.
 pose proof (exception_instruction_1396_value invalid s0 s0 s1 _ _ Source Adapt S1) as V1.
 pose proof (exception_instruction_1516_value invalid s1 s1 s2 _ _ V1 Adapt S2) as V2.
 pose proof (exception_instruction_1706_value invalid s2 s2 s3 _ _ V2 Adapt S3) as V3.
 pose proof (exception_selection_1883_value invalid s3 s3 s4 bits
   (exception_instruction_input_selected s3 bits Size Valid3 V3) S4) as V4.
 pose proof (exception_instruction_1884_value invalid s4 s4 s5 bits V4 S5) as V5.
 pose proof (exception_selection_6811_value invalid s5 s5 s6 bits
   (exception_instruction_extract_identity s5 bits Size V5) S6) as V6.
 assert (Zero6 : VM.find 7088 s6 = Some (Gval (Fuint 32) (nseq 32 false))).
 { eapply exception_selection_7088_value; [reflexivity|exact S6]. }
 assert (Zero7 : VM.find 7088 s7 = Some (Gval (Fuint 32) (nseq 32 false))).
 { eapply exception_selection_7088_value; [reflexivity|exact S7]. }
 pose proof (exception_selection_7089_value invalid s6 s6 s7 bits
   (exception_instruction_selected_7089_nonzero s6 bits _ cw cb Size Raise6 Nonzero V6 Zero6) S7) as V7.
 pose proof (exception_selection_7120_value invalid s7 s7 s8 bits
   (exception_instruction_selected_7120 s7 bits _ Size Valid7 V7 Zero7) S8) as V8.
 exact (reference_exception_instruction_after_three invalid s8 s9 s10 s11 bits Size V8 S9 S10 S11).
Qed.
Print Assumptions reference_exception_payload_nonzero_after_eleven.
