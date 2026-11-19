Require Import CoreSocModel ComparisonNodes ExceptionPCPayloadNodes ExceptionPCPayloadConnections ExceptionPCSelectionNodes ExceptionPCSelectionValues ExceptionPCHistory ExceptionPCAlignedHistory FormalRFResetPropagation.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Theorem reference_exception_pc_payload_after_seven invalid s0 s1 s2 s3 s4 s5 s6 s7 bits :
 size bits = 32%nat ->
 VM.find 7331 s0 = Some (Gval (Fuint 32) bits) ->
 (exists cw cb, VM.find 6780 s2 = Some (Gval (Fuint cw) cb) /\ is_zero cb = false) ->
 VM.find 1707 s3 = Some (Gval (Fuint 1) [::true]) ->
 formal_value_iter invalid flat_memories s0 false s0 flat_statements = Some s1 ->
 formal_value_iter invalid flat_memories s1 false s1 flat_statements = Some s2 ->
 formal_value_iter invalid flat_memories s2 false s2 flat_statements = Some s3 ->
 formal_value_iter invalid flat_memories s3 false s3 flat_statements = Some s4 ->
 formal_value_iter invalid flat_memories s4 false s4 flat_statements = Some s5 ->
 formal_value_iter invalid flat_memories s5 false s5 flat_statements = Some s6 ->
 formal_value_iter invalid flat_memories s6 false s6 flat_statements = Some s7 ->
 VM.find 1670 s7 = Some (Gval (Fuint 32) bits).
Proof.
 intros Size Source Raise Valid S1 S2 S3 S4 S5 S6 S7.
 destruct Raise as [cw [cb [Raise Nonzero]]].
 pose proof (sized_uint_adapt_identity 32 bits Size) as Adapt.
 pose proof (exception_pc_1749_value invalid s0 s0 s1 _ _ Source Adapt S1) as V1.
 pose proof (exception_pc_2812_value invalid s1 s1 s2 bits V1 S2) as V2.
 assert (Zero2 : VM.find 7086 s2 = Some (Gval (Fuint 32) (nseq 32 false))).
 { eapply exception_pc_selection_7086_value; [reflexivity|exact S2]. }
 assert (Zero3 : VM.find 7086 s3 = Some (Gval (Fuint 32) (nseq 32 false))).
 { eapply exception_pc_selection_7086_value; [reflexivity|exact S3]. }
 pose proof (exception_pc_selection_7087_value invalid s2 s2 s3 bits
 (exception_pc_selected_7087_nonzero s2 bits _ cw cb Size Raise Nonzero V2 Zero2) S3) as V3.
 pose proof (exception_pc_selection_7119_value invalid s3 s3 s4 bits
 (exception_pc_selected_7119 s3 bits _ Size Valid V3 Zero3) S4) as V4.
 exact (reference_exception_pc_after_three invalid s4 s5 s6 s7 bits Size V4 S5 S6 S7).
Qed.
Theorem implementation_exception_pc_payload_after_eight invalid s0 s1 s2 s3 s4 s5 s6 s7 s8 bits :
 size bits = 32%nat ->
 take 2 bits = [::false;false] ->
 VM.find 7751 s0 = Some (Gval (Fuint 32) bits) ->
 formal_value_iter invalid flat_memories s0 false s0 flat_statements = Some s1 ->
 formal_value_iter invalid flat_memories s1 false s1 flat_statements = Some s2 ->
 formal_value_iter invalid flat_memories s2 false s2 flat_statements = Some s3 ->
 formal_value_iter invalid flat_memories s3 false s3 flat_statements = Some s4 ->
 formal_value_iter invalid flat_memories s4 false s4 flat_statements = Some s5 ->
 formal_value_iter invalid flat_memories s5 false s5 flat_statements = Some s6 ->
 formal_value_iter invalid flat_memories s6 false s6 flat_statements = Some s7 ->
 formal_value_iter invalid flat_memories s7 false s7 flat_statements = Some s8 ->
 VM.find 1472 s8 = Some (Gval (Fuint 32) bits).
Proof.
 intros Size Low Source S1 S2 S3 S4 S5 S6 S7 S8.
 pose proof (exception_pc_121_value invalid s0 s0 s1 _ _ Source
 (sized_uint_adapt_identity 32 bits Size) S1) as V1.
 exact (implementation_exception_pc_aligned_after_seven invalid s1 s2 s3 s4 s5 s6 s7 s8 bits Size Low V1 S2 S3 S4 S5 S6 S7 S8).
Qed.
Print Assumptions reference_exception_pc_payload_after_seven.
Print Assumptions implementation_exception_pc_payload_after_eight.
