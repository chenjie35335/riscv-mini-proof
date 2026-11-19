Require Import CoreSocModel ComparisonNodes ExceptionEventNodes ExceptionEventConnections LegalAssumptionNodes LegalAssumptionConnections FormalExceptionInput FormalDeclaredConnectionObservation NormalizedBit.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Theorem exception_source128_normalized invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value, VM.find 128 result = Some value /\ normalized_bit value.
Proof.
 intro Step.
 destruct (declared_connection_observation 105 flat_statements exception_input_decl_128 exception_input_mid_128 exception_input_tail_128
 128 442 1 invalid flat_memories old current result
 exception_input_position_128 exception_input_split_128 exception_input_straight_128 exception_input_mid_safe_128 exception_input_tail_safe_128 exception_input_nonregister_128 (Logic.eq_refl _) Step)
 as [source [value [Source [Adapt Value]]]].
 exists value. split; [exact Value|exact (adapted_bit_normalized source value Adapt)].
Qed.
Theorem exception_trap_after_five invalid s0 s1 s2 s3 s4 s5 bit :
 VM.find 128 s0 = Some (Gval (Fuint 1) [::bit]) ->
 formal_value_iter invalid flat_memories s0 false s0 flat_statements = Some s1 ->
 formal_value_iter invalid flat_memories s1 false s1 flat_statements = Some s2 ->
 formal_value_iter invalid flat_memories s2 false s2 flat_statements = Some s3 ->
 formal_value_iter invalid flat_memories s3 false s3 flat_statements = Some s4 ->
 formal_value_iter invalid flat_memories s4 false s4 flat_statements = Some s5 ->
 VM.find 45 s5 = Some (Gval (Fuint 1) [::bit]).
Proof.
 intros Source S1 S2 S3 S4 S5.
 assert (Adapt : adapt_hvalue_as_type (Gval (Fuint 1) [::bit]) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) [::bit])) by (destruct bit; reflexivity).
 pose proof (exception_event_139_value invalid s0 s0 s1 _ _ Source Adapt S1) as V1.
 pose proof (legal_connection_100_value invalid s1 s1 s2 _ _ V1 Adapt S2) as V2.
 assert (V3 : VM.find 9153 s3 = Some (Gval (Fuint 1) [::bit])).
 { rewrite (legal_equation_9153 invalid s2 s2 s3 S3).
   cbn [legal_expr_9153 eval_hfexpr_with_memory eval_href_with_memory]. exact V2. }
 assert (V4 : VM.find 9157 s4 = Some (Gval (Fuint 1) [::bit])).
 { eapply legal_value_9157; [|reflexivity|exact S4].
   cbn [legal_expr_9157 eval_hfexpr_with_memory eval_href_with_memory]. exact V3. }
 exact (legal_connection_45_value invalid s4 s4 s5 _ _ V4 Adapt S5).
Qed.
Theorem exception_event_after_five invalid s0 s1 s2 s3 s4 s5 bit :
 VM.find 128 s0 = Some (Gval (Fuint 1) [::bit]) ->
 formal_value_iter invalid flat_memories s0 false s0 flat_statements = Some s1 ->
 formal_value_iter invalid flat_memories s1 false s1 flat_statements = Some s2 ->
 formal_value_iter invalid flat_memories s2 false s2 flat_statements = Some s3 ->
 formal_value_iter invalid flat_memories s3 false s3 flat_statements = Some s4 ->
 formal_value_iter invalid flat_memories s4 false s4 flat_statements = Some s5 ->
 VM.find 1469 s5 = Some (Gval (Fuint 1) [::bit]).
Proof.
 intros Source S1 S2 S3 S4 S5.
 assert (Adapt : adapt_hvalue_as_type (Gval (Fuint 1) [::bit]) (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) [::bit])) by (destruct bit; reflexivity).
 pose proof (exception_event_773_value invalid s0 s0 s1 [::bit] Source S1) as V1.
 pose proof (exception_event_134_value invalid s1 s1 s2 _ _ V1 Adapt S2) as V2.
 pose proof (exception_event_8153_value invalid s2 s2 s3 [::bit] V2 S3) as V3.
 pose proof (exception_event_8242_value invalid s3 s3 s4 [::bit] V3 S4) as V4.
 exact (exception_event_1469_value invalid s4 s4 s5 _ _ V4 Adapt S5).
Qed.
Print Assumptions exception_event_after_five.
Print Assumptions exception_trap_after_five.
