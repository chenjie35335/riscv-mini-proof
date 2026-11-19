Require Import CoreSocModel ComparisonNodes ReferenceEventNodes ReferenceEventConnections ReferenceEventNormalization BooleanControlFacts BooleanMuxInversion BooleanizeTruth NormalizedBit.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Theorem reference_event_true_after_five invalid s0 s1 s2 s3 s4 s5 :
 formal_value_iter invalid flat_memories s0 false s0 flat_statements = Some s1 ->
 formal_value_iter invalid flat_memories s1 false s1 flat_statements = Some s2 ->
 formal_value_iter invalid flat_memories s2 false s2 flat_statements = Some s3 ->
 formal_value_iter invalid flat_memories s3 false s3 flat_statements = Some s4 ->
 formal_value_iter invalid flat_memories s4 false s4 flat_statements = Some s5 ->
 VM.find 1667 s5 = Some (Gval (Fuint 1) [::true]) ->
 VM.find 1707 s1 = Some (Gval (Fuint 1) [::true]) /\
 exists width bits, VM.find 6780 s0 = Some (Gval (Fuint width) bits) /\ is_zero bits = false.
Proof.
 intros S1 S2 S3 S4 S5 TrueOutput.
 destruct (reference_event_7117_normalized_after_two invalid s0 s1 s2 S1 S2) as [value [Value Normal]].
 assert (Alias : VM.find 7202 s3 = Some value).
 { eapply reference_event_value_7202; [|destruct Normal; reflexivity|exact S3].
   cbn [reference_event_expr_7202 eval_hfexpr_with_memory eval_href_with_memory]. exact Value. }
 destruct (reference_event_connection_1857_observation invalid s3 s3 s4 S4)
 as [source4 [value4 [Source4 [Adapt4 Value4]]]].
 rewrite Alias in Source4. inversion Source4; subst source4.
 destruct (reference_event_connection_1667_observation invalid s4 s4 s5 S5)
 as [source5 [value5 [Source5 [Adapt5 Value5]]]].
 rewrite Value4 in Source5. inversion Source5; subst source5.
 rewrite TrueOutput in Value5. inversion Value5; subst value5.
 pose proof (normalized_adaptation_recovers_bit value4 true (adapted_bit_normalized value value4 Adapt4) Adapt5) as True4.
 rewrite True4 in Adapt4.
 pose proof (normalized_adaptation_recovers_bit value true Normal Adapt4) as True2.
 rewrite True2 in Value.
 rewrite (reference_event_equation_7117 invalid s1 s1 s2 S2) in Value.
 destruct (reference_valid_1707_normalized invalid s0 s0 s1 S1) as [control [Control NC]].
 destruct (reference_event_7083_normalized invalid s0 s0 s1 S1) as [selected [Selected NS]].
 pose proof (reference_event_7116_false invalid s0 s0 s1 S1) as No.
 destruct (normalized_mux_with_false_true flat_memories s1 1707 7083 7116 control selected
 Control NC Selected NS No Value) as [ControlTrue SelectedTrue].
 split.
 - rewrite <- ControlTrue. exact Control.
 - rewrite SelectedTrue in Selected.
   rewrite (reference_event_equation_7083 invalid s0 s0 s1 S1) in Selected.
   exact (booleanize_true_source flat_memories s0 6780 Selected).
Qed.
Print Assumptions reference_event_true_after_five.
