Require Import CoreSocModel ComparisonNodes ReferenceEventNodes ReferenceEventConnections FormalReferenceValid FormalDeclaredConnectionObservation FormalSuccessfulNode BooleanizeTruth NormalizedFalseMux NormalizedBit.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Theorem reference_valid_1707_normalized invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value, VM.find 1707 result = Some value /\ normalized_bit value.
Proof.
 intro Step.
 destruct (declared_connection_observation 1786 flat_statements reference_valid_decl_1707 reference_valid_mid_1707 reference_valid_tail_1707
 1707 1517 1 invalid flat_memories old current result
 reference_valid_position_1707 reference_valid_split_1707 reference_valid_straight_1707 reference_valid_mid_safe_1707 reference_valid_tail_safe_1707 reference_valid_nonregister_1707 (Logic.eq_refl _) Step)
 as [source [value [Source [Adapt Value]]]].
 exists value. split; [exact Value|exact (adapted_bit_normalized source value Adapt)].
Qed.
Theorem reference_event_7083_normalized invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value, VM.find 7083 result = Some value /\ normalized_bit value.
Proof.
 intro Step.
 destruct (formal_successful_node _ _ _ _ _ invalid flat_memories old false current result reference_event_position_7083 Step) as [value Eval].
 change (eval_hfexpr_with_memory flat_memories reference_event_expr_7083 old old = Some value) in Eval.
 exists value. split.
 - rewrite (reference_event_equation_7083 invalid old current result Step). exact Eval.
 - exact (booleanize_result_normalized flat_memories old 6780 value Eval).
Qed.
Theorem reference_event_7116_false invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 7116 result = Some (Gval (Fuint 1) [::false]).
Proof. intro Step. rewrite (reference_event_equation_7116 invalid old current result Step). reflexivity. Qed.
Theorem reference_event_7117_normalized_after_two invalid s0 s1 s2 :
 formal_value_iter invalid flat_memories s0 false s0 flat_statements = Some s1 ->
 formal_value_iter invalid flat_memories s1 false s1 flat_statements = Some s2 ->
 exists value, VM.find 7117 s2 = Some value /\ normalized_bit value.
Proof.
 intros S1 S2.
 destruct (reference_valid_1707_normalized invalid s0 s0 s1 S1) as [control [Control NC]].
 destruct (reference_event_7083_normalized invalid s0 s0 s1 S1) as [selected [Selected NS]].
 pose proof (reference_event_7116_false invalid s0 s0 s1 S1) as No.
 destruct (normalized_mux_with_false_result flat_memories s1 1707 7083 7116 control selected Control NC Selected NS No)
 as [value [Eval Normal]].
 exists value. split; [|exact Normal].
 rewrite (reference_event_equation_7117 invalid s1 s1 s2 S2). exact Eval.
Qed.
Theorem reference_event_7202_normalized_after_three invalid s0 s1 s2 s3 :
 formal_value_iter invalid flat_memories s0 false s0 flat_statements = Some s1 ->
 formal_value_iter invalid flat_memories s1 false s1 flat_statements = Some s2 ->
 formal_value_iter invalid flat_memories s2 false s2 flat_statements = Some s3 ->
 exists value, VM.find 7202 s3 = Some value /\ normalized_bit value.
Proof.
 intros S1 S2 S3.
 destruct (reference_event_7117_normalized_after_two invalid s0 s1 s2 S1 S2) as [value [Value Normal]].
 exists value. split; [|exact Normal].
 eapply reference_event_value_7202; [|destruct Normal; reflexivity|exact S3].
 cbn [reference_event_expr_7202 eval_hfexpr_with_memory eval_href_with_memory]. exact Value.
Qed.
Print Assumptions reference_event_7202_normalized_after_three.
