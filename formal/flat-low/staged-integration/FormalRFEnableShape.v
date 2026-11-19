Require Import FormalRFInputConnections FormalDeclaredConnectionObservation FormalRFWritebackNodes NormalizedBit.
Require Import FormalDeclaredConnection ScalarNodeFrames FormalStatementSegments FormalTypedNodeFrames FormalTypedNodeEquation CoreSocModel ComparisonNodes RegisterInvariants.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Firrtl_with_implicit_widths Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory FormalInitialization.
Local Open Scope N_scope.
Theorem rf_input_enable_normalized invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value, VM.find 784 result = Some value /\ normalized_bit value.
Proof.
 intro Step.
 destruct (declared_connection_observation 793 flat_statements rf_input_decl_784 rf_input_mid_784 rf_input_tail_784
 784 7941 1 invalid flat_memories old current result
 rf_input_position_784 rf_input_split_784 rf_input_straight_784 rf_input_mid_safe_784 rf_input_tail_safe_784
 rf_input_nonregister_784 (Logic.eq_refl _) Step) as [source [value [Source [Adapt Value]]]].
 exists value. split; [exact Value|exact (adapted_bit_normalized source value Adapt)].
Qed.
Lemma normalized_and_zero value :
 normalized_bit value -> eval_binop Band value (Gval (Fuint 1) [::false]) = Some (Gval (Fuint 1) [::false]).
Proof. intro Normal. destruct Normal as [b| | |]; try destruct b; reflexivity. Qed.
Theorem rf_zero_address_disables_write invalid old current result value :
 VM.find 784 old = Some value -> normalized_bit value ->
 VM.find 953 old = Some (Gval (Fuint 1) [::false]) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 954 result = Some (Gval (Fuint 1) [::false]).
Proof.
 intros Enable Normal Zero Step.
 apply (rf_source_node_954 invalid old current result (Gval (Fuint 1) [::false])); [|reflexivity|exact Step].
 unfold rf_source_expr_954. cbn [eval_hfexpr_with_memory eval_href_with_memory].
 rewrite Enable Zero. exact (normalized_and_zero value Normal).
Qed.
Print Assumptions rf_zero_address_disables_write.
