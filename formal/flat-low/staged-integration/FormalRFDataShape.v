Require Import FormalRFDataConnection FormalRFWritebackNodes FormalDeclaredUnaryObservation ScalarSinkTypes.
Require Import FormalDeclaredUnaryConnection.
Require Import FormalDeclaredConnection ScalarNodeFrames FormalStatementSegments FormalTypedNodeFrames FormalTypedNodeEquation CoreSocModel ComparisonNodes RegisterInvariants.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Firrtl_with_implicit_widths Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory FormalInitialization.
Local Open Scope N_scope.
Theorem rf_input_data_typed invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value, VM.find 786 result = Some value /\ type_of_val value = Gtyp (Fuint 32).
Proof.
 intro Step.
 destruct (declared_unary_connection_observation 795 flat_statements rf_input_decl_786 rf_input_mid_786 rf_input_tail_786
 786 7937 (Uextr 31 0) 32 invalid flat_memories old current result
 rf_input_position_786 rf_input_split_786 rf_input_straight_786 rf_input_mid_safe_786 rf_input_tail_safe_786
 rf_input_nonregister_786 (Logic.eq_refl _) Step) as [source [value [Source [Adapt Value]]]].
 exists value. split; [exact Value|exact (adapted_uint_result_type source 32 value Adapt)].
Qed.
Theorem rf_internal_data_typed_after_two invalid old middle result :
 formal_value_iter invalid flat_memories old false old flat_statements = Some middle ->
 formal_value_iter invalid flat_memories middle false middle flat_statements = Some result ->
 exists value, VM.find 955 result = Some value /\ type_of_val value = Gtyp (Fuint 32).
Proof.
 intros First Second.
 destruct (rf_input_data_typed invalid old old middle First) as [value [Value Typed]].
 exists value. split; [|exact Typed].
 apply (rf_source_node_955 invalid middle middle result value); [exact Value|exact Typed|exact Second].
Qed.
Print Assumptions rf_internal_data_typed_after_two.
