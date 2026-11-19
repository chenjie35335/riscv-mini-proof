Require Import CoreSocModel ComparisonNodes LegalAssumptionConnections NormalizedBit.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Theorem legal_wire_45_normalized invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value, VM.find 45 result = Some value /\ normalized_bit value.
Proof.
 intro Step.
 destruct (legal_connection_45_observation invalid old current result Step)
 as [source [value [Source [Adapt Value]]]].
 exists value. split; [exact Value|exact (adapted_bit_normalized source value Adapt)].
Qed.
Theorem legal_wire_63_normalized invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value, VM.find 63 result = Some value /\ normalized_bit value.
Proof.
 intro Step.
 destruct (legal_connection_63_observation invalid old current result Step)
 as [source [value [Source [Adapt Value]]]].
 exists value. split; [exact Value|exact (adapted_bit_normalized source value Adapt)].
Qed.
Theorem legal_wire_100_normalized invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value, VM.find 100 result = Some value /\ normalized_bit value.
Proof.
 intro Step.
 destruct (legal_connection_100_observation invalid old current result Step)
 as [source [value [Source [Adapt Value]]]].
 exists value. split; [exact Value|exact (adapted_bit_normalized source value Adapt)].
Qed.
Print Assumptions legal_wire_45_normalized.
