Require Import CoreSocModel ComparisonNodes JointUpdateConnectionCertificates FormalDeclaredConnectionObservation NormalizedBit.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Theorem early_control_wire_85_normalized invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value, VM.find 85 result = Some value /\ normalized_bit value.
Proof.
 intro Step.
 destruct (declared_connection_observation 62 flat_statements joint_update_connection_85_decl joint_update_connection_85_mid joint_update_connection_85_tail
 85 8251 1 invalid flat_memories old current result
 joint_update_connection_85_position joint_update_connection_85_split joint_update_connection_85_straight joint_update_connection_85_mid_safe joint_update_connection_85_tail_safe joint_update_connection_85_nonregister (Logic.eq_refl _) Step)
 as [source [value [Source [Adapt Value]]]].
 exists value. split; [exact Value|exact (adapted_bit_normalized source value Adapt)].
Qed.
Print Assumptions early_control_wire_85_normalized.
Theorem early_control_wire_1360_normalized invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value, VM.find 1360 result = Some value /\ normalized_bit value.
Proof.
 intro Step.
 destruct (declared_connection_observation 1438 flat_statements joint_update_connection_1360_decl joint_update_connection_1360_mid joint_update_connection_1360_tail
 1360 1392 1 invalid flat_memories old current result
 joint_update_connection_1360_position joint_update_connection_1360_split joint_update_connection_1360_straight joint_update_connection_1360_mid_safe joint_update_connection_1360_tail_safe joint_update_connection_1360_nonregister (Logic.eq_refl _) Step)
 as [source [value [Source [Adapt Value]]]].
 exists value. split; [exact Value|exact (adapted_bit_normalized source value Adapt)].
Qed.
Print Assumptions early_control_wire_1360_normalized.
