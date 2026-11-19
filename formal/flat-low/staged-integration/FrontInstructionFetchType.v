Require Import CoreSocModel ComparisonNodes JointUpdateConnectionCertificates FormalDeclaredConnectionObservation ScalarSinkTypes.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Theorem front_instruction_fetch_type invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists fetched, VM.find 75 result = Some fetched /\ type_of_val fetched = Gtyp (Fuint 32).
Proof.
 intro Step.
 destruct (declared_connection_observation 52 flat_statements joint_update_connection_75_decl
 joint_update_connection_75_mid joint_update_connection_75_tail 75 34 32 invalid flat_memories old current result
 joint_update_connection_75_position joint_update_connection_75_split joint_update_connection_75_straight
 joint_update_connection_75_mid_safe joint_update_connection_75_tail_safe joint_update_connection_75_nonregister
 (Logic.eq_refl true) Step) as [source [value [Source [Adapt Value]]]].
 exists value. split; [exact Value|]. eapply adapted_uint_result_type. exact Adapt.
Qed.
Print Assumptions front_instruction_fetch_type.
