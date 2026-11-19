Require Import StoreWidthCommitCertificate FormalUIntRegisterCommitSource ScalarSinkTypes CoreSocModel ComparisonNodes.
From Coq Require Import NArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories.
Theorem store_width_type_step invalid old current result old_value :
 VM.find 8040 old=Some old_value ->type_of_val old_value=Gtyp(Fuint 6) ->
 formal_value_iter invalid flat_memories old true current flat_statements=Some result ->
 exists value,VM.find 8040 result=Some value /\type_of_val value=Gtyp(Fuint 6).
Proof.
 intros Old Typed Step.
 destruct(formal_committed_uint_register_mux_observation 8546 flat_statements joint_register_8040_decl joint_register_8040_mid joint_register_8040_tail
 8040 joint_register_8040_reg (@Eref VarOrder.T(@Eid VarOrder.T 65)) (@Econst VarOrder.T(Fuint 1)[::false]) (@Eref VarOrder.T(@Eid VarOrder.T 8002)) invalid flat_memories old current result old_value 6
 joint_register_8040_position joint_register_8040_split joint_register_8040_straight joint_register_8040_mid_safe joint_register_8040_tail_safe Old Typed joint_register_8040_identity Step)as[source[value[Eval[Adapt Value]]]].
 exists value. split;[exact Value|exact(adapted_uint_result_type source 6 value Adapt)].
Qed.
