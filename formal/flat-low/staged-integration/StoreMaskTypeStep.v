Require Import StoreMaskCommitCertificate FormalUIntRegisterCommitSource ScalarSinkTypes CoreSocModel ComparisonNodes.
From Coq Require Import NArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories.
Theorem store_mask_type_step invalid old current result old_value :
 VM.find 7924 old=Some old_value ->type_of_val old_value=Gtyp(Fuint 4) ->
 formal_value_iter invalid flat_memories old true current flat_statements=Some result ->
 exists value,VM.find 7924 result=Some value /\type_of_val value=Gtyp(Fuint 4).
Proof.
 intros Old Typed Step.
 destruct(formal_committed_uint_register_mux_observation 8430 flat_statements joint_register_7924_decl joint_register_7924_mid joint_register_7924_tail
 7924 joint_register_7924_reg (@Eref VarOrder.T(@Eid VarOrder.T 65)) (@Econst VarOrder.T(Fuint 1)[::false]) (@Eref VarOrder.T(@Eid VarOrder.T 80)) invalid flat_memories old current result old_value 4
 joint_register_7924_position joint_register_7924_split joint_register_7924_straight joint_register_7924_mid_safe joint_register_7924_tail_safe Old Typed joint_register_7924_identity Step)as[source[value[Eval[Adapt Value]]]].
 exists value. split;[exact Value|exact(adapted_uint_result_type source 4 value Adapt)].
Qed.
