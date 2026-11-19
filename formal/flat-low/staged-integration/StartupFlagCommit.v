Require Import CoreSocModel ComparisonNodes JointRegisterCommits8 FormalExactRegisterDirectCommit.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Theorem startup_flag_commit invalid old current result old_value bit :
 VM.find 7762 old = Some old_value -> type_of_val old_value = Gtyp (Fuint 1) ->
 VM.find 7761 old = Some (Gval (Fuint 1) [::bit]) ->
 formal_value_iter invalid flat_memories old true current flat_statements = Some result ->
 VM.find 7762 result = Some (Gval (Fuint 1) [::bit]).
Proof.
 intros Old Typed Source Step.
 exact (exact_uint_register_direct_commit 8268 flat_statements joint_register_7762_decl joint_register_7762_mid joint_register_7762_tail
 7762 7761 joint_register_7762_reg 1 [::bit] old_value invalid flat_memories old current result
 joint_register_7762_position joint_register_7762_split joint_register_7762_straight
 joint_register_7762_mid_safe joint_register_7762_tail_safe joint_register_7762_identity
 Old Typed (Logic.eq_refl _) Source (Logic.eq_refl _) Step).
Qed.
Print Assumptions startup_flag_commit.
