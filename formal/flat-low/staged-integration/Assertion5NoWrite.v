Require Import WriteEnableNormalized Assertion5ResetGuard FormalNodeEquation NormalizedOr CoreSocModel ComparisonNodes.
From Coq Require Import NArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Lemma assertion5_disabled_no_write env bit :
 VM.find 7582 env=Some(Gval(Fuint 1)[::false]) ->
 VM.find 7589 env=Some(Gval(Fuint 1)[::bit]) ->generated_assert_m0_5_local env.
Proof.
 intros Valid Guard. unfold generated_assert_m0_5_local,generated_expr_true.
 cbn[eval_hfexpr eval_href]. rewrite Valid Guard. destruct bit;vm_compute;intro Impossible;discriminate Impossible.
Qed.
Lemma assertion5_no_write_step invalid old current result bit :
 VM.find 1478 old=Some(Gval(Fuint 1)[::false]) ->
 VM.find 1523 old=Some(Gval(Fuint 1)[::false]) ->
 VM.find 7589 result=Some(Gval(Fuint 1)[::bit]) ->
 formal_value_iter invalid flat_memories old false current flat_statements=Some result ->
 generated_assert_m0_5_local result.
Proof.
 intros DUT Reference Guard Step. apply(assertion5_disabled_no_write result bit);[|exact Guard].
 rewrite(formal_combinational_node_equation _ _ _ _ _ invalid flat_memories old current result write_valid_or_position write_valid_or_suffix write_valid_or_nonregister Step).
 unfold write_valid_or_expression. cbn[eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite DUT Reference. reflexivity.
Qed.
