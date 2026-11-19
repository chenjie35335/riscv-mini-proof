Require Import StoreWriteCompareNode CoreSocModel ComparisonNodes.
From Coq Require Import NArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Lemma store_write_compare_zero invalid old current result :
 VM.find 8002 old=Some(Gval(Fuint 6)(from_N 6 0)) ->
 formal_value_iter invalid flat_memories old false current flat_statements=Some result ->
 VM.find 8027 result=Some(Gval(Fuint 1)[::false]).
Proof.
 intros Width Step. eapply(store_write_compare_node_step 8027 store_write_compare_expr_8027 invalid old current result).
 - unfold store_write_compare_nodes. left;reflexivity.
 - intro site. cbn[store_write_compare_expr_8027 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Width. reflexivity.
 - exact Step.
Qed.
