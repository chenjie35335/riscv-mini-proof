Require Import StoreWriteValidNodes CoreSocModel ComparisonNodes.
From Coq Require Import NArith List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Lemma store_write_valid_false_8030 invalid old current result bit :
 VM.find 8028 old=Some(Gval(Fuint 1)[::false]) ->
 VM.find 8029 old=Some(Gval(Fuint 1)[::bit]) ->
 formal_value_iter invalid flat_memories old false current flat_statements=Some result ->
 VM.find 8030 result=Some(Gval(Fuint 1)[::false]).
Proof.
 intros Source Guard Step. eapply(store_write_valid_node_step 8030 store_write_valid_expr_8030 invalid old current result).
 - unfold store_write_valid_nodes. left;reflexivity.
 - intro site. cbn[store_write_valid_expr_8030 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Source Guard. destruct bit;reflexivity.
 - exact Step.
Qed.
Lemma store_write_valid_false_8081 invalid old current result :
 VM.find 8030 old=Some(Gval(Fuint 1)[::false]) ->
 formal_value_iter invalid flat_memories old false current flat_statements=Some result ->
 VM.find 8081 result=Some(Gval(Fuint 1)[::false]).
Proof.
 intros Source Step. eapply(store_write_valid_node_step 8081 store_write_valid_expr_8081 invalid old current result).
 - unfold store_write_valid_nodes. do 1 right. left;reflexivity.
 - intro site. cbn[store_write_valid_expr_8081 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Source. reflexivity.
 - exact Step.
Qed.
Lemma store_write_valid_false_8082 invalid old current result :
 VM.find 8081 old=Some(Gval(Fuint 1)[::false]) ->
 formal_value_iter invalid flat_memories old false current flat_statements=Some result ->
 VM.find 8082 result=Some(Gval(Fuint 1)[::false]).
Proof.
 intros Source Step. eapply(store_write_valid_node_step 8082 store_write_valid_expr_8082 invalid old current result).
 - unfold store_write_valid_nodes. do 2 right. left;reflexivity.
 - intro site. cbn[store_write_valid_expr_8082 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Source. reflexivity.
 - exact Step.
Qed.
Lemma store_write_valid_false_8202 invalid old current result :
 VM.find 8082 old=Some(Gval(Fuint 1)[::false]) ->
 formal_value_iter invalid flat_memories old false current flat_statements=Some result ->
 VM.find 8202 result=Some(Gval(Fuint 1)[::false]).
Proof.
 intros Source Step. eapply(store_write_valid_node_step 8202 store_write_valid_expr_8202 invalid old current result).
 - unfold store_write_valid_nodes. do 3 right. left;reflexivity.
 - intro site. cbn[store_write_valid_expr_8202 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Source. reflexivity.
 - exact Step.
Qed.
