Require Import StoreOutputOffsetNodes CoreSocModel ComparisonNodes.
From Coq Require Import NArith List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Definition store_output_offset_word b0 b1 := [::false;false;false;b0;b1].
Theorem store_output_offset_value_8031 invalid old current result b0 b1 tail :
 VM.find 8004 old=Some(Gval(Fuint 32)(b0::b1::tail)) ->
 formal_value_iter invalid flat_memories old false current flat_statements=Some result ->
 VM.find 8031 result=Some(Gval(Fuint 2)[::b0;b1]).
Proof.
 intros H0 Step.
 eapply(store_output_offset_node_step 8031 store_output_offset_expr_8031 invalid old current result).
 - unfold store_output_offset_nodes. left;reflexivity.
 - intro site. cbn[store_output_offset_expr_8031 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite H0. destruct b0,b1;cbn[eval_unop];rewrite !take_cons ?take0;reflexivity.
 - exact Step.
Qed.
Theorem store_output_offset_value_8032 invalid old current result b0 b1 :
 VM.find 8031 old=Some(Gval(Fuint 2)[::b0;b1]) ->
 formal_value_iter invalid flat_memories old false current flat_statements=Some result ->
 VM.find 8032 result=Some(Gval(Fuint 1)[::b0 && ~~b1]).
Proof.
 intros H0 Step.
 eapply(store_output_offset_node_step 8032 store_output_offset_expr_8032 invalid old current result).
 - unfold store_output_offset_nodes. do 1 right. left;reflexivity.
 - intro site. cbn[store_output_offset_expr_8032 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite H0. destruct b0,b1;reflexivity.
 - exact Step.
Qed.
Theorem store_output_offset_value_8034 invalid old current result b0 b1 :
 VM.find 8031 old=Some(Gval(Fuint 2)[::b0;b1]) ->
 formal_value_iter invalid flat_memories old false current flat_statements=Some result ->
 VM.find 8034 result=Some(Gval(Fuint 1)[::~~b0 && b1]).
Proof.
 intros H0 Step.
 eapply(store_output_offset_node_step 8034 store_output_offset_expr_8034 invalid old current result).
 - unfold store_output_offset_nodes. do 3 right. left;reflexivity.
 - intro site. cbn[store_output_offset_expr_8034 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite H0. destruct b0,b1;reflexivity.
 - exact Step.
Qed.
Theorem store_output_offset_value_8036 invalid old current result b0 b1 :
 VM.find 8031 old=Some(Gval(Fuint 2)[::b0;b1]) ->
 formal_value_iter invalid flat_memories old false current flat_statements=Some result ->
 VM.find 8036 result=Some(Gval(Fuint 1)[::b0 && b1]).
Proof.
 intros H0 Step.
 eapply(store_output_offset_node_step 8036 store_output_offset_expr_8036 invalid old current result).
 - unfold store_output_offset_nodes. do 5 right. left;reflexivity.
 - intro site. cbn[store_output_offset_expr_8036 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite H0. destruct b0,b1;reflexivity.
 - exact Step.
Qed.
Theorem store_output_offset_value_8033 invalid old current result b0 b1 :
 VM.find 8032 old=Some(Gval(Fuint 1)[::b0 && ~~b1]) ->
 formal_value_iter invalid flat_memories old false current flat_statements=Some result ->
 VM.find 8033 result=Some(Gval(Fuint 4)[::false;false;false;b0 && ~~b1]).
Proof.
 intros H0 Step.
 eapply(store_output_offset_node_step 8033 store_output_offset_expr_8033 invalid old current result).
 - unfold store_output_offset_nodes. do 2 right. left;reflexivity.
 - intro site. cbn[store_output_offset_expr_8033 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite H0. destruct b0,b1;reflexivity.
 - exact Step.
Qed.
Theorem store_output_offset_value_8035 invalid old current result b0 b1 :
 VM.find 8034 old=Some(Gval(Fuint 1)[::~~b0 && b1]) ->
 VM.find 8033 old=Some(Gval(Fuint 4)[::false;false;false;b0 && ~~b1]) ->
 formal_value_iter invalid flat_memories old false current flat_statements=Some result ->
 VM.find 8035 result=Some(Gval(Fuint 5)[::false;false;false;b0 && ~~b1;~~b0 && b1]).
Proof.
 intros H0 H1 Step.
 eapply(store_output_offset_node_step 8035 store_output_offset_expr_8035 invalid old current result).
 - unfold store_output_offset_nodes. do 4 right. left;reflexivity.
 - intro site. cbn[store_output_offset_expr_8035 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite H0 H1. unfold eval_type_of_expr. cbn[type_of_expr' eval_type_of_ref]. rewrite H1. destruct b0,b1;reflexivity.
 - exact Step.
Qed.
Theorem store_output_offset_value_8037 invalid old current result b0 b1 :
 VM.find 8036 old=Some(Gval(Fuint 1)[::b0 && b1]) ->
 VM.find 8035 old=Some(Gval(Fuint 5)[::false;false;false;b0 && ~~b1;~~b0 && b1]) ->
 formal_value_iter invalid flat_memories old false current flat_statements=Some result ->
 VM.find 8037 result=Some(Gval(Fuint 5)(store_output_offset_word b0 b1)).
Proof.
 intros H0 H1 Step.
 eapply(store_output_offset_node_step 8037 store_output_offset_expr_8037 invalid old current result).
 - unfold store_output_offset_nodes. do 6 right. left;reflexivity.
 - intro site. cbn[store_output_offset_expr_8037 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite H0 H1. unfold eval_type_of_expr. cbn[type_of_expr' eval_type_of_ref]. rewrite H1. destruct b0,b1;reflexivity.
 - exact Step.
Qed.
Require Import StoreOffsetValue.
Lemma store_input_output_offset_equal b0 b1 :
 to_nat(store_output_offset_word b0 b1)=to_nat(store_offset_word b0 b1).
Proof. destruct b0,b1;reflexivity. Qed.
