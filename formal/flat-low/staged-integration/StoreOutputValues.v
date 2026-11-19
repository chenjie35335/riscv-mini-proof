Require Import StoreOutputNodes CoreSocModel ComparisonNodes.
From Coq Require Import NArith List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Theorem store_output_mask_step invalid old current result word mask :
 VM.find 7925 old=Some(Gval(Fuint 32)word) ->
 VM.find 8018 old=Some(Gval(Fuint 32)mask) ->
 formal_value_iter invalid flat_memories old false current flat_statements=Some result ->
 VM.find 8038 result=Some(Gval(Fuint 32)(andB word mask)).
Proof.
 intros Word Mask Step. eapply(store_output_node_step 8038 store_output_expr_8038 invalid old current result).
 - unfold store_output_nodes. left;reflexivity.
 - intro site. cbn[store_output_expr_8038 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Word Mask. reflexivity.
 - exact Step.
Qed.
Theorem store_output_shift_step invalid old current result word offset :
 VM.find 8038 old=Some(Gval(Fuint 32)word) ->
 VM.find 8037 old=Some(Gval(Fuint 5)offset) ->
 formal_value_iter invalid flat_memories old false current flat_statements=Some result ->
 VM.find 8039 result=Some(Gval(Fuint 32)(zext_to 32(drop(to_nat offset)word))).
Proof.
 intros Word Offset Step. eapply(store_output_node_step 8039 store_output_expr_8039 invalid old current result).
 - unfold store_output_nodes. right;left;reflexivity.
 - intro site. cbn[store_output_expr_8039 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Word Offset. reflexivity.
 - exact Step.
Qed.
Theorem store_output_two_steps invalid s0 s1 s2 word mask offset :
 VM.find 7925 s0=Some(Gval(Fuint 32)word) ->
 VM.find 8018 s0=Some(Gval(Fuint 32)mask) ->
 VM.find 8037 s1=Some(Gval(Fuint 5)offset) ->
 formal_value_iter invalid flat_memories s0 false s0 flat_statements=Some s1 ->
 formal_value_iter invalid flat_memories s1 false s1 flat_statements=Some s2 ->
 VM.find 8039 s2=Some(Gval(Fuint 32)(zext_to 32(drop(to_nat offset)(andB word mask)))).
Proof.
 intros Word Mask Offset First Second.
 eapply store_output_shift_step;[eapply store_output_mask_step;eassumption|exact Offset|exact Second].
Qed.
