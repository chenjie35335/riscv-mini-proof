Require Import StoreCheckerDataNodes StoreCheckerDataConnection ReferenceRedirectSemantics CoreSocModel ComparisonNodes.
From Coq Require Import NArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Theorem store_checker_data_value_8087 invalid old current result word :
 VM.find 8039 old=Some(Gval(Fuint 32)word) ->
 formal_value_iter invalid flat_memories old false current flat_statements=Some result ->
 VM.find 8087 result=Some(Gval(Fuint 32)word).
Proof.
 intros Source Step. eapply(store_checker_data_node_step 8087 store_checker_data_expr_8087 invalid old current result).
 - unfold store_checker_data_nodes. left;reflexivity.
 - intro site. cbn[store_checker_data_expr_8087 eval_hfexpr_validif_policy eval_href_validif_policy]. exact Source.
 - exact Step.
Qed.
Theorem store_checker_data_value_8088 invalid old current result word :
 VM.find 8087 old=Some(Gval(Fuint 32)word) ->
 formal_value_iter invalid flat_memories old false current flat_statements=Some result ->
 VM.find 8088 result=Some(Gval(Fuint 32)word).
Proof.
 intros Source Step. eapply(store_checker_data_node_step 8088 store_checker_data_expr_8088 invalid old current result).
 - unfold store_checker_data_nodes. do 1 right. left;reflexivity.
 - intro site. cbn[store_checker_data_expr_8088 eval_hfexpr_validif_policy eval_href_validif_policy]. exact Source.
 - exact Step.
Qed.
Theorem store_checker_data_value_8205 invalid old current result word :
 VM.find 8088 old=Some(Gval(Fuint 32)word) ->
 formal_value_iter invalid flat_memories old false current flat_statements=Some result ->
 VM.find 8205 result=Some(Gval(Fuint 32)word).
Proof.
 intros Source Step. eapply(store_checker_data_node_step 8205 store_checker_data_expr_8205 invalid old current result).
 - unfold store_checker_data_nodes. do 2 right. left;reflexivity.
 - intro site. cbn[store_checker_data_expr_8205 eval_hfexpr_validif_policy eval_href_validif_policy]. exact Source.
 - exact Step.
Qed.
Theorem store_checker_data_four_steps invalid s0 s1 s2 s3 s4 word :
 size word=32%nat ->
 VM.find 8039 s0=Some(Gval(Fuint 32)word) ->
 formal_value_iter invalid flat_memories s0 false s0 flat_statements=Some s1 ->
 formal_value_iter invalid flat_memories s1 false s1 flat_statements=Some s2 ->
 formal_value_iter invalid flat_memories s2 false s2 flat_statements=Some s3 ->
 formal_value_iter invalid flat_memories s3 false s3 flat_statements=Some s4 ->
 VM.find 1481 s4=Some(Gval(Fuint 32)word).
Proof.
 intros Size Source S1 S2 S3 S4.
 eapply(store_checker_data_connection_1481 invalid s3 s3 s4 (Gval(Fuint 32)word)).
 - eapply store_checker_data_value_8205;[|exact S3].
   eapply store_checker_data_value_8088;[|exact S2].
   eapply store_checker_data_value_8087;[exact Source|exact S1].
 - apply reference_redirect_adapt_word. exact Size.
 - exact S4.
Qed.
