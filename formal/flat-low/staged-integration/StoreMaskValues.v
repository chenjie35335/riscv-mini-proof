Require Import StoreMaskNodes CoreSocModel ComparisonNodes.
From Coq Require Import NArith List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Definition store_mask_byte (b:bool) := [::b;b;b;b;b;b;b;b].
Theorem store_mask_value_8008 invalid old current result b0 b1 b2 b3 :
 VM.find 7924 old=Some(Gval(Fuint 4)[::b0;b1;b2;b3]) ->
 formal_value_iter invalid flat_memories old false current flat_statements=Some result ->
 VM.find 8008 result=Some(Gval(Fuint 1)[::b0]).
Proof.
 intros Source Step. eapply(store_mask_node_step 8008 store_mask_expr_8008 invalid old current result).
 - unfold store_mask_nodes. left;reflexivity.
 - intro site. cbn[store_mask_expr_8008 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Source. destruct b0,b1,b2,b3;reflexivity.
 - exact Step.
Qed.
Theorem store_mask_value_8009 invalid old current result b0 :
 VM.find 8008 old=Some(Gval(Fuint 1)[::b0]) ->
 formal_value_iter invalid flat_memories old false current flat_statements=Some result ->
 VM.find 8009 result=Some(Gval(Fuint 8)(store_mask_byte b0)).
Proof.
 intros Source Step. eapply(store_mask_node_step 8009 store_mask_expr_8009 invalid old current result).
 - unfold store_mask_nodes. do 1 right. left;reflexivity.
 - intro site. cbn[store_mask_expr_8009 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Source. destruct b0;reflexivity.
 - exact Step.
Qed.
Theorem store_mask_value_8010 invalid old current result b0 b1 b2 b3 :
 VM.find 7924 old=Some(Gval(Fuint 4)[::b0;b1;b2;b3]) ->
 formal_value_iter invalid flat_memories old false current flat_statements=Some result ->
 VM.find 8010 result=Some(Gval(Fuint 1)[::b1]).
Proof.
 intros Source Step. eapply(store_mask_node_step 8010 store_mask_expr_8010 invalid old current result).
 - unfold store_mask_nodes. do 2 right. left;reflexivity.
 - intro site. cbn[store_mask_expr_8010 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Source. destruct b0,b1,b2,b3;reflexivity.
 - exact Step.
Qed.
Theorem store_mask_value_8011 invalid old current result b1 :
 VM.find 8010 old=Some(Gval(Fuint 1)[::b1]) ->
 formal_value_iter invalid flat_memories old false current flat_statements=Some result ->
 VM.find 8011 result=Some(Gval(Fuint 8)(store_mask_byte b1)).
Proof.
 intros Source Step. eapply(store_mask_node_step 8011 store_mask_expr_8011 invalid old current result).
 - unfold store_mask_nodes. do 3 right. left;reflexivity.
 - intro site. cbn[store_mask_expr_8011 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Source. destruct b1;reflexivity.
 - exact Step.
Qed.
Theorem store_mask_value_8012 invalid old current result b0 b1 b2 b3 :
 VM.find 7924 old=Some(Gval(Fuint 4)[::b0;b1;b2;b3]) ->
 formal_value_iter invalid flat_memories old false current flat_statements=Some result ->
 VM.find 8012 result=Some(Gval(Fuint 1)[::b2]).
Proof.
 intros Source Step. eapply(store_mask_node_step 8012 store_mask_expr_8012 invalid old current result).
 - unfold store_mask_nodes. do 4 right. left;reflexivity.
 - intro site. cbn[store_mask_expr_8012 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Source. destruct b0,b1,b2,b3;reflexivity.
 - exact Step.
Qed.
Theorem store_mask_value_8013 invalid old current result b2 :
 VM.find 8012 old=Some(Gval(Fuint 1)[::b2]) ->
 formal_value_iter invalid flat_memories old false current flat_statements=Some result ->
 VM.find 8013 result=Some(Gval(Fuint 8)(store_mask_byte b2)).
Proof.
 intros Source Step. eapply(store_mask_node_step 8013 store_mask_expr_8013 invalid old current result).
 - unfold store_mask_nodes. do 5 right. left;reflexivity.
 - intro site. cbn[store_mask_expr_8013 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Source. destruct b2;reflexivity.
 - exact Step.
Qed.
Theorem store_mask_value_8014 invalid old current result b0 b1 b2 b3 :
 VM.find 7924 old=Some(Gval(Fuint 4)[::b0;b1;b2;b3]) ->
 formal_value_iter invalid flat_memories old false current flat_statements=Some result ->
 VM.find 8014 result=Some(Gval(Fuint 1)[::b3]).
Proof.
 intros Source Step. eapply(store_mask_node_step 8014 store_mask_expr_8014 invalid old current result).
 - unfold store_mask_nodes. do 6 right. left;reflexivity.
 - intro site. cbn[store_mask_expr_8014 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Source. destruct b0,b1,b2,b3;reflexivity.
 - exact Step.
Qed.
Theorem store_mask_value_8015 invalid old current result b3 :
 VM.find 8014 old=Some(Gval(Fuint 1)[::b3]) ->
 formal_value_iter invalid flat_memories old false current flat_statements=Some result ->
 VM.find 8015 result=Some(Gval(Fuint 8)(store_mask_byte b3)).
Proof.
 intros Source Step. eapply(store_mask_node_step 8015 store_mask_expr_8015 invalid old current result).
 - unfold store_mask_nodes. do 7 right. left;reflexivity.
 - intro site. cbn[store_mask_expr_8015 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Source. destruct b3;reflexivity.
 - exact Step.
Qed.

Theorem store_mask_value_8016 invalid old current result a b :
 VM.find 8009 old=Some(Gval(Fuint 8)(store_mask_byte a)) ->
 VM.find 8011 old=Some(Gval(Fuint 8)(store_mask_byte b)) ->
 formal_value_iter invalid flat_memories old false current flat_statements=Some result ->
 VM.find 8016 result=Some(Gval(Fuint 16)(store_mask_byte a++store_mask_byte b)).
Proof.
 intros Low High Step. eapply(store_mask_node_step 8016 store_mask_expr_8016 invalid old current result).
 - unfold store_mask_nodes. do 8 right. left;reflexivity.
 - intro site. cbn[store_mask_expr_8016 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Low High. destruct a,b;reflexivity.
 - exact Step.
Qed.

Theorem store_mask_value_8017 invalid old current result a b :
 VM.find 8013 old=Some(Gval(Fuint 8)(store_mask_byte a)) ->
 VM.find 8015 old=Some(Gval(Fuint 8)(store_mask_byte b)) ->
 formal_value_iter invalid flat_memories old false current flat_statements=Some result ->
 VM.find 8017 result=Some(Gval(Fuint 16)(store_mask_byte a++store_mask_byte b)).
Proof.
 intros Low High Step. eapply(store_mask_node_step 8017 store_mask_expr_8017 invalid old current result).
 - unfold store_mask_nodes. do 9 right. left;reflexivity.
 - intro site. cbn[store_mask_expr_8017 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Low High. destruct a,b;reflexivity.
 - exact Step.
Qed.

Definition store_mask_word b0 b1 b2 b3 :=
 (store_mask_byte b0++store_mask_byte b1)++(store_mask_byte b2++store_mask_byte b3).
Theorem store_mask_value_8018 invalid old current result b0 b1 b2 b3 :
 VM.find 8016 old=Some(Gval(Fuint 16)(store_mask_byte b0++store_mask_byte b1)) ->
 VM.find 8017 old=Some(Gval(Fuint 16)(store_mask_byte b2++store_mask_byte b3)) ->
 formal_value_iter invalid flat_memories old false current flat_statements=Some result ->
 VM.find 8018 result=Some(Gval(Fuint 32)(store_mask_word b0 b1 b2 b3)).
Proof.
 intros Low High Step. eapply(store_mask_node_step 8018 store_mask_expr_8018 invalid old current result).
 - unfold store_mask_nodes. do 10 right. left;reflexivity.
 - intro site. cbn[store_mask_expr_8018 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Low High. destruct b0,b1,b2,b3;reflexivity.
 - exact Step.
Qed.
Theorem store_mask_four_steps invalid s0 s1 s2 s3 s4 b0 b1 b2 b3 :
 VM.find 7924 s0=Some(Gval(Fuint 4)[::b0;b1;b2;b3]) ->
 formal_value_iter invalid flat_memories s0 false s0 flat_statements=Some s1 ->
 formal_value_iter invalid flat_memories s1 false s1 flat_statements=Some s2 ->
 formal_value_iter invalid flat_memories s2 false s2 flat_statements=Some s3 ->
 formal_value_iter invalid flat_memories s3 false s3 flat_statements=Some s4 ->
 VM.find 8018 s4=Some(Gval(Fuint 32)(store_mask_word b0 b1 b2 b3)).
Proof.
 intros Source S1 S2 S3 S4.
 eapply store_mask_value_8018;[| |exact S4].
 - eapply store_mask_value_8016;[| |exact S3].
   + eapply store_mask_value_8009;[|exact S2]. eapply store_mask_value_8008; eassumption.
   + eapply store_mask_value_8011;[|exact S2]. eapply store_mask_value_8010; eassumption.
 - eapply store_mask_value_8017;[| |exact S3].
   + eapply store_mask_value_8013;[|exact S2]. eapply store_mask_value_8012; eassumption.
   + eapply store_mask_value_8015;[|exact S2]. eapply store_mask_value_8014; eassumption.
Qed.
