Require Import StoreOffsetNodes CoreSocModel ComparisonNodes.
From Coq Require Import NArith List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Definition store_offset_word b0 b1 := [::false;false;false;b0;b1;false;false;false].
Theorem store_offset_join invalid old current result b0 b1 :
 VM.find 7828 old=Some(Gval(Fuint 8)[::false;false;false;false;b1;false;false;false]) ->
 VM.find 7830 old=Some(Gval(Fuint 4)[::false;false;false;b0]) ->
 formal_value_iter invalid flat_memories old false current flat_statements=Some result ->
 VM.find 7831 result=Some(Gval(Fuint 8)(store_offset_word b0 b1)).
Proof.
 intros High Low Step. eapply(store_offset_node_step 7831 store_offset_expr_7831 invalid old current result).
 - unfold store_offset_nodes. do 4 right. left;reflexivity.
 - intro site. cbn[store_offset_expr_7831 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite High Low. destruct b0,b1;reflexivity.
 - exact Step.
Qed.

Theorem store_offset_shift_7828 invalid old current result b1 :
 VM.find 7827 old=Some(Gval(Fuint 1)[::b1]) ->
 formal_value_iter invalid flat_memories old false current flat_statements=Some result ->
 VM.find 7828 result=Some(Gval(Fuint 8)[::false;false;false;false;b1;false;false;false]).
Proof.
 intros Source Step. eapply(store_offset_node_step 7828 store_offset_expr_7828 invalid old current result).
 - unfold store_offset_nodes. do 1 right. left;reflexivity.
 - intro site. cbn[store_offset_expr_7828 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Source. destruct b1;reflexivity.
 - exact Step.
Qed.

Theorem store_offset_shift_7830 invalid old current result b0 :
 VM.find 7829 old=Some(Gval(Fuint 1)[::b0]) ->
 formal_value_iter invalid flat_memories old false current flat_statements=Some result ->
 VM.find 7830 result=Some(Gval(Fuint 4)[::false;false;false;b0]).
Proof.
 intros Source Step. eapply(store_offset_node_step 7830 store_offset_expr_7830 invalid old current result).
 - unfold store_offset_nodes. do 3 right. left;reflexivity.
 - intro site. cbn[store_offset_expr_7830 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Source. destruct b0;reflexivity.
 - exact Step.
Qed.

Theorem store_offset_extract_7827 invalid old current result b0 b1 tail :
 VM.find 1155 old=Some(Gval(Fuint 32)(b0::b1::tail)) ->
 formal_value_iter invalid flat_memories old false current flat_statements=Some result ->
 VM.find 7827 result=Some(Gval(Fuint 1)[::b1]).
Proof.
 intros Source Step. eapply(store_offset_node_step 7827 store_offset_expr_7827 invalid old current result).
 - unfold store_offset_nodes. left;reflexivity.
 - intro site. cbn[store_offset_expr_7827 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Source. cbn [eval_unop]. rewrite !take_cons ?take0. reflexivity.
 - exact Step.
Qed.

Theorem store_offset_extract_7829 invalid old current result b0 b1 tail :
 VM.find 1155 old=Some(Gval(Fuint 32)(b0::b1::tail)) ->
 formal_value_iter invalid flat_memories old false current flat_statements=Some result ->
 VM.find 7829 result=Some(Gval(Fuint 1)[::b0]).
Proof.
 intros Source Step. eapply(store_offset_node_step 7829 store_offset_expr_7829 invalid old current result).
 - unfold store_offset_nodes. do 2 right. left;reflexivity.
 - intro site. cbn[store_offset_expr_7829 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Source. cbn [eval_unop]. rewrite !take_cons ?take0. reflexivity.
 - exact Step.
Qed.

Theorem store_offset_three_steps invalid s0 s1 s2 s3 b0 b1 tail :
 VM.find 1155 s0=Some(Gval(Fuint 32)(b0::b1::tail)) ->
 formal_value_iter invalid flat_memories s0 false s0 flat_statements=Some s1 ->
 formal_value_iter invalid flat_memories s1 false s1 flat_statements=Some s2 ->
 formal_value_iter invalid flat_memories s2 false s2 flat_statements=Some s3 ->
 VM.find 7831 s3=Some(Gval(Fuint 8)(store_offset_word b0 b1)).
Proof.
 intros Address Step1 Step2 Step3.
 eapply store_offset_join; [| |exact Step3].
 - eapply store_offset_shift_7828; [|exact Step2].
   eapply store_offset_extract_7827; eassumption.
 - eapply store_offset_shift_7830; [|exact Step2].
   eapply store_offset_extract_7829; eassumption.
Qed.
