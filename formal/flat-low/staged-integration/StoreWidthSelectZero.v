Require Import StoreWidthSelectNode CoreSocModel ComparisonNodes.
From Coq Require Import NArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Lemma store_width_select_zero invalid old current result previous :
 VM.find 7765 old=Some(Gval(Fuint 1)[::false]) ->
 VM.find 7754 old=Some previous ->type_of_val previous=Gtyp(Fuint 2) ->
 VM.find 91 old=Some(Gval(Fuint 2)(from_N 2 0)) ->
 formal_value_iter invalid flat_memories old false current flat_statements=Some result ->
 VM.find 7996 result=Some(Gval(Fuint 2)(from_N 2 0)).
Proof.
 intros Stall Previous Typed Decode Step.
 eapply(store_width_select_node_step 7996 store_width_select_expr_7996 invalid old current result).
 - unfold store_width_select_nodes. left;reflexivity.
 - intro site. cbn[store_width_select_expr_7996 eval_hfexpr_validif_policy eval_href_validif_policy].
   rewrite Stall. cbn. rewrite Decode.
   unfold eval_type_of_expr. cbn[type_of_expr' eval_type_of_ref]. rewrite Previous. cbn[option_map]. rewrite Typed. reflexivity.
 - exact Step.
Qed.
