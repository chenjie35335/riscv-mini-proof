From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From nbits Require Import NBits.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Definition mux_word (bit : bool) (left right : seq bool) :=
 zext_to 32 (take 32 (if bit then left else right)).
Lemma mux_word_size bit left right : size (mux_word bit left right) = 32.
Proof.
 unfold mux_word, zext_to. rewrite size_zext addnC subnK; [reflexivity|].
 rewrite size_take. exact (geq_minl 32 _).
Qed.
Lemma exact_word_mux mm old (condition yes no : VarOrder.T) bit left right :
 VM.find condition old = Some (Gval (Fuint 1) [::bit]) ->
 VM.find yes old = Some (Gval (Fuint 32) left) ->
 VM.find no old = Some (Gval (Fuint 32) right) ->
 eval_hfexpr_with_memory mm
 (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T condition))
 (@Eref VarOrder.T (@Eid VarOrder.T yes)) (@Eref VarOrder.T (@Eid VarOrder.T no))) old old =
 Some (Gval (Fuint 32) (mux_word bit left right)).
Proof.
 intros Condition Left Right. cbn [eval_hfexpr_with_memory eval_href_with_memory]. rewrite Condition.
 destruct bit; cbn [is_zero eval_hfexpr_with_memory eval_href_with_memory];
 unfold eval_type_of_expr; cbn [type_of_expr' eval_type_of_ref]; rewrite Left Right; reflexivity.
Qed.
Print Assumptions exact_word_mux.
